/*
 *------------------------------------------------------------------------
     Code that notes stack pointers and copies stacks fragments

  This code deals exclusively with exception frames, and stack fragments
  between two exception frames in byte-code OCaml.

  In OCaml, stacks grow downwards, from caml_stack_high to caml_stack_low
  (actually, until the threshold, after which the stack is reallocated).
  The bottom (most recent) exception frame is pointed to by caml_trapsp.
  The other exception frames are reachable via Trap_link(ef) field.

  See byterun/stacks.c, byterun/stacks.h and especially 
  byterun/interp.c

  The present code is a slight modification of 
  caml_realloc_stack() in byterun/stacks.c
  Indeed, Caml already copies stacks and adjusts trapsp. We also use
  a great deal of code from callcc.c by Xavier Leroy.

  This file also supports two abstract data types: |ek| for exception frame
  pointers, and |ekfragment| for the stack fragment between two exception
  frames. These data types are used in delimcc.ml

  The type ek is actually int, or to be more precise, Value_int()
  from the OCaml point of view and ptrdiff_t from the C point of view.
  The pointer difference is in the units of `value'. Because `value'
  has a sufficient size to hold a pointer, ptrdiff_t in units of value
  will definitely fit within value even taking the tag bit into account.
  
  ek is the relative exception frame pointer, the base being either
  caml_stack_high or the top (least recent) of the copied fragment.
  The pointer must be relative because the stack can be
  reallocated and because we copy the stack ourselves.
  The reallocation cannot occur while the control is in any of the functions
  of this file (re-allocation may only occur only on APPLY and similar
  bytecode instruction).

  ekfragment is the copy of a part of the stack, from
  some trapsp up to (but not including) some other exception frame
  down the Trap_link

  NB: caml_trace_flag...

  This code also supports serialization of captured delimited continuations,
  specifically, `relativization' of captured continuations to replace
  references to closures in global data with `indices'. We introduce
  a new abstract data type global_data_idx for that purpose. See more comments
  in delimcc.ml.

  $Id: stacks.c,v 1.5 2006/02/02 01:29:28 oleg Exp $

 *------------------------------------------------------------------------
 */

#include <string.h>
#include "misc.h"
#include <alloc.h>
#include "memory.h"
#include <mlvalues.h>
#include <stacks.h>

/* needed for the debugging printing of values */
#include <custom.h>
#include <intext.h>

/* For debugging */
#include <stdio.h>

#define DEBUG_SER 0

/* In OCaml 3.11, Is_atom disappeared. We emulate: */
#if !defined(Is_atom)
#define Is_atom(v) (Is_block(v) && Wosize_val(v) == 0)
#endif

#if !defined(Is_in_value_area)
#define Is_in_value_area(v) (Is_young(v) || Is_in_heap(v))
#endif

#if !defined(Is_in_heap_or_young)
#define Is_in_heap_or_young(v) (Is_young(v) || Is_in_heap(v))
#endif

#if defined(Classify_addr)
#define Is_code_ptr(a) (Classify_addr(a) & In_code_area)
#else
#define Is_code_ptr(a) ((char *) v >= caml_code_area_start && \
	                (char *) v < caml_code_area_end)
#endif

/* Under no circumstances EVER EVER EVER should assert be disabled!!! */

#define myassert(x) ((x) ? 1 : \
  (fprintf(stderr, "\nFailed assert %s in %s at %d\n", #x,__FILE__, __LINE__),\
  exit(8)))


/* Print the information about Caml interpreter stacks */
static void print_gl_stack(char * title)
{
  fprintf(stderr, "\n%s\n",title);
  fprintf(stderr, "caml_stack_low       %p\n", caml_stack_low);
  fprintf(stderr, "caml_stack_high      %p\n", caml_stack_high);
  fprintf(stderr, "caml_stack_threshold %p\n", caml_stack_threshold);
  fprintf(stderr, "caml_extern_sp       %p\n", caml_extern_sp);
  fprintf(stderr, "caml_trapsp          %p\n", caml_trapsp);
}

/* Walk the trapsp link */
static void print_exc_trace(char * title)
{
  value * p;
  fprintf(stderr, "\nexc_trace: %s\n",title);
  fprintf(stderr, "caml_trapsp          %p\n", caml_trapsp);
  for(p = caml_trapsp; p < caml_stack_high; p = Trap_link(p))
    fprintf(stderr, "  %p\n",p);
}

/* Get the current value of trapsp (relative to caml_stack_high)
*/
value get_trapsp(value unit)
{
  myassert(caml_extern_sp >= caml_stack_low);
  myassert(caml_extern_sp <= caml_stack_high);
  myassert(caml_trapsp    <= caml_stack_high);

  return Val_long(caml_stack_high - caml_trapsp);
}

/* Print out the value of trapsp */
value dbg_print_trapsp(value k)
{
  const ptrdiff_t t = Long_val(k);
  value * const captured_k = caml_stack_high - t;
  print_gl_stack("dbg_print_trapsp");
  fprintf(stderr, "captured k %p (%x)\n",captured_k,t);
  return Val_unit;
}


/* add_trapsp (ek1,ek2) --> ek1 + ek2
*/
value add_trapsp(value block_twok)
{
  const value ek1v = Field(block_twok, 0);
  const value ek2v = Field(block_twok, 1);

  return Val_long(Long_val(ek1v) + Long_val(ek2v));
}

/* sub_trapsp (ek1,ek2) --> ek1 - ek2
*/
value sub_trapsp(value block_twok)
{
  const ptrdiff_t ek1 = Long_val(Field(block_twok, 0));
  const ptrdiff_t ek2 = Long_val(Field(block_twok, 1));

  myassert( ek1 >= ek2 );

  return Val_long(ek1 - ek2);
}


/*
  external pop_stack_fragment : ek1 -> ek2 -> ekfragment
  Copy the stack between ek1 and ek2: from ek2 upwards but not including
  ek1. Return the fragment of stack.
  Reset caml_trapsp to be ek1.
  ek2 must be already set on the trap...

  This code is largely based on callcc.c by Xavier Leroy.
*/

value pop_stack_fragment(value vek1, value vek2)
{
  const ptrdiff_t ek1 = Long_val(vek1);
  const ptrdiff_t ek2 = Long_val(vek2);
  value * const tp1 = caml_stack_high - ek1;
  value * const tp2 = caml_stack_high - ek2;
  value *p, *q;
  mlsize_t size, i;
  value block;

  myassert(tp2 < tp1);		/* stack grows downwards */
  size = tp1 - tp2;		/* tp2 is more recent ptr */

  /*
  print_gl_stack("pop_stack_fragment");
  fprintf(stderr, "between %p and %p (size %ld)\n",tp2,tp1,size);
  print_exc_trace("pop_stack_fragment: before");
  */

  if (size < Max_young_wosize) {
    block = alloc(size, 0);
    memcpy(&Field(block, 0), tp2, size * sizeof(value));
  } else {
    block = alloc_shr(size, 0);
    for (i = 0; i < size; i++)
      initialize(&Field(block, i), tp2[i]);
  }

  /* We check the invariants after the allocation of block, which may
     cause a GC run. Stack should not be moved though. */
  myassert(caml_extern_sp >= caml_stack_low);
  myassert(caml_extern_sp <= caml_stack_high);
  myassert(caml_trapsp    < caml_stack_high);
  myassert(tp1            < caml_stack_high);
  myassert(caml_trapsp    == tp2);
  myassert(caml_extern_sp <  tp2);

  /* Check the invariant that tp1 must occur somewhere in the Trap_link
     chain
  */
  for(p=caml_trapsp; p == tp1; p = Trap_link(p))
    if( !(p < caml_stack_high) )
      { print_gl_stack("ERROR: tp1 is not found in the Trap_link chain!!!");
        print_exc_trace("ERROR: tp1 is not found...");
        myassert(0);
      }
      
  /* Adjust the links in the copied code: make them relative to
     tp2: the bottom of the copied stack
  */
  p = tp2;
  while (1) {
    myassert( p < caml_stack_high );
    q = Trap_link(p);
    if (q == tp1)
    {
      /* end of the chain */
      Field(block, (value*)(&(Trap_link(p))) - tp2) = Val_long(0);
      break;
    }
    Field(block, (value*)(&(Trap_link(p))) - tp2) = Val_long(q - tp2);
    p = q;
  }
  caml_trapsp = tp1;		/* Reset the chain */
  return block;
}


/*
  external reset_trapsp : ek -> unit
  Set caml_trapsp to an earlier value that corresponds to ek.
  The next raise will drop then the stack fragment till ek.
  This code makes abort essentially just as efficient as raise.
*/

value reset_trapsp(value val_ek)
{
  value * const tp = caml_stack_high - Long_val(val_ek);
  value *p;

  /*
  print_gl_stack("reset_trapsp");
  fprintf(stderr, "to %p\n",tp);
  print_exc_trace("reset_trapsp: before");
  */

  /* We check the invariants */
  myassert(caml_extern_sp >= caml_stack_low);
  myassert(caml_extern_sp <= caml_stack_high);
  myassert(caml_trapsp    <  caml_stack_high);
  myassert(tp             >= caml_trapsp);
  myassert(caml_extern_sp <  tp);

  /* Check the invariant that tp must occur somewhere in the Trap_link
     chain
  */
  for(p=caml_trapsp; p == tp; p = Trap_link(p))
    if( !(p < caml_stack_high) )
    { print_gl_stack("ERROR: tp is not found in the Trap_link chain!!!");
      print_exc_trace("ERROR: tp is not found...");
      myassert(0);
    }
      
  caml_trapsp = tp;		/* Reset the chain */
  return Val_unit;
}


/*
  push the stack fragment between the caml_extern_sp and caml_trapsp
  so that the current exception frame links to the top of the
  pushed fragment.
  Set caml_trapsp to the bottom of the pushed fragment.
  The stack fragment is a part of the stack between two exception
  frames (exclusive of the top, inclusive of the bottom frames).

  This code is largely based on callcc.c by Xavier Leroy.
*/

value push_stack_fragment(value ekfragment)
{
  const mlsize_t size = Wosize_val(ekfragment);
  value *p, *new_sp, *new_trapsp;

  /*
  print_gl_stack("push_stack_fragment");
  print_exc_trace("push_stack_fragment: before");
  */

  myassert(caml_extern_sp >= caml_stack_low);
  myassert(caml_extern_sp <= caml_stack_high);
  myassert(caml_trapsp    < caml_stack_high);
  myassert(caml_trapsp    > caml_extern_sp);

  if( caml_extern_sp - size < caml_stack_threshold )
  {
    print_gl_stack("push_stack_fregment: no stack space! Have I forgotten"
		   " to call ensure_stack_space?");
    myassert(0);
  #if 0
    /* Old way, pre 3.11: */
    print_gl_stack("Reallocating OCaml stack!");
       caml_realloc_stack(Stack_threshold / sizeof(value)); */
    return push_stack_fragment(ekfragment); /* Redo */
  #endif
  }

  new_sp = caml_extern_sp - size;
  new_trapsp = caml_trapsp - size;
  memmove(new_sp, caml_extern_sp, 
	          (caml_trapsp - caml_extern_sp) * sizeof(value));
  memcpy(new_trapsp, &Field(ekfragment,0), size * sizeof(value));

  /* adjust the links of exc frames (convert to abs addresses)
     and connect the copied frames to the existing frames
  */
  for (p = new_trapsp; (value)Trap_link(p) != Val_long(0); p = Trap_link(p)) {
    myassert( p < caml_stack_high );
    Trap_link(p) = new_trapsp + Long_val((value) Trap_link(p));
  }
  Trap_link(p) = caml_trapsp;
  caml_extern_sp = new_sp;
  caml_trapsp    = new_trapsp;

  /*
  print_exc_trace("push_stack_fragment: after");
  */
  return Val_unit;
}

value size_stack_fragment(value ekfragment)
{
  return Val_long(Wosize_val(ekfragment));
}

/*
 * Simple routines to write a string to stderr or to report an error
   and quit.
   We use these routines rather than OCaml's own print_endline
   to avoid dealing with OCaml's channels, etc. and triggering other errors
   along the way.
 */

value dbg_fatal_error(value message)
{
  myassert(Is_block(message) && Tag_val(message) == String_tag);
  caml_fatal_error(String_val(message));
  return Val_unit;		/* Doesn't return, actually */
}

value dbg_note(value message)
{
  myassert(Is_block(message) && Tag_val(message) == String_tag);
  fprintf(stderr,"%s\n",String_val(message));
  return Val_unit;
}

/*
 * More debuging support.
 * Given a value, print out the information about it.
 * Return TRUE if the value contains traversable components
 */
 
value describe_value(value v)
{
  if(Is_long(v))
  {
    fprintf(stderr,"int %ld\n",Long_val(v));
    return Val_false;
  }
  else if( Is_atom(v) )
  {
    fprintf(stderr,"atom %d\n",Tag_val(v));
    return Val_false;
  }
  else if ( Is_code_ptr(v) ) {
    fprintf(stderr,"code ptr %p\n",(void *)v);
    return Val_false;
  }
  else if( !Is_in_value_area(v) )
  {
    fprintf(stderr,"ptr outside OCaml %p\n",(void *)v);
    return Val_false;
  }
  else
  {
    const mlsize_t size = Wosize_val(v);
    const tag_t tag = Tag_val(v);
    fprintf(stderr,"%s tag %d size %lu",
	   (Is_young(v) ? "young" : "old"), tag, size);
    switch(tag)
    {
    case String_tag:
      fprintf(stderr," string `%s'",String_val(v));
      break;

    case Double_tag:
      fprintf(stderr," double %g",*((double *)v));
      break;

    case Double_array_tag:
      fprintf(stderr," double array of %lu elems",size/Double_wosize);
      break;

    case Infix_tag:
      fprintf(stderr," infix");
      break;

    case Abstract_tag:
      fprintf(stderr," abstract");
      break;

    case Custom_tag:
      fprintf(stderr," custom %s",Custom_ops_val(v)->identifier);
      break;
    }
    fprintf(stderr,"\n");
    return tag < No_scan_tag ? Val_true : Val_false;
  }
}


/*
 * Relativitize val
 * This has to be C code, particularly written to perform no allocations
 * whatsoever, so not to trigger GC. Only then updating the values in place
 * is safe.
 * Return the (possibly updated inplace) value.
 * That value must be quickly serialized, and then restored (absolutized),
 * because we might have disturbed the closures that are are not
 * only captured in continuations but also used elsewhere.
 * In the recoding mode, we do not do any updates.
 */


/* Locate the closure in the global array. Return either
   global_data_idx value, or Val_false
   If arr_update_flag is true, we add the closure to the table
   if we did not find it. Empty elements in the array are marked by
   Val_long(0)
*/
static value rel_closure(value global_data_arr, value arr_update_flag, value v)
{
  const mlsize_t size = Wosize_val(global_data_arr);
  mlsize_t i = 0;

#if defined(DEBUG_SER) && DEBUG_SER
  fprintf(stderr,"Trying to relativitize closure %p, code ptr %p\n",
	  (void *)v,(void*)(Field(v,0)));
#endif

  for(i=0; i<size; i++)
  {
    const value f = Field(global_data_arr,i);
    if( Field(f,0) == v )
    {
      fprintf(stderr,"Found at idx %lu\n",i);
      return Field(f,1);
    }
    if( Field(f,0) == Val_long(0) ) /* empty slot */
    { if( arr_update_flag == Val_true )
      {
	fprintf(stderr,"Recording at idx %lu\n",i);
	myassert( Is_in_heap(v) );	/* must be in the old heap */
	Modify(&(Field(f,0)),v);
	/* return Field(f,1); */
	return Val_false;    /* Traverse the recorded closure nevertheless */
      }
      else return Val_false;
    }
  }
  return Val_false;
}


/* We use the explicit stack rather than recursive calls, because
   we wish to check for cycles, which are quite possible during the
   traversal.
*/

static struct rel_rec_cont_t
{
  value rr_v;				/* value being traversed */
  mlsize_t rr_i; 			/* field being traversed */
} rel_rec_cont [15];			/* max depth */
static int rel_rec_cont_cnt = 0;
static const int rel_rec_cont_max = 
  sizeof(rel_rec_cont)/sizeof(rel_rec_cont[0]);

static void print_rel_rec_cont(void)
{
  int i = 0;
  for(i=0; i<rel_rec_cont_cnt; i++)
  {
    fprintf(stderr,"Field %lu of ",rel_rec_cont[i].rr_i);
    if( describe_value(rel_rec_cont[i].rr_v) == Val_true &&
	Tag_val(rel_rec_cont[i].rr_v) == Closure_tag)
      fprintf(stderr, "  closure, code ptr %p\n",
	      Code_val(rel_rec_cont[i].rr_v));
  }
}

static value rel_rec(value global_data_arr, value arr_update_flag, value v) 
{
 tailcall:
  if(Is_long(v) || Is_atom(v) || !Is_in_value_area(v) )
    goto finish;

#if defined(DEBUG_SER) && DEBUG_SER
  fprintf(stderr, "examining %p, first field %p size %lu tag %d young %d\n",
	  (void*)v,(void*)(Wosize_val(v) == 0 ? 0 : Field(v,0)),
	  Wosize_val(v), Tag_val(v), Is_young(v));
#endif

  if(Tag_val(v) == Custom_tag &&
     strcmp(Custom_ops_val(v)->identifier,"delimcc_gdix") != 0)
  {
    fprintf(stderr, "custom value %s at %p: serialization problematic\n",
	    Custom_ops_val(v)->identifier, (void*)v);
    print_rel_rec_cont();
  }

  /* The value is certainly in the young or old heap */
  if( Tag_val(v) >= No_scan_tag )
    goto finish;

  /* Check if we have already seen this value */
  {
    int i = 0;
    for(i=0; i<rel_rec_cont_cnt; i++)
      if(rel_rec_cont[i].rr_v == v)
	goto finish;
  }

  /* A closure without env: don't bother relativitize or traverse */
  if(Tag_val(v) == Closure_tag && Wosize_val(v) == 1)
    goto finish;

  /* The candidate for relativitization */
  if(Tag_val(v) == Closure_tag && !(Is_young(v)))
  {
    const value f = rel_closure(global_data_arr,arr_update_flag,v);
    if( f != Val_false )
    {
      v = f;
      goto finish;
    }
    /* If not relativitized, traverse the closure, even if its is in
       the old heap. Young closures could get into the old heap easily,
       after a GC... */
  }

  /* The following is taken from byterun/extern.c */
  if (Tag_val(v) == Forward_tag)
  {
    const value f = Forward_val (v);
    if (Is_block (f)
	&& (!Is_in_value_area(f) || Tag_val (f) == Forward_tag 
	    || Tag_val (f) == Lazy_tag || Tag_val (f) == Double_tag))
      { /* Do not short-circuit the pointer. */
        goto finish;
      }
    /* Fall through. The Forward record will be traversed as usual
    v = f;
    goto tailcall;
    */
  }

  if(Wosize_val(v) == 0)
    goto finish;		/* nothing to traverse */

  /* Traversing the value */
  if(rel_rec_cont_cnt >= rel_rec_cont_max)
    goto finish;		/* too deep */

  
  rel_rec_cont[rel_rec_cont_cnt].rr_v = v;
  rel_rec_cont[rel_rec_cont_cnt].rr_i = 0;
  rel_rec_cont_cnt++;
  v = Field(v,0);
  goto tailcall;

 finish:			/* The result must be in v */

  if( rel_rec_cont_cnt == 0 )	/* if stack is empty */
    return v;

  {
    rel_rec_cont_cnt--;
    const value old_value = rel_rec_cont[rel_rec_cont_cnt].rr_v;
    const mlsize_t old_i = rel_rec_cont[rel_rec_cont_cnt].rr_i;
    const mlsize_t new_i = old_i + 1;
    /* Don't mess with the value in the recording mode */
    if( Field(old_value,old_i) != v && arr_update_flag == Val_false )
	Modify(&(Field(old_value,old_i)),v);
    if(new_i >= Wosize_val(old_value))
    {
      v = old_value;
      goto finish;
    } else {
      rel_rec_cont[rel_rec_cont_cnt].rr_i = new_i;
      rel_rec_cont_cnt++;
      v = Field(old_value,new_i);
      goto tailcall;
    }
  }
}

/* The main function: validate the input data and call rel_rec
   to do the real work.
   external relativitize : 
   (Obj.t * global_data_idx) array -> bool -> Obj.t -> Obj.t
*/
value relativitize(value global_data_arr, value arr_update_flag, value v)
{
  myassert( rel_rec_cont_cnt == 0 );
  myassert( Is_block(global_data_arr) && Is_in_value_area(global_data_arr) );
  myassert( Tag_val(global_data_arr) == 0 &&
	    Wosize_val(global_data_arr) > 0 );
  {
    const value f0 = Field(global_data_arr,0);
    myassert( Is_block(f0) && Is_in_value_area(f0) &&
	      Tag_val(f0) == 0 && Wosize_val(f0) == 2 );
  }
  return rel_rec(global_data_arr,arr_update_flag,v);
}


/*
 * Absolutize val: reverse of Relativitize 
 * This has to be C code, particularly written to perform no allocations
 * whatsoever, so not to trigger GC. Only then updating the values in place
 * is safe.
 * Return the (possibly updated inplace) value.
 */

static value abs_rec(value global_data_arr, value v) 
{
 tailcall:
  if(Is_long(v) || Is_atom(v) || !Is_in_value_area(v) )
    goto finish;

#if defined(DEBUG_SER) && DEBUG_SER
  fprintf(stderr, "abs examining %p, first field %p size %lu tag %d young %d\n",
	  (void*)v,(void*)(Wosize_val(v) == 0 ? 0 : Field(v,0)),
	  Wosize_val(v), Tag_val(v), Is_young(v));
#endif
  /* The value is certainly in the young or old heap */

  /* A closure without env: don't bother relativitize or traverse */
  if(Tag_val(v) == Closure_tag && Wosize_val(v) == 1)
    goto finish;

  /* The candidate for absolutization */
  if(Tag_val(v) == Custom_tag && Wosize_val(v) == 2 &&
     strcmp(Custom_ops_val(v)->identifier,"delimcc_gdix") == 0)
  {
    const int32 i = *((int32 *) Data_custom_val(v));
    value f;
#if defined(DEBUG_SER) && DEBUG_SER
    fprintf(stderr, "absolutizing %d\n",i);
#endif
    myassert( i < Wosize_val(global_data_arr) );
    f = Field(global_data_arr,i);
    myassert( Is_block(f) && Wosize_val(f) == 2 );
    {
      const value f1 = Field(f,1);
      myassert( Is_block(f1) && Wosize_val(f1) == 2 &&
		*((int32 *) Data_custom_val(f1)) == i);
    }
    v = Field(f,0);
    myassert( Is_block(v) && Is_in_heap(v) && Tag_val(v) == Closure_tag );
    goto finish;
  }

  if( Tag_val(v) >= No_scan_tag )
    goto finish;

  /* Check if we have already seen this value */
  {
    int i = 0;
    for(i=0; i<rel_rec_cont_cnt; i++)
      if(rel_rec_cont[i].rr_v == v)
	goto finish;
  }

  /* It was the candidate for relativitization. After reloading,
     the old/new status might have changed!
  if(Tag_val(v) == Closure_tag && !(Is_young(v)))
    goto finish;
  */
  /* The following is taken from byterun/extern.c */
  if (Tag_val(v) == Forward_tag)
  {
    const value f = Forward_val (v);
    if (Is_block (f)
	&& (!Is_in_value_area(f) || Tag_val (f) == Forward_tag 
	    || Tag_val (f) == Lazy_tag || Tag_val (f) == Double_tag) )
      { /* Do not short-circuit the pointer. */
        goto finish;
      }
    /* Fall through. The Forward record will be traversed as usual
    v = f;
    goto tailcall;
    */
  }

  if(Wosize_val(v) == 0)
    goto finish;		/* nothing to traverse */

  /* Traversing the value */
  if(rel_rec_cont_cnt >= rel_rec_cont_max)
    goto finish;		/* too deep */

  
  rel_rec_cont[rel_rec_cont_cnt].rr_v = v;
  rel_rec_cont[rel_rec_cont_cnt].rr_i = 0;
  rel_rec_cont_cnt++;
  v = Field(v,0);
  goto tailcall;

 finish:			/* The result must be in v */

  if( rel_rec_cont_cnt == 0 )	/* if stack is empty */
    return v;

  {
    rel_rec_cont_cnt--;
    const value old_value = rel_rec_cont[rel_rec_cont_cnt].rr_v;
    const mlsize_t old_i = rel_rec_cont[rel_rec_cont_cnt].rr_i;
    const mlsize_t new_i = old_i + 1;
    if( Field(old_value,old_i) != v )
	Modify(&(Field(old_value,old_i)),v);
    if(new_i >= Wosize_val(old_value))
    {
      v = old_value;
      goto finish;
    } else {
      rel_rec_cont[rel_rec_cont_cnt].rr_i = new_i;
      rel_rec_cont_cnt++;
      v = Field(old_value,new_i);
      goto tailcall;
    }
  }
}

/* The main function: validate the input data and call abs_rec
   to do the real work.
   external absolutize : 
   (Obj.t * global_data_idx) array -> Obj.t -> Obj.t
*/

value absolutize(value global_data_arr, value v)
{
  myassert( rel_rec_cont_cnt == 0 );
  myassert( Is_block(global_data_arr) && Is_in_value_area(global_data_arr) );
  myassert( Tag_val(global_data_arr) == 0 &&
	    Wosize_val(global_data_arr) > 0 );
  {
    const value f0 = Field(global_data_arr,0);
    myassert( Is_block(f0) && Is_in_value_area(f0) &&
	      Tag_val(f0) == 0 && Wosize_val(f0) == 2 );
  }
  return abs_rec(global_data_arr,v);
}


/* The main serialization routine: relativitize, immediately serialize,
   and then restore.
*/

extern value caml_output_value(value vchan, value v, value flags);

value output_delim_value(value global_data_arr,
			 value vchan, value v, value flags)
{
  CAMLparam2 (global_data_arr, v);
  relativitize(global_data_arr,Val_false,v);
  caml_output_value(vchan, v, flags);
  absolutize(global_data_arr, v);
  CAMLreturn (Val_unit);
}


/* Implementing the custom data type global_data_ix
   The contents is the int32 index in the global data table.
   Don't forget to invoke global_data_register_custom_ops ()
   somewhere in the initialization code.
*/

static void gdix_serialize(value v, uintnat * wsize_32, uintnat * wsize_64)
{
  caml_serialize_int_4((*((int32 *) Data_custom_val(v))));
  *wsize_32 = *wsize_64 = 4;
}

static uintnat gdix_deserialize(void * dst)
{
  *((int32 *) dst) = caml_deserialize_sint_4();
  return 4;
}

static struct custom_operations global_data_ix_ops = {
  "delimcc_gdix",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  gdix_serialize,
  gdix_deserialize
};

value global_data_register_custom_ops(value unit) /* unit->unit*/
{
  caml_register_custom_operations(&global_data_ix_ops);
  return Val_unit;
}

CAMLexport value global_data_ix_make(value i) /* int->global_data_idx */
{
  value res = caml_alloc_custom(&global_data_ix_ops, 4, 0, 1);
  myassert( Is_long(i) );
  (*((int32 *) Data_custom_val(res))) = Long_val(i);
  return res;
}


/* Some old code, kept for reference. It works for simple cases,
   but the full tests0 gives the Segmentation fault in the interpreter.
   Somewhere the closure replacement is not invariant. Sigh.
   It does work in many cases, involving thunks, currying, etc.
*/

#if 0
static value global_data = Val_long(0);

value set_global_data(value global_data_arr)
{
  myassert( Is_block(global_data_arr) && Is_in_value_area(global_data_arr) );
  myassert( Tag_val(global_data_arr) == 0 &&
	    Wosize_val(global_data_arr) > 0 );
  {
    const value f0 = Field(global_data_arr,0);
    myassert( Is_block(f0) && Is_in_value_area(f0) &&
	      Tag_val(f0) == 0 && Wosize_val(f0) == 2 );
  }
  caml_register_global_root(&global_data);
  global_data = global_data_arr;
  return Val_unit;
}

value get_global_fn(value vi)
{
  const int i = Long_val(vi);
  mlsize_t size = 0;
  value f;

  myassert(Is_block(global_data) && Is_in_value_area(global_data));
  size = Wosize_val(global_data);
  myassert(i >= 0 && i < size);
  f = Field(global_data,i);
  myassert(Is_block(f) && Wosize_val(f) == 2 &&
	   Is_block(Field(f,0)) && Tag_val(Field(f,0)) == Closure_tag);
  fprintf(stderr,"get_global_fn %d, code ptr %p\n",i,
	  Code_val(Field(f,0)));
  return Field(f,0);
}

static value rel_closure(value global_data_arr, value arr_update_flag, value v)
{
  const mlsize_t size = Wosize_val(global_data_arr);
  const void * our_closure = Code_val(Field(Field(global_data_arr,0),1));
  mlsize_t i = 0;

  fprintf(stderr,"Trying to relativitize closure %p, code ptr %p\n",
	  (void *)v,(void*)(Field(v,0)));

  for(i=0; i<size; i++)
  {
    const value f = Field(global_data_arr,i);
    if( Field(f,0) == v )
    {
      fprintf(stderr,"Found at idx %lu\n",i);
      return Field(f,1);
    }
    if( Field(f,0) == Val_long(0) ) /* empty slot */
    { if( Code_val(v) == our_closure )
	  return Val_false;
      if( arr_update_flag == Val_true )
      {
	fprintf(stderr,"Recording at idx %lu\n",i);
	myassert( Is_in_heap(v) );	/* must be in the old heap */
	Modify(&(Field(f,0)),v);
	return Field(f,1);
      }
      else return Val_false;
    }
  }
  return Val_false;
}

#endif
