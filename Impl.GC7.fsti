/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// Low* Specification and Implementation of a Mark and Sweep Garbage Collector (GC) that acts on OCaml style objects and a heap memory compatible with OCaml heap memory. Each of the sub-functions that make up a Mark and sweep GC like, root_greying, mark and sweep is implemented in Low* and their output is proven to be equivalent to their respective functional counter parts. The same startegy can be applied for adding more features and verifying them on the go.
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------

module Impl.GC7

module Sq =  FStar.Seq
module Sq_base = FStar.Seq.Base

module H = FStar.HyperStack
module HA = FStar.HyperStack.All

module Usize = FStar.UInt64

module B = LowStar.Buffer

/// S represents the functional layer where functional GC is implemented---------------------------------------------------------------------------------------
module S = Spec.GC7
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------
/// G represents the graph layer where graph and reachability definitions are there
module G = Spec.Graph3
/// ----------------------------------------------------------------------------------------------------------------------------------------------------------
module MB = LowStar.Monotonic.Buffer

module ST = FStar.HyperStack.ST

module L = FStar.List.Tot

open LowStar.BufferOps

open FStar.Mul 
open FStar.Endianness

open LowStar.Endianness

module C = C.Loops

/// ----------------------------------------------------------------------------------------------------------------------------------------------------------
#set-options "--max_fuel 3 --max_ifuel 0 --z3rlimit 50"

(*heap memory is modelled as a byte addressable array*)
type heap = g: B.buffer UInt8.t{B.length g == S.heap_size}

let v_id_f (v_id: Usize.t{Usize.v v_id < S.heap_size /\
                          Usize.v v_id % Usize.v S.mword == 0})
           : GTot S.hp_addr = v_id

(*For reading the color of an object. S.getcolor is the functional equivalent*)
let getColor  (h:Usize.t{Usize.v h < S.heap_size /\
                          Usize.v h % Usize.v S.mword == 0})
         : HA.Stack (S.color)
          (fun m -> True)
          (fun h0 x h1 -> x == S.getColor (v_id_f h) /\ h0 == h1 /\ B.modifies (B.loc_none) h0 h1) = 
 let _ = S.max_color_size_lemma () in
 let _ = assert (Usize.v S.max_color = pow2 2 - 1) in
 
 let c' = Usize.shift_right h 8ul in
 let c = Usize.logand c' 3UL in
 
 assert (Usize.v c' == Usize.v h/ pow2 8);
 assert (Usize.v c' <= pow2 64/pow2 8);
 Math.Lemmas.pow2_minus 64 8;
 assert (Usize.v c' <= pow2 56);
 UInt.logand_le #64 (Usize.v c') 3;
 assert (Usize.v c <= Usize.v c');

 assert (Usize.v c <= Usize.v S.max_color);
 assert (Usize.v  h <= UInt.max_int 64);
 assert (Usize.v h <= pow2 64 - 1);
 assert (Usize.v c <=  pow2 64 - 1);
 assert (Usize.v S.max_color <= pow2 64 - 1);
 c

let makeHeader   (wz:S.wosize)
                 (c:S.color)
                 (tg:S.tag)
       : HA.Stack Usize.t
         (fun m -> True) 
       (fun h0 x h1 -> x == S.makeHeader wz c tg) = 
S.makeHeader wz c tg


val load64_le_i_new 
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:UInt64.t{FStar.UInt64.v i + 8 <= MB.length b})
  : HA.Stack u64
      (requires fun h -> MB.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        MB.live h1 b /\
        le_to_n (Seq.slice (MB.as_seq h1 b) (FStar.UInt64.v i) (FStar.UInt64.v i + 8)) == FStar.UInt64.v z)
        
inline_for_extraction
let read_word_from_byte_buffer1 (g: heap) 
                                (byte_index: S.hp_addr)
        : HA.Stack (UInt64.t) 
            (fun m -> B.live m g) 
            (fun m0 x m1 ->  m0 == m1  /\ (B.live m1 g) /\
                          (x == S.read_word (B.as_seq m1 g) byte_index) /\
                          (B.modifies (B.loc_none) m0 m1))  = load64_le_i g (UInt32.uint_to_t (UInt64.v byte_index))

inline_for_extraction
let read_word_from_byte_buffer3 (g: heap) 
                                (byte_index: S.hp_addr)
        : HA.Stack (UInt64.t) 
            (fun m -> B.live m g) 
            (fun m0 x m1 ->  m0 == m1  /\ (B.live m1 g) /\
                          (x == S.read_word (B.as_seq m1 g) byte_index) /\
                          (B.modifies (B.loc_none) m0 m1))  = load64_le_i_new g byte_index


#restart-solver

inline_for_extraction
let write_word_to_byte_buffer3  (g: heap) 
                               (byte_index: S.hp_addr)
                               (v:UInt64.t)
  : HA.Stack unit
     (requires fun h -> B.live h g (*/\
                     (UInt32.v (UInt32.uint_to_t (UInt64.v byte_index)) < B.length g / 8)*) /\
                     store_pre g (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)))) 8 (fun s -> le_to_n s == UInt64.v v) h)
     
     (ensures fun h0 _ h1 -> B.modifies (B.loc_buffer g) h0 h1 /\
                          S.write_word (B.as_seq h0 g) byte_index v == B.as_seq h1 g) = 
 let h0 = ST.get () in
 store64_le_i g FStar.UInt32.(UInt32.uint_to_t (UInt64.v byte_index)) v;
 let h1 = ST.get () in

//le_to_n produces a value
 assert (le_to_n (Seq.slice (B.as_seq h1 g) (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)))) 
                                                     (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)) + 8))) == UInt64.v v);
 assert (Seq.equal (Seq.slice (B.as_seq h0 g) 0 (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)))))
                      (Seq.slice (B.as_seq h1 g) 0 FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)))));
 assert (Seq.equal (Seq.slice (B.as_seq h0 g) (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)) + 8)) (B.length g))
                      (Seq.slice (B.as_seq h1 g) (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v byte_index)) + 8)) (B.length g)));


 assert (S.read_word (B.as_seq h1 g) (byte_index) == v);
 assert (Seq.length (B.as_seq h1 g) == Seq.length (B.as_seq h0 g));
 Seq.lemma_eq_elim (S.write_word (B.as_seq h0 g) byte_index v) (B.as_seq h1 g);
 assert (S.write_word (B.as_seq h0 g) byte_index v == B.as_seq h1 g);
 ()

#push-options "--split_queries"

#restart-solver 

let wosize_of_block (v_id: Usize.t)
                    (g:heap)
           : HA.Stack (S.wosize)
             (fun m -> B.live m g (*/\ S.well_formed_heap2 (B.as_seq m g)*) /\ 
              (Usize.v v_id >= 0 /\ Usize.v v_id < S.heap_size) /\
              (Usize.v v_id % Usize.v S.mword == 0) (*/\
              S.is_valid_header (v_id_f v_id) (B.as_seq m g)*)) 
       
             (fun h0 x h1 -> h0 == h1 /\ x == S.wosize_of_object1 (v_id_f v_id) (B.as_seq h1 g) /\ h0 == h1 /\
                          (B.modifies (B.loc_none) h0 h1)) = 
let index = read_word_from_byte_buffer1 g v_id in
let wz = S.getWosize index in
wz


let color_of_block  (v_id: Usize.t)
                    (g:heap)
           : HA.Stack (S.color)
             (fun m -> B.live m g /\ S.well_formed_heap2 (B.as_seq m g) /\ 
              Usize.v v_id >= 0 /\ Usize.v v_id < S.heap_size /\
              (Usize.v v_id % Usize.v S.mword == 0) /\
              S.is_valid_header (v_id_f v_id) (B.as_seq m g)) 
       
             (fun h0 x h1 -> h0 == h1 /\ x == S.color_of_object1 (v_id_f v_id) (B.as_seq h1 g) /\ h0 == h1 /\
                          (B.modifies (B.loc_none) h0 h1)) = 
let index = read_word_from_byte_buffer1 g v_id in
let cl = S.getColor index in (*Since wosize is a Usize.t, this is fine*)
cl


let tag_of_block (v_id: Usize.t)
                 (g:heap)
           : HA.Stack (S.tag)
             (fun m -> B.live m g /\ S.well_formed_heap2 (B.as_seq m g) /\ 
              Usize.v v_id >= 0 /\ Usize.v v_id < S.heap_size /\
              (Usize.v v_id % Usize.v S.mword == 0) /\
              S.is_valid_header (v_id_f v_id) (B.as_seq m g)) 
       
             (fun h0 x h1 -> h0 == h1 /\ x == S.tag_of_object1 (v_id_f v_id) (B.as_seq h1 g) /\
                          (B.modifies (B.loc_none) h0 h1) /\ h0 == h1) = 
let index = read_word_from_byte_buffer1 g v_id in
let tg = S.getTag index in 
tg


#restart-solver 


let colorHeader1  (g:heap) 
                  (v_id:Usize.t{Usize.v v_id < S.heap_size /\
                                  Usize.v v_id % Usize.v S.mword == 0})
                  (c:S.color) 
            : HA.Stack (unit)
            (fun m -> B.live m g /\
                   S.well_formed_heap2 (B.as_seq m g) /\
                   (Usize.v v_id >= 0 /\ Usize.v v_id < S.heap_size) (*/\
                    (UInt32.v (UInt32.uint_to_t (UInt64.v v_id)) < B.length g / 8)*) /\
                   S.is_valid_header (v_id_f v_id) (B.as_seq m g))
            (fun m0 () m1 -> B.live m1 g /\ B.modifies (B.loc_buffer g) m0 m1 /\
                          ((B.as_seq m1 g) == S.colorHeader1 (v_id_f v_id) (B.as_seq m0 g) c)) = 
 let h0 = ST.get() in
 let wz = wosize_of_block v_id g in

 let h1 = ST.get() in
 assert (h0 == h1);
 let tg = tag_of_block v_id g in

 let h2 = ST.get() in
 assert (h1 == h2);
 let h_val = S.makeHeader wz c tg in 

 let h3 = ST.get() in
 
 assert (wz == S.getWosize h_val);
 assert (c == S.getColor h_val);
 assert (tg == S.getTag h_val);
 //assert  (UInt32.v (UInt32.uint_to_t (UInt64.v v_id)) < B.length g / 8);
 assert  (store_pre g (FStar.UInt32.(v (UInt32.uint_to_t (UInt64.v v_id)))) 8 (fun s -> le_to_n s == UInt64.v h_val) h3);
 write_word_to_byte_buffer3 g v_id h_val;
 
 let h = ST.get() in
 assert (B.modifies (B.loc_buffer g) h3 h);
 assert (B.modifies (B.loc_buffer g) h2 h);
 assert (B.modifies (B.loc_buffer g) h0 h);
 assert ((B.as_seq h g) == S.colorHeader1 (v_id_f v_id) (B.as_seq h0 g) c);
 ()

#restart-solver 

/// Function that pushes into the stack
let push_to_stack (g:heap)
                  (st: B.buffer Usize.t{B.length st == S.heap_size})
                  (st_len: B.buffer Usize.t)
                  (elem: Usize.t{Usize.v elem < S.heap_size /\
                                  Usize.v elem % Usize.v S.mword == 0})
             : HA.Stack unit
               (fun m ->  B.live m g /\ B.live m st /\ B.live m st_len /\ B.length st_len == 1 /\
                       
                       B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_len) /\
                       B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                       B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_len) /\
                      
                       
                       Usize.v (Seq.index (B.as_seq m st_len) 0) < S.heap_size (*/\
                       (UInt32.v (UInt32.uint_to_t (UInt64.v elem)) < B.length g / 8)*) /\
                        
                       S.well_formed_heap2 (B.as_seq m g) /\
                       (G.is_vertex_set (Seq.slice (B.as_seq m st) 0 
                                         (Usize.v (Seq.index (B.as_seq m st_len) 0)))) /\
                        (~(Seq.mem (v_id_f elem) (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_len) 0))))) /\
                       (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_len) 0))) ==> Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                       (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_len) 0))) ==>  Usize.v x % Usize.v S.mword == 0 ) /\
                       (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_len) 0))) ==> S.is_valid_header x (B.as_seq m g)) /\
                       (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\ S.isGrayObject1 x (B.as_seq m g) <==>
                                           Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_len) 0)))) /\
                       (Usize.v (v_id_f elem) >= 0 /\ Usize.v (v_id_f elem) < S.heap_size) /\
                       (S.is_valid_header (v_id_f elem) (B.as_seq m g)))
               (fun m0 _ m1 -> B.live m1 st /\ B.live m1 g /\ B.live m1 st_len /\ B.length st_len == 1 /\
                            Usize.v (Seq.index (B.as_seq m1 st_len) 0) <= S.heap_size /\
                            B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_len) /\
                            B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                            B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_len) /\
                            (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_len))) m0 m1) /\ 
                            (S.well_formed_heap2 (B.as_seq m1 g)) /\
                            (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0)(*  + 1*))) ==>
                                     Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                            (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0) (*  + 1*))) ==>
                                     S.is_valid_header x (B.as_seq m1 g)) /\
                            (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m1 g)) /\
                                               S.isGrayObject1 x (B.as_seq m1 g) <==>
                                               Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0)(* + 1 *)))) /\
                            (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_len) 0))) ==>
                                    Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0) (* + 1*)))) /\
                            (Seq.mem (v_id_f elem) (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0)(* + 1*)))) /\
                            (G.is_vertex_set (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0)))) (*/\
                            (Seq.length (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0) + 1)) ==
                                      Seq.length (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0))) + 1) *) /\
                           
                            (Seq.length (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0))) ==
                                         Seq.length (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_len) 0))) + 1) /\
                             (*Spec Equivalence---------------------------------------------------------------------------------------------*)
                             Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_len) 0)(* + 1*)) ==
                              fst (S.push_to_stack2 (B.as_seq m0 g) (Seq.slice (B.as_seq m0 st) 0 
                                                    (Usize.v (Seq.index (B.as_seq m0 st_len) 0))) elem) /\
                                                    
                             B.as_seq m1 g == snd (S.push_to_stack2 (B.as_seq m0 g) (Seq.slice (B.as_seq m0 st) 0 
                                                    (Usize.v (Seq.index (B.as_seq m0 st_len) 0))) elem) /\
                             (*-------------------------------------------------------------------------------------------------------------*)
                            (Usize.v (v_id_f elem) >= 0 /\ Usize.v (v_id_f elem) < S.heap_size) /\
                             S.is_valid_header (v_id_f elem) (B.as_seq m1 g) /\
                             (S.heap_remains_same_except_index_v_id (v_id_f elem) (B.as_seq m0 g) (B.as_seq m1 g)) /\
                             (S.objects2 0UL (B.as_seq m0 g) ==
                             S.objects2 0UL (B.as_seq m1 g))) = 
 let open Usize in
 let h0 = ST.get() in
 let i = !*st_len in
 B.upd st (UInt32.uint_to_t (Usize.v i  )) elem;
 st_len.(0ul) <- !*st_len +^ 1UL;
 let h1 = ST.get() in
 let i1 = !*st_len in
 assert (B.modifies (B.loc_union (B.loc_buffer st) (B.loc_buffer st_len)) h0 h1);
 colorHeader1 g elem S.gray;
 let h2 = ST.get() in
 assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st) (B.loc_buffer st_len))) h0 h2);
 assert (G.is_vertex_set (Seq.slice (B.as_seq h0 st) 0 (Usize.v i)));
 assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v i)) ==> Usize.v x >= 0 /\ Usize.v x < S.heap_size);
 let _ = Seq.lemma_eq_intro (Seq.slice (B.as_seq h2 st) 0 (Usize.v i + 1))
                                         (fst (S.push_to_stack2 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v i)) elem))in
 Seq.lemma_eq_intro (B.as_seq h2 g) (snd (S.push_to_stack2 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v i)) elem));
 
 assert (S.well_formed_heap2 (B.as_seq h2 g));
 assert (forall x. Seq.mem x (Seq.slice (B.as_seq h2 st) 0 (Usize.v i + 1)) ==> Usize.v x >= 0 /\ Usize.v x < S.heap_size);
 assert (forall y. Seq.mem y (Seq.slice (B.as_seq h2 st) 0 (Usize.v i + 1)) ==> S.is_valid_header y (B.as_seq h2 g));
 S.objects2_equal_lemma 0UL (B.as_seq h0 g) (B.as_seq h2 g);
assert (S.objects2 0UL (B.as_seq h0 g) == S.objects2 0UL (B.as_seq h2 g)) ;
assert (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h2 g)) /\
                                               S.isGrayObject1 x (B.as_seq h2 g) <==>
                                               Seq.mem x (Seq.slice (B.as_seq h2 st) 0 (Usize.v i + 1)));

assert (forall x. Seq.mem x (Seq.slice (B.as_seq h2 st) 0 (Usize.v i)) ==> Seq.mem x (Seq.slice (B.as_seq h2 st) 0 (Usize.v i + 1)));
assert (Seq.mem (v_id_f elem) (Seq.slice (B.as_seq h2 st) 0 (Usize.v i + 1)));
assert (G.is_vertex_set (Seq.slice (B.as_seq h2 st) 0 (Usize.v i + 1)));
assert (S.is_valid_header (v_id_f elem) (B.as_seq h2 g));
assert (Seq.length (Seq.slice (B.as_seq h2 st) 0 (Usize.v i + 1)) == Seq.length (Seq.slice (B.as_seq h2 st) 0 (Usize.v i)) + 1);
assert (Seq.length (Seq.slice (B.as_seq h2 st) 0 (Usize.v i1)) == Seq.length (Seq.slice (B.as_seq h2 st) 0 (Usize.v i)) + 1);
assert (Seq.length (Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h2 st_len) 0))) ==
                  Seq.length (Seq.slice (B.as_seq h2 st) 0 (Usize.v i)) + 1);
assert (Seq.length (Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h2 st_len) 0))) ==
                  Seq.length (Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_len) 0))) + 1);
assert (S.heap_remains_same_except_index_v_id (v_id_f elem) (B.as_seq h1 g) (B.as_seq h2 g));
assert (S.heap_remains_same_except_index_v_id (v_id_f elem) (B.as_seq h0 g) (B.as_seq h2 g))

#restart-solver

let isPointer (v_id: Usize.t)
              (g:heap)
           : HA.Stack (bool)
             (fun m -> B.live m g /\
              Usize.v v_id >= 0 /\ Usize.v v_id < S.heap_size /\
              (Usize.v v_id % Usize.v S.mword == 0)) 
       
             (fun h0 b h1 -> h0 == h1 /\ b == S.isPointer (v_id_f v_id) (B.as_seq h1 g) /\
                          (B.modifies (B.loc_none) h0 h1) /\ h0 == h1) = 
  if Usize.logand (read_word_from_byte_buffer1 g v_id) 1UL = 0UL then true else false 


/// In paper, this function is called as darken_body
let fieldPush2_body  (g:heap)
                     (st: B.buffer Usize.t{B.length st == S.heap_size })
                     (st_top: B.buffer Usize.t)
                     (h_index:Usize.t{Usize.v h_index >= 0 /\ Usize.v h_index < S.heap_size /\
                                      Usize.v h_index % Usize.v S.mword == 0})
                     (wz:S.wosize)
                     (i:Usize.t) 
             : HA.Stack unit
          (fun m -> (*concrete memory properties*)
                 B.live m g /\ B.live m st /\ B.live m st_top /\ 
                 B.length st_top == 1 /\

                 (*Since st_top is used for slice calculation of st, st_top contents should be less than or equal to st length*)
                 (*Usize.v (Seq.index (B.as_seq m st_top) 0) < B.length st /\*)
                 (Usize.v (Seq.index (B.as_seq m st_top) 0) <= S.heap_size) /\
                 (*Find out a property that ensures that stack has always enough room to push the successors of h_index*)
               

                 Usize.v i >= 1 /\
                 Usize.v i < Usize.v wz + 1 /\
        
                 B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                 
                 B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                 B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                 

                 (*algebraic properties to connect with Spec*)
                 S.well_formed_heap2 (B.as_seq m g) /\
                 S.is_valid_header (v_id_f h_index) (B.as_seq m g) /\
                 (Usize.v wz == Usize.v (S.getWosize (S.read_word (B.as_seq m g) h_index))) /\
                 (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 
                                               (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                                               Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                 (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>  Usize.v x % Usize.v S.mword == 0 ) /\
                 (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 
                                               (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq m g)) /\
                 (G.is_vertex_set (Seq.slice (B.as_seq m st) 0 
                                               (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                 (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\ S.isGrayObject1 x (B.as_seq m g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq m st) 0 
                                               (Usize.v (Seq.index (B.as_seq m st_top) 0))))

            )
            (fun m0 _ m1 -> B.live m1 g /\ B.live m1 st /\ B.live m1 st_top /\ 
                         B.length st_top == 1 /\

                        (*Since st_top is used for slice calculation of st, st_top contents should be less than or equal to st length*)
                         Usize.v (Seq.index (B.as_seq m1 st_top) 0) <= S.heap_size /\
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                 
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                         B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) (*/\
                         Usize.v wz == Usize.v (S.getWosize (Seq.index (B.as_seq m1 g) (Usize.v h_index)))*) /\
                 
                         S.well_formed_heap2 (B.as_seq m1 g) /\

                         S.is_valid_header (v_id_f h_index) (B.as_seq m1 g) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                                                           Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>  Usize.v x % Usize.v S.mword == 0 ) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 
                                                           (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                         S.is_valid_header x (B.as_seq m1 g)) /\
                         (G.is_vertex_set (Seq.slice (B.as_seq m1 st) 0 
                                        (Usize.v (Seq.index (B.as_seq m1 st_top) 0)))) /\
                         (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m1 g)) /\ S.isGrayObject1 x (B.as_seq m1 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq m1 st) 0 
                                               (Usize.v (Seq.index (B.as_seq m1 st_top) 0)))) /\
                         (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) m0 m1) /\
                         (S.objects2 0UL (B.as_seq m1 g) ==
                          S.objects2 0UL (B.as_seq m0 g)) /\
                         (B.as_seq m1 g) ==  (snd (S.fieldPush_spec_body (B.as_seq m0 g)
                                                      (Seq.slice (B.as_seq m0 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq m0 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i))) /\
                         Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0)) ==
                         (fst (S.fieldPush_spec_body (B.as_seq m0 g)
                                                      (Seq.slice (B.as_seq m0 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq m0 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i)))) =
  let h1 = ST.get() in

  S.field_limits_allocated_blocks_lemma (B.as_seq h1 g);
  S.field_contents_within_limits_allocated_blocks_lemma (B.as_seq h1 g);
   
  let succ_index = Usize.add h_index (Usize.mul i S.mword) in

  assert (Usize.v succ_index < S.heap_size); 

  S.max_wosize_times_mword_multiple_of_mword i;

  assert ((Usize.v (Usize.mul i S.mword) % Usize.v S.mword == 0));
  
  S.sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i S.mword);

  assert ((Usize.v h_index + Usize.v (Usize.mul i S.mword)) % (Usize.v S.mword) == 0);

  assert (Usize.v succ_index % Usize.v S.mword == 0);
  assert (S.is_hp_addr succ_index);
  let succ = read_word_from_byte_buffer3 g succ_index in
  let h2 = ST.get() in
  assert (h1 == h2); (*No heap change, hence this assert passes*)
  assert (succ == S.read_word (B.as_seq h1 g) succ_index);
  assert (Seq.mem h_index (S.objects2 0UL (B.as_seq h1 g)));
 if isPointer succ_index g then 
 (
  if color_of_block succ g = S.white then
   (
       S.valid_succ_color_lemma (B.as_seq h1 g) (v_id_f succ);
       assert (Seq.mem (v_id_f succ) (S.objects2 0UL (B.as_seq h1 g)) /\
                        (S.color_of_object1 (v_id_f succ) (B.as_seq h1 g) <> S.gray));
       S.stack_less_than_heap_size_when_one_non_gray_exists (B.as_seq h1 g) 
                                                              (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                              (v_id_f succ);
                                                              
       assert (Seq.length (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) < S.heap_size);

       assert (Usize.v (Seq.index (B.as_seq h1 st_top) 0) < S.heap_size);
       assert (~(S.isGrayObject1 (v_id_f succ) (B.as_seq h1 g)) /\ ~(S.isBlackObject1 (v_id_f succ) (B.as_seq h1 g)));
       //assert (S.unvisited (v_id_f succ) (B.as_seq h1 g));
       assert (~(Seq.mem (v_id_f succ) (Seq.slice (B.as_seq h1 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))));
       assert (S.is_valid_header (v_id_f succ) (B.as_seq h1 g));
       assert (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h1 g)) /\
                              S.isGrayObject1 x (B.as_seq h1 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h1 st) 0 
                                                  (Usize.v (Seq.index (B.as_seq h1 st_top) 0))));
       assert (Usize.v (Seq.index (B.as_seq h1 st_top) 0) < S.heap_size);
      

       assert (S.well_formed_heap2 (B.as_seq h1 g));
       assert ((G.is_vertex_set (Seq.slice (B.as_seq h1 st) 0 
                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))));
       
       push_to_stack g st st_top succ;
       let h3 = ST.get() in
       assert (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)(* + 1*)) ==
                              fst (S.push_to_stack2 (B.as_seq h1 g) (Seq.slice (B.as_seq h1 st) 0 
                                                    (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) succ));
       assert (B.as_seq h3 g == snd (S.push_to_stack2 (B.as_seq h1 g) (Seq.slice (B.as_seq h1 st) 0 
                                                    (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) succ));

       Seq.lemma_eq_intro (B.as_seq h3 g) 
                          (snd (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i)));

       
       Seq.lemma_eq_intro (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                           (fst (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i)));
        assert ((B.as_seq h3 g) ==  (snd (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i))));
        assert (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)) ==
                 (fst (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i))));
        assert (~(h1 == h3));
        assert (B.live h3 g /\ B.live h3 st /\ B.live h3 st_top /\
                   B.length st_top == 1);

        assert (S.well_formed_heap2 (B.as_seq h3 g));

              
        assert (forall x. Seq.mem x (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0))) ==>
                                     Usize.v x >= 0 /\ Usize.v x < S.heap_size);
        assert (forall x. Seq.mem x (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq h3 g));

       assert (G.is_vertex_set (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))));
        assert (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h3 g)) /\ S.isGrayObject1 x (B.as_seq h3 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))));
        assert ((B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h1 h3));
        
        assert (S.objects2 0UL (B.as_seq h3 g) ==
                S.objects2 0UL (B.as_seq h1 g));
        assert (S.objects2 0UL (B.as_seq h3 g) ==
                     S.objects2 0UL (B.as_seq h1 g));
       
        ()
    )
   else 
    (
       
      let h3 = ST.get() in
      assert (h1 == h3);
      assert (Usize.v (Seq.index (B.as_seq h3 st_top) 0) <= S.heap_size);
      Seq.lemma_eq_intro (B.as_seq h3 g) 
                          (snd (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i)));   
      
      
      Seq.lemma_eq_intro (Seq.slice (B.as_seq h3 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                           (fst (S.fieldPush_spec_body (B.as_seq h1 g)
                                                        (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                       (h_index)
                                                       (wz)
                                                       (i)));
      
      
        assert ((B.as_seq h3 g) ==  (snd (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i))));
        assert (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)) ==
                 (fst (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i))));
        assert (forall x. Seq.mem x (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0))) ==>
                                     Usize.v x >= 0 /\ Usize.v x < S.heap_size);
        assert (forall x. Seq.mem x (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq h3 g));
        assert (G.is_vertex_set (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))));

        assert (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h3 g)) /\ S.isGrayObject1 x (B.as_seq h3 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))));
        assert (S.objects2 0UL (B.as_seq h3 g) ==
                S.objects2 0UL (B.as_seq h1 g));
        assert (S.objects2 0UL (B.as_seq h3 g) ==
                     S.objects2 0UL (B.as_seq h1 g));
      
      
      
      
      
      ()
          
    )
  )
  else
  (
    let h3 = ST.get() in
      assert (h1 == h3);
      assert (Usize.v (Seq.index (B.as_seq h3 st_top) 0) <= S.heap_size);
      Seq.lemma_eq_intro (B.as_seq h3 g) 
                          (snd (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i)));   
      
      
      Seq.lemma_eq_intro (Seq.slice (B.as_seq h3 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                           (fst (S.fieldPush_spec_body (B.as_seq h1 g)
                                                        (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                       (h_index)
                                                       (wz)
                                                       (i)));
      
      
        assert ((B.as_seq h3 g) ==  (snd (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i))));
        assert (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)) ==
                 (fst (S.fieldPush_spec_body (B.as_seq h1 g)
                                                      (Seq.slice (B.as_seq h1 st) 0 
                                                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                      (h_index)
                                                      (wz)
                                                      (i))));
        assert (forall x. Seq.mem x (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0))) ==>
                                     Usize.v x >= 0 /\ Usize.v x < S.heap_size);
        assert (forall x. Seq.mem x (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq h3 g));
        assert (G.is_vertex_set (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))));

        assert (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h3 g)) /\ S.isGrayObject1 x (B.as_seq h3 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))));
        assert (S.objects2 0UL (B.as_seq h3 g) ==
                S.objects2 0UL (B.as_seq h1 g));
        assert (S.objects2 0UL (B.as_seq h3 g) ==
                     S.objects2 0UL (B.as_seq h1 g));
      
      
      
      
      
      ()
  )

#restart-solver 

#restart-solver 
/// ------------------------------------------------------------------------------------------------------------------------------------------------------------------
/// In the paper, this function is called as darken. The loop invariant based proofs are interesting. It proves that the recursive functional darken in F* is functionally equivalent to the iterative and imperative darken in Low*
/// ------------------------------------------------------------------------------------------------------------------------------------------------------------------
let fieldPush2_loop (g:heap)
                     (st: B.buffer Usize.t{B.length st == S.heap_size })
                     (st_top: B.buffer Usize.t)
                     (h_index:Usize.t{Usize.v h_index >= 0 /\ Usize.v h_index < S.heap_size /\
                                      Usize.v h_index % Usize.v S.mword == 0})
                     (wz:S.wosize)
         : HA.Stack unit
          (fun m -> (*concrete memory properties*)
                 B.live m g /\ B.live m st /\ B.live m st_top /\ 
                 B.length st_top == 1 /\

                 (*Since st_top is used for slice calculation of st, st_top contents should be less than or equal to st length*)
                 Usize.v (Seq.index (B.as_seq m st_top) 0) <= S.heap_size /\

                 (*Usize.v (Seq.index (B.as_seq m st_len) 0) + Seq.length (B.as_seq m succ) < S.heap_size /\*)
                 B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                 
                 B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                 B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                 

                 (*algebraic properties to connect with Spec*)
                 S.well_formed_heap2 (B.as_seq m g) /\
                 S.is_valid_header (v_id_f h_index) (B.as_seq m g) /\
                 
                 (Usize.v wz == Usize.v (S.getWosize (S.read_word (B.as_seq m g) h_index))) /\
                 
                 (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 
                                               (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                                               Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                 (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>  Usize.v x % Usize.v S.mword == 0 ) /\
                 (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 
                                               (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq m g)) /\
                 (G.is_vertex_set (Seq.slice (B.as_seq m st) 0 
                                               (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                 (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\ S.isGrayObject1 x (B.as_seq m g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq m st) 0 
                                               (Usize.v (Seq.index (B.as_seq m st_top) 0))))
                 

            )
          (fun m0 () m1 ->  B.live m1 g /\ B.live m1 st /\ B.live m1 st_top /\ 
                         B.length st_top == 1 /\
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                 
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                         B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                         (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) m0 m1) /\
                         Usize.v (Seq.index (B.as_seq m1 st_top) 0) <= S.heap_size /\
                         (S.well_formed_heap2 (B.as_seq m1 g)) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                                     Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>  Usize.v x % Usize.v S.mword == 0 ) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 
                                               (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq m1 g)) /\
                         (G.is_vertex_set (Seq.slice (B.as_seq m1 st) 0 
                                               (Usize.v (Seq.index (B.as_seq m1 st_top) 0)))) /\
                         (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m1 g)) /\ S.isGrayObject1 x (B.as_seq m1 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq m1 st) 0 
                                               (Usize.v (Seq.index (B.as_seq m1 st_top) 0)))) /\
                         (S.objects2 0UL (B.as_seq m1 g) ==
                          S.objects2 0UL (B.as_seq m0 g)) /\
                          (B.as_seq m1 g)  ==
                                 snd (S.fieldPush_spec1 (B.as_seq m0 g) 
                                      (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      1UL) /\
                         (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==
                               fst (S.fieldPush_spec1 (B.as_seq m0 g) 
                                      (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      1UL)) = 
 let h0 = ST.get() in
 let inv h (i: nat) = B.live h g /\ B.live h st /\ B.live h st_top /\
                    B.length st_top == 1  /\
                    Usize.v (Seq.index (B.as_seq h st_top) 0) <= S.heap_size /\
                     
                    B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                    B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                    B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                   
                    i <= Usize.v wz + 1 /\
                    i >= 1 /\
                    (Usize.v wz == Usize.v (S.getWosize (S.read_word (B.as_seq h g) h_index))) /\
                    
                    S.well_formed_heap2 (B.as_seq h g) /\

                    S.is_valid_header (v_id_f h_index) (B.as_seq h g) /\
                    
                    (forall x. Seq.mem x (Seq.slice (B.as_seq h st) 0 
                                               (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==>
                                               Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                    (forall x. Seq.mem x (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==>  Usize.v x % Usize.v S.mword == 0 ) /\
                    
                    (forall x. Seq.mem x (Seq.slice (B.as_seq h st) 0 
                                               (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq h g)) /\
                    (G.is_vertex_set (Seq.slice (B.as_seq h st) 0 
                                               (Usize.v (Seq.index (B.as_seq h st_top) 0)))) /\

                    (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h g)) /\ S.isGrayObject1 x (B.as_seq h g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h st) 0 
                                               (Usize.v (Seq.index (B.as_seq h st_top) 0)))) /\
                    (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h0 h) /\
                    (S.objects2 0UL (B.as_seq h g) ==
                     S.objects2 0UL (B.as_seq h0 g)) /\
                    S.fieldPush_spec1 (B.as_seq h g) 
                                      (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      (Usize.uint_to_t i) ==
                    S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      1UL in
 
 let body (i: UInt32.t{ 1 <= UInt32.v i /\ UInt32.v i < Usize.v wz + 1})
    : HA.Stack unit
    (requires (fun m -> inv m (UInt32.v i)))
    (ensures (fun m0 () m1 -> inv m0 (UInt32.v i) /\ inv m1 (UInt32.v i + 1))) =
 let h1 = ST.get() in
 fieldPush2_body g st st_top h_index wz (Usize.uint_to_t (UInt32.v i));
 let h3 = ST.get() in
 let i' = Usize.((Usize.uint_to_t (UInt32.v i ) ) +^ 1UL) in
 assert ((B.as_seq h3 g) ==  (snd (S.fieldPush_spec_body (B.as_seq h1 g)
                                                         (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                         (h_index)
                                                         (wz)
                                                         ((Usize.uint_to_t (UInt32.v i))))));
                
 assert (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)) ==
                 (fst (S.fieldPush_spec_body (B.as_seq h1 g)
                                             (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                             (h_index)
                                             (wz)
                                             ((Usize.uint_to_t (UInt32.v i ) )))));

 assert (S.fieldPush_spec1 (B.as_seq h3 g) 
                           (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                           (h_index) 
                           (wz) 
                           (i') ==
         S.fieldPush_spec1 (snd (S.fieldPush_spec_body (B.as_seq h1 g)
                                                       (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                       (h_index)
                                                       (wz)
                                                       ((Usize.uint_to_t (UInt32.v i ) ))))
                           (fst (S.fieldPush_spec_body (B.as_seq h1 g)
                                                       (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                       (h_index)
                                                       (wz)
                                                       ((Usize.uint_to_t (UInt32.v i ) ))))
                           (h_index) 
                           (wz) 
                           (i'));

 S.fieldPush_fieldPush_spec_body_lemma (B.as_seq h1 g)
                                       (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                       (h_index)
                                       (wz)
                                       ((Usize.uint_to_t (UInt32.v i ) ))
                                       (i');

 assert (S.fieldPush_spec1 (B.as_seq h3 g) 
                           (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                           (h_index) 
                           (wz) 
                           (i') ==
        S.fieldPush_spec1 (B.as_seq h1 g) 
                          (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                          (h_index) 
                          (wz) 
                          ((Usize.uint_to_t (UInt32.v i ) )));

assert (S.fieldPush_spec1 (B.as_seq h1 g) 
                          (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                          (h_index) 
                          (wz) 
                          ((Usize.uint_to_t (UInt32.v i ) )) ==
          S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      1UL);
 
assert (S.fieldPush_spec1 (B.as_seq h3 g) 
                                      (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      (i') ==
                    S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      1UL) in
 C.Loops.for 1ul (UInt32.uint_to_t (Usize.v Usize.(wz +^ 1UL) ) ) inv body;
 let h4 = ST.get() in
 assert (S.fieldPush_spec1 (B.as_seq h4 g) 
                                      (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      (Usize.(wz +^ 1UL)) ==
                    S.fieldPush_spec1 (B.as_seq h0 g) 
                                      (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      1UL);

S.fieldPush_fieldPush_spec_body_lemma1 (B.as_seq h4 g) 
                                        (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0)))
                                        (h_index) 
                                        (wz) 
                                        (Usize.(wz +^ 1UL));

assert ((Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==
            fst (S.fieldPush_spec1 (B.as_seq h4 g) 
                                      (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      (Usize.(wz +^ 1UL))));

assert ((B.as_seq h4 g)  ==
           snd (S.fieldPush_spec1 (B.as_seq h4 g) 
                                      (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0)))
                                      (h_index) 
                                      (wz) 
                                      (Usize.(wz +^ 1UL))));
                                      
 assert ((B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h0 h4));
 assert (Usize.v (Seq.index (B.as_seq h4 st_top) 0) <= S.heap_size);
 assert (forall x. Seq.mem x (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==>
                                     Usize.v x >= 0 /\ Usize.v x < S.heap_size);
 assert (forall x. Seq.mem x (Seq.slice (B.as_seq h4 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq h4 g));
 assert (G.is_vertex_set (Seq.slice (B.as_seq h4 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h4 st_top) 0))));

 assert (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h4 g)) /\ S.isGrayObject1 x (B.as_seq h4 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h4 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h4 st_top) 0))));
 assert (S.objects2 0UL (B.as_seq h4 g) ==
                     S.objects2 0UL (B.as_seq h0 g))


#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver

/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// In the paper, the below function is mark_body
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
let mark_heap_body  (g:heap) (*S_heap, B_heap*)
                    (st: B.buffer Usize.t{B.length st == S.heap_size })
                    (st_top: B.buffer Usize.t) 
              : HA.Stack (unit)
           (*----------------------------------------Pre-conditions---------------------------------------------*)
           
           (fun m ->  (*Liveness of buffers------------------------------------------------------------------------*)
                   B.live m g /\ B.live m st /\ B.live m st_top /\ 

                   (*Length of st_top---------------------------------------------------------------------------*)
                   B.length st_top == 1 /\

                   (*Disjointness of buffers--------------------------------------------------------------------*)
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\

                   (*Range of st_top----------------------------------------------------------------------------*)
                   Usize.v (Seq.index (B.as_seq m st_top) 0) <= S.heap_size /\
                   Usize.v (Seq.index (B.as_seq m st_top) 0) > 0 /\

                   (*Algebraic properties of the contents of the buffers. This should match with spec-----------*)
                   S.well_formed_heap2 (B.as_seq m g) /\
                    (*We need to reason about only the used parts of st; that is upto st_top---------------------*)
                   (G.is_vertex_set (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>  Usize.v x % Usize.v S.mword == 0 ) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m g)) /\
                               
                   (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\
                                    S.isGrayObject1 x (B.as_seq m g) <==>
                                Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))))  
            (fun m0 _ m1 -> B.live m1 g /\ B.live m1 st /\ B.live m1 st_top /\ 
                           
                           B.length st_top == 1 /\
                           
                           B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                           B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                           B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                           
                           (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) m0 m1) /\
                            Usize.v (Seq.index (B.as_seq m1 st_top) 0) <= S.heap_size /\
                            
                           (S.well_formed_heap2 (B.as_seq m1 g)) /\
                         
                           (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                                     Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                           (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>  Usize.v x % Usize.v S.mword == 0 ) /\
                         
                           (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 
                                               (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq m1 g)) /\
                           (G.is_vertex_set (Seq.slice (B.as_seq m1 st) 0 
                                               (Usize.v (Seq.index (B.as_seq m1 st_top) 0)))) /\
                         
                           (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m1 g)) /\
                                  S.isGrayObject1 x (B.as_seq m1 g) <==>
                                     Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0)))) /\
                         
                           (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0)) ==
                           fst (S.mark5_body (B.as_seq m0 g) 
                                             (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_top) 0))))) /\
                           
                           (B.as_seq m1 g == snd (S.mark5_body (B.as_seq m0 g) 
                                                         (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_top) 0))))) /\
                           
                           (S.objects2 0UL (B.as_seq m0 g) ==
                               S.objects2 0UL (B.as_seq m1 g))) = 
 let open Usize in
    let h0 = ST.get() in
    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size);

    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq h0 g));
    let prev_top = !*st_top in   
    (*No heap change after reading*)
    
    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v prev_top)) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size);

    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v prev_top)) ==>
                                              S.is_valid_header (v_id_f x) (B.as_seq h0 g));
               
 
    Seq.lemma_slice_snoc (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0));
    
    st_top.(0ul) <- !*st_top -^ 1UL;
    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v prev_top)) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size);

    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v prev_top)) ==>
                                              S.is_valid_header (v_id_f x) (B.as_seq h0 g));

    let h0' = ST.get() in

    let curr_top = !*st_top in

    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0' st) 0 (Usize.v prev_top)) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size);

    assert (Usize.v curr_top == Usize.v prev_top - 1);

    assert (curr_top == B.get h0' st_top 0);
    assert (curr_top == Seq.index (B.as_seq h0' st_top) 0);

    assert (prev_top == B.get h0 st_top 0);
    assert (prev_top == Seq.index (B.as_seq h0 st_top) 0);

    assert (Usize.v curr_top == Usize.v (Seq.index (B.as_seq h0 st_top) 0) - 1);

    assert (Usize.v (Seq.index (B.as_seq h0' st_top) 0) == Usize.v (Seq.index (B.as_seq h0 st_top) 0) - 1);

    assert (B.as_seq h0' st == B.as_seq h0 st);

    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0' st) 0 (Usize.v curr_top)) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size);

    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0' st) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size);

    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0' st) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0);
                                              
    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0' st) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq h0' g));
    let h1 = ST.get() in

    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size);
    assert (forall x. Seq.mem x (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq h1 g));
                                              
    let x =  st.(UInt32.uint_to_t (Usize.v !*st_top )) in // last element of the stack is popped
   
    assert (S.is_valid_header x (B.as_seq h1 g));
    assert (x == Seq.index (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                          (Usize.v (Seq.index (B.as_seq h0 st_top) 0) - 1));

    (*The length of the stack is equal to the value stored at the st_top at h0 memory state*)
    assert (Seq.length (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) == (Usize.v (Seq.index (B.as_seq h0 st_top) 0)));

    assert (x == Seq.index (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                          (Usize.v (Seq.index (B.as_seq h0' st_top) 0)));

   assert (x == Seq.index (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                          (Usize.v (Seq.index (B.as_seq h1 st_top) 0)));
    G.is_vertex_set_lemma3 (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)));
    assert (G.is_vertex_set (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0))));

    (*st in func == (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
      Seq.slice  st                                                                         0 (Seq.length st - 1) == 
     (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0)))*)

    assert (G.is_vertex_set (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))));
    
 
    colorHeader1 g x S.black;

    let h1' = ST.get() in
    assert (S.well_formed_heap2 (B.as_seq h1 g));
    assert (B.as_seq h1' g == S.colorHeader1 x (B.as_seq h1 g) S.black);

    assert (B.modifies (B.loc_buffer g) h1 h1');
    assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_buffer st_top)) h0 h1');

    let wz = wosize_of_block x g in
    assert (S.color_of_object1 (v_id_f x) (B.as_seq h1' g) == S.black);
    assert (S.well_formed_heap2 (B.as_seq h1' g));
    assert (S.objects2 0UL (B.as_seq h0 g) ==
              S.objects2 0UL (B.as_seq h1' g));
    assert (Seq.length (B.as_seq h0 g) == Seq.length (B.as_seq h1' g));
    assert (S.wosize_of_object1 (v_id_f x) (B.as_seq h0 g) ==
                S.wosize_of_object1 (v_id_f x) (B.as_seq h1' g) /\
            S.tag_of_object1 (v_id_f x) (B.as_seq h0 g) == 
                S.tag_of_object1 (v_id_f x) (B.as_seq h1' g) /\
            S.is_valid_header (v_id_f x) (B.as_seq h1' g) /\ 
            S.is_valid_header (v_id_f x) (B.as_seq h0 g));
   S.get_allocated_block_addresses_lemma (B.as_seq h0 g) (B.as_seq h1' g) (v_id_f x) S.black;
 
   assert (S.get_allocated_block_addresses (B.as_seq h0 g) == 
                S.get_allocated_block_addresses (B.as_seq h1' g));
                
   G.is_vertex_set_lemma5 (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)));
   assert (~(Seq.mem x (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0)))));
   //assert (~(Seq.mem x (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))));
   Seq.lemma_mem_snoc (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0))) x;

   assert (forall y. Seq.mem y (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0))) \/  (y == x) <==>
               Seq.mem y (S.objects2 0UL (B.as_seq h1 g)) /\  S.isGrayObject1 y (B.as_seq h1 g));
   assert (S.all_mem_st_mem_st__except_v_id_in_stack x 
                                                     (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                       (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0))));
   assert (S.color_of_object1 x (B.as_seq h1' g) == 3UL);
   S.objects2_equal_lemma 0UL (B.as_seq h0 g) (B.as_seq h1' g);

   assert (S.objects2 0UL (B.as_seq h0 g) ==
           S.objects2 0UL (B.as_seq h1' g));
   
   (*assert (Seq.equal (Seq.slice (B.as_seq h1 st) 0 
                         (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                     (Seq.slice (B.as_seq h1' st) 0 
                         (Usize.v (Seq.index (B.as_seq h1' st_top) 0))));*)
   S.slice_coloring_lemma (B.as_seq h1 g) 
                          (B.as_seq h1' g) 
                          x 
                          (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                          (Seq.index (B.as_seq h0' st_top) 0);
                          
   assert (forall x. Seq.mem x (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0))) <==>
         Seq.mem x (S.objects2 0UL (B.as_seq h1' g)) /\ S.isGrayObject1 x (B.as_seq h1' g));
 
 
   let h2 = ST.get() in
   assert (h1' == h2);
   assert (S.objects2 0UL (B.as_seq h0 g) ==  S.objects2 0UL (B.as_seq h2 g));
   assert (Usize.v x < S.heap_size);
   
   assert(S.well_formed_heap2 (B.as_seq h2 g)); 
   assert (S.is_valid_header x (B.as_seq h2 g));
   assert ((Usize.v wz == Usize.v (S.getWosize (S.read_word (B.as_seq h2 g) x))));
   (*assert ((forall y. Seq.mem y (Seq.slice (B.as_seq h2 st) 0 
                                      (Usize.v (Seq.index (B.as_seq h2 st_top) 0))) ==>
                                               Usize.v y >= 0 /\ Usize.v y < S.heap_size));
   assert (forall y. Seq.mem y (Seq.slice (B.as_seq h2 st) 0 
                                      (Usize.v (Seq.index (B.as_seq h2 st_top) 0))) ==>
                                             S.is_valid_header y (B.as_seq h2 g));
   assert (G.is_vertex_set (Seq.slice (B.as_seq h2 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h2 st_top) 0))));
   
   
   assert (forall x. Seq.mem x (Seq.slice (B.as_seq h1' st) 0 
                         (Usize.v (Seq.index (B.as_seq h1' st_top) 0))) <==>
         Seq.mem x (S.objects2 0UL (B.as_seq h1' g)) /\
                                                        S.isGrayObject1 x (B.as_seq h1' g));
 
 
  assert (forall x. Seq.mem x (Seq.slice (B.as_seq h2 st) 0 
                         (Usize.v (Seq.index (B.as_seq h2 st_top) 0))) <==>
         Seq.mem x (S.objects2 0UL (B.as_seq h2 g)) /\
                                                        S.isGrayObject1 x (B.as_seq h2 g));
   assert (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h2 g)) /\ S.isGrayObject1 x (B.as_seq h2 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h2 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h2 st_top) 0))));
   assert (Usize.v (v_id_f x) >= 0 /\ Usize.v (v_id_f x) < S.heap_size);*)
   
   fieldPush2_loop  g st st_top x wz;
 
   let h3 = ST.get() in
   (*assert (B.live h3 g /\ B.live h3 st /\ B.live h3 st_top /\ 
           B.length st_top == 1 /\
           B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                 
           B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
           B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
           (B.modifies (B.loc_union (B.loc_buffer g) 
                       (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h0 h3) /\
           Usize.v (Seq.index (B.as_seq h3 st_top) 0) <= S.heap_size /\
          (S.well_formed_heap2 (B.as_seq h3 g)) /\
          (forall x. Seq.mem x (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0))) ==>
                                     Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
          (forall x. Seq.mem x (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq h3 g)) /\
         (G.is_vertex_set (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))) /\
         (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h3 g)) /\ S.isGrayObject1 x (B.as_seq h3 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h3 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))));*)

 
  assert (S.well_formed_heap2 (B.as_seq h3 g));
  (*assert (forall x. Seq.mem x (Seq.slice (B.as_seq h2 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h2 st_top) 0))) ==>
                                        Usize.v x >= 0 /\ Usize.v x < S.heap_size );
  assert (forall x. Seq.mem x (Seq.slice (B.as_seq h2 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h2 st_top) 0))) ==> S.is_valid_header x (B.as_seq h2 g));
  assert (G.is_vertex_set (Seq.slice (B.as_seq h2 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h2 st_top) 0))));

  assert (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h2 g)) /\ S.isGrayObject1 x (B.as_seq h2 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h2 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h2 st_top) 0))));
  
  assert (Usize.v (v_id_f x) >= 0 /\ Usize.v (v_id_f x) < S.heap_size);

  assert (S.is_valid_header (v_id_f x) (B.as_seq h2 g));*)

  //assert (Usize.v wz <= Usize.v (S.getWosize (Seq.index (B.as_seq h2 g) (Usize.v x))));
 
 
 assert (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)) ==
              fst (S.fieldPush_spec1 (B.as_seq h2 g) 
                                    (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0)))
                                    (*(Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h2 st_top) 0)))*)
                                    (x) 
                                    (wz) 
                                    1UL));

  assert ((B.as_seq h3 g) == 
              snd (S.fieldPush_spec1 (B.as_seq h2 g) 
                                    (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0)))
                                    (*(Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h2 st_top) 0)))*)
                                    (x) 
                                    (wz) 
                                    1UL));

  (*assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) ==> Usize.v x >= 0 /\ Usize.v x < S.heap_size);
  assert (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) ==> S.is_valid_header (v_id_f x) (B.as_seq h0 g));
  assert (G.is_vertex_set (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))));
  assert ((forall x. Seq.mem x (S.objects2 0UL (B.as_seq h0 g)) /\ S.isGrayObject1 (v_id_f x) (B.as_seq h0 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))));
                                                  
  assert (~(G.is_emptySet (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))));
  assert ((v_id_f x) == Seq.index (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                           (Seq.length ((Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))) - 1));

  assert (B.as_seq h0 st == B.as_seq h1 st);
  assert (B.as_seq h1 st == B.as_seq h2 st);
  assert (B.as_seq h1 st_top == B.as_seq h2 st_top);*)
  //assert (Usize.v (Seq.index (B.as_seq h1 st_top) 0) == Usize.v (Seq.index (B.as_seq h0 st_top) 0) - 1);
  
  S.mark5_body_fieldPush_lemma (B.as_seq h0 g) 
                               (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                               (x)
                               (B.as_seq h2 g)
                               (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0)))
                               (*(Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h2 st_top) 0)))*)
                               (wz);


                               
 
 assert (fst (S.mark5_body (B.as_seq h0 g)  
                             (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))) ==
           fst (S.fieldPush_spec1 (B.as_seq h2 g)
                                  (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0)))
                                  (x) 
                                  (wz)
                                  1UL) );
 assert (snd (S.mark5_body (B.as_seq h0 g)  
                             (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))) ==
           snd (S.fieldPush_spec1 (B.as_seq h2 g)
                                  (Seq.slice (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) 0 (Usize.v (Seq.index (B.as_seq h0' st_top) 0)))
                                  (x) 
                                  (wz)
                                  1UL));
   
 assert (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)) ==
                          fst (S.mark5_body (B.as_seq h0 g) 
                                             (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))));

 assert (B.as_seq h3 g == snd (S.mark5_body (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 
                                                    (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))));
 assert ((S.objects2 0UL (B.as_seq h0 g) ==
                          S.objects2 0UL (B.as_seq h3 g)));
  
 ()

#restart-solver 

/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// The mark function, which is proved to be functionally equivalent to functional mark
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
let mark_heap5  (g:heap) (*S_heap, B_heap*)
                (st: B.buffer Usize.t{B.length st == S.heap_size})
                (st_top: B.buffer Usize.t) (*Try to use variable instead of buffer*)
         : HA.Stack (unit)
           (*----------------------------------------Pre-conditions---------------------------------------------*)
           
           (fun m ->  (*Liveness of buffers------------------------------------------------------------------------*)
                   B.live m g /\ B.live m st /\ B.live m st_top /\ 

                   (*Length of st_top---------------------------------------------------------------------------*)
                   B.length st_top == 1 /\

                   (*Disjointness of buffers--------------------------------------------------------------------*)
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\

                   (*Range of st_top----------------------------------------------------------------------------*)
                   Usize.v (Seq.index (B.as_seq m st_top) 0) <= S.heap_size /\
                   Usize.v (Seq.index (B.as_seq m st_top) 0) >= 0 /\
                   (*Algebraic properties of the contents of the buffers. This should match with spec-----------*)
                   S.well_formed_heap2 (B.as_seq m g) /\
                   
                   (*We need to reason about only the used parts of st; that is upto st_top---------------------*)
                   (G.is_vertex_set (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==> Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0) /\
                                              
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m g)) /\
                               
                   (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\
                                    S.isGrayObject1 x (B.as_seq m g) <==>
                                Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))))

                    (*-----------------------------------------Post-conditions---------------------------------------------*)
           (*S.mark (B.as_seq m1 g) (B.as_seq m1 st upto stack_top)  == S.mark (B.as_seq m0 g) (B.as_seq m0 st upto stack_top)*)
           (fun m0 () m1 -> B.live m1 g /\ B.live m1 st /\ B.live m1 st_top /\
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                         B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                         S.well_formed_heap2 (B.as_seq m1 g) /\
                         Usize.v (B.get m1 st_top 0) == 0 /\
                         B.length st == S.heap_size /\
                         B.length st_top == 1 /\
                         Usize.v (Seq.index (B.as_seq m1 st_top) 0) <= S.heap_size /\
                         (G.is_vertex_set (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0)))) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m1 g) /\
                         (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m1 g)) /\
                                    S.isGrayObject1 x (B.as_seq m1 g) <==>
                                Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))))) /\
                          (B.as_seq m1 g) == S.mark5 (B.as_seq m0 g) (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_top) 0))) /\
                          (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) m0 m1)
                         
                         ) = 
let open Usize in
let h_init = ST.get() in
(*Put assumes and connect FStar mark and LowStar mark*)
(*B.as_seq h g == S.mark (B.as_seq h0 g) (B.as_seq h0 st)*)
(*We start with h0 heap. 
 Loop invariant should hold;
 (1) Before every iteration
 (2) During every iteration and 
 (3) At the end of every iteration
 Before the first iteration, g in the invariant is g itself.*)                       
  
 let inv h =  B.live h g /\ B.live h st /\ B.live h st_top /\ 
             
             (*B.length st_top == 1 /\
             B.length st == S.heap_size + 1 /\*)
             Usize.v (Seq.index (B.as_seq h st_top) 0) <= S.heap_size /\
             
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
             B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\

             (*B.get h st_top 0 >^ 0ul /\*)

             S.well_formed_heap2 (B.as_seq h g) /\
             (S.objects2 0UL (B.as_seq h g) ==
               S.objects2 0UL (B.as_seq h_init g)) /\
              (G.is_vertex_set (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0)))) /\
              (forall x. Seq.mem x (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

              (forall x. Seq.mem x (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0) /\
              (forall x. Seq.mem x (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq h g)) /\
                               
              (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h g)) /\
                                    S.isGrayObject1 x (B.as_seq h g) <==>
                                Seq.mem x (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0)))) /\
              S.mark5 (B.as_seq h g) (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==
              S.mark5 (B.as_seq h_init g) (Seq.slice (B.as_seq h_init st) 0 (Usize.v (Seq.index (B.as_seq h_init st_top) 0))) /\
             B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h_init h in
  
  let guard (test: bool) h = inv h /\ 
   (test = true  ==> Usize.v (B.get h st_top 0) > 0) /\
   (test = false ==> Usize.v (B.get h st_top 0) = 0)  in
  
   let test ()
     : HA.Stack bool 
       (requires (fun h -> inv h)) 
       (ensures (fun _ ret h1 -> guard ret h1)) = (!*st_top) >^ 0UL in
  
  let body ()
     : HA.Stack unit 
       (requires (fun h -> guard true h)) 
       (ensures (fun _ _ h1 -> inv h1)) = 
   let h0 = ST.get() in   
   assert (B.live h0 g /\ B.live h0 st /\ B.live h0 st_top /\ 
             
             (*B.length st_top == 1 /\
             B.length st == S.heap_size + 1 /\*)
             Usize.v (Seq.index (B.as_seq h0 st_top) 0) <= S.heap_size /\
             
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
             B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\

             (*B.get h st_top 0 >^ 0ul /\*)

             S.well_formed_heap2 (B.as_seq h0 g) /\
             (S.objects2 0UL (B.as_seq h0 g) ==
               S.objects2 0UL (B.as_seq h_init g)) /\
              (G.is_vertex_set (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))) /\
              (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
              (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0) /\
                  
              (forall x. Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq h0 g)) /\
               (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h0 g)) /\
                                    S.isGrayObject1 x (B.as_seq h0 g) <==>
                                Seq.mem x (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))) /\

             S.mark5 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))) ==
               S.mark5 (B.as_seq h_init g) (Seq.slice (B.as_seq h_init st) 0 (Usize.v (Seq.index (B.as_seq h_init st_top) 0))) /\
             B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h_init h0);
   assert (Usize.v (B.get h0 st_top 0) > 0);
   mark_heap_body g st st_top;
   
   let h4 = ST.get() in
   assert (B.live h4 g /\ B.live h4 st /\ B.live h4 st_top /\ 
                         B.length st_top == 1 /\
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                 
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                         B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                         (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h0 h4) /\
                         Usize.v (Seq.index (B.as_seq h4 st_top) 0) <= S.heap_size /\
                         (S.well_formed_heap2 (B.as_seq h4 g)) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==>
                                     Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                         (forall x. Seq.mem x (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq h4 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==>
                                               S.is_valid_header x (B.as_seq h4 g)) /\
                         (G.is_vertex_set (Seq.slice (B.as_seq h4 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h4 st_top) 0)))) /\
                         (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h4 g)) /\
                                 S.isGrayObject1 x (B.as_seq h4 g) <==>
                                                  Seq.mem x (Seq.slice (B.as_seq h4 st) 0 
                                               (Usize.v (Seq.index (B.as_seq h4 st_top) 0)))) /\
                         (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0)) ==
                          fst (S.mark5_body (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 
                                                    (Usize.v (Seq.index (B.as_seq h0 st_top) 0))))) /\
                         (B.as_seq h4 g == snd (S.mark5_body (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 
                                                    (Usize.v (Seq.index (B.as_seq h0 st_top) 0))))) /\
                          (S.objects2 0UL (B.as_seq h0 g) ==
                           S.objects2 0UL (B.as_seq h4 g)));
  
   S.mark_mark_body_lemma (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 
                                                    (Usize.v (Seq.index (B.as_seq h0 st_top) 0)));

   assert (S.mark5 (B.as_seq h4 g) 
                   (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==
          S.mark5 (B.as_seq h0 g) (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0))));
   assert (S.mark5 (B.as_seq h4 g) 
                   (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==
          S.mark5 (B.as_seq h_init g) (Seq.slice (B.as_seq h_init st) 0 (Usize.v (Seq.index (B.as_seq h_init st_top) 0))));
                                                    
   
   assert (Usize.v (B.get h4 st_top 0) >= 0);
   
  assert (B.live h4 g /\ B.live h4 st /\ B.live h4 st_top /\ 
             
             (*B.length st_top == 1 /\
             B.length st == S.heap_size + 1 /\*)
             Usize.v (Seq.index (B.as_seq h4 st_top) 0) <= S.heap_size /\
             
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
             B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\

             (*B.get h st_top 0 >^ 0ul /\*)

             S.well_formed_heap2 (B.as_seq h4 g) /\
             (S.objects2 0UL (B.as_seq h4 g) ==
               S.objects2 0UL (B.as_seq h_init g)) /\
              (G.is_vertex_set (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0)))) /\
              (forall x. Seq.mem x (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
              (forall x. Seq.mem x (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq h4 g)) /\
                               
              (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h4 g)) /\
                                    S.isGrayObject1 x (B.as_seq h4 g) <==>
                                Seq.mem x (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0)))) /\
               S.mark5 (B.as_seq h4 g) (Seq.slice (B.as_seq h4 st) 0 (Usize.v (Seq.index (B.as_seq h4 st_top) 0))) ==
               S.mark5 (B.as_seq h_init g) (Seq.slice (B.as_seq h_init st) 0 (Usize.v (Seq.index (B.as_seq h_init st_top) 0))) /\
             B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h_init h4)
  in
  C.Loops.while #(inv) #(guard) test body;
  let h5 = ST.get() in
  assert (B.live h5 g /\ B.live h5 st /\ B.live h5 st_top /\
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                         B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                         B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                         S.well_formed_heap2 (B.as_seq h5 g) /\
                         Usize.v (B.get h5 st_top 0) == 0 /\
                         B.length st == S.heap_size /\
                         B.length st_top == 1 /\
                         Usize.v (Seq.index (B.as_seq h5 st_top) 0) <= S.heap_size /\
                         (G.is_vertex_set (Seq.slice (B.as_seq h5 st) 0 (Usize.v (Seq.index (B.as_seq h5 st_top) 0)))) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq h5 st) 0 (Usize.v (Seq.index (B.as_seq h5 st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq h5 st) 0 (Usize.v (Seq.index (B.as_seq h5 st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq h5 g) /\
                         (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h5 g)) /\
                                    S.isGrayObject1 x (B.as_seq h5 g) <==>
                                Seq.mem x (Seq.slice (B.as_seq h5 st) 0 (Usize.v (Seq.index (B.as_seq h5 st_top) 0))))));
  S.mark_mark_body_lemma1 (B.as_seq h5 g) (Seq.slice (B.as_seq h5 st) 0 (Usize.v (Seq.index (B.as_seq h5 st_top) 0)));
  assert ((B.as_seq h5 g) == S.mark5 (B.as_seq h_init g) 
                                     (Seq.slice (B.as_seq h_init st) 0 (Usize.v (Seq.index (B.as_seq h_init st_top) 0))));
  assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h_init h5);
  ()


#restart-solver

#restart-solver

/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// The root greying function, which is proved to be functionally equivalent to functional root greying
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
let create_root_stack_and_gray_modified_heap_loop  (g:heap)
                                                   (st: B.buffer Usize.t{B.length st == S.heap_size})
                                                   (st_top: B.buffer Usize.t) 
                                                   (h_list: B.buffer Usize.t {B.length h_list == S.heap_size})
                                                   (h_list_length: Usize.t)
           : HA.Stack (unit)
           (*----------------------------------------Pre-conditions---------------------------------------------*)
           
           (fun m ->  (*Liveness of buffers------------------------------------------------------------------------*)
                   B.live m g /\ B.live m st /\ B.live m st_top /\ B.live m h_list /\

                   (*Length of st_top---------------------------------------------------------------------------*)
                   B.length st_top == 1 /\
                   
                   (*Disjointness of buffers = C(4,2) = (4!/(2! * 2!))------------------------------------------*)
                   (*4 buffers, so 6 pairwise combinations*)
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_list) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer h_list) /\
                   B.loc_disjoint (B.loc_buffer st_top) (B.loc_buffer h_list) /\
                   
                   

                   (*Range of st_top----------------------------------------------------------------------------*)
                   Usize.v (Seq.index (B.as_seq m st_top) 0) <= S.heap_size /\
                   Usize.v (Seq.index (B.as_seq m st_top) 0) >= 0 /\

                   (*Range of h_list_length---------------------------------------------------------------------*)
                   Usize.v h_list_length <= S.heap_size /\
                   
                   (*Algebraic properties of the contents of the buffers. This should match with spec-----------*)
                   (*heap-------------------------------------*)
                   S.well_formed_heap2 (B.as_seq m g) /\
                   
                   (*We need to reason about only the used parts of st; that is upto st_top---------------------*)
                   (*stack--------------------------------------------------------------------------------------*)
                   (G.is_vertex_set (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>  Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0) /\
                                             
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m g)) /\
                               
                   (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\
                                    S.isGrayObject1 x (B.as_seq m g) <==>
                                Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                   
                   (*We need to reason about only the used parts of h_list; that is upto h_list_length---------------*)
                   (*h_list------------------------------------------------------------------------------------------*)

                   (G.is_vertex_set (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length))) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) ==> 
                                               Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                   (forall x. Seq.mem x (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) ==> 
                                              Usize.v x % Usize.v S.mword == 0) /\
                                              
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m g)) /\
                   
                   S.mutually_exclusive_sets (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) 
                                             (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length))
                               
                   
                   )

                    (*-----------------------------------------Post-conditions---------------------------------------------*)
           (*S.mark (B.as_seq m1 g) (B.as_seq m1 st upto stack_top)  == S.mark (B.as_seq m0 g) (B.as_seq m0 st upto stack_top)*)
           (fun m0 () m1 ->  B.live m1 g /\ B.live m1 st /\ B.live m1 st_top /\ B.live m1 h_list /\
                          B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                          B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                          B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                          B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_list) /\
                          B.loc_disjoint (B.loc_buffer st) (B.loc_buffer h_list) /\
                          B.loc_disjoint (B.loc_buffer st_top) (B.loc_buffer h_list) /\
                        
                          S.well_formed_heap2 (B.as_seq m1 g) /\
                         (*When the function exits the loop, the stack top should point to the initial length of h_list*)
                         (*That is, the stack should contain all the elements of h_list*)
                          
                         (Usize.v (B.get m1 st_top 0) <= S.heap_size) /\
                         B.length st == S.heap_size /\
                         B.length st_top == 1 /\
                        
                         
                         Usize.v (Seq.index (B.as_seq m1 st_top) 0) <= S.heap_size /\
                         (G.is_vertex_set (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0)))) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0) /\
                                             
                         (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) m0 m1) /\
                         (forall x. Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m1 g) /\
                         (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m1 g)) /\
                                    S.isGrayObject1 x (B.as_seq m1 g) <==>
                                Seq.mem x (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))))) /\
                         
                         (B.as_seq m1 g)  ==  snd (S.create_root_stack_and_gray_modified_heap (B.as_seq m0 g) 
                                                                                (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq m0 h_list) 0 (Usize.v h_list_length))) /\
                         
                         (Seq.slice (B.as_seq m1 st) 0 (Usize.v (Seq.index (B.as_seq m1 st_top) 0))) ==
                               fst (S.create_root_stack_and_gray_modified_heap (B.as_seq m0 g) 
                                                                                    (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_top) 0)))
                                                                               (Seq.slice (B.as_seq m0 h_list) 0 (Usize.v h_list_length)))) = 
    
  let h0 = ST.get() in
  let inv h (i: nat) = B.live h g /\ B.live h st /\ B.live h st_top /\
                    B.length st_top == 1  /\
                    
                    Usize.v (Seq.index (B.as_seq h st_top) 0) <= S.heap_size /\
                    B.length st_top == 1  /\
                    B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                    B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                    B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                    B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_list) /\
                    B.loc_disjoint (B.loc_buffer st) (B.loc_buffer h_list) /\
                    B.loc_disjoint (B.loc_buffer st_top) (B.loc_buffer h_list) /\
                     
                    (Usize.v (B.get h st_top 0) <= S.heap_size) /\
                    (*One loop invariant - *)
                    (* (Seq.slice (B.as_seq m0 h_list) 0 (Usize.v (Seq.index (B.as_seq m0 h_list_length) 0)))*)
                    B.length st == S.heap_size /\
                    B.length st_top == 1 /\
                   
                    (i <=  Usize.v h_list_length) /\
                    (i >= 0) /\
                    S.well_formed_heap2 (B.as_seq h g)/\
                    Usize.v (Seq.index (B.as_seq h st_top) 0) <= S.heap_size /\
                    
                    (G.is_vertex_set (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0)))) /\
                    
                    (forall x. Seq.mem x (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==>
                                              Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\
                                              
                   (forall x. Seq.mem x (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0) /\
                                             
                   (forall x. Seq.mem x (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq h g)) /\
                               
                    
                               
                   (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h g)) /\
                                    S.isGrayObject1 x (B.as_seq h g) <==>
                                Seq.mem x (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))))  /\
                                
                   (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h0 h)  /\
                   
                   (G.is_vertex_set (Seq.slice (B.as_seq h0 h_list) (i) (Usize.v h_list_length))) /\
                   
                   (forall x. Seq.mem x (Seq.slice (B.as_seq h0 h_list) (i) (Usize.v h_list_length)) ==> 
                                               Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                   (forall x. Seq.mem x (Seq.slice (B.as_seq h0 h_list) (i) (Usize.v h_list_length)) ==> 
                                              Usize.v x % Usize.v S.mword == 0) /\
                                              
                   (forall x. Seq.mem x (Seq.slice (B.as_seq h0 h_list) (i) (Usize.v h_list_length)) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq h g)) /\
                   
                   S.mutually_exclusive_sets (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0))) 
                                             (Seq.slice (B.as_seq h0 h_list) (i) (Usize.v h_list_length)) /\
                   (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g)  
                                                               (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                               (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length)) ==
                     S.create_root_stack_and_gray_modified_heap (B.as_seq h g)  
                                                               (Seq.slice (B.as_seq h st) 0 (Usize.v (Seq.index (B.as_seq h st_top) 0)))
                                                               (Seq.slice (B.as_seq h0 h_list) (i) (Usize.v h_list_length)))                                   
                    in
  let body (i: UInt32.t{ 0 <= UInt32.v i /\ UInt32.v i < Usize.v h_list_length})
    : HA.Stack unit
    (requires (fun m -> inv m (UInt32.v i)))
    (ensures (fun m0 () m1 -> inv m0 (UInt32.v i) /\ inv m1 (UInt32.v i + 1))) = 
    let h1 = ST.get() in
    let hd =  h_list.(i) in 
    assert (S.mutually_exclusive_sets (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) 
                                             (Seq.slice (B.as_seq h0 h_list) (UInt32.v i) (Usize.v h_list_length)));
    assert ((forall x. Seq.mem x (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) ==> 
                     ~(Seq.mem x (Seq.slice (B.as_seq h0 h_list) (UInt32.v i) (Usize.v h_list_length)))) /\
            (forall x. Seq.mem x (Seq.slice (B.as_seq h0 h_list) (UInt32.v i) (Usize.v h_list_length)) ==> 
                     ~(Seq.mem x (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))))));
    assert  (forall x. Seq.mem x (S.objects2 0UL (B.as_seq h1 g)) /\
                       S.isGrayObject1 x (B.as_seq h1 g) <==>
                          Seq.mem x (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))));
    assert (S.color_of_object1 hd (B.as_seq h1 g) <> S.gray);
    S.stack_less_than_heap_size_when_one_non_gray_exists (B.as_seq h1 g) 
                                                              (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                              (v_id_f hd);
    assert (Seq.length (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) < S.heap_size);
    assert (Usize.v (Seq.index (B.as_seq h1 st_top) 0) < S.heap_size);
    push_to_stack g st st_top hd;
    let h2 = ST.get() in
    assert (B.as_seq h2 g == snd (S.push_to_stack2 (B.as_seq h1 g) 
                                                   (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) 
                                                   hd));
    assert (Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h2 st_top) 0)) == fst (S.push_to_stack2 (B.as_seq h1 g) 
                                                                                             (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) 
                                                                                             hd));  
    assert (G.is_vertex_set (Seq.slice (B.as_seq h1 h_list) (UInt32.v i) (Usize.v h_list_length)));
    assert (G.is_vertex_set (Seq.slice (B.as_seq h2 h_list) (UInt32.v i) (Usize.v h_list_length)));
    assert (Seq.length (Seq.slice (B.as_seq h2 h_list) 0 (Usize.v h_list_length)) == (Usize.v h_list_length));
    assert (UInt32.v i < Usize.v h_list_length);
    G.is_vertex_set_lemma6 (Seq.slice (B.as_seq h2 h_list) 0 (Usize.v h_list_length)) (i);
    assert (G.is_vertex_set (Seq.slice (Seq.slice (B.as_seq h2 h_list) 0 (Usize.v h_list_length)) (UInt32.v i + 1) (Usize.v h_list_length)));
    Seq.lemma_eq_intro (Seq.slice (Seq.slice (B.as_seq h2 h_list) 0 (Usize.v h_list_length)) (UInt32.v i + 1) (Usize.v h_list_length))
                       (Seq.slice (B.as_seq h2 h_list) (UInt32.v i + 1) (Usize.v h_list_length));
    assert ((Seq.slice (Seq.slice (B.as_seq h2 h_list) 0 (Usize.v h_list_length)) (UInt32.v i + 1) (Usize.v h_list_length)) ==
               (Seq.slice (B.as_seq h2 h_list) (UInt32.v i + 1) (Usize.v h_list_length)));
               
    assert (G.is_vertex_set (Seq.slice (B.as_seq h2 h_list) (UInt32.v i + 1) (Usize.v h_list_length)));
    G.is_vertex_set_lemma7 (Seq.slice (B.as_seq h2 h_list) 0 (Usize.v h_list_length)) (i);
    assert (~(Seq.mem (Seq.index (Seq.slice (B.as_seq h2 h_list) 0 (Usize.v h_list_length)) (UInt32.v i)) 
                (Seq.slice (B.as_seq h2 h_list) (UInt32.v i + 1) (Usize.v h_list_length))));
    assert (hd == Seq.index (Seq.slice (B.as_seq h2 h_list) 0 (Usize.v h_list_length)) (UInt32.v i));
    assert (S.mutually_exclusive_sets (Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h2 st_top) 0))) 
                                             (Seq.slice (B.as_seq h2 h_list) (UInt32.v i + 1) (Usize.v h_list_length)));
    assert (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h1 h2);
    S.create_root_stack_and_gray_modified_heap_rec_lemma2 (B.as_seq h1 g) 
                                                          (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                          (Seq.slice (B.as_seq h1 h_list) 0 (Usize.v h_list_length))
                                                          (i);
    assert  (S.create_root_stack_and_gray_modified_heap (B.as_seq h1 g)  
                                                               (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0)))
                                                               (Seq.slice (B.as_seq h1 h_list) (UInt32.v i) (Usize.v h_list_length)) ==
             S.create_root_stack_and_gray_modified_heap (B.as_seq h2 g)  
                                                               (Seq.slice (B.as_seq h2 st) 0 (Usize.v (Seq.index (B.as_seq h2 st_top) 0)))
                                                               (Seq.slice (B.as_seq h2 h_list) (UInt32.v i + 1) (Usize.v h_list_length)))
   in
   C.Loops.for 0ul (UInt32.uint_to_t (Usize.v h_list_length)) inv body;
   let h3 = ST.get() in
   assert (S.create_root_stack_and_gray_modified_heap (B.as_seq h3 g)  
                                                   (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                                                   (Seq.slice (B.as_seq h3 h_list) (Usize.v h_list_length) (Usize.v h_list_length)) ==
           S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g)  
                                                    (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                    (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length)));


   S.create_root_stack_and_gray_modified_heap_base_lemma1 (B.as_seq h3 g)
                                                          (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                                                          (Seq.slice (B.as_seq h3 h_list) 0 (Usize.v h_list_length))
                                                          (h_list_length);
                                                          
    
   assert ((B.as_seq h3 g) == snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h3 g)  
                                                   (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                                                   (Seq.slice (B.as_seq h3 h_list) (Usize.v h_list_length) (Usize.v h_list_length))));
   
   
   assert ((Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0))) ==
             fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h3 g)  
                                                   (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)))
                                                   (Seq.slice (B.as_seq h3 h_list) (Usize.v h_list_length) (Usize.v h_list_length))));
   
   
   assert ((B.as_seq h3 g)  ==  snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                                (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))));
                         
   assert (Seq.slice (B.as_seq h3 st) 0 (Usize.v (Seq.index (B.as_seq h3 st_top) 0)) ==
                               fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                               (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                               (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))));
   
   assert (B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h0 h3);
   ()

#restart-solver 

let wosize_of_block1 (v_id: Usize.t)
                    (g:heap)
           : HA.Stack unit
             (fun m -> B.live m g (*/\ S.well_formed_heap2 (B.as_seq m g)*) /\ 
              (Usize.v v_id >= 0 /\ Usize.v v_id < S.heap_size) /\
              (Usize.v v_id % Usize.v S.mword == 0) (*/\
              S.is_valid_header (v_id_f v_id) (B.as_seq m g)*)) 
       
             (fun h0 x h1 -> True) = 
let index = read_word_from_byte_buffer1 g v_id in
let wz = S.getWosize index in
()


#restart-solver 

/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// The sweep body without a free list maintanence - Functionally proved to equivalent to functional sweep body
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
let sweep_body_helper (g:heap)
                      (h_index: B.buffer Usize.t)
           : HA.Stack unit
               (fun m ->  B.live m g /\ B.live m h_index /\

                       B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
                       
                       S.well_formed_heap2 (B.as_seq m g) /\
                       S.noGreyObjects (B.as_seq m g) /\
                       B.length h_index == 1 /\
                       (Usize.v (Seq.index (B.as_seq m h_index) 0) >= 0 /\ 
                       Usize.v  (Seq.index (B.as_seq m h_index) 0) < S.heap_size) /\
                       (Usize.v (Seq.index (B.as_seq m h_index) 0) % Usize.v S.mword == 0) /\
                       (S.is_valid_header (v_id_f (Seq.index (B.as_seq m h_index) 0)) (B.as_seq m g)))
                       
               (fun m0 _ m1 -> B.live m1 g /\
                            B.modifies (B.loc_buffer g) m0 m1 /\
                            (B.as_seq m1 g == S.sweep_body_helper (B.as_seq m0 g) (Seq.index (B.as_seq m0 h_index) 0))) = 
 let open Usize in
 let h0 = ST.get() in
 let h_index_val = !*h_index in
 let c = color_of_block h_index_val g in
 assert (~(c == S.gray));
 if (c = S.white) then 
 (
    let h1 = ST.get() in
    assert (h0 == h1);
    colorHeader1 g h_index_val S.blue;
    let h2 = ST.get() in
    assert (B.as_seq h2 g == S.colorHeader1 h_index_val (B.as_seq h1 g) S.blue);

    assert (B.modifies (B.loc_buffer g) h1 h2);
    S.colorHeader1_wosizeLemma h_index_val (B.as_seq h1 g) S.blue h_index_val;
   assert (S.objects2 h_index_val (B.as_seq h1 g) == S.objects2 h_index_val (B.as_seq h2 g));
   Seq.lemma_eq_intro (B.as_seq h2 g) (S.sweep_body_helper (B.as_seq h1 g) h_index_val)
   
 )
 else
 (
   if (c = S.black) then 
   (
      let h3 = ST.get() in
      assert (h0 == h3);
      colorHeader1 g h_index_val S.white;
      let h4 = ST.get() in
      assert (B.as_seq h4 g == S.colorHeader1 h_index_val (B.as_seq h3 g) S.white);

      assert (B.modifies (B.loc_buffer g) h3 h4);
      S.colorHeader1_wosizeLemma h_index_val (B.as_seq h3 g) S.white h_index_val;
      assert (S.objects2 h_index_val (B.as_seq h3 g) == S.objects2 h_index_val (B.as_seq h4 g));
      Seq.lemma_eq_intro (B.as_seq h4 g) (S.sweep_body_helper (B.as_seq h3 g) h_index_val)
      
   )
   else
   (
     let h5 = ST.get() in
     assert (c == S.blue);
     S.objects2_equal_lemma h_index_val (B.as_seq h5 g) (B.as_seq h5 g);
     assert (S.objects2 h_index_val (B.as_seq h5 g) == S.objects2 h_index_val (B.as_seq h0 g));
     Seq.lemma_eq_intro (B.as_seq h5 g) (S.sweep_body_helper (B.as_seq h0 g) h_index_val)
   )
 )


#restart-solver

#restart-solver


#restart-solver 

#restart-solver
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// The sweep without a free list maintanence - Functionally proved to equivalent to functional sweep
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------

let sweep1 (g:heap)
           (h_index: B.buffer Usize.t)
           : HA.Stack unit
               (fun m ->  B.live m g /\ B.live m h_index /\

                       B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
                       
                       S.well_formed_heap2 (B.as_seq m g) /\
                       S.noGreyObjects (B.as_seq m g) /\
                       B.length h_index == 1 /\
                       (Usize.v (Seq.index (B.as_seq m h_index) 0) >= 0) /\
                       (Usize.v  (Seq.index (B.as_seq m h_index) 0) < S.heap_size) /\
                       (Usize.v (Seq.index (B.as_seq m h_index) 0) % Usize.v S.mword == 0) /\
                       (S.is_valid_header (v_id_f (Seq.index (B.as_seq m h_index) 0)) (B.as_seq m g)) /\
                       (Seq.length (S.objects2 (Seq.index (B.as_seq m h_index) 0) (B.as_seq m g)) > 0))
                       
               (fun m0 _ m1 -> B.live m1 g /\ B.live m1 h_index /\
                            B.modifies (B.loc_union (B.loc_buffer g) (B.loc_buffer h_index)) m0 m1 /\
                           (B.as_seq m1 g == S.sweep1 (B.as_seq m0 g) (Seq.index (B.as_seq m0 h_index) 0))) = 
let open Usize in
let h_init = ST.get() in
let inv h =  B.live h g /\ B.live h h_index /\
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
             B.modifies (B.loc_union (B.loc_buffer g) (B.loc_buffer h_index)) h_init h /\
             (Usize.v (Seq.index (B.as_seq h h_index) 0) % Usize.v S.mword == 0) /\
             S.well_formed_heap2 (B.as_seq h g) /\
             S.noGreyObjects (B.as_seq h g) /\
             (Usize.v (Seq.index (B.as_seq h h_index) 0) >= 0) /\
             (S.objects2 0UL ((B.as_seq h_init g)) == S.objects2 0UL (B.as_seq h g)) /\
             (Usize.v  (Seq.index (B.as_seq h h_index) 0) >= S.heap_size ==> 
                            B.as_seq h g == S.sweep1 (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0)) /\
             (Usize.v  (Seq.index (B.as_seq h h_index) 0) < S.heap_size ==>
                   (S.is_valid_header (v_id_f (Seq.index (B.as_seq h h_index) 0)) (B.as_seq h g)) /\
                   (Seq.length (S.objects2 (Seq.index (B.as_seq h h_index) 0) (B.as_seq h g)) > 0) /\
             S.sweep1 (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0) == S.sweep1 (B.as_seq h g) (Seq.index (B.as_seq h h_index) 0)) in
let guard (test: bool) h = inv h /\ 
   (test = true  ==> Usize.v (B.get h h_index 0) < S.heap_size) /\
   (test = false ==> Usize.v (B.get h h_index 0) >= S.heap_size)  in             
let test ()
     : HA.Stack bool 
       (requires (fun h -> inv h)) 
       (ensures (fun _ ret h1 -> guard ret h1)) = (!*h_index) <^ UInt64.uint_to_t (S.heap_size) in
let body ()
     : HA.Stack unit 
       (requires (fun h -> guard true h)) 
       (ensures (fun _ _ h1 -> inv h1)) = 
 let h0 = ST.get() in
 let h_index_val = !*h_index in
 let h1 = ST.get() in
 assert (h1 == h0);
 let wz = wosize_of_block h_index_val g in
 let h_index_new =  Usize.add h_index_val (Usize.mul (Usize.add wz 1UL) S.mword) in
 let h2 = ST.get() in
 assert (h1 == h2);
 assert (guard true h0);
 assert (Usize.v (B.get h0 h_index 0) < S.heap_size);
 assert (Usize.v (B.get h2 h_index 0) < S.heap_size);
 assert (Usize.v h_index_val < S.heap_size);
 
 let h3 = ST.get() in
 assert (h3 == h2);
 sweep_body_helper g h_index; 
 let h4 = ST.get() in
 assert (B.as_seq h4 g == S.sweep_body_helper (B.as_seq h3 g) (Seq.index (B.as_seq h3 h_index) 0));
 h_index.(0ul) <- h_index_new;
 S.wosize_plus_times_mword_multiple_of_mword1 wz;
 S.sum_of_multiple_of_mword_is_multiple_of_mword h_index_val (Usize.mul (Usize.add wz 1UL) S.mword);
 let h5 = ST.get() in
 if (Usize.v h_index_new >= S.heap_size) then
  (
      ()
   )
    else
    (
      assert (S.is_hp_addr h_index_new);
      S.objects2_mem_lemma1_app h_index_val (B.as_seq h3 g);
      assert (S.is_valid_header h_index_new (B.as_seq h3 g));
      assert (S.is_valid_header h_index_new (B.as_seq h5 g));
      assert (Seq.mem h_index_val (S.objects2 0UL (B.as_seq h3 g)));
      assert (Seq.length (S.objects2 0UL (B.as_seq h3 g)) > 0);
      assert (Seq.length (S.objects2 h_index_val (B.as_seq h3 g)) > 0);
      assert (Seq.length (S.objects2 h_index_val (B.as_seq h5 g)) > 0);
      S.objects2_length_lemma1 (B.as_seq h5 g) h_index_val h_index_new; 
      assert (Seq.length (S.objects2 h_index_new (B.as_seq h5 g)) > 0);
      assert (B.live h5 g /\ B.live h5 h_index /\
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
             B.modifies (B.loc_union (B.loc_buffer g) (B.loc_buffer h_index)) h0 h5 /\
             (Usize.v (Seq.index (B.as_seq h5 h_index) 0) % Usize.v S.mword == 0) /\
             S.well_formed_heap2 (B.as_seq h5 g));
      assert (Usize.v (Seq.index (B.as_seq h5 h_index) 0) >= 0);
             
      assert (Usize.v  (Seq.index (B.as_seq h5 h_index) 0) < S.heap_size ==>
                   (S.is_valid_header (v_id_f (Seq.index (B.as_seq h5 h_index) 0)) (B.as_seq h5 g)) /\
                   (Seq.length (S.objects2 (Seq.index (B.as_seq h5 h_index) 0) (B.as_seq h5 g)) > 0));
      assert (S.noGreyObjects (B.as_seq h5 g));
      ()
    )
  in
  C.Loops.while #(inv) #(guard) test body;    
  let h_after = ST.get() in
  assert (Usize.v (B.get h_after h_index 0) >= S.heap_size);
  assert (Usize.v  (Seq.index (B.as_seq h_init h_index) 0) < S.heap_size);           
  assert (B.as_seq h_after g == S.sweep1 (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0));        
  ()

#restart-solver 

#restart-solver 

#restart-solver

#restart-solver

/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// The sweep body with a free list maintanence - Functionally proved to equivalent to functional sweep body with free list
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
let sweep_body_helper_with_free_list1 (g:heap)
                                     (h_index: B.buffer Usize.t)
                                     (free_list_ptr: B.buffer Usize.t)
               : HA.Stack unit
               (fun m ->  B.live m g /\ B.live m h_index /\ B.live m free_list_ptr /\

                       B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
                       B.loc_disjoint (B.loc_buffer g) (B.loc_buffer free_list_ptr) /\
                       B.loc_disjoint (B.loc_buffer h_index) (B.loc_buffer free_list_ptr) /\
                       
                       S.well_formed_heap2 (B.as_seq m g) /\
                       S.noGreyObjects (B.as_seq m g) /\
                       B.length h_index == 1 /\
                       B.length free_list_ptr == 1 /\ 
                       (Usize.v (Seq.index (B.as_seq m h_index) 0) >= 0 /\ 
                       Usize.v  (Seq.index (B.as_seq m h_index) 0) < S.heap_size) /\
                       (Usize.v (Seq.index (B.as_seq m h_index) 0) % Usize.v S.mword == 0) /\
                       (S.is_valid_header (v_id_f (Seq.index (B.as_seq m h_index) 0)) (B.as_seq m g)) /\
                       
                       (Usize.v (Seq.index (B.as_seq m free_list_ptr) 0) >= 0 /\ 
                       Usize.v  (Seq.index (B.as_seq m free_list_ptr) 0) < S.heap_size) /\
                       (Usize.v (Seq.index (B.as_seq m free_list_ptr) 0) % Usize.v S.mword == 0) /\
                       (S.is_valid_header (v_id_f (Seq.index (B.as_seq m free_list_ptr) 0)) (B.as_seq m g)) /\
                       S.color_of_object1 (v_id_f (Seq.index (B.as_seq m free_list_ptr) 0)) (B.as_seq m g) == S.blue)
                       
               (fun m0 _ m1 -> B.live m1 g /\  B.live m1 h_index /\ B.live m1 free_list_ptr /\
                            
                            B.modifies (B.loc_union (B.loc_buffer g) (B.loc_buffer free_list_ptr)) m0 m1 /\
                            (B.as_seq m1 g == (fst (S.sweep_body_with_free_list (B.as_seq m0 g) 
                                 (Seq.index (B.as_seq m0 h_index) 0) (Seq.index (B.as_seq m0 free_list_ptr) 0)))) /\
                            (Seq.index (B.as_seq m1 free_list_ptr) 0 == 
                                 (snd (S.sweep_body_with_free_list (B.as_seq m0 g) (Seq.index (B.as_seq m0 h_index) 0) (Seq.index (B.as_seq m0 free_list_ptr) 0))))
                           ) = 
 let open Usize in
 let h0 = ST.get() in
 let h_index_val = !*h_index in
 assert (h_index_val == Seq.index (B.as_seq h0 h_index) 0);
 let c = color_of_block h_index_val g in
 assert (~(c == S.gray));
 assert (S.well_formed_heap2 (B.as_seq h0 g));
 assert (Seq.length (S.objects2 0UL (B.as_seq h0 g)) > 0);
 let wz = wosize_of_block h_index_val g in
 assert (Usize.v wz <> 0);
 if (c = S.white) then 
 (
    let h1 = ST.get() in
    assert (h0 == h1);
    colorHeader1 g h_index_val S.blue;
    let h2 = ST.get() in
    assert (B.as_seq h2 g == S.colorHeader1 h_index_val (B.as_seq h1 g) S.blue);

    assert (B.modifies (B.loc_buffer g) h1 h2);
    S.colorHeader1_wosizeLemma h_index_val (B.as_seq h1 g) S.blue h_index_val;
    assert (S.objects2 h_index_val (B.as_seq h1 g) == S.objects2 h_index_val (B.as_seq h2 g));
    Seq.lemma_eq_intro (B.as_seq h2 g) (S.sweep_body_helper (B.as_seq h1 g) h_index_val);
    assert (B.as_seq h2 g == S.sweep_body_helper (B.as_seq h1 g) h_index_val);
    assert (S.well_formed_heap2 (B.as_seq h2 g));
    assert (S.objects2 0UL (B.as_seq h1 g) == S.objects2 0UL (B.as_seq h2 g));
    assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h1 free_list_ptr) 0)) (B.as_seq h1 g));
    let free_list_ptr_val = !*free_list_ptr in
    let first_field_free_list_ptr = Usize.add free_list_ptr_val S.mword in
    S.sum_of_multiple_of_mword_is_multiple_of_mword free_list_ptr_val S.mword;
    assert (Usize.v first_field_free_list_ptr < S.heap_size);
    assert (Usize.v first_field_free_list_ptr % Usize.v S.mword == 0);
    assert (S.is_hp_addr first_field_free_list_ptr);

    (*updating the first field of the free_list --> heap change*)
    write_word_to_byte_buffer3 g first_field_free_list_ptr h_index_val;
    //S.write_word_lemma (B.as_seq h2 g) first_field_free_list_ptr h_index_val;
    S.write_word_to_blue_object_field_lemma1 (B.as_seq h2 g) free_list_ptr_val first_field_free_list_ptr h_index_val;
    S.write_word_to_blue_object_field_lemma (B.as_seq h2 g) free_list_ptr_val first_field_free_list_ptr h_index_val;
    let h3 = ST.get() in
    assert (B.modifies (B.loc_buffer g) h2 h3);
    (*Updating the free list pointer to point to h_index ---> no heap change*)
    free_list_ptr.(0ul) <- h_index_val;
    let h4 = ST.get() in
    assert (B.modifies (B.loc_buffer free_list_ptr) h3 h4);
    assert (B.as_seq h4 g == B.as_seq h3 g);
    assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_buffer free_list_ptr)) h1 h4);
    Seq.lemma_eq_intro (B.as_seq h4 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) h_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0)));
    Seq.lemma_eq_intro (B.as_seq h4 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 h_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0)));
    assert (Seq.index (B.as_seq h4 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) h_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0))));
    assert (Seq.index (B.as_seq h4 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 h_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
     assert (B.as_seq h4 g == (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 h_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
     ()
   
 )
 else
 (
   if (c = S.black) then 
   (
      let h3 = ST.get() in
      assert (h0 == h3);
      colorHeader1 g h_index_val S.white;
      let h4 = ST.get() in
      assert (B.as_seq h4 g == S.colorHeader1 h_index_val (B.as_seq h3 g) S.white);

      assert (B.modifies (B.loc_buffer g) h3 h4);
      S.colorHeader1_wosizeLemma h_index_val (B.as_seq h3 g) S.white h_index_val;
      assert (S.objects2 h_index_val (B.as_seq h3 g) == S.objects2 h_index_val (B.as_seq h4 g));
      Seq.lemma_eq_intro (B.as_seq h4 g) (S.sweep_body_helper (B.as_seq h3 g) h_index_val);
      Seq.lemma_eq_intro (B.as_seq h4 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) h_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0)));
      Seq.lemma_eq_intro (B.as_seq h4 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 h_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0)));
      assert (Seq.index (B.as_seq h4 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) h_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0))));
      assert (Seq.index (B.as_seq h4 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 h_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
      assert (B.as_seq h4 g == (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 h_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
      ()
      
   )
   else
   (
     let h5 = ST.get() in
     assert (c == S.blue);
     S.objects2_equal_lemma h_index_val (B.as_seq h5 g) (B.as_seq h5 g);
     assert (S.objects2 h_index_val (B.as_seq h5 g) == S.objects2 h_index_val (B.as_seq h0 g));
     Seq.lemma_eq_intro (B.as_seq h5 g) (S.sweep_body_helper (B.as_seq h0 g) h_index_val);
     Seq.lemma_eq_intro (B.as_seq h5 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) h_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0)));
     assert (Seq.index (B.as_seq h0 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) h_index_val (Seq.index (B.as_seq h0 free_list_ptr) 0))));
     Seq.lemma_eq_intro (B.as_seq h5 g) (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 h_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0)));
     assert (Seq.index (B.as_seq h0 free_list_ptr) 0 == (snd (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 h_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
     assert (B.as_seq h5 g == (fst (S.sweep_body_with_free_list (B.as_seq h0 g) (Seq.index (B.as_seq h0 h_index) 0) (Seq.index (B.as_seq h0 free_list_ptr) 0))));
     ()
   )
 )


#restart-solver 

#restart-solver 

#restart-solver

/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// The sweep body with a free list maintanence - Functionally proved to equivalent to functional sweep with free list
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// 
let sweep1_with_free_list1 (g:heap)
                           (h_index: B.buffer Usize.t)
                           (free_list_ptr: B.buffer Usize.t)
           : HA.Stack unit
               (fun m ->  B.live m g /\ B.live m h_index /\ B.live m free_list_ptr /\

                       B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
                       B.loc_disjoint (B.loc_buffer g) (B.loc_buffer free_list_ptr) /\
                       B.loc_disjoint (B.loc_buffer h_index) (B.loc_buffer free_list_ptr) /\
                       
                       S.well_formed_heap2 (B.as_seq m g) /\
                       S.noGreyObjects (B.as_seq m g) /\
                       B.length h_index == 1 /\
                       B.length free_list_ptr == 1 /\
                       (Usize.v (Seq.index (B.as_seq m h_index) 0) >= 0) /\
                       (Usize.v  (Seq.index (B.as_seq m h_index) 0) < S.heap_size) /\
                       (Usize.v (Seq.index (B.as_seq m h_index) 0) % Usize.v S.mword == 0) /\
                       (S.is_valid_header (v_id_f (Seq.index (B.as_seq m h_index) 0)) (B.as_seq m g)) (*/\
                       (Seq.length (S.objects2 (Seq.index (B.as_seq m h_index) 0) (B.as_seq m g)) > 0)*) /\
                       
                       (Usize.v (Seq.index (B.as_seq m free_list_ptr) 0) >= 0 /\ 
                       Usize.v  (Seq.index (B.as_seq m free_list_ptr) 0) < S.heap_size) /\
                       (Usize.v (Seq.index (B.as_seq m free_list_ptr) 0) % Usize.v S.mword == 0) /\
                       (S.is_valid_header (v_id_f (Seq.index (B.as_seq m free_list_ptr) 0)) (B.as_seq m g)) /\
                       (S.color_of_object1 (v_id_f (Seq.index (B.as_seq m free_list_ptr) 0)) (B.as_seq m g) == S.blue))
                       
               (fun m0 _ m1 -> B.live m1 g /\ B.live m1 h_index  /\ B.live m1 free_list_ptr /\
                            (fst (S.sweep_with_free_list (B.as_seq m0 g) (Seq.index (B.as_seq m0 h_index) 0) 
                                        (Seq.index (B.as_seq m0 free_list_ptr) 0)) == B.as_seq m1 g) /\
                            (snd (S.sweep_with_free_list (B.as_seq m0 g) 
                                        (Seq.index (B.as_seq m0 h_index) 0) (Seq.index (B.as_seq m0 free_list_ptr) 0)) ==  
                                               Seq.index (B.as_seq m1 free_list_ptr) 0) /\
                            (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer free_list_ptr) (B.loc_buffer h_index))) m0 m1)) =
let open Usize in
let h_init = ST.get() in
let inv h =  B.live h g /\ B.live h h_index /\ B.live h free_list_ptr /\

             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer free_list_ptr) /\
             B.loc_disjoint (B.loc_buffer h_index) (B.loc_buffer free_list_ptr) /\
             
             
             B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer free_list_ptr) (B.loc_buffer h_index))) h_init h /\
             (Usize.v (Seq.index (B.as_seq h h_index) 0) % Usize.v S.mword == 0) /\
             S.well_formed_heap2 (B.as_seq h g) /\
             
             B.length h_index == 1 /\
             B.length free_list_ptr == 1 /\ 
             
             S.noGreyObjects (B.as_seq h g) /\
             (Usize.v (Seq.index (B.as_seq h h_index) 0) >= 0) /\
             (S.objects2 0UL ((B.as_seq h_init g)) == S.objects2 0UL (B.as_seq h g))  /\
              
             
             (Usize.v (Seq.index (B.as_seq h free_list_ptr) 0) >= 0 /\ 
              Usize.v  (Seq.index (B.as_seq h free_list_ptr) 0) < S.heap_size) /\
              (Usize.v (Seq.index (B.as_seq h free_list_ptr) 0) % Usize.v S.mword == 0) /\
             (S.is_valid_header (v_id_f (Seq.index (B.as_seq h free_list_ptr) 0)) (B.as_seq h g)) /\
             (S.color_of_object1 (v_id_f (Seq.index (B.as_seq h free_list_ptr) 0)) (B.as_seq h g) == S.blue) /\
             (Usize.v  (Seq.index (B.as_seq h h_index) 0) >= S.heap_size ==> 
                       (B.as_seq h g == 
                          (fst (S.sweep_with_free_list (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)))) /\
                        (Seq.index (B.as_seq h free_list_ptr) 0 == 
                          (snd (S.sweep_with_free_list (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0))))) /\
             (*(Usize.v  (Seq.index (B.as_seq h h_index) 0) < S.heap_size ==>
                   (S.is_valid_header (v_id_f (Seq.index (B.as_seq h h_index) 0)) (B.as_seq h g)) /\
                   (S.sweep_with_free_list (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0) == 
                      S.sweep_with_free_list (B.as_seq h g) (Seq.index (B.as_seq h h_index) 0) (Seq.index (B.as_seq h free_list_ptr) 0)))*) 
             (Usize.v  (Seq.index (B.as_seq h h_index) 0) < S.heap_size ==>
                   (S.is_valid_header (v_id_f (Seq.index (B.as_seq h h_index) 0)) (B.as_seq h g)) /\
                   (fst (S.sweep_with_free_list (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) == 
                      fst (S.sweep_with_free_list (B.as_seq h g) (Seq.index (B.as_seq h h_index) 0) (Seq.index (B.as_seq h free_list_ptr) 0))) /\
                    (snd (S.sweep_with_free_list (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) == 
                      snd (S.sweep_with_free_list (B.as_seq h g) (Seq.index (B.as_seq h h_index) 0) (Seq.index (B.as_seq h free_list_ptr) 0))) )  in
let guard (test: bool) h = inv h /\ 
   (test = true  ==> Usize.v (B.get h h_index 0) < S.heap_size) /\
   (test = false ==> Usize.v (B.get h h_index 0) >= S.heap_size)  in             
let test ()
     : HA.Stack bool 
       (requires (fun h -> inv h)) 
       (ensures (fun _ ret h1 -> guard ret h1)) = (!*h_index) <^ UInt64.uint_to_t (S.heap_size) in
let body ()
     : HA.Stack unit 
       (requires (fun h -> guard true h)) 
       (ensures (fun _ _ h1 -> inv h1)) = 
 let h0 = ST.get() in
 let h_index_val = !*h_index in
 let h1 = ST.get() in
 assert (h1 == h0);
 let wz = wosize_of_block h_index_val g in
 let h_index_new =  Usize.add h_index_val (Usize.mul (Usize.add wz 1UL) S.mword) in
 let h2 = ST.get() in
 assert (h1 == h2);
 assert (guard true h0);
 assert (Usize.v (B.get h0 h_index 0) < S.heap_size);
 assert (Usize.v (B.get h2 h_index 0) < S.heap_size);
 assert (Usize.v h_index_val < S.heap_size);
 
 let h3 = ST.get() in
 assert (h3 == h2);
 sweep_body_helper_with_free_list1 g h_index free_list_ptr; 
 let h4 = ST.get() in
 assert (B.as_seq h4 g == (fst (S.sweep_body_with_free_list (B.as_seq h3 g) 
                                 (Seq.index (B.as_seq h3 h_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0))));
 assert(Seq.index (B.as_seq h4 free_list_ptr) 0 == 
                                 (snd (S.sweep_body_with_free_list (B.as_seq h3 g) (Seq.index (B.as_seq h3 h_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0))));
 S.sweep_body_with_free_list_lemma (B.as_seq h3 g) (Seq.index (B.as_seq h3 h_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0);
 S.sweep_body_with_free_list_lemma1 (B.as_seq h3 g) (Seq.index (B.as_seq h3 h_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0);
 S.sweep_body_with_free_list_lemma2 (B.as_seq h3 g) (Seq.index (B.as_seq h3 h_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0);
 assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_buffer free_list_ptr)) h3 h4);
 h_index.(0ul) <- h_index_new;
 S.wosize_plus_times_mword_multiple_of_mword1 wz;
 S.sum_of_multiple_of_mword_is_multiple_of_mword h_index_val (Usize.mul (Usize.add wz 1UL) S.mword);
 let h5 = ST.get() in
 assert (B.modifies (B.loc_buffer h_index) h4 h5);
 assert (B.as_seq h4 g == B.as_seq h5 g);
 assert(Seq.index (B.as_seq h4 free_list_ptr) 0 == Seq.index (B.as_seq h5 free_list_ptr) 0);
 assert (B.as_seq h5 g == (fst (S.sweep_body_with_free_list (B.as_seq h3 g) 
                                 (Seq.index (B.as_seq h3 h_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0))));
 assert(Seq.index (B.as_seq h5 free_list_ptr) 0 == 
                                 (snd (S.sweep_body_with_free_list (B.as_seq h3 g) (Seq.index (B.as_seq h3 h_index) 0) (Seq.index (B.as_seq h3 free_list_ptr) 0))));
 assert (Usize.v (Seq.index (B.as_seq h5 h_index) 0) == Usize.v h_index_new);
 if (Usize.v h_index_new >= S.heap_size) then
  (
             assert (B.live h5 g /\ B.live h5 h_index /\ B.live h5 free_list_ptr /\

             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
             B.loc_disjoint (B.loc_buffer g) (B.loc_buffer free_list_ptr) /\
             B.loc_disjoint (B.loc_buffer h_index) (B.loc_buffer free_list_ptr));
      ()
   )
    else
    (
      assert (S.is_hp_addr h_index_new);
      S.objects2_mem_lemma1_app h_index_val (B.as_seq h3 g);
      assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer free_list_ptr) (B.loc_buffer h_index))) h0 h5);
      assert (Usize.v (Seq.index (B.as_seq h5 h_index) 0) % Usize.v S.mword == 0);
      assert (S.well_formed_heap2 (B.as_seq h5 g));
             
      assert (B.length h_index == 1);
      assert (B.length free_list_ptr == 1);
             
      assert (S.noGreyObjects (B.as_seq h5 g));
      assert (Usize.v (Seq.index (B.as_seq h5 h_index) 0) >= 0);
      assert (S.objects2 0UL ((B.as_seq h0 g)) == S.objects2 0UL (B.as_seq h5 g));
      assert (Usize.v  (Seq.index (B.as_seq h5 h_index) 0) < S.heap_size ==>
                   (S.is_valid_header (v_id_f (Seq.index (B.as_seq h5 h_index) 0)) (B.as_seq h5 g)));
             
      assert (Usize.v (Seq.index (B.as_seq h5 free_list_ptr) 0) >= 0 /\ 
              Usize.v  (Seq.index (B.as_seq h5 free_list_ptr) 0) < S.heap_size);
      assert (Usize.v (Seq.index (B.as_seq h5 free_list_ptr) 0) % Usize.v S.mword == 0);
      assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h5 free_list_ptr) 0)) (B.as_seq h5 g));
      assert (S.color_of_object1 (v_id_f (Seq.index (B.as_seq h5 free_list_ptr) 0)) (B.as_seq h5 g) == S.blue); 
      
      ()
    )
  in
  C.Loops.while #(inv) #(guard) test body;    
  let h_after = ST.get() in
  assert (Usize.v (B.get h_after h_index 0) >= S.heap_size);
  assert (Usize.v (Seq.index (B.as_seq h_after h_index) 0) > 0);
  assert (Usize.v  (Seq.index (B.as_seq h_init h_index) 0) < S.heap_size); 
  assert (Usize.v (Seq.index (B.as_seq h_after h_index) 0) >= S.heap_size);
  assert (fst (S.sweep_with_free_list (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) ==
           B.as_seq h_after g);
  assert (snd (S.sweep_with_free_list (B.as_seq h_init g) (Seq.index (B.as_seq h_init h_index) 0) (Seq.index (B.as_seq h_init free_list_ptr) 0)) ==
           Seq.index (B.as_seq h_after free_list_ptr) 0);
  assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer free_list_ptr) (B.loc_buffer h_index))) h_init h_after);
 ()

#restart-solver 


#restart-solver

#restart-solver

let mark_and_sweep_GC1_aux1  (g:heap)
                             (st: B.buffer Usize.t{B.length st == S.heap_size})
                             (st_top: B.buffer Usize.t) 
                             (h_list: B.buffer Usize.t {B.length h_list == S.heap_size})
                             (h_list_length: Usize.t) 
                             (h_index: B.buffer Usize.t) 
                  : HA.Stack unit 
                    (fun m ->  (*Liveness of buffers------------------------------------------------------------------------*)
                   B.live m g /\ B.live m st /\ B.live m st_top /\ B.live m h_list /\ B.live m h_index /\

                   (*Length of st_top---------------------------------------------------------------------------*)
                   B.length st_top == 1 /\
                   B.length h_index == 1 /\
                   
                   (*Disjointness of buffers = C(5,2) = (5!/(2! * 3!)) =10 ------------------------------------------*)
                   (*4 buffers, so 6 pairwise combinations*)
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_list) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer h_list) /\
                   B.loc_disjoint (B.loc_buffer st_top) (B.loc_buffer h_list) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer h_index) /\
                   B.loc_disjoint (B.loc_buffer st_top) (B.loc_buffer h_index) /\
                   B.loc_disjoint (B.loc_buffer h_list) (B.loc_buffer h_index) /\

                   (*Range of st_top----------------------------------------------------------------------------*)
                   Usize.v (Seq.index (B.as_seq m st_top) 0) <= S.heap_size /\
                   Usize.v (Seq.index (B.as_seq m st_top) 0) >= 0 /\

                   (*Range of h_list_length---------------------------------------------------------------------*)
                   Usize.v h_list_length <= S.heap_size /\
                   
                   (*Algebraic properties of the contents of the buffers. This should match with spec-----------*)
                   (*heap-------------------------------------*)
                   S.well_formed_heap2 (B.as_seq m g) /\
                   
                   (*We need to reason about only the used parts of st; that is upto st_top---------------------*)
                   (*stack--------------------------------------------------------------------------------------*)
                   (G.is_vertex_set (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>  Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0) /\
                                             
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m g)) /\
                               
                   (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\
                                    S.isGrayObject1 x (B.as_seq m g) <==>
                                Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                   
                   (*We need to reason about only the used parts of h_list; that is upto h_list_length---------------*)
                   (*h_list------------------------------------------------------------------------------------------*)

                   (G.is_vertex_set (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length))) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) ==> 
                                               Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                   (forall x. Seq.mem x (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) ==> 
                                              Usize.v x % Usize.v S.mword == 0) /\
                                              
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m g)) /\
                   
                   S.mutually_exclusive_sets (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) 
                                             (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) /\
                   
                   (Usize.v (Seq.index (B.as_seq m h_index) 0) == 0) /\
                   (Usize.v  (Seq.index (B.as_seq m h_index) 0) < S.heap_size) /\
                   (Usize.v (Seq.index (B.as_seq m h_index) 0) % Usize.v S.mword == 0) /\
                   (S.is_valid_header (v_id_f (Seq.index (B.as_seq m h_index) 0)) (B.as_seq m g)) /\
                   (Seq.length (S.objects2 (Seq.index (B.as_seq m h_index) 0) (B.as_seq m g)) > 0))
                       
                    (fun m0 _ m1 -> True)=
let h0 = ST.get () in
create_root_stack_and_gray_modified_heap_loop g st st_top h_list h_list_length;
let h1 = ST.get () in
assert ((B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h0 h1));
assert (Usize.v (Seq.index (B.as_seq h0 h_index) 0) == 0);
assert (Usize.v (Seq.index (B.as_seq h1 h_index) 0) == 0);
assert (S.well_formed_heap2 (B.as_seq h1 g));
assert (Seq.length (S.objects2 0UL (B.as_seq h1 g)) > 0);
assert (Seq.length (S.objects2 (Seq.index (B.as_seq h1 h_index) 0) (B.as_seq h1 g)) > 0);
assert (S.is_valid_header 0UL (B.as_seq h1 g));
assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h1 h_index) 0)) (B.as_seq h1 g));
//assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h1 h_index) 0)) (B.as_seq h1 g));

                                                                             
                         
assert ((B.as_seq h1 g) == snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                                (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))));                         


assert ((Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) ==
                               fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                   (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                   (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))));
mark_heap5 g st st_top;
let h2 = ST.get () in
assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h1 h2);
assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h0 h2);

assert ((B.as_seq h2 g) == S.mark5 (B.as_seq h1 g) (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))));

assert ((B.as_seq h2 g) == S.mark5 (snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                                (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))))
                                   (fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                   (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                   (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length)))));

S.well_formed_heap2_after_mark5 (B.as_seq h1 g) ((Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))));
assert (S.well_formed_heap2 (B.as_seq h2 g));
S.no_grey_objects_after_mark5 (B.as_seq h1 g) ((Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))));
assert (Usize.v (Seq.index (B.as_seq h2 h_index) 0) == 0);
assert (S.well_formed_heap2 (B.as_seq h2 g));
assert (Seq.length (S.objects2 0UL (B.as_seq h2 g)) > 0);
assert (Seq.length (S.objects2 (Seq.index (B.as_seq h2 h_index) 0) (B.as_seq h2 g)) > 0);
assert (S.is_valid_header 0UL (B.as_seq h2 g));
assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h2 h_index) 0)) (B.as_seq h2 g));
assert (S.noGreyObjects (B.as_seq h2 g));
assert (B.live h2 g /\ B.live h2 h_index /\

        B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index));
assert (S.well_formed_heap2 (B.as_seq h2 g) /\
        S.noGreyObjects (B.as_seq h2 g) /\
        B.length h_index == 1 /\
       (Usize.v (Seq.index (B.as_seq h2 h_index) 0) >= 0) /\
       (Usize.v  (Seq.index (B.as_seq h2 h_index) 0) < S.heap_size) /\
       (Usize.v (Seq.index (B.as_seq h2 h_index) 0) % Usize.v S.mword == 0));
assert (Seq.length (S.objects2 (Seq.index (B.as_seq h0 h_index) 0) (B.as_seq h0 g)) > 0);
assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h0 h_index) 0)) (B.as_seq h0 g));
assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h0 h2);

assert (Seq.length (S.objects2 (Seq.index (B.as_seq h2 h_index) 0) (B.as_seq h2 g)) > 0);
assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h2 h_index) 0)) (B.as_seq h2 g));

sweep1 g h_index;
let h3 = ST.get() in
assert (B.live h2 g /\ B.live h2 h_index /\
        B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index)); 
                       
assert (B.as_seq h3 g == S.sweep1 (B.as_seq h2 g) (Seq.index (B.as_seq h2 h_index) 0));
assert (B.as_seq h3 g == S.sweep1 (S.mark5 (snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                                (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))))
                                   (fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                   (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                   (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length)))))
                                   (Seq.index (B.as_seq h2 h_index) 0));
assert (Seq.index (B.as_seq h2 h_index) 0 == Seq.index (B.as_seq h0 h_index) 0);
assert (B.as_seq h3 g == S.sweep1 (S.mark5 (snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                                (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))))
                                   (fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                   (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                   (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length)))))
                                   (Seq.index (B.as_seq h0 h_index) 0));
S.sweep1_heap_lemma (B.as_seq h2 g);
S.sweep1_heap_color_lemma (B.as_seq h2 g);
 assert (S.well_formed_heap2 (B.as_seq h3 g));
 assert (S.noGreyObjects (B.as_seq h3 g));
 assert (S.noBlackObjects (B.as_seq h3 g));
 assert (S.only_white_and_blue_blocks (B.as_seq h3 g));
 assert ((S.well_formed_heap2 (B.as_seq h2 g)) /\ (S. noGreyObjects (B.as_seq h2 g))); 
 assert (S.is_valid_header (Seq.index (B.as_seq h0 h_index) 0) (B.as_seq h2 g));
 assert (Seq.length (S.objects2 (Seq.index (B.as_seq h0 h_index) 0)  (B.as_seq h2 g)) > 0);
 ()

#restart-solver 

/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// mark and sweep GC that uses the functionally verified functions. Proved to be equivalent to its functional counter parts.
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
let mark_and_sweep_GC1_aux3  (g:heap)
                             (st: B.buffer Usize.t{B.length st == S.heap_size})
                             (st_top: B.buffer Usize.t) 
                             (h_list: B.buffer Usize.t {B.length h_list == S.heap_size})
                             (h_list_length: Usize.t) 
                             (h_index: B.buffer Usize.t) 
                  : HA.Stack unit 
                    (fun m ->  (*Liveness of buffers------------------------------------------------------------------------*)
                   B.live m g /\ B.live m st /\ B.live m st_top /\ B.live m h_list /\ B.live m h_index /\

                   (*Length of st_top---------------------------------------------------------------------------*)
                   B.length st_top == 1 /\
                   B.length h_index == 1 /\
                   
                   (*Disjointness of buffers = C(5,2) = (5!/(2! * 3!)) =10 ------------------------------------------*)
                   (*4 buffers, so 6 pairwise combinations*)
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer st_top) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer st_top) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_list) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer h_list) /\
                   B.loc_disjoint (B.loc_buffer st_top) (B.loc_buffer h_list) /\
                   B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index) /\
                   B.loc_disjoint (B.loc_buffer st) (B.loc_buffer h_index) /\
                   B.loc_disjoint (B.loc_buffer st_top) (B.loc_buffer h_index) /\
                   B.loc_disjoint (B.loc_buffer h_list) (B.loc_buffer h_index) /\

                   (*Range of st_top----------------------------------------------------------------------------*)
                   Usize.v (Seq.index (B.as_seq m st_top) 0) <= S.heap_size /\
                   Usize.v (Seq.index (B.as_seq m st_top) 0) >= 0 /\

                   (*Range of h_list_length---------------------------------------------------------------------*)
                   Usize.v h_list_length <= S.heap_size /\
                   
                   (*Algebraic properties of the contents of the buffers. This should match with spec-----------*)
                   (*heap-------------------------------------*)
                   S.well_formed_heap2 (B.as_seq m g) /\
                   
                   (*We need to reason about only the used parts of st; that is upto st_top---------------------*)
                   (*stack--------------------------------------------------------------------------------------*)
                   (G.is_vertex_set (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>  Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==> Usize.v x % Usize.v S.mword == 0) /\
                                             
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m g)) /\
                               
                   (forall x. Seq.mem x (S.objects2 0UL (B.as_seq m g)) /\
                                    S.isGrayObject1 x (B.as_seq m g) <==>
                                Seq.mem x (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0)))) /\
                   
                   (*We need to reason about only the used parts of h_list; that is upto h_list_length---------------*)
                   (*h_list------------------------------------------------------------------------------------------*)

                   (G.is_vertex_set (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length))) /\
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) ==> 
                                               Usize.v x >= 0 /\ Usize.v x < S.heap_size) /\

                   (forall x. Seq.mem x (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) ==> 
                                              Usize.v x % Usize.v S.mword == 0) /\
                                              
                   (forall x. Seq.mem x (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) ==>
                               S.is_valid_header (v_id_f x) (B.as_seq m g)) /\
                   
                   S.mutually_exclusive_sets (Seq.slice (B.as_seq m st) 0 (Usize.v (Seq.index (B.as_seq m st_top) 0))) 
                                             (Seq.slice (B.as_seq m h_list) 0 (Usize.v h_list_length)) /\
                   
                   (Usize.v (Seq.index (B.as_seq m h_index) 0) == 0) /\
                   (Usize.v  (Seq.index (B.as_seq m h_index) 0) < S.heap_size) /\
                   (Usize.v (Seq.index (B.as_seq m h_index) 0) % Usize.v S.mword == 0) /\
                   (S.is_valid_header (v_id_f (Seq.index (B.as_seq m h_index) 0)) (B.as_seq m g)) /\
                   (Seq.length (S.objects2 (Seq.index (B.as_seq m h_index) 0) (B.as_seq m g)) > 0))
                       
                   (fun m0 _ m1 ->   let g2 = (S.mark5 (snd (S.create_root_stack_and_gray_modified_heap (B.as_seq m0 g) 
                                                                                (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq m0 h_list) 0 (Usize.v h_list_length))))
                                   (fst (S.create_root_stack_and_gray_modified_heap (B.as_seq m0 g) 
                                   (Seq.slice (B.as_seq m0 st) 0 (Usize.v (Seq.index (B.as_seq m0 st_top) 0)))
                                   (Seq.slice (B.as_seq m0 h_list) 0 (Usize.v h_list_length))))) in
                                   let sw = (Seq.index (B.as_seq m0 h_index) 0) in
                                   (S.well_formed_heap2 g2) /\
                                   (S.noGreyObjects g2) /\
                                   B.as_seq m1 g == S.sweep1 g2 sw)= 
 let h0 = ST.get () in
create_root_stack_and_gray_modified_heap_loop g st st_top h_list h_list_length;
let h1 = ST.get () in
assert ((B.modifies (B.loc_union (B.loc_buffer g) 
                                 (B.loc_union (B.loc_buffer st) (B.loc_buffer st_top))) h0 h1));
assert (Usize.v (Seq.index (B.as_seq h0 h_index) 0) == 0);
assert (Usize.v (Seq.index (B.as_seq h1 h_index) 0) == 0);
assert (S.well_formed_heap2 (B.as_seq h1 g));
assert (Seq.length (S.objects2 0UL (B.as_seq h1 g)) > 0);
assert (Seq.length (S.objects2 (Seq.index (B.as_seq h1 h_index) 0) (B.as_seq h1 g)) > 0);
assert (S.is_valid_header 0UL (B.as_seq h1 g));
assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h1 h_index) 0)) (B.as_seq h1 g));
//assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h1 h_index) 0)) (B.as_seq h1 g));

                                                                             
                         
assert ((B.as_seq h1 g) == snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                                (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))));                         


assert ((Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))) ==
                               fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                   (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                   (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))));
mark_heap5 g st st_top;
let h2 = ST.get () in
assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h1 h2);
assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h0 h2);

assert ((B.as_seq h2 g) == S.mark5 (B.as_seq h1 g) (Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))));

assert ((B.as_seq h2 g) == S.mark5 (snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                                (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))))
                                   (fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                   (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                   (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length)))));

S.well_formed_heap2_after_mark5 (B.as_seq h1 g) ((Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))));
assert (S.well_formed_heap2 (B.as_seq h2 g));
S.no_grey_objects_after_mark5 (B.as_seq h1 g) ((Seq.slice (B.as_seq h1 st) 0 (Usize.v (Seq.index (B.as_seq h1 st_top) 0))));
assert (Usize.v (Seq.index (B.as_seq h2 h_index) 0) == 0);
assert (S.well_formed_heap2 (B.as_seq h2 g));
assert (Seq.length (S.objects2 0UL (B.as_seq h2 g)) > 0);
assert (Seq.length (S.objects2 (Seq.index (B.as_seq h2 h_index) 0) (B.as_seq h2 g)) > 0);
assert (S.is_valid_header 0UL (B.as_seq h2 g));
assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h2 h_index) 0)) (B.as_seq h2 g));
assert (S.noGreyObjects (B.as_seq h2 g));
assert (B.live h2 g /\ B.live h2 h_index /\

        B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index));
assert (S.well_formed_heap2 (B.as_seq h2 g) /\
        S.noGreyObjects (B.as_seq h2 g) /\
        B.length h_index == 1 /\
       (Usize.v (Seq.index (B.as_seq h2 h_index) 0) >= 0) /\
       (Usize.v  (Seq.index (B.as_seq h2 h_index) 0) < S.heap_size) /\
       (Usize.v (Seq.index (B.as_seq h2 h_index) 0) % Usize.v S.mword == 0));
assert (Seq.length (S.objects2 (Seq.index (B.as_seq h0 h_index) 0) (B.as_seq h0 g)) > 0);
assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h0 h_index) 0)) (B.as_seq h0 g));
assert (B.modifies (B.loc_union (B.loc_buffer g) (B.loc_union (B.loc_buffer st_top) (B.loc_buffer st))) h0 h2);

assert (Seq.length (S.objects2 (Seq.index (B.as_seq h2 h_index) 0) (B.as_seq h2 g)) > 0);
assert (S.is_valid_header (v_id_f (Seq.index (B.as_seq h2 h_index) 0)) (B.as_seq h2 g));

sweep1 g h_index;
let h3 = ST.get() in
assert (B.live h2 g /\ B.live h2 h_index /\
        B.loc_disjoint (B.loc_buffer g) (B.loc_buffer h_index)); 
                       
assert (B.as_seq h3 g == S.sweep1 (B.as_seq h2 g) (Seq.index (B.as_seq h2 h_index) 0));
assert (B.as_seq h3 g == S.sweep1 (S.mark5 (snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                                (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))))
                                   (fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                   (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                   (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length)))))
                                   (Seq.index (B.as_seq h2 h_index) 0));
assert (Seq.index (B.as_seq h2 h_index) 0 == Seq.index (B.as_seq h0 h_index) 0);
assert (B.as_seq h3 g == S.sweep1 (S.mark5 (snd (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                                                                (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                                                                (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length))))
                                   (fst (S.create_root_stack_and_gray_modified_heap (B.as_seq h0 g) 
                                   (Seq.slice (B.as_seq h0 st) 0 (Usize.v (Seq.index (B.as_seq h0 st_top) 0)))
                                   (Seq.slice (B.as_seq h0 h_list) 0 (Usize.v h_list_length)))))
                                   (Seq.index (B.as_seq h0 h_index) 0));
S.sweep1_heap_lemma (B.as_seq h2 g);
S.sweep1_heap_color_lemma (B.as_seq h2 g);
 assert (S.well_formed_heap2 (B.as_seq h3 g));
 assert (S.noGreyObjects (B.as_seq h3 g));
 assert (S.noBlackObjects (B.as_seq h3 g));
 assert (S.only_white_and_blue_blocks (B.as_seq h3 g));
 assert ((S.well_formed_heap2 (B.as_seq h2 g)) /\ (S. noGreyObjects (B.as_seq h2 g))); 
 assert (S.is_valid_header (Seq.index (B.as_seq h0 h_index) 0) (B.as_seq h2 g));
 assert (Seq.length (S.objects2 (Seq.index (B.as_seq h0 h_index) 0)  (B.as_seq h2 g)) > 0);
 ()
                   
(*The above mark and sweep GC uses sweep without free list. If the sweep is replaced with sweep with free list, then the GC changes to another variant where a free list is also maintained. The same proving startegy as above can be used for proving it's functioonal equivalence.*)

(*Many more features can be added in any sub-function and the proving startegy remains more or less the same*)
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
