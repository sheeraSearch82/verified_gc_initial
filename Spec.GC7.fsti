module Spec.GC7

open FStar.Seq
open FStar.Seq.Base

open FStar.Mul
//open FStar.Bytes
open FStar.Endianness

module H = FStar.HyperStack
module HA = FStar.HyperStack.All

//Machine integer
module Usize = FStar.UInt64

module U8 = FStar.UInt8

module U32 = FStar.UInt32

module G = Spec.Graph3

module D = DFS2

 (*Karamel is not going to extract the definition*)
///Machine words corresponding to a 64 bit machine
//If using a 32 bit machine, mword = 8ul
noextract inline_for_extraction
unfold let mword = 8UL

 (*Karamel is not going to extract the definition*)
///Machine words corresponding to a 64 bit machine

/// heap_size indicates the heap memory size. A valid object address should lie between heap_low to heap_high.

noextract inline_for_extraction
unfold let heap_size = 1024

//type mword = m:Usize.t{Usize.v m > 0}

let is_heap_size_multiple_of_mwords ()
          : Tot (b:bool{b == true <==> heap_size % (Usize.v mword) == 0})= 
  if (heap_size % (Usize.v mword) = 0) then true
 else
   false

let test  =
  assert (is_heap_size_multiple_of_mwords ())

(*Colors used in OCaml for 64 bit machine. For 32 bit machine, ul has to be used instead of UL*)
let blue = 0UL
let white = 1UL
let gray = 2UL
let black = 3UL

/// ------------OCaml object header for a 64 bit machine--------------------
///        wosize          color       tag
/// |--------------------|---------|------------|--------------------------
///       54 bits          2 bits       8 bits      variable length fields

(*max word size for data fields for 64 bit machines*)
(*----------------------------------------------------------------------------------------------------------------------*)
let max_wosize =
  Usize.sub (Usize.shift_left 1UL 54ul) 1UL

(*max color value*)
let max_color =
  Usize.sub (Usize.shift_left 1UL 2ul) 1UL

(*max tag value*)
let max_tag = Usize.sub (Usize.shift_left 1UL 8ul) 1UL

(*---------------------------------------------------------------------------------------------------------------------*)
(*max_wosize, max_color, max_tag properties*)
val max_wosize_lemma : unit -> Lemma (Usize.v max_wosize = pow2 54 - 1)

val max_color_size_lemma : unit -> Lemma (Usize.v max_color = pow2 2 - 1)

val max_tag_size_lemma : unit -> Lemma (Usize.v max_tag = pow2 8 - 1)
(*---------------------------------------------------------------------------------------------------------------------*)

(*Definitions*)
type heap = g:seq U8.t{Seq.length g == heap_size /\ is_heap_size_multiple_of_mwords ()}

type wosize = sz:Usize.t{0 <= Usize.v sz /\ Usize.v sz <= Usize.v max_wosize}

type color = cl:Usize.t{0 <= Usize.v cl /\ Usize.v cl <= Usize.v max_color}

type tag = tg:Usize.t{0 <= Usize.v tg /\ Usize.v tg <= Usize.v max_tag}

val is_size_fits_after_subtraction :(x:Usize.t) ->
                                    (y:Usize.t) ->
                       Tot (b:bool{b == true <==> UInt.fits (Usize.v x - Usize.v y) Usize.n})

type hp_addr = h:Usize.t {Usize.v h >= 0 /\ Usize.v h < heap_size /\ (Usize.v h % 8 == 0)}

type hp_addr_32 = h:UInt32.t {UInt32.v h >= 0 /\ UInt32.v h < heap_size /\ (UInt32.v h % 8 == 0)}

let is_hp_addr (h:Usize.t) 
             : Tot (b:bool{b == true <==> (Usize.v h < heap_size) /\ (Usize.v h % Usize.v mword = 0)})=
   if ((Usize.v h < heap_size) && (Usize.v h % Usize.v mword = 0)) then true
   else
     false 

let read_word (byte_array: heap) 
              (byte_index:hp_addr)
        : Tot (v:UInt64.t{v ==  uint64_of_le (slice byte_array (Usize.v byte_index) ((Usize.v byte_index) + Usize.v mword))})    =  
 let word_array = slice byte_array (Usize.v byte_index) ((Usize.v byte_index) + Usize.v mword) in // Extract the word from byte array
 uint64_of_le word_array

let read_word1 (byte_array: heap) 
               (byte_index:hp_addr_32)  
        : Tot (v:UInt64.t{v ==  uint64_of_le (slice byte_array (UInt32.v byte_index) ((UInt32.v byte_index) + Usize.v mword))})    =  
 let word_array = slice byte_array (UInt32.v byte_index) ((UInt32.v byte_index) + Usize.v mword) in // Extract the word from byte array
 uint64_of_le word_array

let replace_range (source: heap) 
                  (start_index:hp_addr {Usize.v start_index < length source}) 
                  (replacement: seq UInt8.t{length replacement == Usize.v mword}) 
  : Pure (seq UInt8.t) (requires length replacement <= length source - (Usize.v start_index)) 
               
                (ensures fun result -> (*1*)   (length result == length source) /\
                                    (*2*)   (forall (i:nat{i < length source}). 
                                                 index result i == (
                                                       if i >= (Usize.v start_index) && i < (Usize.v start_index) + (length replacement) then
                                                         (index replacement (i - (Usize.v start_index))) 
                                                       else 
                                                          index source i))) =
  let before_start = slice source 0 (Usize.v start_index) in
  let after_end = slice source ((Usize.v start_index) + (length replacement)) (length source) in
  append before_start (append replacement after_end)

let replace_range1 (source: heap) 
                   (start_index:hp_addr) 
                   (replacement: seq UInt8.t{length replacement == Usize.v mword}) 
  : Pure (seq UInt8.t) (requires True) 
                       (ensures fun result -> (*1*)   (length result == length source) /\
                                    (*2*)   (forall (i:nat{i < length source}). 
                                                 index result i == (
                                                       if i >= (Usize.v start_index) && i < (Usize.v start_index) + (length replacement) then
                                                         (index replacement (i - (Usize.v start_index))) 
                                                       else 
                                                          index source i))) =
  let before_start = slice source 0 (Usize.v start_index) in
  let after_end = slice source ((Usize.v start_index) + (length replacement)) (length source) in
  let result = append before_start (append replacement after_end) in
  assert (forall i. i > (Usize.v start_index) && i < (Usize.v start_index) + (length replacement) ==> i % Usize.v mword <> 0);
  assert (forall i. Usize.v i >= 0 /\ Usize.v i < Usize.v start_index /\ Usize.v i % Usize.v mword == 0 ==> index result (Usize.v i) == index source (Usize.v i));
  assert (forall i. Usize.v i >= 0 /\ Usize.v i < Usize.v start_index ==> index result (Usize.v i) == index source (Usize.v i));
  assert (Seq.length before_start == Usize.v start_index);
  assert ((Seq.length before_start) % Usize.v mword == 0);
  assert (Seq.length after_end == length source - (Usize.v start_index + length replacement));
  assert (Seq.length after_end % Usize.v mword == 0);
  lemma_eq_elim (slice result (Usize.v start_index) ((Usize.v start_index) + UInt64.v mword)) replacement;
  lemma_eq_elim (slice result 0 (Usize.v start_index)) before_start;
  assert (read_word result start_index == uint64_of_le replacement);
  result


let replace_range_structure_lemma (source: heap) 
                                  (start_index:hp_addr) 
                                  (replacement: seq UInt8.t{length replacement == Usize.v mword}) 
                    : Lemma
                      (ensures replace_range source start_index replacement == 
                        append (slice source 0 (Usize.v start_index)) (append replacement (slice source ((Usize.v start_index) + (length replacement)) (length source)))) =
  ()

(*This was not an easy proof. Requires proof by contradiction.*)
let replace_range_before_start_lemma (source: heap) 
                                     (start_index:hp_addr) 
                                     (replacement: seq UInt8.t{length replacement == Usize.v mword})
                                     (i:hp_addr{(Usize.v i >= 0) /\ (Usize.v i < Usize.v start_index) /\ (Usize.v i % Usize.v mword == 0)})
                    : Lemma
                      (ensures (read_word (replace_range source start_index replacement) i == read_word source i))=
  let s = replace_range source start_index replacement in
  let value1 = read_word s i in
  let value2 = read_word source i in
  lemma_eq_elim (slice s (Usize.v start_index) ((Usize.v start_index) + UInt64.v mword)) replacement;
  assert (read_word s start_index == uint64_of_le replacement);
  if (value1 = value2) then ()
  else
   (
     assert (value1 <> value2);
     assert (forall i. Usize.v i >= 0 /\ Usize.v i < Usize.v start_index ==> index s (Usize.v i) == index source (Usize.v i));
     assert (forall i. Usize.v i >= 0 /\ Usize.v i < Usize.v start_index /\ (Usize.v i % Usize.v mword == 0) ==> index s (Usize.v i) == index source (Usize.v i));
     assert (forall j. Usize.v j > Usize.v i /\ Usize.v j < (Usize.v i + Usize.v mword) ==> Usize.v j < Usize.v start_index);
     assert (forall j. Usize.v j > Usize.v i /\ Usize.v j < (Usize.v i + Usize.v mword) ==> (index source (Usize.v j) == index s (Usize.v j)));
     lemma_eq_elim (slice s (Usize.v i) (Usize.v i + Usize.v mword)) (slice source (Usize.v i) (Usize.v i + Usize.v mword));
     assert (Seq.slice s (Usize.v i) (Usize.v i + Usize.v mword) == Seq.slice source (Usize.v i) (Usize.v i + Usize.v mword));
     assert (uint64_of_le (Seq.slice s (Usize.v i) (Usize.v i + Usize.v mword)) == uint64_of_le (Seq.slice source (Usize.v i) (Usize.v i + Usize.v mword)));
     assert (value1 == value2);
     ()
   )

let replace_range_before_start_all_lemma (source: heap) 
                                         (start_index:hp_addr) 
                                         (replacement: seq UInt8.t{length replacement == Usize.v mword})
                           : Lemma
                             (ensures (forall (i:hp_addr). (Usize.v i >= 0) /\ (Usize.v i < Usize.v start_index) /\ (Usize.v i % Usize.v mword == 0) ==>
                                             read_word (replace_range source start_index replacement) i == read_word source i))=
 Classical.forall_intro (Classical.move_requires (replace_range_before_start_lemma source start_index replacement))

let replace_range_after_start_end_lemma (source: heap) 
                                        (start_index:hp_addr) 
                                        (replacement: seq UInt8.t{length replacement == Usize.v mword})
                                        (i:hp_addr{(Usize.v i >= (Usize.v start_index) + (length replacement)) /\ (Usize.v i < length source) /\ (Usize.v i % Usize.v mword == 0)})
                    : Lemma
                      (ensures (read_word (replace_range source start_index replacement) i == read_word source i))=
  let s = replace_range source start_index replacement in
  let value1 = read_word s i in
  let value2 = read_word source i in
  lemma_eq_elim (slice s (Usize.v start_index) ((Usize.v start_index) + UInt64.v mword)) replacement;
  assert (read_word s start_index == uint64_of_le replacement);
  if (value1 = value2) then ()
  else
   (
     assert (forall i. Usize.v i >= ((Usize.v start_index) + (length replacement)) /\ Usize.v i < length source ==> index s (Usize.v i) == index source (Usize.v i));
     assert (forall i. Usize.v i >= ((Usize.v start_index) + (length replacement)) /\ Usize.v i < length source /\ (Usize.v i % Usize.v mword == 0) ==> index s (Usize.v i) == index source (Usize.v i));
     assert (forall j. Usize.v j > Usize.v i /\ Usize.v j < (Usize.v i + Usize.v mword) ==> Usize.v j < length source);
     assert (forall j. Usize.v j > Usize.v i /\ Usize.v j < (Usize.v i + Usize.v mword) ==> (index source (Usize.v j) == index s (Usize.v j)));
     lemma_eq_elim (slice s (Usize.v i) (Usize.v i + Usize.v mword)) (slice source (Usize.v i) (Usize.v i + Usize.v mword));
     assert (Seq.slice s (Usize.v i) (Usize.v i + Usize.v mword) == Seq.slice source (Usize.v i) (Usize.v i + Usize.v mword));
     assert (uint64_of_le (Seq.slice s (Usize.v i) (Usize.v i + Usize.v mword)) == uint64_of_le (Seq.slice source (Usize.v i) (Usize.v i + Usize.v mword)));
     assert (value1 == value2);
     ()
   )

let replace_range_after_start_end_all_lemma (source: heap) 
                                            (start_index:hp_addr) 
                                            (replacement: seq UInt8.t{length replacement == Usize.v mword})
                           : Lemma
                             (ensures (forall (i:hp_addr). (Usize.v i >= ((Usize.v start_index) + (length replacement))) /\ (Usize.v i < length source) /\ (Usize.v i % Usize.v mword == 0) ==>
                                             read_word (replace_range source start_index replacement) i == read_word source i))=
 Classical.forall_intro (Classical.move_requires (replace_range_after_start_end_lemma source start_index replacement))

let write_word (byte_array: heap)
               (byte_index: hp_addr)
               (value: UInt64.t)
  : Pure (heap) 
    (requires True)
    (ensures fun result -> length result == length byte_array /\
                        (forall (i:nat{i < length byte_array}). 
                                                 index result i == (
                                                       if i >= (Usize.v byte_index) && 
                                                          i < ((Usize.v byte_index) + (length (FStar.Endianness.le_of_uint64 value))) then
                                                         (index (FStar.Endianness.le_of_uint64 value) (i - (Usize.v byte_index))) 
                                                       else 
                                                          index byte_array i)) /\
                        read_word result byte_index == value) =  
 let bytes = FStar.Endianness.le_of_uint64 value in
 assert (uint64_of_le bytes == value);
 assert (length bytes == Usize.v mword);
 let result = replace_range byte_array byte_index bytes in
 lemma_eq_elim (slice result (Usize.v byte_index) ((Usize.v byte_index) + UInt64.v mword)) bytes; 
 result

let read_and_write_are_valid (byte_array: heap)
                             (byte_index:hp_addr)
                             (value: UInt64.t)
  : Lemma (read_word (write_word byte_array byte_index value) byte_index == value) = ()

let write_word_replacement_lemma (byte_array: heap)
                                 (byte_index: hp_addr)
                                 (value: UInt64.t)
            : Lemma
              (ensures (forall (i:hp_addr). Usize.v i >= (Usize.v byte_index) /\  Usize.v i < ((Usize.v byte_index) + Usize.v mword) /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) byte_index == value)) = ()
    
let write_word_before_start_lemma (byte_array: heap)
                                  (byte_index: hp_addr)
                                  (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). Usize.v i >= 0 /\  Usize.v i < Usize.v byte_index /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) = 
 replace_range_before_start_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)


let write_word_after_start_end_lemma (byte_array: heap)
                                     (byte_index: hp_addr)
                                     (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). (Usize.v i >= ((Usize.v byte_index) + Usize.v mword)) /\ (Usize.v i < length byte_array) /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) =
 replace_range_after_start_end_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)


let write_word_lemma (byte_array: heap)
                     (byte_index: hp_addr)
                     (value: UInt64.t)
                : Lemma 
                  ((forall (i:hp_addr). read_word (write_word byte_array byte_index value) i == (
                                                           if Usize.v i >= (Usize.v byte_index) && 
                                                              Usize.v i < ((Usize.v byte_index) + (Usize.v mword)) && 
                                                              (Usize.v i % Usize.v mword = 0) then
                                                                  value 
                                                             else 
                                                                read_word byte_array i))) = 
write_word_replacement_lemma byte_array byte_index value;  
write_word_before_start_lemma byte_array byte_index value;
write_word_after_start_end_lemma byte_array byte_index value;
()


/// Extract wosize from header value
val getWosize : (h:Usize.t) ->
          Tot (wz:wosize{wz == Usize.shift_right h 10ul})

/// Extract color from header value
val getColor : (h:Usize.t) ->
          Tot (c:color{c = Usize.logand (Usize.shift_right h 8ul) 3UL})

/// Extract tag from header value
val getTag : (h:Usize.t) ->
          Tot (tg:tag{tg == Usize.logand h 255UL})

val color_of_object1 : (v_id: hp_addr) ->
                       (g:heap)->
             Tot (c:color{c == getColor(read_word g v_id)}) 

val wosize_of_object1 : (v_id: hp_addr) ->
                        (g:heap)->
             Tot (w:wosize{w == getWosize(read_word g v_id)}) 


val tag_of_object1 : (v_id: hp_addr) ->
                     (g:heap)->
             Tot (t:tag{t == getTag(read_word g v_id)}) 


val isBlueObject1 :(v_id: hp_addr)->
                   (g:heap) ->
         Tot (b: bool {b == true <==> (color_of_object1 v_id g) == blue}) 

val isWhiteObject1 : (v_id: hp_addr)->
                     (g:heap) ->
         Tot (b: bool {b == true <==> (color_of_object1 v_id g) == white}) 

val isGrayObject1 : (v_id: hp_addr)->
                    (g:heap) ->
         Tot (b: bool {b == true <==> (color_of_object1 v_id g) == gray}) 

val isBlackObject1 : (v_id: hp_addr)->
                     (g:heap) ->
         Tot (b: bool {b == true <==> (color_of_object1 v_id g) == black}) 

val makeHeader : (wz:wosize) ->
                 (c:color) ->
                 (tg:tag) ->
             Tot (h:Usize.t{wz == getWosize h /\
                            c == getColor h /\
                            tg == getTag h})
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// h_index = start byte address of the object
/// wz = wosize type
/// is_fields_within_limit1 is true iff start address + ((wz + 1) * mword - 1) < heap_size
/// Let heap_size = 24
/// start_address = 8
/// wz = 1
/// (wz + 1) * mword = 2 * mword = 2 * 8 = 16
/// That is the object starting at address 8 can have a single field to fit within the heap size limit.
/// ----------------------------------------------------------------------------------------------------------------------------------------------------------------
/// 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24
/// |..................|  |.....................| |
///      header                    field 1        heap_size
/// -----------------------------------------------------------------------------------------------------------------------------------------------------------------


val isPointer : (v_id: hp_addr) ->
                (g:heap) ->
            Tot (b:bool{b == true <==> Usize.logand (read_word g v_id) 1UL == 0UL})

val is_fields_within_limit1  : (h_index: hp_addr) ->
                               (wz: wosize)->
              Tot (b:bool{b == true <==> (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size)})

val is_fields_contents_within_limit2 : (h_index: hp_addr) ->
                                       (wz: wosize{is_fields_within_limit1 h_index wz}) ->
                                       (g:heap) ->
                            Tot (b:bool{b == true <==> (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}).isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) >= 0 /\
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) < heap_size)})
                            (decreases (Usize.v wz))

let wosize_times_mword_multiple_of_mword (wz:wosize)
                     :Lemma 
                      (ensures (Usize.v (Usize.mul wz mword) % Usize.v mword == 0)) = ()


let sum_of_multiple_of_mword_is_multiple_of_mword (x:Usize.t{Usize.v x % Usize.v mword == 0})
                                                  (y:Usize.t{Usize.v y % Usize.v mword == 0})
                                :Lemma 
                                 (ensures ((Usize.v x + Usize.v y) % Usize.v mword == 0)) = ()

val objects3 : (h_index: hp_addr)->
               (g:heap) ->
        Tot (s:seq Usize.t {Seq.length s > 0 ==> (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                 (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                                                 (Seq.mem h_index s) /\
                                                 (forall x. Seq.mem x s ==> 
                                                                     is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                 (G.is_vertex_set s) /\
                                                 (forall x. Seq.mem x s ==> Usize.v x >= Usize.v h_index) /\
                                                 (forall x. Seq.mem x s ==> Usize.v (getWosize (read_word g x)) > 0) /\
                                                 (forall x. Seq.mem x s ==> Usize.v x + Usize.v mword < heap_size) /\
                                                 ((forall x y. Seq.mem x s /\ 
                                                   (Usize.v y >= Usize.v x + Usize.v mword) /\ 
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y s)))})
                       (decreases (heap_size - Usize.v h_index))

val objects2 : (h_index: hp_addr)->
               (g:heap) ->
        Tot (s:seq Usize.t {Seq.length s > 0 ==> (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                 (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                                                 (Seq.mem h_index s) /\
                                                 (forall x. Seq.mem x s ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                 (forall x. Seq.mem x s ==> Usize.v x >= Usize.v h_index) /\
                                                 (forall x. Seq.mem x s ==> Usize.v (getWosize (read_word g x)) > 0) /\
                                                 (G.is_vertex_set s) /\
                                                 (forall x. Seq.mem x s ==> Usize.v x + Usize.v mword < heap_size) /\
                                                 ((forall x y. Seq.mem x s /\ 
                                                   (Usize.v y >= Usize.v x + Usize.v mword) /\ 
                                                   (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1)) ==>
                                                   ~(Seq.mem y s)))})
                                                                     
                       (decreases (heap_size - Usize.v h_index))

val objects2_mem_lemma1 :   (h_index: hp_addr) ->
                            (g:heap) ->
                           
                      
            Lemma 
            (ensures ((Seq.length (objects2 h_index g) > 0  ==> (forall x. Seq.mem x (objects2 h_index g) /\ 
                                                                  Usize.v (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) < heap_size ==> 
                                                                       Seq.mem (Usize.add x (Usize.mul (Usize.add (getWosize (read_word g x)) 1UL) mword)) 
                                                                           (objects2 h_index g)))))
            (decreases (heap_size - Usize.v h_index))

val objects2_equal_lemma :(h_index:hp_addr) ->
                          (g:heap) ->
                          (g':heap) ->
                     Lemma
                       (requires (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index))


val objects2_equal_lemma3 :(h_index:hp_addr) ->
                           (g:heap) ->
                           (g':heap) ->
                       Lemma
                       (requires (objects2 0UL g == objects2 0UL g') /\
                                 (Seq.mem h_index (objects2 0UL g)) /\
                                 (forall x. Seq.mem x (objects2 0UL g) ==> getWosize (read_word g x) == getWosize (read_word g' x)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index))
                       
val objects2_length_lemma :(h_index:hp_addr) ->
                           (g:heap) ->
                     Lemma
                     (ensures (Seq.length (objects2 h_index g) <= (heap_size - Usize.v h_index)))
                     (decreases (heap_size - Usize.v h_index))

val objects2_color_lemma : (h_index:hp_addr) ->
                           (g:heap) ->
                     Lemma
                     (ensures (forall x. Seq.mem x (objects2 h_index g) ==> color_of_object1 x g == white \/
                                                                       color_of_object1 x g == gray \/
                                                                       color_of_object1 x g == black \/
                                                                       color_of_object1 x g == blue))
                     (decreases (heap_size - Usize.v h_index))



#restart-solver

val is_fields_contents_within_limit2_lemma : (h_index: hp_addr) ->
                                             (wz: wosize{is_fields_within_limit1 h_index wz}) ->
                                             (wz': wosize{is_fields_within_limit1 h_index wz'})->
                                             (g:heap) ->
                                             (g':heap) ->
                                          
                            Lemma
                            (requires (wz == wz') /\
                                      (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}). 
                                                    
                                                    Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) == 
                                                    Usize.v (read_word g' (Usize.add h_index (Usize.mul i mword)))))
                                                                 
                            (ensures (is_fields_contents_within_limit2 h_index wz g == true <==>
                                      is_fields_contents_within_limit2 h_index wz' g' == true))
                            (decreases (Usize.v wz))

val check_all_block_fields_within_limit2 :(g:heap)->
                                          (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x f' ==> 
                                                                 Seq.mem x (objects2 0UL g))})->
                               Tot (b: bool{b == true <==> (forall x. Seq.mem x f' ==> 
                                            is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)})
                                (decreases length f')



#restart-solver

let max_wosize_times_mword_multiple_of_mword (i: Usize.t{(Usize.v i <= Usize.v max_wosize)})
                     :Lemma 
                      (ensures ((Usize.v (Usize.mul i mword) % Usize.v mword == 0))) = ()
                      
let h_index_field_index_mword_multiple_lemma1 (g:heap)
                                             (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()
                                    
let h_index_field_index_all_mword_multiple_lemma1(g:heap)
                                                 (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                                   
                                : Lemma
                                 
                                  (ensures (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g h_index)) ==> 
                                          (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (h_index_field_index_mword_multiple_lemma1 g h_index (getWosize (read_word g h_index))))

let objects_mem_h_index_field_index_all_mword_multiple (g:heap)
                                                       (f':seq hp_addr{(forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g))})
                                        : Lemma
                                          (ensures (forall x. Seq.mem x f' ==>
                                                       ((forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)))) =
Classical.forall_intro (Classical.move_requires (h_index_field_index_all_mword_multiple_lemma1 g))

#push-options "--split_queries"

#restart-solver 

val check_all_block_fields_within_limit2_lemma :(g:heap)->
                                                (g':heap)->
                                                (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                 (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                 (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g))})->
                                                (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f'' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g'))})->
                                  Lemma
                                  (requires (f' == f'')  /\
                                            (objects2 0UL g ==
                                             objects2 0UL g') /\
                                            (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x)) /\
                                (forall x y. Seq.mem x f' /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                                      Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y))
                                  (ensures check_all_block_fields_within_limit2 g f' == true <==>
                                           check_all_block_fields_within_limit2 g' f'' == true)
                                   (decreases length f') 


let heap_remains_same_except_index_v_id  (v_id:hp_addr)
                                         (g:heap)
                                         (g':heap{Seq.length g == Seq.length g'}) =
  forall (x:Usize.t {Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). x <> v_id ==>
           read_word g x == read_word g' x 

#restart-solver 

(*val check_all_block_fields_within_limit2_lemma3 :   (g:heap) ->
                                                    (g':heap) ->
                                                    (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                 (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                 (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g))})->
                                                    (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f'' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g'))})->
                                                    (x:hp_addr{Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})->
                                                          
                                                    (k:hp_addr{Usize.v k == Usize.v x + Usize.v mword})->
                                  Lemma
                                  (requires (f' == f'')  /\
                                            (objects2 0UL g ==
                                             objects2 0UL g') /\
                                           
                                            (forall p. Seq.mem p (objects2 0UL g) ==> read_word g p ==
                                                                                  read_word g' p) /\                                     
                                            (forall p. Seq.mem p (objects2 0UL g) ==> is_fields_within_limit1 p  (getWosize (read_word g p))) /\
                                            (forall p. Seq.mem p (objects2 0UL g) ==> 
                                                      (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))}). 
                                                            is_hp_addr (Usize.add x (Usize.mul i mword)))) /\
                                            (forall p. Seq.mem p (objects2 0UL g) /\ p <> x ==> 
                                                   (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                                       Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word g' j == read_word g j)) /\
                                            
                                            
                                            (forall (i:Usize.t {Usize.v i > 1 /\ Usize.v i <= Usize.v (getWosize (read_word g x))}).
                                                     Usize.v (read_word g (Usize.add x (Usize.mul i mword))) == 
                                                     Usize.v (read_word g' (Usize.add x (Usize.mul i mword)))) /\
                                            
                                              (isPointer k g ==> (Usize.v (read_word g k) >= 0 /\ Usize.v (read_word g k) < heap_size)) /\
                                              (isPointer k g' ==> (Usize.v (read_word g' k) >= 0 /\ Usize.v (read_word g' k) < heap_size)))
                                  
                                  (ensures check_all_block_fields_within_limit2 g f' == true <==>
                                           check_all_block_fields_within_limit2 g' f'' == true)
                                   (decreases length f')*)
                                   
#push-options "--z3rlimit 100" //--fuel 2 --ifuel 4" 

val is_fields_points_to_blocks2 :    (h_index: hp_addr) ->
                                     (g:heap)->
                                     (wz: wosize{(is_fields_within_limit1 h_index wz /\
                                               is_fields_contents_within_limit2 h_index wz g)}) ->
                                     (f':seq Usize.t { (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                    (forall x. Seq.mem x f' ==> 
                                                     Seq.mem x (objects2 0UL g))})->
                                 
                   Tot (b:bool{b == true <==> (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\ 
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul i mword)) g  ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (objects2 0UL g))}) 

val is_fields_points_to_blocks2_lemma : (h_index: hp_addr) ->
                                        (g:heap)->  
                                        (wz: wosize{(is_fields_within_limit1 h_index wz /\
                                                     is_fields_contents_within_limit2 h_index wz g)}) ->
                                        (f':seq Usize.t { (forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                          (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g))})->
                                        (g':heap)-> 
                                        (wz': wosize{(is_fields_within_limit1 h_index wz' /\
                                                      is_fields_contents_within_limit2 h_index wz' g')}) ->
                                        (f'':seq Usize.t { (forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g'))})->
                                  Lemma
                                  (requires (wz == wz') /\
                                            (f' == f'')  /\
                                            (objects2 0UL g == objects2 0UL g') /\
                                      (forall x. Usize.v x  >= Usize.v h_index + Usize.v mword /\
                                            Usize.v x <= Usize.v h_index + (Usize.v wz * Usize.v mword) ==> read_word g x == read_word g' x))
                                  (ensures is_fields_points_to_blocks2 h_index g wz f' == true <==>
                                            is_fields_points_to_blocks2 h_index g' wz' f'' == true)
                                  (decreases (Usize.v wz)) 

val check_fields_points_to_blocks2:(g:heap)->
                                   (f':seq Usize.t { (forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                     (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g)) /\
                                                     check_all_block_fields_within_limit2  g f'}) ->
                                   
                              
                               Tot (b:bool{b == true <==> (forall x. Seq.mem x f' ==>
                                          is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (objects2 0UL g))})
                               (decreases length f') 


val check_fields_points_to_blocks2_lemma :(g:heap)->
                                          (g':heap) ->
                                          (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g)) /\
                                                           check_all_block_fields_within_limit2 g f'}) ->
                                          
                                                           
                                          (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                            (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g')) /\
                                                            check_all_block_fields_within_limit2 g' f''}) ->
                                          
                                           Lemma
                                           (requires (f' == f'')  /\ (objects2 0UL g == objects2 0UL g') /\
                               
                                                     (forall (x:Usize.t{Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). 
                                                               getWosize (read_word g x) == getWosize (read_word g' x)) /\ 
                                                     
                                                     (forall x y. Seq.mem x f' /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                                                            Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                              read_word g y == read_word g' y))
                                           
                                           (ensures check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true)
                                           (decreases length f') 


                                   
(*val check_fields_points_to_blocks2_lemma1 : (g:heap)->
                                            (g':heap)->
                                            (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g)) /\
                                                           check_all_block_fields_within_limit2 g f'}) ->
                                          
                                                           
                                            (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                            (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g')) /\
                                                            check_all_block_fields_within_limit2 g' f''}) ->
                                              (x: hp_addr{Seq.mem x (objects2 0UL g)})->
                                              (k:hp_addr{Usize.v k == Usize.v x + Usize.v mword})->
                                        Lemma
                                          (requires (f' == f'')  /\ (objects2 0UL g == objects2 0UL g') /\
                                                     (forall p. Seq.mem p (objects2 0UL g) ==> read_word g p ==
                                                                                  read_word g' p) /\ 
                                                     (forall p. Seq.mem p f'/\ p <> x ==> 
                                                        (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                                       Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word g' j == read_word g j)) /\
                                                     
                                                     (forall (j:hp_addr). Usize.v j  > Usize.v x + Usize.v mword /\
                                                        Usize.v j <= Usize.v x + (Usize.v (getWosize (read_word g' x)) * Usize.v mword) ==> read_word g j == read_word g' j) /\
                                                     (isPointer k g  ==> Seq.mem (read_word g k) (objects2 0UL g)) /\
                                                     (isPointer k g' ==> Seq.mem (read_word g' k) (objects2 0UL g'))
                                                     
                                               )      
                                          (ensures check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true)
                                          (decreases length f') *)


val well_formed_heap2 : (g:heap) ->
                 Tot (b:bool{b == true <==> Seq.length (objects2 0UL g) > 0  /\
                                          (check_all_block_fields_within_limit2 g (objects2 0UL g)) /\
                                          (check_fields_points_to_blocks2 g (objects2 0UL g))})

val is_valid_header : (h:hp_addr) -> // index should be passed to check for header validity
                      (g:heap {well_formed_heap2 g}) ->
                Tot (b:bool{b == true <==> (Seq.mem h (objects2 0UL g))})

let get_block_address_length_lemma (g:heap {well_formed_heap2 g}) 
                               : Lemma
                                 (Seq.length (objects2 0UL g) <= heap_size) =
  objects2_length_lemma 0UL g;
  assert (Seq.length (objects2 0UL g) <= heap_size);
  ()

val objects2_equal_lemma1 : (g:heap{well_formed_heap2 g}) ->
                            (g':heap)->
                            (h_index:hp_addr{is_valid_header h_index g})->
                      Lemma
                       (requires (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g' p) ==  getWosize (read_word g p)))
                       (ensures objects2 h_index g == objects2 h_index g')
                       (decreases (heap_size - Usize.v h_index)) 
                       
val objects2_cons_lemma1 : (h_index: hp_addr)->
                           (g:heap)->
                           (h_index_new:hp_addr{h_index_new == (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword))})->
                           
            Lemma 
            (ensures (Seq.length (objects2 h_index g) > 0 /\ 
                        Usize.v h_index_new < heap_size ==> 
                         ((objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g)) /\
                         (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)))))
                         
val objects2_length_lemma1 :(g:heap{well_formed_heap2 g}) ->
                            (h_index:hp_addr{is_valid_header h_index g}) ->
                            (h_index_new:hp_addr{h_index_new == (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword))})->
                  Lemma
                  (requires (Seq.length (objects2 h_index g) > 0) /\ (Usize.v h_index_new < heap_size))
                  (ensures ((Seq.length (objects2 h_index_new g) > 0))) 


val get_allocated_block_addresses : (g:heap {well_formed_heap2 g}) ->
                            Tot (allocs: seq Usize.t {(forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x allocs ==> is_hp_addr x) /\
                                                      (forall x. Seq.mem x allocs ==> is_valid_header x g) /\
                                                      (G.is_vertex_set allocs) /\
                                                      (G.subset_vertices allocs (objects2 0UL g)) /\
                                                      (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                                 (isGrayObject1 x g) \/
                                                                                (isBlackObject1 x g)) /\
                                                      (forall x. Seq.mem x (objects2 0UL g) /\
                                                           ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                               Seq.mem x allocs)})

val get_allocated_block_addresses_lemma :   (g:heap {well_formed_heap2 g}) ->
                                            (g':heap{well_formed_heap2 g'})->
                                            (v_id:hp_addr) ->
                                            (c:color)->
                           Lemma
                           (requires (objects2 0UL g ==
                                      objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id v_id g g' /\
                                      color_of_object1 v_id g' == c /\
                                      (color_of_object1 v_id g == white \/ color_of_object1 v_id g == gray \/ 
                                      color_of_object1 v_id g == black) /\
                                      wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                                      tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                                      is_valid_header v_id g /\ is_valid_header v_id g' /\
                                      (c == 1UL \/ c == 2UL \/ c == 3UL))
                           (ensures (get_allocated_block_addresses g == get_allocated_block_addresses g'))
                           
val get_black_block_addresses : (g:heap {well_formed_heap2 g}) ->
                                (allocs: seq Usize.t {Seq.equal allocs (get_allocated_block_addresses g) /\
                                                     (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x allocs ==> is_valid_header x g) /\
                                                     (G.is_vertex_set allocs) /\
                                                     (G.subset_vertices allocs 
                                                       (objects2 0UL g)) /\
                                                     (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                               (isGrayObject1 x g) \/
                                                                               (isBlackObject1 x g))}) ->
                            Tot (blacks: G.vertex_list (*seq Usize.t*)
                                          {(forall x. Seq.mem x blacks ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x blacks ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x blacks ==> is_valid_header x g) /\
                                                     (G.is_vertex_set blacks) /\
                                                     (G.subset_vertices blacks allocs) /\
                                                     (G.subset_vertices blacks 
                                                         (objects2 0UL g)) /\
                                                     (G.subset_vertices blacks (get_allocated_block_addresses g)) /\
                                                     (forall x. Seq.mem x blacks ==> color_of_object1 x g == black) /\
                                                     (forall x. Seq.mem x (objects2 0UL g) /\
                                                                          isBlackObject1 x g ==> Seq.mem x blacks) /\
                                                     (forall x. Seq.mem x blacks <==> 
                                                         Seq.mem x (objects2 0UL g) /\
                                                         isBlackObject1 x g) /\
                                                     (forall x. Seq.mem x blacks <==> Seq.mem x (get_allocated_block_addresses g) /\ 
                                                        color_of_object1 x g == black)})

val get_gray_block_addresses : (g:heap {well_formed_heap2 g}) ->
                                (allocs: seq Usize.t {Seq.equal allocs (get_allocated_block_addresses g) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                   (forall x. Seq.mem x allocs ==> is_valid_header x g) /\
                                                    (G.is_vertex_set allocs) /\
                                                    (G.subset_vertices allocs 
                                                       (objects2 0UL g)) /\
                                                    (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                               (isGrayObject1 x g) \/
                                                                               (isBlackObject1 x g))}) ->
                            Tot (grays: G.vertex_list (*seq Usize.t*)
                                          {(forall x. Seq.mem x grays ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x grays ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x grays ==> is_valid_header x g) /\
                                                     (G.is_vertex_set grays) /\
                                                     (G.subset_vertices grays allocs) /\
                                                     (G.subset_vertices grays 
                                                         (objects2 0UL g)) /\
                                                     (G.subset_vertices grays (get_allocated_block_addresses g)) /\
                                                     (forall x. Seq.mem x grays ==> color_of_object1 x g == gray) /\
                                                     (forall x. Seq.mem x (objects2 0UL g) /\
                                                                          isGrayObject1 x g ==> Seq.mem x grays) /\
                                                     (forall x. Seq.mem x grays <==> 
                                                         Seq.mem x (objects2 0UL g) /\
                                                         isGrayObject1 x g) /\
                                                     (forall x. Seq.mem x grays <==> Seq.mem x (get_allocated_block_addresses g) /\ 
                                                        color_of_object1 x g == gray)})

val get_white_block_addresses : (g:heap {well_formed_heap2 g}) ->
                                (allocs: seq Usize.t {Seq.equal allocs (get_allocated_block_addresses g) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                   (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                   (forall x. Seq.mem x allocs ==> is_valid_header x g) /\
                                                    (G.is_vertex_set allocs) /\
                                                    (G.subset_vertices allocs 
                                                       (objects2 0UL g)) /\
                                                    (forall x. Seq.mem x allocs ==> (isWhiteObject1 x g) \/ 
                                                                               (isGrayObject1 x g) \/
                                                                               (isBlackObject1 x g))}) ->
                            Tot (whites: G.vertex_list (*seq Usize.t*)
                                          {(forall x. Seq.mem x whites ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x whites ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x whites ==> is_valid_header x g) /\
                                                     (G.is_vertex_set whites) /\
                                                     (G.subset_vertices whites allocs) /\
                                                     (G.subset_vertices whites 
                                                         (objects2 0UL g)) /\
                                                     (G.subset_vertices whites (get_allocated_block_addresses g)) /\
                                                     (forall x. Seq.mem x whites ==> color_of_object1 x g == white) /\
                                                     (forall x. Seq.mem x (objects2 0UL g) /\
                                                                          isWhiteObject1 x g ==> Seq.mem x whites) /\
                                                     (forall x. Seq.mem x whites <==> 
                                                         Seq.mem x (objects2 0UL g) /\
                                                         isWhiteObject1 x g) /\
                                                     (forall x. Seq.mem x whites <==> Seq.mem x (get_allocated_block_addresses g) /\ 
                                                        color_of_object1 x g == white)})

#restart-solver 

let subtraction_lemma (h_index: nat)
                      (i:nat)
                      (j:nat)
             :Lemma
              (requires (j > i))
              (ensures (((h_index + j) - (h_index + i)) == (j - i))) = ()

#push-options "--z3rlimit 500"

#restart-solver

#restart-solver

let slice_has_property (property: Usize.t -> prop)
                  (g: seq Usize.t)
                  (i: Usize.t)
                  (j: Usize.t {Usize.v i <= Usize.v j /\ Usize.v j < length g})
  = (forall x. mem x (slice g  (Usize.v i)  (Usize.v j)) ==> property x)

let subslice_has_property_aux (property: Usize.t -> prop)
                              (g: seq Usize.t)
                              (i j k: Usize.t)
                              (l: Usize.t{Usize.v i <=  Usize.v k /\ Usize.v k <= Usize.v l /\ Usize.v l <= Usize.v j /\ Usize.v j < length g})
                              (x: Usize.t { mem x (slice g (Usize.v k) (Usize.v l)) })
  : Lemma (requires slice_has_property property g i j)
          (ensures property x) = 
  let p = Usize.v k - Usize.v i in
  let seq_ij = slice g (Usize.v i) (Usize.v j) in
  let seq_kl = slice g (Usize.v k) (Usize.v l) in
  let id = index_mem x seq_kl in
  assert (index seq_ij (id+p) == x);
  assert (index seq_kl id == x)

let subtraction_lemma1 (h_index: nat)
                       (i:nat)
                       (j:nat)
             :Lemma
              (requires (j > i))
              (ensures ((h_index + j) > (h_index + i))) = ()

/// i ...................................................j......................................
///                  id



//#push-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#restart-solver

/// (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) --> This condition is trivially true.
/// But SMT solver is not able to infer it.
/// Hence before calling this function, create a lemma that brings the above conditio into context


#restart-solver 

let rec is_fields_points_to_f (g:heap{well_formed_heap2 g})
                              (h_index: hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)}) 
                              
                              (wz: wosize{(is_fields_within_limit1 h_index wz) /\
                                             (is_fields_contents_within_limit2 h_index wz g) /\
                                             (Usize.v wz <= Usize.v (getWosize (read_word g h_index))) /\
                                             (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)})
                              (f':seq Usize.t { (forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g))})
                                 
                  : Tot (b:bool{b == true <==> (forall i.  (Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) f')})
                     (decreases (Usize.v wz)) = 
if (Usize.v wz = 0) then true
    else
      (
        assert (Usize.v wz > 0);
        //get the successor_index = h_index + wz * mword
        let s = Usize.add h_index (Usize.mul wz mword) in
        assert ((Usize.v s >= Usize.v h_index + Usize.v mword) /\ (Usize.v s <= Usize.v h_index + (Usize.v wz * Usize.v mword)));

        // For recursing, find wz' = wz - 1
        let wz' = Usize.sub wz 1UL in

        //if the value stored at s is a pointer
        assert (well_formed_heap2 g);
        assert (Seq.length g == heap_size);
          //Get the value stored at s,succ = g[s]
        let succ = read_word g s in
        assert ((Usize.v s >= Usize.v h_index + Usize.v mword) /\ (Usize.v s <= Usize.v h_index + (Usize.v wz * Usize.v mword)));

          //Get the header of succ. succ_hdr = succ - mword
       
        if (isPointer s g) then
         (
           if (Seq.mem succ f') then
           (
             assert (Seq.mem succ f');
             is_fields_points_to_f g h_index wz' f'
           )
           //header is not part, so invalid pointer stored at the index s.
           else
          (
            false 
          )
         )
        else
         (
            assert (~(isPointer s g));
            let b =  is_fields_points_to_f g h_index wz' f' in
            assert (b == true <==> (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v wz') /\ 
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul i mword)) g  ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) f'));
      
            assert (b == true <==> (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\ 
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul i mword)) g  ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) f'));
           b
         )
       )

#restart-solver 

let is_fields_points_to_allocs2 (h_index: hp_addr) 
                                (g:heap{well_formed_heap2 g /\ is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)}) 
                                (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                             is_fields_contents_within_limit2 h_index wz g) /\
                                             (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)})
                               : Tot (b:bool{b == true <==> (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
                                                                 (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
                                                                 isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                    Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g))}) = 
 assert (is_fields_within_limit1 h_index wz);
 assert (is_fields_contents_within_limit2 h_index wz g);
 let f' = get_allocated_block_addresses g in 
 assert ((forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size));
 assert (G.is_vertex_set f');
 assert (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g));
 let b = is_fields_points_to_f g h_index wz f' in
 b

let rec check_fields_points_to_allocs2 (g:heap{well_formed_heap2 g})
                                       (f':seq Usize.t {(forall x. Seq.mem x f' ==>  Seq.mem x (get_allocated_block_addresses g))}) 
                              
                            : Pure (bool)
                              (requires ((forall i x.  Seq.mem x f' /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)))
                              (ensures fun b -> (b == true <==> (forall x. Seq.mem x f' ==>
                                          is_fields_points_to_f g x (getWosize (read_word g x)) (get_allocated_block_addresses g))))
                              (decreases length f') = 
match length f' with
   | 0 -> true
   | _ -> assert (length f' > 0);
         let hd = Seq.head f' in
         let tl = Seq.tail f' in
         let wz = getWosize (read_word g hd) in
         if Usize.v wz = 0 then
           check_fields_points_to_allocs2 g tl
            
         else
           (
            assert (Usize.v wz > 0);
            if (is_fields_points_to_f g hd(getWosize (read_word g hd)) (get_allocated_block_addresses g)) then
            (
              check_fields_points_to_allocs2 g tl
            )
            else
            (
              false 
            )
           )

#restart-solver

(*Explicitly passing the requires condition of check_fields_points_to_allocs2 is needed to typecheck*)
let test1 (g:heap{well_formed_heap2 g /\
           (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
           (check_fields_points_to_allocs2 g (get_allocated_block_addresses g))}) = 
assert(check_fields_points_to_allocs2 g (get_allocated_block_addresses g));
assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (get_allocated_block_addresses g));
()
   

let well_formed_allocated_blocks (g:heap{well_formed_heap2 g})
                      : Tot (b:bool{b == true <==> check_fields_points_to_allocs2 g (get_allocated_block_addresses g)}) =
  let f = get_allocated_block_addresses g in
  if  check_fields_points_to_allocs2 g f then
    true
  else
   false


#restart-solver

let h_index_field_index_mword_multiple_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                             (h_index: hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()
                                    
let h_index_field_index_all_mword_multiple_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                 (h_index: hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g)})  
                                : Lemma
                                  (ensures (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (h_index_field_index_mword_multiple_lemma g h_index wz))

let h_index_field_index_mword_multiple_lemma3 (g:heap{well_formed_heap2 g})
                                             (h_index: hp_addr{is_valid_header h_index g})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()

let h_index_field_index_all_mword_multiple_lemma3 (g:heap{well_formed_heap2 g})
                                                 (h_index: hp_addr{is_valid_header h_index g})
                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g)})  
                                : Lemma
                                  (ensures (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (h_index_field_index_mword_multiple_lemma3 g h_index wz))
 
#restart-solver 

#restart-solver 

let fieldaddress_within_limits_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                     (x:hp_addr{is_valid_header x g /\ Seq.mem x (get_allocated_block_addresses g)})
                                     (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))})
                          : Lemma
                            (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                            (ensures (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 h_index_field_index_mword_multiple_lemma g x (getWosize (read_word g x)) i

let fieldaddress_within_limits_lemma3 (g:heap{well_formed_heap2 g})
                                     (x:hp_addr{is_valid_header x g })
                                     (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))})
                          : Lemma
                            (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                            (ensures (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 h_index_field_index_mword_multiple_lemma3 g x (getWosize (read_word g x)) i

let fieldaddress_within_limits_lemma_x_i_all(g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                             (x:hp_addr{is_valid_header x g /\ Seq.mem x (get_allocated_block_addresses g)})
                           : Lemma
                             (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                             (ensures (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma g x))


let fieldaddress_within_limits_lemma_x_i_all3 (g:heap{well_formed_heap2 g})
                                              (x:hp_addr{is_valid_header x g})
                           : Lemma
                             (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                             (ensures (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma3 g x))


let fieldaddress_within_limits_lemma_x_all (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                    : Lemma
                                      (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                                      (ensures (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma_x_i_all g))


let fieldaddress_within_limits_lemma_x_all3 (g:heap{well_formed_heap2 g})
                                    : Lemma
                                      (requires (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                                      (ensures (forall i x.  Seq.mem x (objects2 0UL g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma_x_i_all3 g))


let test_allocs (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                (h_index: hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                              (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                 : Lemma 
                   (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                      (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                      (Usize.v (getWosize (read_word g x)) <= Usize.v (getWosize (read_word g x))) /\
                                      (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v  (getWosize (read_word g x)) ==> 
                                             (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)))
                                             
                   (ensures ((forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v wz)/\
                                   (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
                                   isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                   Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g)))) =
 assert (well_formed_allocated_blocks g);
 assert (check_fields_points_to_allocs2 g (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_points_to_f g x (getWosize (read_word g x)) (get_allocated_block_addresses g));
 assert (Seq.mem h_index (get_allocated_block_addresses g));  
 assert (is_fields_points_to_f g h_index (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
 assert (forall i.  (Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
               (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
               isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g));
 ()

let valid_header_lemma (g: heap {well_formed_heap2 g})
                       (g':heap {well_formed_heap2 g'})
                       (v_id: hp_addr {is_valid_header v_id g})
               : Lemma
                 (requires (getWosize  (read_word g v_id) == getWosize (read_word g' v_id)) /\
                           (getTag     (read_word g v_id) == getTag    (read_word g' v_id)) /\
                          
                           (heap_remains_same_except_index_v_id v_id g g'))
                 (ensures (is_valid_header v_id g')) = 
 objects2_equal_lemma 0UL g g';
 ()

let field_reads_equal_lemma (g:heap{well_formed_heap2 g})
                            (g':heap)
                            (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                            (x:hp_addr{Seq.mem x (objects2 0UL g) /\ x <> h_index})
                            (y:hp_addr{Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword)})
                  : Lemma
                    (requires (objects2 0UL g == objects2 0UL g') /\
                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                    (ensures (read_word g y == read_word g' y)) = 
 assert (~(Seq.mem y (objects2 0UL g)));
 assert (y <> h_index);
 assert (read_word g y == read_word g' y);
 assert (Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y);
()

let field_reads_equal_h_index_lemma (g:heap{well_formed_heap2 g})
                                    (g':heap)
                                    (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                    (y:hp_addr{Usize.v y >= Usize.v h_index + Usize.v mword /\
                                       Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword)})
                  : Lemma
                    (requires (objects2 0UL g == objects2 0UL g') /\
                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                    (ensures (read_word g y == read_word g' y)) = 
assert (~(Seq.mem y (objects2 0UL g)));
assert (y <> h_index);
assert (read_word g y == read_word g' y);
()


let field_reads_all_equal_lemma (g:heap{well_formed_heap2 g})
                                (g':heap)
                                (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                (x:hp_addr{Seq.mem x (objects2 0UL g) /\ x <> h_index})
                      : Lemma
                        (requires (objects2 0UL g == objects2 0UL g') /\
                              (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                        (ensures (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                        read_word g y == read_word g' y)) = 
 Classical.forall_intro (Classical.move_requires (field_reads_equal_lemma g g' h_index x))

let field_reads_all_equal_h_index_lemma (g:heap{well_formed_heap2 g})
                                        (g':heap)
                                        (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                            : Lemma
                              (requires (objects2 0UL g == objects2 0UL g') /\
                                        (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t))
                              (ensures (forall y. Usize.v y >= Usize.v h_index + Usize.v mword /\
                                             Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                                   read_word g y == read_word g' y)) = 
 
 Classical.forall_intro (Classical.move_requires (field_reads_equal_h_index_lemma g g' h_index))


let field_reads_all_equal_for_all_objects_lemma (g:heap{well_formed_heap2 g})
                                                (g':heap)
                                                (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                                 :Lemma
                                 (requires (objects2 0UL g == objects2 0UL g') /\
                                          (forall (t:hp_addr). t <> h_index ==> read_word g t == read_word g' t)) 
                                 (ensures (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) /\
                                       x <> h_index ==>  read_word g y == read_word g' y)) =
Classical.forall_intro (Classical.move_requires (field_reads_all_equal_lemma g g' h_index))


#restart-solver 

#push-options "--z3rlimit 500"

#restart-solver

(*let well_formed_heap2_lemma (g:heap{well_formed_heap2 g})
                            (g':heap)
                : Lemma
                  (requires (objects2 0UL g == objects2 0UL g') /\
                            (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x)) /\
                            (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y))*)

let colorHeader1  (v_id:hp_addr)  
                  (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                  (c:color)
             : Tot (g': heap{Seq.length g == Seq.length g' /\
                             read_word g' v_id == makeHeader (wosize_of_object1 v_id g) (c) (tag_of_object1 v_id g) /\
                            heap_remains_same_except_index_v_id v_id g g' /\
                            color_of_object1 v_id g' == c /\
                            wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                            tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                            objects2 0UL g == objects2 0UL g' /\
                            well_formed_heap2 g' /\ is_valid_header v_id g'}) = 
 let wz = getWosize (read_word g v_id) in
 let tg = getTag (read_word g v_id) in  
 let h = makeHeader wz c tg in
 assert (wz == getWosize h);
 assert (c == getColor h);
 assert (tg == getTag h);
 assert (Usize.v v_id >= 0);
 assert (Usize.v v_id < heap_size);
 assert (Usize.v v_id < Seq.length g);
 assert (well_formed_heap2 g);
 let h_index = v_id in
 assert (Seq.mem h_index (objects2 0UL g));
 assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 assert (forall (x:hp_addr). x <> h_index ==> read_word g x == read_word g' x);
 assert (heap_remains_same_except_index_v_id h_index g g');
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). x <> h_index ==> getWosize (read_word g x) == getWosize (read_word g' x));
 assert (getWosize (read_word g h_index) == getWosize (read_word g' h_index));
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x));
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.mem v_id (objects2 0UL g'));
 
 assert (is_fields_contents_within_limit2 v_id wz g);
 
 
 assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> v_id ==>
                             read_word g x == read_word g' x);


 field_reads_all_equal_for_all_objects_lemma g g' h_index;
 field_reads_all_equal_h_index_lemma g g' h_index;
 assert ((forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));

 assert (forall x. Seq.mem x (objects2 0UL g) ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x  (objects2 0UL g) ==> is_hp_addr x);
 assert (check_all_block_fields_within_limit2 g (objects2 0UL g));


 
                                                             
 check_all_block_fields_within_limit2_lemma g g' (objects2 0UL g) (objects2 0UL g');

 assert (check_all_block_fields_within_limit2 g' (objects2 0UL g'));

 

 check_fields_points_to_blocks2_lemma g g' (objects2 0UL g) (objects2 0UL g');
                                           
 assert (Seq.length (objects2 0UL g') > 0);
 assert (check_all_block_fields_within_limit2 g' (objects2 0UL g'));
 assert (check_fields_points_to_blocks2 g' (objects2 0UL g'));
 assert (well_formed_heap2 g');
 
 valid_header_lemma g g' v_id;
 assert (is_valid_header v_id g');
 g'



#restart-solver 

let colorHeader1_Lemma  (v_id:hp_addr)  
                        (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                        (c:color)
              : Lemma
                ((check_all_block_fields_within_limit2 (colorHeader1 v_id g c) (objects2 0UL (colorHeader1 v_id g c))) /\
                  check_fields_points_to_blocks2 (colorHeader1 v_id g c) (objects2 0UL (colorHeader1 v_id g c))) = 
 let wz = getWosize (read_word g v_id) in
 let tg = getTag (read_word g v_id) in  
 let h = makeHeader wz c tg in
 assert (wz == getWosize h);
 assert (c == getColor h);
 assert (tg == getTag h);
 assert (Usize.v v_id >= 0);
 assert (Usize.v v_id < heap_size);
 assert (Usize.v v_id < Seq.length g);
 assert (well_formed_heap2 g);
 let h_index = v_id in
 assert (Seq.mem h_index (objects2 0UL g));
 assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 assert (forall (x:hp_addr). x <> h_index ==> read_word g x == read_word g' x);
 assert (heap_remains_same_except_index_v_id h_index g g');
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). x <> h_index ==> getWosize (read_word g x) == getWosize (read_word g' x));
 assert (getWosize (read_word g h_index) == getWosize (read_word g' h_index));
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x));
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.mem v_id (objects2 0UL g'));
 
 assert (is_fields_contents_within_limit2 v_id wz g);
 
 
 assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> v_id ==>
                             read_word g x == read_word g' x);


 field_reads_all_equal_for_all_objects_lemma g g' h_index;
 field_reads_all_equal_h_index_lemma g g' h_index;
 assert ((forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));
                                                             
 check_all_block_fields_within_limit2_lemma g g' (objects2 0UL g) (objects2 0UL g');
 assert (check_all_block_fields_within_limit2 g' (objects2 0UL g'));
 check_fields_points_to_blocks2_lemma g g' (objects2 0UL g) (objects2 0UL g');
 assert (check_fields_points_to_blocks2 g' (objects2 0UL g'));
 ()


let colorHeader1_allocated_blocks_Lemma  (g:heap{well_formed_heap2 g})
                                         (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})  
                                         (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                        : Lemma
                          (get_allocated_block_addresses g == get_allocated_block_addresses (colorHeader1 v_id g c)) = 
 let g' = colorHeader1 v_id g c in
 get_allocated_block_addresses_lemma g g' v_id c;
 ()


let colorHeader1_fields_lemma  (v_id:hp_addr)  
                               (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                               (c:color)
             : Lemma 
               (ensures    (*header coloring does not change wosize*)
                           (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word (colorHeader1 v_id g c) x)) /\

                           (*header coloring does not change field values*)
                           (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word (colorHeader1 v_id g c) y)) = 
 let wz = getWosize (read_word g v_id) in
 let tg = getTag (read_word g v_id) in  
 let h = makeHeader wz c tg in
 assert (wz == getWosize h);
 assert (c == getColor h);
 assert (tg == getTag h);
 assert (Usize.v v_id >= 0);
 assert (Usize.v v_id < heap_size);
 assert (Usize.v v_id < Seq.length g);
 assert (well_formed_heap2 g);
 let h_index = v_id in
 assert (Seq.mem h_index (objects2 0UL g));
 assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 assert (forall (x:hp_addr). x <> h_index ==> read_word g x == read_word g' x);
 assert (heap_remains_same_except_index_v_id h_index g g');
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). x <> h_index ==> getWosize (read_word g x) == getWosize (read_word g' x));
 assert (getWosize (read_word g h_index) == getWosize (read_word g' h_index));
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x));
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (Seq.mem v_id (objects2 0UL g'));
 
 assert (is_fields_contents_within_limit2 v_id wz g);
 
 
 assert (forall x. Seq.mem x (objects2 0UL g) /\ x <> v_id ==>
                             read_word g x == read_word g' x);


 field_reads_all_equal_for_all_objects_lemma g g' h_index;
 field_reads_all_equal_h_index_lemma g g' h_index;
 assert ((forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y));
 ()

#restart-solver 

#restart-solver

#restart-solver

#restart-solver

(*let colorHeader1_fields_allocated_blocks_helper_lemma  (v_id:hp_addr)  
                                                       (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                                                       (c:color) 
                                                       (h_index:hp_addr{is_valid_header h_index g})
                                                       (y:Usize.t{Usize.v y >= 1 /\
                                                                  Usize.v y <= (Usize.v (getWosize (read_word g h_index))) /\
                                                                  is_hp_addr (Usize.add h_index (Usize.mul y mword))})
                        : Lemma
                          (requires (forall x. Seq.mem x (objects2 0UL (colorHeader1 v_id g c)) ==> 
                                           (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                                 Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word (colorHeader1 v_id g c) y)))
                          (ensures read_word g (Usize.add h_index (Usize.mul y mword)) == 
                                   read_word (colorHeader1 v_id g c) (Usize.add h_index (Usize.mul y mword))) = 
 let objs1 = objects2 0UL g in
 let g' = colorHeader1 v_id g c in
 let objs2 = objects2 0UL g' in
 assert (objs1 == objs2);
 assert (Seq.mem h_index objs2);
 assert (is_valid_header h_index g');
 assert (forall y. Usize.v y >= Usize.v h_index + Usize.v mword /\
              Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                               read_word g y == read_word (colorHeader1 v_id g c) y);
 
 let p = Usize.add h_index (Usize.mul y mword) in
 assert (is_hp_addr p);
 assert (Usize.v p >=  Usize.v h_index + Usize.v mword);
 assert (Usize.v p <=  Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword));
 assert (read_word g p == read_word (colorHeader1 v_id g c) p);
 ()
                                                             
#restart-solver 

let colorHeader1_fields_allocated_blocks_all_helper_lemma  (v_id:hp_addr)  
                                                           (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                                                           (c:color) 
                                                           (h_index:hp_addr{is_valid_header h_index g})
                                                       
                        : Lemma
                          (requires        (objects2 0UL g == objects2 0UL (colorHeader1 v_id g c)) /\
                                           (forall x. Seq.mem x (objects2 0UL (colorHeader1 v_id g c)) ==> 
                                           (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                                 Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word (colorHeader1 v_id g c) y)))
                          (ensures (forall y. Usize.v y >= 1 /\ Usize.v y <= (Usize.v (getWosize (read_word g h_index))) /\
                                                         is_hp_addr (Usize.add h_index (Usize.mul y mword)) ==>
                                   read_word g (Usize.add h_index (Usize.mul y mword)) == 
                                   read_word (colorHeader1 v_id g c) (Usize.add h_index (Usize.mul y mword)))) = 
Classical.forall_intro (Classical.move_requires (colorHeader1_fields_allocated_blocks_helper_lemma v_id g c h_index))
                                                                  
let colorHeader1_fields_allocated_blocks_all_helper_lemma1  (v_id:hp_addr)  
                                                            (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                                                            (c:color) 
                          : Lemma
                          (requires (objects2 0UL g == objects2 0UL (colorHeader1 v_id g c)) /\
                                    (forall x. Seq.mem x (objects2 0UL (colorHeader1 v_id g c)) ==> 
                                     (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                                 Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word (colorHeader1 v_id g c) y)))
                          (ensures (forall x. Seq.mem x (objects2 0UL (colorHeader1 v_id g c)) ==>
                                      (forall y. Usize.v y >= 1 /\ Usize.v y <= (Usize.v (getWosize (read_word g x))) /\
                                                         is_hp_addr (Usize.add x (Usize.mul y mword)) ==>
                                                         read_word g (Usize.add x (Usize.mul y mword)) == 
                                                         read_word (colorHeader1 v_id g c) (Usize.add x (Usize.mul y mword))))) = 
Classical.forall_intro (Classical.move_requires (colorHeader1_fields_allocated_blocks_all_helper_lemma v_id g c))
                                                           
let colorHeader1_fields_allocated_blocks_lemma  (v_id:hp_addr)  
                                                (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                                                (c:color) 
                  : Lemma
                    (requires (objects2 0UL g == objects2 0UL (colorHeader1 v_id g c)) /\
                                    (forall x. Seq.mem x (objects2 0UL (colorHeader1 v_id g c)) ==> 
                                     (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                                 Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word (colorHeader1 v_id g c) y)))
                    (ensures (forall y. Seq.mem y (get_allocated_block_addresses (colorHeader1 v_id g c)) ==>
                                         Usize.v (getWosize (read_word g y)) == Usize.v (getWosize (read_word (colorHeader1 v_id g c) y))) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses(colorHeader1 v_id g c)) ==> 
                                (forall y. Usize.v y >= 1 /\
                                Usize.v y <= (Usize.v (getWosize (read_word g x))) /\
                                is_hp_addr ((Usize.add x (Usize.mul y mword))) ==>
                                                             read_word g (Usize.add x (Usize.mul y mword)) == 
                                                             read_word (colorHeader1 v_id g c) (Usize.add x (Usize.mul y mword)))))= 
colorHeader1_fields_lemma v_id g c;  
assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word (colorHeader1 v_id g c) x));
assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 v_id g c)) ==> getWosize (read_word g x) == getWosize (read_word (colorHeader1 v_id g c) x));
assert (forall y. Seq.mem y (get_allocated_block_addresses (colorHeader1 v_id g c)) ==> getWosize (read_word g y) == getWosize (read_word (colorHeader1 v_id g c) y));
assert (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word (colorHeader1 v_id g c) y);
assert (forall x. Seq.mem x (objects2 0UL g) ==> 
                      (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word (colorHeader1 v_id g c) y));
colorHeader1_fields_allocated_blocks_all_helper_lemma1 v_id g c;

assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 v_id g c)) ==>
                                      (forall y. Usize.v y >= 1 /\ Usize.v y <= (Usize.v (getWosize (read_word g x))) /\
                                                         is_hp_addr (Usize.add x (Usize.mul y mword)) ==>
                                                         read_word g (Usize.add x (Usize.mul y mword)) == 
                                                         read_word (colorHeader1 v_id g c) (Usize.add x (Usize.mul y mword))));

assert (forall x. Seq.mem x (get_allocated_block_addresses (colorHeader1 v_id g c)) ==>
                                      (forall y. Usize.v y >= 1 /\ Usize.v y <= (Usize.v (getWosize (read_word g x))) /\
                                                         is_hp_addr (Usize.add x (Usize.mul y mword)) ==>
                                                         read_word g (Usize.add x (Usize.mul y mword)) == 
                                                         read_word (colorHeader1 v_id g c) (Usize.add x (Usize.mul y mword))));
()
*)

#push-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 4"

#restart-solver

let field_limits_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                    : Lemma
                      (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)))) = 
 assert (well_formed_heap2 g);
 let objs = objects2 0UL g in
 assert (forall x. Seq.mem x objs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 assert (G.subset_vertices (get_allocated_block_addresses g) objs);
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 ()

let field_contents_within_limits_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                                            : Lemma
                                              (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) = 
 assert (well_formed_heap2 g);
 let objs = objects2 0UL g in
 assert (check_all_block_fields_within_limit2 g objs);
 assert ((forall x. Seq.mem x objs ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
 assert (G.subset_vertices (get_allocated_block_addresses g) objs);  
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
 ()


#restart-solver 


#restart-solver


let rec is_fields_points_to_f_lemma (g:heap{well_formed_heap2 g})
                                    (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})
                                    (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                                    (g':heap{(well_formed_heap2 g')})
                                    (y:hp_addr{is_valid_header y g /\ Seq.mem y (get_allocated_block_addresses g)})
                                    
                                    (wz: wosize{ is_fields_within_limit1 y wz /\
                                                 is_fields_contents_within_limit2 y wz g /\
                                                 (Usize.v wz <= Usize.v (getWosize (read_word g y))) /\
                                                 (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v y  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)})

                                     (f':seq Usize.t { (forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                      (forall x. Seq.mem x f' ==> 
                                                             Seq.mem x (get_allocated_block_addresses g))})
                                    (wz1: wosize{ is_fields_within_limit1 y wz1 /\
                                                  is_fields_contents_within_limit2 y wz1 g' /\
                                                  (Usize.v wz1 <= Usize.v (getWosize (read_word g' y))) /\
                                                  (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz1 ==> (Usize.v y  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)})
                                   
                                    (f1:seq Usize.t { (forall x. Seq.mem x f1 ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x f1 ==> is_hp_addr x) /\
                                                      (forall x. Seq.mem x f1 ==> 
                                                            Seq.mem x (get_allocated_block_addresses g'))})
                                   : Lemma
                                     (requires ((f' == f1) /\ (wz == wz1) /\
                                                (forall x. Usize.v x  >= Usize.v y + Usize.v mword /\
                                                      Usize.v x <= Usize.v y + (Usize.v wz * Usize.v mword) ==> read_word g x == read_word g' x) /\
                                                      
                                                       (Seq.equal g' (colorHeader1 v_id g c))))
                                     (ensures (is_fields_points_to_f g y wz f' ==> is_fields_points_to_f g' y wz1 f1))
                                     (decreases (Usize.v wz)) = 
 if (Usize.v wz = 0) then ()
    else
      (
        assert (Usize.v wz > 0);
        //get the successor_index = h_index + wz * mword
        let s = Usize.add y (Usize.mul wz mword) in
        assert ((Usize.v s >= Usize.v y + Usize.v mword) /\ (Usize.v s <= Usize.v y + (Usize.v wz * Usize.v mword)));

        // For recursing, find wz' = wz - 1
        let wz' = Usize.sub wz 1UL in

        //if the value stored at s is a pointer
        assert (well_formed_heap2 g);
        assert (Seq.length g == heap_size);
          //Get the value stored at s,succ = g[s]
        let succ = read_word g s in
        let succ' = read_word g' s in

        assert (succ == succ');
        assert ((Usize.v s >= Usize.v y + Usize.v mword) /\ (Usize.v s <= Usize.v y + (Usize.v wz * Usize.v mword)));

          //Get the header of succ. succ_hdr = succ - mword
       
        if (isPointer s g) then
         (
           if (Seq.mem succ f') then
           (
             assert (Seq.mem succ f');
             assert (Seq.mem succ f1);
             assert ((forall x. Usize.v x  >= Usize.v y + Usize.v mword /\
                          Usize.v x <= Usize.v y + (Usize.v wz' * Usize.v mword) ==> read_word g x == read_word g' x));
             assert (is_fields_within_limit1 y wz' /\
                    is_fields_contents_within_limit2 y wz' g');
             assert (Usize.v wz' <= Usize.v (getWosize (read_word g' y)));
             assert (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz' ==> (Usize.v y  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
             is_fields_points_to_f_lemma g v_id c g' y wz' f' wz' f1
           )
           //header is not part, so invalid pointer stored at the index s.
           else
          (
            ()
          )
         )
        else
         (
            assert (~(isPointer s g));
            assert (is_fields_within_limit1 y wz);
            assert (is_fields_within_limit1 y wz');

            assert ( is_fields_contents_within_limit2 y wz g);
            assert ( is_fields_contents_within_limit2 y wz' g);

            assert ( is_fields_contents_within_limit2 y wz g');
            assert ( is_fields_contents_within_limit2 y wz' g');

            assert (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> (Usize.v y  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);

            assert (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz' ==> (Usize.v y  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);

            assert (Usize.v wz <= Usize.v (getWosize (read_word g y)));

            assert (Usize.v wz' <= Usize.v (getWosize (read_word g y)));

            assert (forall x. Usize.v x >= Usize.v y + Usize.v mword /\
                         Usize.v x <= Usize.v y + (Usize.v wz * Usize.v mword) ==> read_word g x == read_word g' x);

            assert (forall x. Usize.v x >= Usize.v y + Usize.v mword /\
                         Usize.v x <= Usize.v y + (Usize.v wz' * Usize.v mword) ==> read_word g x == read_word g' x);

            is_fields_points_to_f_lemma g v_id c g' y wz' f' wz' f1; 
            ()
         )
       )

 
     

#restart-solver 

#restart-solver 

let rec all_allocated_blocks_have_allocated_successors_lemma_helper (g:heap{well_formed_heap2 g})
                                                                    (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})
                                                                    (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                                                                    (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c)})
                                                                    (f: seq Usize.t {  (forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                       (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                                                       (forall x. Seq.mem x f ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                                                       (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                                                       (forall x. Seq.mem x f ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                                                                       (G.is_vertex_set f)})
                                                                    
                                                                    (f': seq Usize.t { (forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                       (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                                       (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
                                                                                       (forall x. Seq.mem x f' ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g') /\
                                                                                       (forall x. Seq.mem x f' ==> Seq.mem x (get_allocated_block_addresses g')) /\
                                                                                       (G.is_vertex_set f')})
                                   : Lemma
                                     (requires (f == f') /\
                                                (forall x y. Seq.mem y f /\ Usize.v x  >= Usize.v y + Usize.v mword /\
                                                      Usize.v x <= Usize.v y + (Usize.v (getWosize (read_word g y)) * Usize.v mword) ==> read_word g x == read_word g' x) /\
                                                (forall i x.  Seq.mem x f' /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                                     (ensures ((check_fields_points_to_allocs2 g f) ==>
                                                 (check_fields_points_to_allocs2 g' f')))
                                     (decreases (Seq.length f)) = 
 match length f with
   | 0 -> ()
   | _ -> assert (length f > 0);
         let hd = Seq.head f in
         let tl = Seq.tail f in
         let wz = getWosize (read_word g hd) in
         let wz' = getWosize (read_word g' hd) in
         assert (wz == wz');
         get_allocated_block_addresses_lemma g g' v_id c;
         assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
         if Usize.v wz = 0 then
         (
           //check_fields_points_to_allocs3 g tl
           G.is_vertex_set_lemma f;
           assert (G.is_vertex_set tl);
           assert ((forall x. Seq.mem x tl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                   (forall x. Seq.mem x tl ==> Usize.v x % Usize.v mword == 0) /\
                   (forall x. Seq.mem x tl ==> Seq.mem x (get_allocated_block_addresses g')));
           all_allocated_blocks_have_allocated_successors_lemma_helper g v_id c g' tl tl
         )
            
         else
           (
            assert (Usize.v wz > 0);
             
            assert ((forall x. Usize.v x  >= Usize.v hd + Usize.v mword /\
                          Usize.v x <= Usize.v hd + (Usize.v wz' * Usize.v mword) ==> read_word g x == read_word g' x));

            assert (is_fields_within_limit1 hd wz);
            assert (is_fields_within_limit1 hd wz');

            assert (is_fields_contents_within_limit2 hd wz g);
            assert (is_fields_contents_within_limit2 hd wz' g);
            assert (is_fields_contents_within_limit2 hd wz' g');
            assert (Usize.v wz' <= Usize.v (getWosize (read_word g' hd)));
          
            
            is_fields_points_to_f_lemma g v_id c g' hd wz f wz' f';
            is_fields_points_to_f_lemma g v_id c g' hd wz (get_allocated_block_addresses g) wz' (get_allocated_block_addresses g');
            
            if (is_fields_points_to_f g hd (getWosize (read_word g hd)) (get_allocated_block_addresses g)) then
            (
              //assert (is_fields_points_to_allocs2 hd g (getWosize (Seq.index g (Usize.v hd))));
              assert (is_fields_points_to_f g' hd (getWosize (read_word g' hd)) (get_allocated_block_addresses g'));
              //check_fields_points_to_allocs3 g tl
             G.is_vertex_set_lemma f;
             assert (G.is_vertex_set tl);
             assert ((forall x. Seq.mem x tl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                   (forall x. Seq.mem x tl ==> Usize.v x % Usize.v mword == 0) /\
                   (forall x. Seq.mem x tl ==> Seq.mem x (get_allocated_block_addresses g')));
             all_allocated_blocks_have_allocated_successors_lemma_helper g v_id c g' tl tl
            )
            else
            (
              ()
            )
           )

#push-options "--z3rlimit 1000"


let well_formed_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                                                 
                                       (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})
                                       (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                                       (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })
                                       
                                  : Lemma
                                    (requires (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                              (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                              (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
                                              (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                              (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g') /\
                                              (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                              (forall i x.  Seq.mem x (get_allocated_block_addresses g') /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                                    (ensures well_formed_allocated_blocks g ==> well_formed_allocated_blocks g') =
 get_allocated_block_addresses_lemma g g' v_id c;
 let f = get_allocated_block_addresses g in
 let f' = get_allocated_block_addresses g' in
 assert (f == f');
 field_reads_all_equal_for_all_objects_lemma g g' v_id;
 field_reads_all_equal_h_index_lemma g g' v_id;
 assert ((forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size));
 assert ( (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 assert (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 assert (forall x. Seq.mem x f' ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
 assert ((forall x y. Seq.mem y f /\ Usize.v x  >= Usize.v y + Usize.v mword /\
                               Usize.v x <= Usize.v y + (Usize.v (getWosize (read_word g y)) * Usize.v mword) ==>  read_word g x == read_word g' x));  
 
 assert (forall i x.  Seq.mem x f' /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
 assert ((forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
         (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
         (forall x. Seq.mem x f ==> Seq.mem x (get_allocated_block_addresses g)) /\
         (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
         (forall x. Seq.mem x f ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
         (G.is_vertex_set f)); 
 assert (f == f');

 assert (is_valid_header v_id g /\ is_valid_header v_id g');
 assert (well_formed_heap2 g');
 assert (Seq.mem v_id f /\ Seq.mem v_id f');        
 all_allocated_blocks_have_allocated_successors_lemma_helper g v_id c g' f f';
 assert (check_fields_points_to_allocs2 g f ==> check_fields_points_to_allocs2 g' f');
 assert (well_formed_allocated_blocks g ==> well_formed_allocated_blocks g');
 ()

let test_color_lemma (v_id:hp_addr)  
                     (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                     (c:color) =
 let g' = colorHeader1 v_id g c in
 colorHeader1_Lemma v_id g c;
 assert (check_all_block_fields_within_limit2 g' (objects2 0UL g'));
 assert ((forall x. Seq.mem x (objects2 0UL g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g'));
 assert (well_formed_heap2 g);
 assert (check_all_block_fields_within_limit2 g (objects2 0UL g));
 assert ((forall x. Seq.mem x (objects2 0UL g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
 ()

let cons_property_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                        (h_index:hp_addr{Seq.mem h_index (get_allocated_block_addresses g)})
                        (s:seq G.edge{(forall x. Seq.mem x s ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                            Seq.mem (snd x) (get_allocated_block_addresses g)) /\
                                      (forall x. Seq.mem x s ==> fst x == h_index)})
                        (s_cons:G.edge{Seq.mem (fst s_cons) (get_allocated_block_addresses g) /\
                                       Seq.mem (snd s_cons) (get_allocated_block_addresses g) /\
                                       fst s_cons == h_index})
                 : Lemma
                   (ensures (forall x. Seq.mem x (Seq.cons s_cons s) ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                                    Seq.mem (snd x) (get_allocated_block_addresses g)) /\
                            (forall x. Seq.mem x (Seq.cons s_cons s) ==> fst x == h_index)) = 
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert ((forall x. Seq.mem x s' ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                 Seq.mem (snd x) (get_allocated_block_addresses g)) /\
         (forall x. Seq.mem x s' ==> fst x == h_index)) ; 
 ()
                   
#restart-solver

let cons_length_lemma1 (#a:Type)
                       (s:seq a)
                       (s_cons:a)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s)) == Seq.length s + 1)=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ; 
 ()

#restart-solver 

let length_empty_lemma (s:seq UInt64.t)
                : Lemma
                  (requires s == Seq.empty)
                  (ensures (Seq.length s == 0)) = ()
                  
let mem_empty_lemma (s:seq UInt64.t)
              : Lemma
                (requires s == Seq.empty)
                (ensures (~(exists x. Seq.mem x s))) = ()

let cons_mem_property_lemma (s:seq UInt64.t)
                            (elem: UInt64.t)
               : Lemma
                 (requires (forall x. Seq.mem x s ==> Usize.v x > 0 /\ Usize.v x < heap_size) /\
                           (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                           (forall x. Seq.mem x s ==> is_hp_addr x) /\
                           
                           (Usize.v elem > 0 /\ Usize.v elem < heap_size) /\
                           (Usize.v elem % Usize.v mword == 0) /\
                           (is_hp_addr elem))
                (ensures ( (forall x. Seq.mem x (cons elem s) ==> Usize.v x > 0 /\ Usize.v x < heap_size) /\
                           (forall x. Seq.mem x (cons elem s) ==> Usize.v x % Usize.v mword == 0) /\
                           (forall x. Seq.mem x (cons elem s) ==> is_hp_addr x))) =
                           
 mem_cons elem s;
 ()

#push-options "--z3rlimit 1000"

#restart-solver

let cons_length_lemma (s:seq Usize.t)
                      (s_cons:Usize.t)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s)) == Seq.length s + 1)=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ; 
 ()

#restart-solver 

let rec create_successors_list_for_h_index (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                           (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                           (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                           (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                       : Tot (s_list:seq Usize.t(*{Seq.length s_list == (Usize.v wz + 1) - Usize.v i}*)) 
                         
                         (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
       assert ((Usize.v i < Usize.v wz + 1) /\ Seq.length s_list > 0 ==> Seq.index s_list (Usize.v i - 1) == read_word g ( Usize.add h_index (Usize.mul i mword)));
       s_list
 
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      if isPointer succ_index g  then
      (
        assert (succ == read_word g succ_index);
        assert (is_valid_header h_index g);
        assert (Seq.mem h_index (objects2 0UL g));
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        
        test_allocs g h_index wz;
        assert (Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g));
        assert (Seq.mem succ (get_allocated_block_addresses g));
        assert (Seq.mem succ (objects2 0UL g));
        assert (is_valid_header succ g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        
        let s_list' = create_successors_list_for_h_index g h_index wz i' in
        

        lemma_tl succ s_list'; 
        
        let s_list = Seq.cons succ s_list' in 
        
        assert (Seq.head s_list == succ);

        
      
        s_list
      )
      else
      (
        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        let s_list = create_successors_list_for_h_index g h_index wz i' in
        s_list
      )
    )

#restart-solver

#restart-solver

#restart-solver 


let rec create_edge_pairs_for_h_index (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                           (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                           (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                           (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                       : Tot (f':seq (G.edge) {(forall x. Seq.mem x f' ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                                     Seq.mem (snd x) (get_allocated_block_addresses g)) /\
                                               (forall x. Seq.mem x f' ==> fst x == h_index)}) 
                        (decreases ((Usize.v wz + 1) - Usize.v i)) = 
                        
 if Usize.v i = Usize.v wz + 1 then
    (
       let e = Seq.empty #G.edge in
       assert (Seq.length e == 0);
       assert ((Seq.length e == (Usize.v wz + 1) - Usize.v i));
       e
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      if isPointer succ_index g  then
      (
        assert (succ == read_word g succ_index);
        assert (is_valid_header h_index g);
        assert (Seq.mem h_index (objects2 0UL g));
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        
        test_allocs g h_index wz;
        assert (Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g));
        assert (Seq.mem succ (get_allocated_block_addresses g));
        assert (Seq.mem succ (objects2 0UL g));
        assert (is_valid_header succ g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);

        let e' = create_edge_pairs_for_h_index g h_index wz i' in
        assert ((forall x. Seq.mem x e' ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                    Seq.mem (snd x) (get_allocated_block_addresses g)) /\
                (forall x. Seq.mem x e' ==> fst x == h_index));
        

       let edge_pair = (h_index,succ) in
       assert (fst edge_pair == h_index);
       assert (Seq.mem (fst edge_pair) (get_allocated_block_addresses g));
       assert (Seq.mem (snd edge_pair) (get_allocated_block_addresses g));
       lemma_tl edge_pair e'; 
       
       let e = Seq.cons edge_pair e' in 
      
       cons_property_lemma g h_index e' edge_pair;

       
      
       assert ((forall x. Seq.mem x e ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                    Seq.mem (snd x) (get_allocated_block_addresses g)) /\
              (forall x. Seq.mem x e ==> fst x == h_index));
       e
        
      )
      else
      (
        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        let e = create_edge_pairs_for_h_index g h_index wz i' in
        e
      )
    )

#restart-solver

#restart-solver

let rec create_edge_pairs_for_h_index_length_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                                   (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                  (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                  (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1}) 
                               : Lemma
                                 (ensures (Seq.length (create_edge_pairs_for_h_index g h_index wz i) <= (Usize.v wz + 1) - Usize.v i))
                                 (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v wz + 1 then
    (
       let e = Seq.empty #G.edge in
       assert (Seq.length e == 0);
       assert (Seq.length e <= (Usize.v wz + 1) - Usize.v i);
       ()
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      if isPointer succ_index g  then
      (
        assert (succ == read_word g succ_index);
        assert (is_valid_header h_index g);
        assert (Seq.mem h_index (objects2 0UL g));
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        
        test_allocs g h_index wz;
        assert (Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g));
        assert (Seq.mem succ (get_allocated_block_addresses g));
        assert (Seq.mem succ (objects2 0UL g));
        assert (is_valid_header succ g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);

        let e' = create_edge_pairs_for_h_index g h_index wz i' in
        
        create_edge_pairs_for_h_index_length_lemma g h_index wz i';
        assert (Seq.length e' <= (Usize.v wz + 1) - Usize.v i');
        
        assert ((forall x. Seq.mem x e' ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                    Seq.mem (snd x) (get_allocated_block_addresses g)) /\
                (forall x. Seq.mem x e' ==> fst x == h_index));
        

       let edge_pair = (h_index,succ) in
       assert (fst edge_pair == h_index);
       assert (Seq.mem (fst edge_pair) (get_allocated_block_addresses g));
       assert (Seq.mem (snd edge_pair) (get_allocated_block_addresses g));
       lemma_tl edge_pair e'; 
       
       let e = Seq.cons edge_pair e' in 
      
       cons_property_lemma g h_index e' edge_pair;

       cons_length_lemma1 e' edge_pair;

       assert (Seq.length e == Seq.length e' + 1);
      
       assert (Seq.length e <= (Usize.v wz + 1) - Usize.v i);
      
       assert ((forall x. Seq.mem x e ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                    Seq.mem (snd x) (get_allocated_block_addresses g)) /\
              (forall x. Seq.mem x e ==> fst x == h_index));
       ()
        
      )
      else
      (
        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        let e = create_edge_pairs_for_h_index g h_index wz i' in
        create_edge_pairs_for_h_index_length_lemma g h_index wz i';
        assert (Seq.length e <= (Usize.v wz + 1) - Usize.v i');
        assert (Seq.length e <= (Usize.v wz + 1) - Usize.v i);
        ()
      )
    )
                                                  
(*wz + 1 = 5
 i = 2
 i' = 3
 length e' <= 5 - 3 = 2
 length e' <= 2

 e == e'
 length e <= 5 - 2 = 3
 length e <= 2 ==> length e <= 3
 
 length e' <= 2
 length e == length e' + 1
 
 length e' <= 2
 length e' + 1 <= 2 + 1
 length e <= 3*)                                         
                                                  


let create_edge_pairs_for_h_index_length_mem_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                                       (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                       (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                                    (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                          (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                             : Lemma
                               (ensures ((forall x. Seq.mem x (create_edge_pairs_for_h_index g h_index wz 1UL) ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                                                                             Seq.mem (snd x) (get_allocated_block_addresses g)) /\
                                        (forall x. Seq.mem x (create_edge_pairs_for_h_index g h_index wz 1UL) ==> fst x == h_index) /\
                                        Seq.length (create_edge_pairs_for_h_index g h_index wz 1UL) <= Usize.v wz)) = 
let e = create_edge_pairs_for_h_index g h_index wz 1UL in
create_edge_pairs_for_h_index_length_lemma g h_index wz 1UL;
assert (Seq.length (create_edge_pairs_for_h_index g h_index wz 1UL) <= Usize.v wz);
()

#restart-solver 

#restart-solver 


let success_fn_test (i:Usize.t)
                    (e:seq (G.edge){(forall x. Seq.mem x e ==> fst x == i)}) =
  let s = G.successors_fn2 i e in
  assert (forall x. Seq.mem x s <==> Seq.mem (i,x) e);
  G.successors_fn2_pick_second_lemma i e;
  assert (G.pick_second e == s);
  ()

#restart-solver 

let rec create_edge_list_from_heap   (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                     (f: seq Usize.t { (forall x. Seq.mem x f ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                       (forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                       (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                       (forall x. Seq.mem x f ==> is_valid_header x g) /\
                                                       (G.is_vertex_set f) /\
                                                       (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                                                                             (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                       : Tot
                         (f': seq (G.edge){(forall x. Seq.mem x f' ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                              Seq.mem (snd x) (get_allocated_block_addresses g)) /\
                                            (forall x. Seq.mem x f' ==> Seq.mem (fst x) f) /\
                                            (forall x. Seq.mem x f ==> G.successors_fn2 x f' == 
                                                                 G.successors_fn2 x 
                                                                                  (create_edge_pairs_for_h_index g 
                                                                                                                 x 
                                                                                                                 (getWosize (read_word g x))
                                                                                                                 1UL))})
                         (decreases (Seq.length f)) = 

if length f = 0 then Seq.empty #G.edge 
 else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));
   
   //assert (G.subset_vertices tl (get_block_addresses_if_valid_block_size2 0UL g));
   let rest_of_f = create_edge_list_from_heap g tl in
   assert (forall x. Seq.mem x rest_of_f ==> Seq.mem (fst x) tl);
   assert (forall x. Seq.mem x rest_of_f ==> Seq.mem (fst x) tl);

   assert (~(exists x. Seq.mem x rest_of_f /\ (fst x) == hd));
   assert (forall x. Seq.mem x rest_of_f ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                        Seq.mem (snd x) (get_allocated_block_addresses g));

   assert (forall x. Seq.mem x tl ==> G.successors_fn2 x rest_of_f == G.successors_fn2 x (create_edge_pairs_for_h_index g 
                                                                                                          x 
                                                                                                          (getWosize (read_word g x))
                                                                                                          1UL));
   let wz = getWosize (read_word g hd) in
   
   let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz 1UL in
   assert (forall x. Seq.mem x edge_pairs_for_hd ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                        Seq.mem (snd x) (get_allocated_block_addresses g));
   assert (forall x. Seq.mem x edge_pairs_for_hd ==> (fst x) == hd);

   assert (forall x. Seq.mem x tl ==> ~(exists y. Seq.mem y edge_pairs_for_hd /\ (fst y) == x));
   
   G.successors_fn2_pick_second_lemma hd edge_pairs_for_hd;
   
   assert (G.successors_fn2 hd edge_pairs_for_hd == G.pick_second edge_pairs_for_hd);
   let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
   Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   assert (forall x. Seq.mem x f' ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                        Seq.mem (snd x) (get_allocated_block_addresses g));
   G.successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 hd (edge_pairs_for_hd) (rest_of_f) f';
   assert (G.successors_fn2 hd f' == G.successors_fn2 hd (edge_pairs_for_hd));
   assert (G.successors_fn2 hd f' == G.successors_fn2 hd (create_edge_pairs_for_h_index g hd 
                                                                                          (getWosize (read_word g hd))
                                                                                          1UL));
   assert (cons hd tl == f);

   G.successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e tl (edge_pairs_for_hd) (rest_of_f) f';
   
   assert (forall x. Seq.mem x tl ==> G.successors_fn2 x f' == G.successors_fn2 x rest_of_f);
   assert (forall x. Seq.mem x tl ==> G.successors_fn2 x f' == G.successors_fn2 x (create_edge_pairs_for_h_index g 
                                                                                                          x 
                                                                                                          (getWosize (read_word g x))
                                                                                                          1UL));
   assert (forall x. Seq.mem x f ==> G.successors_fn2 x f' == G.successors_fn2 x (create_edge_pairs_for_h_index g 
                                                                                                          x 
                                                                                                          (getWosize (read_word g x))
                                                                                                          1UL));
   f'
 )

let create_edge_list_for_graph (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
               : Tot
                 (f': seq (G.edge){(forall x. Seq.mem x f' ==> Seq.mem (fst x) (get_allocated_block_addresses g) /\
                                                         Seq.mem (snd x) (get_allocated_block_addresses g))}) =
  let allocs = get_allocated_block_addresses g in
  create_edge_list_from_heap g allocs
  

#reset-options "--z3rlimit 1000"


  let create_graph_from_heap (g:heap {well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                   : Pure (G.graph_state #unit #unit)
                    (requires True)
                    (ensures fun f -> (G.is_vertex_set f.vertices)/\
                                   (Seq.equal (f.vertices) (get_allocated_block_addresses g))) = 
  
  {
    vertices  = get_allocated_block_addresses g;
    edge_set  = create_edge_list_for_graph g;
  }


let graph_successors_mem_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                      (h_index:hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                                : Lemma
                                  (ensures (forall x. Seq.mem x  (G.successors (create_graph_from_heap g) h_index) ==> 
                                                         Seq.mem x (get_allocated_block_addresses g))) = 
let grph = create_graph_from_heap g in
 let allocs = get_allocated_block_addresses g in
 G.successors_successors_fn2_connect_lemma grph h_index;  
 assert (G.successors grph h_index == G.successors_fn2 h_index grph.edge_set);
 assert (G.successors grph h_index == G.successors_fn2 h_index (create_edge_list_for_graph g));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 assert (forall x. Seq.mem x allocs ==> Seq.mem x (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x allocs ==> is_valid_header x g);
 assert (G.is_vertex_set allocs);
 assert (forall x. Seq.mem x allocs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 assert (forall x. Seq.mem x allocs ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
 assert (forall x. Seq.mem x allocs ==> 
                 (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0));                                     
                                                     
 assert (G.successors grph h_index == G.successors_fn2 h_index (create_edge_list_from_heap g allocs));
 assert (Seq.mem h_index allocs);                                                         

 let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL in 
 assert (G.successors_fn2 h_index (create_edge_list_from_heap g allocs) == 
           G.successors_fn2 h_index h_index_edge_list);                                                                                                                            
                                                                                                                           
 assert (G.successors grph h_index == G.successors_fn2 h_index h_index_edge_list);
                                                        
                                                                                           
 G.successors_fn2_pick_second_lemma h_index h_index_edge_list;

 assert (G.successors_fn2 h_index h_index_edge_list ==
                G.pick_second h_index_edge_list);                                                                                                

 create_edge_pairs_for_h_index_length_mem_lemma g h_index (getWosize (read_word g h_index));
 assert (forall x. Seq.mem x h_index_edge_list ==> Seq.mem (snd x) (get_allocated_block_addresses g));
 G.pick_second_mem_lemma grph h_index_edge_list;

 assert (forall x. Seq.mem x (G.pick_second h_index_edge_list) ==> Seq.mem x (get_allocated_block_addresses g));

 assert (forall x. Seq.mem x (G.successors_fn2 h_index h_index_edge_list) ==> Seq.mem x (get_allocated_block_addresses g));

 assert (forall x. Seq.mem x (G.successors grph h_index) ==> Seq.mem x (get_allocated_block_addresses g));
 ()
                       

let graph_successors_length_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                  (h_index:hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                                : Lemma
                                  (ensures (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v (getWosize (read_word g h_index)))) =
let grph = create_graph_from_heap g in
 let allocs = get_allocated_block_addresses g in
 G.successors_successors_fn2_connect_lemma grph h_index;  
 assert (G.successors grph h_index == G.successors_fn2 h_index grph.edge_set);
 assert (G.successors grph h_index == G.successors_fn2 h_index (create_edge_list_for_graph g));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 assert (forall x. Seq.mem x allocs ==> Seq.mem x (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x allocs ==> is_valid_header x g);
 assert (G.is_vertex_set allocs);
 assert (forall x. Seq.mem x allocs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 assert (forall x. Seq.mem x allocs ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
 assert (forall x. Seq.mem x allocs ==> 
                 (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0));                                     
                                                     
 assert (G.successors grph h_index == G.successors_fn2 h_index (create_edge_list_from_heap g allocs));
 assert (Seq.mem h_index allocs);
 assert (G.successors_fn2 h_index (create_edge_list_from_heap g allocs) == G.successors_fn2 h_index 
                                                                                            (create_edge_pairs_for_h_index g 
                                                                                                                           h_index 
                                                                                                                           (getWosize (read_word g h_index)) 
                                                                                                                           1UL));
 
 assert (G.successors grph h_index == G.successors_fn2 h_index
                                                        (create_edge_pairs_for_h_index g 
                                                                                       h_index 
                                                                                       (getWosize (read_word g h_index)) 
                                                                                       1UL));
                                                                                           
 G.successors_fn2_pick_second_lemma h_index (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);

 assert (G.successors_fn2 h_index (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) ==
                G.pick_second (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL));
 
 G.pick_second_length_lemma (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
 assert (Seq.length (G.pick_second (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL)) == 
         Seq.length (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL));

 create_edge_pairs_for_h_index_length_mem_lemma g h_index (getWosize (read_word g h_index));

 assert (Seq.length (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) <= Usize.v (getWosize (read_word g h_index)));

 assert (Seq.length (G.pick_second (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL)) <= Usize.v (getWosize (read_word g h_index)));

 assert (Seq.length (G.successors_fn2 h_index (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL)) <= Usize.v (getWosize (read_word g h_index)));
 assert (Seq.length (G.successors grph h_index) <= Usize.v (getWosize (read_word g h_index)));
 ()

let size_less_heap_size_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})

                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                             (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                  : Lemma
                    (requires (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size))
                    (ensures (Usize.v (Usize.add h_index (Usize.mul i mword))< heap_size)) = ()

#restart-solver 

#restart-solver 


let seq_empty_lemma ()
            : Lemma
              (ensures (Seq.length (Seq.empty #G.edge) == 0)) = ()
     

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver


#restart-solver

#push-options "--split_queries"

#restart-solver

let rec create_edge_pairs_for_h_index_lemma1 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                             (wz: wosize{(wz == getWosize (read_word g h_index))})

                                            
                         
                                             (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                                             (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})

                                             (c:color{c == 3UL \/ c == 2UL})

                                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })

                                             (wz1: wosize{(wz1 == getWosize (read_word g' h_index))})
                                             
                        : Lemma
                          (requires (well_formed_allocated_blocks g') /\
                                    (objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (wz == wz1) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g') /\
                                    (forall j x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                    (forall j x.  Seq.mem x (get_allocated_block_addresses g') /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)
                                    )
                          (ensures (create_edge_pairs_for_h_index g h_index wz i == create_edge_pairs_for_h_index g' h_index wz1 i))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 
                          
if Usize.v i = Usize.v wz + 1 then
    (
       let e = Seq.empty #G.edge in
       seq_empty_lemma ();
       assert (create_edge_pairs_for_h_index g h_index wz i == create_edge_pairs_for_h_index g' h_index wz1 i);
       ()
    )
  else
   (
     assert (objects2 0UL g == objects2 0UL g');
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g');

     assert (heap_remains_same_except_index_v_id v_id g g');

     field_reads_all_equal_for_all_objects_lemma g g' v_id;

      
      

     assert ((forall x (y:hp_addr{(length (slice g' (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8) /\
                              (length (slice g (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8)}). Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) /\
                                       x <> v_id ==>  read_word g y == read_word g' y));
     field_reads_all_equal_h_index_lemma g g' v_id;

     assert (forall (y:hp_addr{(length (slice g' (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8) /\
                              (length (slice g (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8)}). Usize.v y >= Usize.v h_index + Usize.v mword /\
                                             Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                                   read_word g y == read_word g' y);
     let succ_index = Usize.add h_index (Usize.mul i mword) in

     assert (Usize.v i < Usize.v wz + 1);
     assert (well_formed_allocated_blocks g');

     assert (is_fields_within_limit1 h_index wz);

     assert (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size);

     assert (Usize.v i < Usize.v wz + 1);

     assert (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size);
     
     assert (Usize.v succ_index < heap_size);

     
     //assert (heap_remains_same_except_index_v_id v_id g g');

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
                                       
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);



      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);

      lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8); 
      
      let succ1 = read_word g' succ_index in
      assert (succ1 == read_word g' succ_index);

      assert (Usize.v succ_index >= Usize.v h_index + Usize.v mword /\
             Usize.v succ_index <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword));
      assert (succ == succ1);

      let i' = Usize.(i +^ 1UL) in
      if isPointer succ_index g  then
      (
          let e' = create_edge_pairs_for_h_index g h_index wz i' in

          create_edge_pairs_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;

          assert (create_edge_pairs_for_h_index g h_index wz i' == create_edge_pairs_for_h_index g' h_index wz1 i');
      
          let edge_pair = (h_index,succ) in
          let edge_pair' = (h_index,succ1) in

          assert (edge_pair == edge_pair');

          lemma_tl edge_pair e'; 
          let e = Seq.cons edge_pair e' in 

          lemma_tl edge_pair' e'; 
          let e1 = Seq.cons edge_pair' e' in 

          assert (e == e1);
          assert (create_edge_pairs_for_h_index g h_index wz i == create_edge_pairs_for_h_index g' h_index wz1 i);
      
          ()
      )
      else
      (
        let e' = create_edge_pairs_for_h_index g h_index wz i' in

        create_edge_pairs_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;

        assert (create_edge_pairs_for_h_index g h_index wz i' == create_edge_pairs_for_h_index g' h_index wz1 i');
        assert (create_edge_pairs_for_h_index g h_index wz i == create_edge_pairs_for_h_index g' h_index wz1 i);
        ()
      )
   )

#restart-solver 


#reset-options "--z3rlimit 1000"

let rec create_edge_list_from_heap_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                         (f: seq Usize.t { (forall x. Seq.mem x f ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                           (forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                           (forall x. Seq.mem x f ==> is_valid_header x g) /\
                                                           (G.is_vertex_set f) /\
                                                           (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                                                                             (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                                           
                                           (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})
                                           
                                           (c:color{c == 3UL \/ c == 2UL})
                                           
                                           (g':heap{well_formed_heap2 g' /\ well_formed_allocated_blocks g' /\ Seq.equal g' (colorHeader1 v_id g c)})
                                           (f1: seq Usize.t {(forall x. Seq.mem x f1 ==> Seq.mem x (get_allocated_block_addresses g')) /\
                                                             (forall x. Seq.mem x f1 ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x f1 ==> Usize.v x % Usize.v mword == 0) /\
                                                             (forall x. Seq.mem x f1 ==> is_valid_header x g') /\
                                                             (G.is_vertex_set f1) /\
                                                             (forall x. Seq.mem x f1 ==> is_fields_within_limit1 x (getWosize (read_word g' x)) /\
                                                                             is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g' /\
                                                                             (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g' x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         : Lemma
                           (requires (f == f1))
                           (ensures (create_edge_list_from_heap g f == create_edge_list_from_heap g' f1))
                           (decreases (Seq.length f)) = 
 if length f = 0 then ()
 else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));
   
   //assert (G.subset_vertices tl (get_block_addresses_if_valid_block_size2 0UL g));
   let rest_of_f = create_edge_list_from_heap g tl in

   assert (f == f1);
   let rest_of_f' = create_edge_list_from_heap g' tl in
   
   let wz = getWosize (read_word g hd) in

   let wz' = getWosize (read_word g' hd) in

   assert (wz == wz');

   let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz 1UL in

   let edge_pairs_for_hd1 = create_edge_pairs_for_h_index g' hd wz 1UL in

   assert (Usize.v hd >= 0 /\ Usize.v hd < heap_size /\
          (Usize.v hd % Usize.v mword == 0) /\
          is_valid_header hd g /\
          (Seq.mem hd (get_allocated_block_addresses g)));

   assert (objects2 0UL g == objects2 0UL g');
   assert (heap_remains_same_except_index_v_id v_id g g');

   colorHeader1_allocated_blocks_Lemma g v_id c;
   assert (get_allocated_block_addresses g == get_allocated_block_addresses g');

   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));

   assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x)));

   assert  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);

   assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');

   
   fieldaddress_within_limits_lemma_x_all g;
   
   assert  (forall j x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0);

   fieldaddress_within_limits_lemma_x_all g';

   assert (forall j x.  Seq.mem x (get_allocated_block_addresses g') /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0);
   
   create_edge_pairs_for_h_index_lemma1 g hd wz 1UL v_id c g' wz;

   assert (edge_pairs_for_hd == edge_pairs_for_hd1);

   create_edge_list_from_heap_lemma g tl v_id c g' tl;

   assert (rest_of_f == rest_of_f');

   let p1 = Seq.append (edge_pairs_for_hd) (rest_of_f) in
   let p2 = Seq.append (edge_pairs_for_hd1) (rest_of_f') in
   assert (p1 == p2);
   ()
 )

let create_edge_list_for_graph_lemma (g:heap{well_formed_heap2 g}) 
                                     (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})
                                     (c:color{c == 3UL \/ c== 2UL})
                    : Lemma 
                      (requires (well_formed_allocated_blocks g /\
                                 well_formed_allocated_blocks (colorHeader1 v_id g c)))
                      (ensures (create_edge_list_for_graph g == create_edge_list_for_graph (colorHeader1 v_id g c))) = 
  let allocs = get_allocated_block_addresses g in

  field_limits_allocated_blocks_lemma g;
  field_contents_within_limits_allocated_blocks_lemma g;
  fieldaddress_within_limits_lemma_x_all g;
  assert (forall x. Seq.mem x allocs ==> Seq.mem x (get_allocated_block_addresses g));
  assert (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
  assert (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0);
  assert (forall x. Seq.mem x allocs ==> is_valid_header x g);
  assert (G.is_vertex_set allocs);
  assert (forall x. Seq.mem x allocs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
  assert (forall x. Seq.mem x allocs ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
  assert (forall x. Seq.mem x allocs ==> 
                 (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)); 
  let f  = create_edge_list_from_heap g allocs in
  
  let g' = colorHeader1 v_id g c in
  let allocs' = get_allocated_block_addresses g' in
  get_allocated_block_addresses_lemma g g' v_id c;
  assert (allocs == allocs');

  field_limits_allocated_blocks_lemma g';
  field_contents_within_limits_allocated_blocks_lemma g';
  fieldaddress_within_limits_lemma_x_all g';
  
  let f' = create_edge_list_from_heap g' allocs' in
  create_edge_list_from_heap_lemma g allocs v_id c g' allocs';
  assert (f == f');
  ()

let create_graph_from_heap_lemma (g:heap {well_formed_heap2 g})
                                 (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})
                                 (c:color{c == 3UL \/ c== 2UL})
                         : Lemma 
                           (requires (well_formed_allocated_blocks g /\
                                      well_formed_allocated_blocks (colorHeader1 v_id g c)))
                           (ensures (create_graph_from_heap g == create_graph_from_heap (colorHeader1 v_id g c))) = 
 let g' = colorHeader1 v_id g c in
 let allocs = get_allocated_block_addresses g in
 let allocs' = get_allocated_block_addresses g' in

 get_allocated_block_addresses_lemma g g' v_id c;
 assert (allocs == allocs');

 create_edge_list_for_graph_lemma g v_id c;
 assert (create_edge_list_for_graph g == create_edge_list_for_graph g');

 let grph1 = create_graph_from_heap g in
 let grph2 = create_graph_from_heap g' in
 assert (grph1 == grph2);
 ()

let create_graph_from_heap_lemma_gray (g:heap {well_formed_heap2 g})
                                      (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})
                      : Lemma 
                        (requires (well_formed_allocated_blocks g /\
                                   well_formed_allocated_blocks (colorHeader1 v_id g 2UL)))
                        (ensures (create_graph_from_heap g == create_graph_from_heap (colorHeader1 v_id g 2UL))) =
  create_graph_from_heap_lemma g v_id 2UL

#reset-options "--z3rlimit 100"

let tail_cons (#a:eqtype)
              (s: seq a)
              (x: a)
        : Lemma
          (ensures (Seq.tail (Seq.cons x s) == s)) = 
 lemma_tl x s;
 ()
          
let cons_length_lemma2 (#a:Type)
                       (s:seq a)
                       (s_cons:a)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s)) > 0)=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ; 
 ()

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver





let rec create_successors_pick_second_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                            (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                            (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                            (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                           : Lemma
                             (ensures (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i))
                             (decreases ((Usize.v wz + 1) - Usize.v i)) = 
if Usize.v i = Usize.v wz + 1 then
    (
       seq_empty_lemma ();
       assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);
       ()
 
    )
  else
    (
      let succ_index = Usize.add h_index (Usize.mul i mword) in
      assert (Usize.v i < Usize.v wz + 1);
      assert (well_formed_allocated_blocks g);

      assert (is_fields_within_limit1 h_index wz);
      assert (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size);

      assert (Usize.v i < Usize.v wz + 1);

      assert (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size);
     
      assert (Usize.v succ_index < heap_size);
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);

      let i' = Usize.(i +^ 1UL) in
      
      if isPointer succ_index g  then
      (
        let e' = create_edge_pairs_for_h_index g h_index wz i' in
        let sl' = create_successors_list_for_h_index g h_index wz i' in
        create_successors_pick_second_lemma g h_index wz i';

        assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i') == create_successors_list_for_h_index g h_index wz i');

        assert (G.pick_second e' == sl');
      
        lemma_tl succ sl'; 
        let s_list = Seq.cons succ sl' in
        
        cons_length_lemma2 sl' succ;
        Seq.head_cons succ sl';

       
        assert (Seq.length s_list > 0);
        assert (Seq.head s_list == succ);
      
        let edge_pair = (h_index,succ) in
        lemma_tl edge_pair e'; 
        let e = Seq.cons edge_pair e' in 
        
        cons_length_lemma2 e' edge_pair;
        Seq.head_cons  edge_pair e'; 
        assert (Seq.head e == edge_pair);
        assert (s_list == Seq.cons succ (G.pick_second e'));
        assert (Seq.cons succ (G.pick_second e') == s_list);

        assert (succ == snd (edge_pair));

        assert (Seq.cons (snd edge_pair) (G.pick_second e') == s_list);

        cons_length_lemma1 e' edge_pair; 
        assert (Seq.length e > 0);

        tail_cons e' edge_pair;
        assert (Seq.tail e == e');

        G.pick_second_lemma e;
      
        assert (G.pick_second e == Seq.cons (snd edge_pair) (G.pick_second e'));

        assert (G.pick_second e == s_list);
        assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);
        ()
      )
      else
      (
        let e' = create_edge_pairs_for_h_index g h_index wz i' in
        let sl' = create_successors_list_for_h_index g h_index wz i' in
        create_successors_pick_second_lemma g h_index wz i';

        assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i') == create_successors_list_for_h_index g h_index wz i');
        assert (G.pick_second (create_edge_pairs_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i);
        ()
      )
    )

let graph_successors_heap_create_successor_list_equivalence_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                                  (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))})
                                : Lemma
                                  (requires (is_fields_within_limit1 h_index (getWosize (read_word g h_index)) /\
                                                                       is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g /\
                                                         (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)))
                                  (ensures G.successors (create_graph_from_heap g) h_index == 
                                             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) = 
 
 let grph = create_graph_from_heap g in
 let allocs = get_allocated_block_addresses g in
 G.successors_successors_fn2_connect_lemma grph h_index;
 assert (G.successors grph h_index == G.successors_fn2 h_index grph.edge_set);
 assert (G.successors grph h_index == G.successors_fn2 h_index (create_edge_list_for_graph g));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 assert (G.successors grph h_index == G.successors_fn2 h_index (create_edge_list_from_heap g allocs));
 assert (Seq.mem h_index allocs);
 assert (G.successors_fn2 h_index (create_edge_list_from_heap g allocs) ==  
           G.successors_fn2 h_index (create_edge_pairs_for_h_index g  h_index (getWosize (read_word g h_index)) 1UL));
                                                                                                                
 assert (G.successors grph h_index == G.successors_fn2 h_index (create_edge_pairs_for_h_index g  h_index (getWosize (read_word g h_index)) 1UL));                                                                                                                
                                                                                 
 G.successors_fn2_pick_second_lemma h_index (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);   

 assert (G.successors_fn2 h_index (create_edge_pairs_for_h_index g  h_index (getWosize (read_word g h_index)) 1UL) ==
              G.pick_second (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL));
                                                                
 create_successors_pick_second_lemma g h_index (getWosize (read_word g h_index)) 1UL;

 assert (G.pick_second (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) == 
           create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);

 assert (G.successors_fn2 h_index (create_edge_pairs_for_h_index g  h_index (getWosize (read_word g h_index)) 1UL) ==
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);

 assert (G.successors grph h_index ==  create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);

 assert (G.successors (create_graph_from_heap g) h_index == 
                                             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
 ()




val is_visited : (v_id:hp_addr) ->
                 (g:heap) ->
          Tot (b:bool{b == true <==>  (color_of_object1 v_id g) == black})


let unvisited  (v_id:hp_addr)
               (g:heap{color_of_object1 v_id g == white \/
                       color_of_object1 v_id g == gray \/
                       color_of_object1 v_id g == black})
         : Tot (b:bool{(b == true <==> (~(is_visited v_id g) /\ ~(isGrayObject1 v_id g))) /\
                        (b == true <==> color_of_object1 v_id g == white)}) =
 if not(is_visited v_id g) && not(isGrayObject1 v_id g) then true
 else
  false 

let unvisited_lemma  (v_id:hp_addr)
                     (g:heap{color_of_object1 v_id g == white \/
                             color_of_object1 v_id g == gray \/
                             color_of_object1 v_id g == black})
            : Lemma
              (requires (color_of_object1 v_id g == gray \/
                         color_of_object1 v_id g == black))
              (ensures (color_of_object1 v_id g <> white)) = ()

type stack = s:seq Usize.t {forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size}

type stack_heap_pair = stack & heap


#reset-options "--z3rlimit 500"

#push-options "--z3rlimit 50"

#restart-solver 

let push_to_stack2  (g:heap{well_formed_heap2 g})
                    (st: seq Usize.t{G.is_vertex_set st /\
                                   (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                   (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                   (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)})
                    (x: hp_addr{~(Seq.mem x st) /\
                                (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                (Usize.v x % Usize.v mword == 0) /\
                                is_valid_header x g (*/\ color_of_block x g == white*)}) 
                                
            : Tot (st': stack_heap_pair{well_formed_heap2 (snd st') /\
                                  (forall x. Seq.mem x st ==> Seq.mem x (fst st')) /\
                                  
                                  Seq.mem x (fst st') /\
                                  
                                  (G.is_vertex_set (fst st')) /\
                                  
                                  Seq.length (fst st') == Seq.length st + 1 /\
                                  
                                  (forall y. Seq.mem y (fst st') ==> Usize.v y >= 0 /\ Usize.v y < heap_size) /\

                                  (forall y. Seq.mem y (fst st') ==> Usize.v y % Usize.v mword == 0) /\
                                  
                                  (forall y. Seq.mem y (fst st') ==> is_valid_header y (snd st')) /\
                                  
                                  (forall x. Seq.mem x (objects2 0UL g) /\
                                               isGrayObject1 x (snd st') <==>
                                               Seq.mem x (fst st')) /\
                                               
                                  (forall x. Seq.mem x (objects2 0UL (snd st')) /\
                                               isGrayObject1 x (snd st') <==>
                                               Seq.mem x (fst st'))}) = 
if Seq.length st = 0 then
(
   let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
    assert (Seq.mem x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');
    objects2_equal_lemma 0UL g g';
    
    assert (objects2 0UL g == objects2 0UL g');
                                            
    assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');

    assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');
    assert (heap_remains_same_except_index_v_id x g g');
    assert ((forall x. Seq.mem x stk' ==> Usize.v x % Usize.v mword == 0));
    (stk', g')
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem x st));
  G.snoc_unique_lemma x st;
  assert (G.is_vertex_set st');
  assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  

  assert (forall y. Seq.mem y st' ==> is_valid_header y g);
  assert (forall y. Seq.mem y st' ==> is_valid_header y g');
  
  assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  assert (heap_remains_same_except_index_v_id x g g');
  (st',g')
)

let push_to_stack2_heap_state_lemma  (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{G.is_vertex_set st /\
                                                     (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                     (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                               Seq.mem x st)})
                                     (x: hp_addr{~(Seq.mem x st) /\
                                                  (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                  (Usize.v x % Usize.v mword == 0) /\
                                                  is_valid_header x g (*/\ color_of_block x g == white*)}) 
                  : Lemma  
                    (ensures (heap_remains_same_except_index_v_id x g (snd (push_to_stack2 g st x)))) = ()

#restart-solver 

#restart-solver 

let push_to_stack2_field_size_lemma  (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{G.is_vertex_set st /\
                                           (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                           (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                           (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                           (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)})
                                     (x: hp_addr{~(Seq.mem x st) /\
                                                  (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                  (Usize.v x % Usize.v mword == 0) /\
                                                  is_valid_header x g (*/\ color_of_block x g == white*)}) 
                  : Lemma  
                    (ensures (forall (y:Usize.t{Usize.v y < heap_size /\  Usize.v y % Usize.v mword == 0}). (getWosize (read_word g y)) ==
                                               (getWosize (read_word (snd (push_to_stack2 g st x)) y)))) = ()

let push_to_stack2_lemma (g:heap{well_formed_heap2 g})
                         (st: seq Usize.t{G.is_vertex_set st /\
                                   (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                   (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                   (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)})
                          (x: hp_addr{~(Seq.mem x st) /\
                                (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                (Usize.v x % Usize.v mword == 0) /\
                                is_valid_header x g /\ color_of_object1 x g == white}) 
                   : Lemma
                     (ensures (get_allocated_block_addresses g == get_allocated_block_addresses (snd (push_to_stack2 g st x)))) =
if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
   
    G.is_vertex_set_lemma2 stk';
    
    objects2_equal_lemma 0UL g g';

    assert (color_of_object1 x g == white);
    get_allocated_block_addresses_lemma g g' x 2UL;
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  G.snoc_unique_lemma x st;
  assert (color_of_object1 x g == white);
  get_allocated_block_addresses_lemma g g' x 2UL;
  ()
)

let push_to_stack2_lemma_block_address (g:heap{well_formed_heap2 g})
                         (st: seq Usize.t{G.is_vertex_set st /\
                                   (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                   (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                   (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)})
                          (x: hp_addr{~(Seq.mem x st) /\
                                (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                (Usize.v x % Usize.v mword == 0) /\
                                is_valid_header x g /\ color_of_object1 x g == white}) 
                   : Lemma
                     (ensures (objects2 0UL g == objects2 0UL (snd (push_to_stack2 g st x)))) =
if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
   
    G.is_vertex_set_lemma2 stk';
    
    objects2_equal_lemma 0UL g g';

    assert (color_of_object1 x g == white);
    get_allocated_block_addresses_lemma g g' x 2UL;
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  G.snoc_unique_lemma x st;
  assert (color_of_object1 x g == white);
  get_allocated_block_addresses_lemma g g' x 2UL;
  ()
)

let push_to_stack2_lemma_valid_header (g:heap{well_formed_heap2 g})
                         (st: seq Usize.t{G.is_vertex_set st /\
                                   (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                   (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                   (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)})
                         (x: hp_addr{~(Seq.mem x st) /\
                                (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                (Usize.v x % Usize.v mword == 0) /\
                                is_valid_header x g /\ color_of_object1 x g == white}) 
                   : Lemma
                     (ensures (forall x. is_valid_header x g ==> is_valid_header x (snd (push_to_stack2 g st x)))) =
  push_to_stack2_lemma_block_address g st x;
  ()

#restart-solver 

let push_to_stack2_visited_list_valid_header_lemma  (g:heap{well_formed_heap2 g})
                                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                                    (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                    (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                         Seq.mem x st)})
                                                    (x: hp_addr{~(Seq.mem x st) /\
                                                                 (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                 (Usize.v x % Usize.v mword == 0) /\
                                                                 is_valid_header x g /\ color_of_object1 x g == white}) 
                                                    (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (G.is_vertex_set vl) /\
                                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                    }) 
                        : Lemma
                          (ensures (forall x. Seq.mem x vl ==> is_valid_header x (snd (push_to_stack2 g st x)))) = 
 push_to_stack2_lemma_valid_header g st x; 
 ()


let push_to_stack2_lemma_gray_nodes (g:heap{well_formed_heap2 g})
                         (st: seq Usize.t{G.is_vertex_set st /\
                                   (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                   (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                   (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)})
                         (x: hp_addr{~(Seq.mem x st) /\
                                (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                (Usize.v x % Usize.v mword == 0) /\
                                is_valid_header x g /\ color_of_object1 x g == white}) 
                   : Lemma
                     (ensures (forall y. is_valid_header y g /\ isGrayObject1 y g /\ x <> y ==> is_valid_header y (snd (push_to_stack2 g st x)) /\
                                                                                      isGrayObject1 y (snd (push_to_stack2 g st x)))) = 
if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
   
    G.is_vertex_set_lemma2 stk';
    
    objects2_equal_lemma 0UL g g';

    assert (color_of_object1 x g == white);
    get_allocated_block_addresses_lemma g g' x 2UL;
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  assert (heap_remains_same_except_index_v_id x g g');
  assert (is_valid_header x g);
  assert (~(isGrayObject1 x g));
  objects2_equal_lemma 0UL g g';
  assert (is_valid_header x g');
  assert (isGrayObject1 x g');
  assert (forall y. is_valid_header y g /\ isGrayObject1 y g /\ x <> y ==> is_valid_header y g' /\
                                                                                      isGrayObject1 y g');
  G.snoc_unique_lemma x st;
  assert (color_of_object1 x g == white);
  get_allocated_block_addresses_lemma g g' x 2UL;
  ()
)

#restart-solver 

#reset-options "--z3rlimit 1000" 

//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries"

#restart-solver

(*length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8*)
let push_to_stack2_fields_allocated_blocks_lemma  (g:heap{well_formed_heap2 g})
                                                  (st: seq Usize.t{G.is_vertex_set st /\
                                                                   (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                   (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                   (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)})
                                                  (x: hp_addr{~(Seq.mem x st) /\
                                                               (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (Usize.v x % Usize.v mword == 0) /\
                                                               is_valid_header x g}) 
                                
            : Lemma
              (ensures (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                                   getWosize (read_word (snd (push_to_stack2 g st x)) t)) /\

                           (*header coloring does not change field values*)
                           (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (push_to_stack2 g st x)) y)) = 
 if Seq.length st = 0 then
(
   let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
    assert (Seq.mem x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');
    objects2_equal_lemma 0UL g g';
    
    assert (objects2 0UL g == objects2 0UL g');
    colorHeader1_fields_lemma x g gray;
                                            
    assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');

    assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');
    assert (heap_remains_same_except_index_v_id x g g');
    assert ((forall x. Seq.mem x stk' ==> Usize.v x % Usize.v mword == 0));
    assert (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                                   getWosize (read_word (snd (push_to_stack2 g st x)) t));
    
    assert (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y);
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem x st));
  G.snoc_unique_lemma x st;
  assert (G.is_vertex_set st');
  assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  colorHeader1_fields_lemma x g gray;

  assert (forall y. Seq.mem y st' ==> is_valid_header y g);
  assert (forall y. Seq.mem y st' ==> is_valid_header y g');
  
  assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  assert (heap_remains_same_except_index_v_id x g g');
  assert (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                                   getWosize (read_word (snd (push_to_stack2 g st x)) t));
    
  assert (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y);
  ()
)


let push_to_stack2_lemma_black_nodes (g:heap{well_formed_heap2 g})
                         (st: seq Usize.t{G.is_vertex_set st /\
                                   (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                   (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                   (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)})
                         (x: hp_addr{~(Seq.mem x st) /\
                                (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                (Usize.v x % Usize.v mword == 0) /\
                                is_valid_header x g /\ color_of_object1 x g == white}) 
                   : Lemma
                     (ensures (forall y. is_valid_header y g /\ isBlackObject1 y g /\ x <> y ==> is_valid_header y (snd (push_to_stack2 g st x)) /\
                                                                                      isBlackObject1 y (snd (push_to_stack2 g st x)))) = 
if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
   
    G.is_vertex_set_lemma2 stk';
    
    objects2_equal_lemma 0UL g g';

    assert (color_of_object1 x g == white);
    get_allocated_block_addresses_lemma g g' x 2UL;
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  assert (heap_remains_same_except_index_v_id x g g');
  assert (is_valid_header x g);
  assert (~(isGrayObject1 x g));
  objects2_equal_lemma 0UL g g';
  assert (is_valid_header x g');
  assert (isGrayObject1 x g');
  assert (forall y. is_valid_header y g /\ isBlackObject1 y g /\ x <> y ==> is_valid_header y g' /\
                                                                                      isBlackObject1 y g');
  G.snoc_unique_lemma x st;
  assert (color_of_object1 x g == white);
  get_allocated_block_addresses_lemma g g' x 2UL;
  ()
)

#restart-solver 

#restart-solver

#push-options "--z3rlimit 500"


let colorHeader1_color_Lemma (v_id:hp_addr)  
                             (g:heap{well_formed_heap2 g /\ is_valid_header v_id g /\ color_of_object1 v_id g == white}) 
                             (c:color{c == 2UL})
              : Lemma
                (color_of_object1 v_id (colorHeader1 v_id g c) == 2UL /\
                 color_of_object1 v_id (colorHeader1 v_id g c) <> black /\
                 color_of_object1 v_id g <> black) = ()
                
#restart-solver

#restart-solver 

#push-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 4" 

let push_to_stack2_lemma_black_nodes1 (g:heap{well_formed_heap2 g})
                                      (st: seq Usize.t{G.is_vertex_set st /\
                                                     (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                     (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                             Seq.mem x st)})
                                      (x: hp_addr{~(Seq.mem x st) /\
                                          (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                          (Usize.v x % Usize.v mword == 0) /\
                                          is_valid_header x g /\ color_of_object1 x g == white /\
                                          (*Introduction of the below condition was needed to typecheck*)
                                          is_fields_within_limit1 x (getWosize (read_word g x))}) 
                   : Lemma 
                     (ensures G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x))))) = 
 if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g 2UL in 
    assert (well_formed_heap2 g');
    
    objects2_equal_lemma 0UL g g';
    
    colorHeader1_color_Lemma x g 2UL;

    assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id x g g' /\
                                      color_of_object1 x g' == 2UL /\
                                      (color_of_object1 x g == white \/ color_of_object1 x g == gray \/ 
                                      color_of_object1 x g == black) /\
                                      wosize_of_object1 x g' == wosize_of_object1 x g /\
                                      tag_of_object1 x g' == tag_of_object1 x g /\
                                      is_valid_header x g /\ is_valid_header x g');
    
    get_allocated_block_addresses_lemma g g' x 2UL;

    assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
    
    let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
    let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
   
    G.is_vertex_set_lemma2 stk';
    
    assert (color_of_object1 x g == white);
    assert (color_of_object1 x g <> black);
    assert (color_of_object1 x g' <> black);
    assert (heap_remains_same_except_index_v_id x g g');
    assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
    assert (G.subset_vertices blacks blacks');
    assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))));
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 

  assert (well_formed_heap2 g');

  objects2_equal_lemma 0UL g g';

  colorHeader1_color_Lemma x g 2UL;

  assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id x g g' /\
                                      color_of_object1 x g' == 2UL /\
                                      (color_of_object1 x g == white \/ color_of_object1 x g == gray \/ 
                                      color_of_object1 x g == black) /\
                                      wosize_of_object1 x g' == wosize_of_object1 x g /\
                                      tag_of_object1 x g' == tag_of_object1 x g /\
                                      is_valid_header x g /\ is_valid_header x g');
    
  get_allocated_block_addresses_lemma g g' x 2UL;
  
  let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
  let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
 
  assert (heap_remains_same_except_index_v_id x g g');
  assert (color_of_object1 x g == white);
  assert (color_of_object1 x g <> black);
  assert (color_of_object1 x g' <> black);
  assert (is_valid_header x g);
  assert (~(isGrayObject1 x g));
  
  assert (is_valid_header x g');
  assert (isGrayObject1 x g');
  assert (forall y. is_valid_header y g /\ isBlackObject1 y g /\ x <> y ==> is_valid_header y g' /\
                                                                                      isBlackObject1 y g');
  G.snoc_unique_lemma x st;
  assert (color_of_object1 x g == white);
 
  assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
  assert (G.subset_vertices blacks blacks');
  assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))));
  ()
)

let colorHeader1_subset_lemma  (v_id:hp_addr)  
                               (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                        
              : Lemma
                (ensures (forall x. Seq.mem x (get_black_block_addresses g (get_allocated_block_addresses g)) ==>
                                    Seq.mem x (get_black_block_addresses (colorHeader1 v_id g black) 
                                                 (get_allocated_block_addresses (colorHeader1 v_id g black)))) /\
                          G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                            (get_black_block_addresses (colorHeader1 v_id g black) 
                                                 (get_allocated_block_addresses (colorHeader1 v_id g black)))) = 
let g' = colorHeader1 v_id g black in
let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
assert (heap_remains_same_except_index_v_id v_id g g');
assert (color_of_object1 v_id g' == black);
assert (forall x. Seq.mem x blacks /\ x <> v_id ==> Seq.mem x blacks');
assert (forall x. Seq.mem x blacks ==> Seq.mem x blacks');
assert (G.subset_vertices blacks blacks');
()

let colorHeader1_mem_lemma (v_id:hp_addr)  
                           (g:heap{well_formed_heap2 g /\ is_valid_header v_id g})
                 : Lemma 
                   (ensures (~(exists y. (Seq.mem y (objects2 0UL (colorHeader1 v_id g black)) /\
                                     isBlackObject1 y (colorHeader1 v_id g black)) /\
                                   ~(Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g) /\
                                    (v_id <> y)))) = 
 let g' = colorHeader1 v_id g black in
 colorHeader1_subset_lemma v_id g;
 assert (~(exists y. (Seq.mem y (objects2 0UL (colorHeader1 v_id g black)) /\
                                     isBlackObject1 y (colorHeader1 v_id g black)) /\
                                   ~(Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g) /\
                                    (v_id <> y)));
 ()

#restart-solver

let colorHeader1_mem_lemma_gray (v_id:hp_addr{ (Usize.v v_id >= 0 /\ Usize.v v_id < heap_size) /\
                                               (Usize.v v_id % Usize.v mword == 0)})  
                                (g:heap{well_formed_heap2 g /\ is_valid_header v_id g /\ (color_of_object1 v_id g == white) /\
                                        (is_fields_within_limit1 v_id (getWosize (read_word g v_id)))})
                 : Lemma 
                   (ensures (~(exists y. (Seq.mem y (get_black_block_addresses (colorHeader1 v_id g gray) 
                                                  (get_allocated_block_addresses (colorHeader1 v_id g gray)))) /\
                                    ~(Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)))))) = 
let g' = colorHeader1 v_id g gray in
 assert (well_formed_heap2 g');
    
 objects2_equal_lemma 0UL g g';
    
 colorHeader1_color_Lemma v_id g 2UL;

 assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id v_id g g' /\
                                      color_of_object1 v_id g' == 2UL /\
                                      (color_of_object1 v_id g == white \/ color_of_object1 v_id g == gray \/ 
                                      color_of_object1 v_id g == black) /\
                                      wosize_of_object1 v_id g' == wosize_of_object1 v_id g /\
                                      tag_of_object1 v_id g' == tag_of_object1 v_id g /\
                                      is_valid_header v_id g /\ is_valid_header v_id g');
    
 get_allocated_block_addresses_lemma g g' v_id 2UL;

 assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
 let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
 let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
 
 assert (color_of_object1 v_id g <> black);
 assert (color_of_object1 v_id g' <> black);
 
 assert (G.subset_vertices blacks blacks');
 assert (~(exists y. (Seq.mem y blacks') /\ ~(Seq.mem y blacks)));
 ()


#restart-solver 

#restart-solver

let push_to_stack2_mem_lemma_black_nodes (g:heap{well_formed_heap2 g})
                                         (st: seq Usize.t{G.is_vertex_set st /\
                                                     (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                     (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                     (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                             Seq.mem x st)})
                                         (x: hp_addr{~(Seq.mem x st) /\
                                          (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                          is_valid_header x g /\ color_of_object1 x g == white /\
                                          (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                          (Usize.v x % Usize.v mword == 0)}) 
                   : Lemma 
                     (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                               Seq.mem y (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))))) = 
  if Seq.length st = 0 then
  (
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 

    assert (well_formed_heap2 g');
    
    objects2_equal_lemma 0UL g g';
    
    colorHeader1_color_Lemma x g 2UL;

    assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id x g g' /\
                                      color_of_object1 x g' == 2UL /\
                                      (color_of_object1 x g == white \/ color_of_object1 x g == gray \/ 
                                      color_of_object1 x g == black) /\
                                      wosize_of_object1 x g' == wosize_of_object1 x g /\
                                      tag_of_object1 x g' == tag_of_object1 x g /\
                                      is_valid_header x g /\ is_valid_header x g');
    
    get_allocated_block_addresses_lemma g g' x 2UL;
    
    let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
    let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
   
    G.is_vertex_set_lemma2 stk';
    assert (color_of_object1 x g == white);
    assert (color_of_object1 x g <> black);
    assert (color_of_object1 x g' <> black);
    assert (heap_remains_same_except_index_v_id x g g');
    assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
    assert (G.subset_vertices blacks blacks');
    
    
    colorHeader1_mem_lemma_gray x g;
    assert (~(exists y. (Seq.mem y blacks') /\ ~(Seq.mem y blacks)));
    assert (forall y. Seq.mem y blacks' <==> Seq.mem y blacks);
    assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g');
    ()
  )

 else
 (
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 

  assert (well_formed_heap2 g');
    
  objects2_equal_lemma 0UL g g';
    
  colorHeader1_color_Lemma x g 2UL;

  assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id x g g' /\
                                      color_of_object1 x g' == 2UL /\
                                      (color_of_object1 x g == white \/ color_of_object1 x g == gray \/ 
                                      color_of_object1 x g == black) /\
                                      wosize_of_object1 x g' == wosize_of_object1 x g /\
                                      tag_of_object1 x g' == tag_of_object1 x g /\
                                      is_valid_header x g /\ is_valid_header x g');
    
  get_allocated_block_addresses_lemma g g' x 2UL;
  assert (is_valid_header x g');
  
  let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
  let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
 
  assert (heap_remains_same_except_index_v_id x g g');
  assert (color_of_object1 x g == white);
  assert (color_of_object1 x g <> black);
  assert (color_of_object1 x g' <> black);
  assert (is_valid_header x g);
  assert (~(isGrayObject1 x g));
 
  assert (isGrayObject1 x g');
  G.snoc_unique_lemma x st;
  assert (G.is_vertex_set st');
  assert (forall y. is_valid_header y g /\ isBlackObject1 y g /\ x <> y ==> is_valid_header y g' /\
                                                                                      isBlackObject1 y g');
 
  assert (color_of_object1 x g == white);
  
  assert (forall y. Seq.mem y blacks ==> Seq.mem y blacks');
  assert (G.subset_vertices blacks blacks');
  
  colorHeader1_mem_lemma_gray x g;
  assert (~(exists y. (Seq.mem y blacks') /\ ~(Seq.mem y blacks)));
  assert (forall y. Seq.mem y blacks' <==> Seq.mem y blacks);
  assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g');
  ()
)

#restart-solver

#restart-solver

#restart-solver



#restart-solver 

let push_to_stack2_mem_lemma_black_nodes_for_visited_list  (g:heap{well_formed_heap2 g})
                                                           (st: seq Usize.t{G.is_vertex_set st /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                            (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                             Seq.mem x st)})
                                                           (x: hp_addr{~(Seq.mem x st) /\
                                                                      (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      is_valid_header x g /\ color_of_object1 x g == white /\
                                                                      (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (Usize.v x % Usize.v mword == 0)}) 
                   : Lemma 
                     (ensures (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==> 
                                       Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y (snd (push_to_stack2 g st x)))) = 
push_to_stack2_mem_lemma_black_nodes g st x;
let st1,g1 = push_to_stack2 g st x in
assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                               Seq.mem y (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
assert (forall x. Seq.mem x (get_black_block_addresses g (get_allocated_block_addresses g)) <==> Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g);
assert (forall x. Seq.mem x (get_black_block_addresses g1 (get_allocated_block_addresses g1)) <==> Seq.mem x (objects2 0UL g1) /\ isBlackObject1 x g1);
assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>  Seq.mem x (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>  Seq.mem x (objects2 0UL g1) /\ isBlackObject1 x g1);                                                  
assert (g1 == snd (push_to_stack2 g st x));                                                              
assert (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>  
                                         Seq.mem x (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 x g1);

assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  
                                         Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y (snd (push_to_stack2 g st x)));                             
()

let push_to_stack_mem_lemma_black_nodes_visited_list_lemma (g:heap{well_formed_heap2 g})
                                                           (st: seq Usize.t{G.is_vertex_set st /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                      Seq.mem x st)})
                                                           (x: hp_addr{~(Seq.mem x st) /\
                                                                      (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                       is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                       (Usize.v x % Usize.v mword == 0) /\
                                                                       is_valid_header x g /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                                          (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                         (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                         (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                         (G.is_vertex_set vl) /\
                                                                         (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>
                                                                         Seq.mem x vl)
                                                                       })
                                : Lemma
                                  (ensures (forall y. Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y (snd (push_to_stack2 g st x)) <==>  Seq.mem y vl)) = 
 assert ((forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl));
 push_to_stack2_mem_lemma_black_nodes_for_visited_list  g st x;
 assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                                       isBlackObject1 y (snd (push_to_stack2 g st x)));  
 assert (forall y. Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                                       isBlackObject1 y (snd (push_to_stack2 g st x)) <==> Seq.mem y vl);
                                                                        
 ()
                                                                        





let push_to_stack2_well_formed_allocated_blocks_lemma  (g:heap{well_formed_heap2 g})
                                                       (st: seq Usize.t{G.is_vertex_set st /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                      Seq.mem x st)})
                                                       (x: hp_addr{~(Seq.mem x st) /\
                                                                      (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                       is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                       (Usize.v x % Usize.v mword == 0) /\
                                                                       is_valid_header x g /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                                       (c:color{c == 2UL})
                                   : Lemma
                                     (requires well_formed_allocated_blocks g)
                                     (ensures (well_formed_allocated_blocks (snd (push_to_stack2 g st x)))) = 
  if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g c in 

    assert (well_formed_heap2 g');
    
    objects2_equal_lemma 0UL g g';
    
    assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id x g g' /\
                                      color_of_object1 x g' == 2UL /\
                                      (color_of_object1 x g == white \/ color_of_object1 x g == gray \/ 
                                      color_of_object1 x g == black) /\
                                      wosize_of_object1 x g' == wosize_of_object1 x g /\
                                      tag_of_object1 x g' == tag_of_object1 x g /\
                                      is_valid_header x g /\ is_valid_header x g');
    
    get_allocated_block_addresses_lemma g g' x c;
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
    colorHeader1_Lemma x g c; 

    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g;

    assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
    well_formed_allocated_blocks_lemma g x c g';
    

    assert (well_formed_allocated_blocks g');
    
    assert (Seq.mem x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');
   
    
    assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');

    assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');
    assert (heap_remains_same_except_index_v_id x g g');
    assert (well_formed_allocated_blocks (snd (push_to_stack2 g st x)));
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g c in 

  assert (well_formed_heap2 g');
    
  objects2_equal_lemma 0UL g g';
    
  assert ((objects2 0UL g ==  objects2 0UL g') /\
                                      Seq.length g == Seq.length g' /\
                                      heap_remains_same_except_index_v_id x g g' /\
                                      color_of_object1 x g' == 2UL /\
                                      (color_of_object1 x g == white \/ color_of_object1 x g == gray \/ 
                                      color_of_object1 x g == black) /\
                                      wosize_of_object1 x g' == wosize_of_object1 x g /\
                                      tag_of_object1 x g' == tag_of_object1 x g /\
                                      is_valid_header x g /\ is_valid_header x g');
    
   get_allocated_block_addresses_lemma g g' x c;

   assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
   colorHeader1_Lemma x g c;

   assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');

   fieldaddress_within_limits_lemma_x_all g;

   assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   well_formed_allocated_blocks_lemma g x c g';
    

   assert (well_formed_allocated_blocks g');

   assert (G.is_vertex_set st);
   assert (~(Seq.mem x st));
  
   G.snoc_unique_lemma x st;
   assert (G.is_vertex_set st');
   assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  

   assert (forall y. Seq.mem y st' ==> is_valid_header y g);
   assert (forall y. Seq.mem y st' ==> is_valid_header y g');
  
   assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
   assert (heap_remains_same_except_index_v_id x g g');
   assert (well_formed_allocated_blocks (snd (push_to_stack2 g st x)));
    ()
)

#restart-solver

#restart-solver

let push_to_stack_heap_and_push_to_graph_equality_lemma (g:heap{well_formed_heap2 g})
                                                        (st: seq Usize.t{G.is_vertex_set st /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                      Seq.mem x st)})
                                                       (x: hp_addr{~(Seq.mem x st) /\
                                                                      (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                       is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                       (Usize.v x % Usize.v mword == 0) /\
                                                                       is_valid_header x g /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                                       (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                         (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                         (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                         (G.is_vertex_set vl) /\
                                                                         (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>
                                                                         Seq.mem x vl)
                                                                       })
                                         : Lemma
                                          (requires (well_formed_allocated_blocks g) /\
                                                    (G.subset_vertices st (get_allocated_block_addresses g)) /\
                                                    (G.subset_vertices vl (get_allocated_block_addresses g)) /\
                                                    (~(Seq.mem x st) /\ ~(Seq.mem x vl)) /\
                                                    (Seq.mem x (get_allocated_block_addresses g)) /\
                                                    (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                    (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                                          (ensures (fst (push_to_stack2 g st x) == G.push_to_stack_graph (create_graph_from_heap g) vl st x)) = 
 let grph = create_graph_from_heap g in
if Seq.length st = 0 then
 (
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
   
    G.is_vertex_set_lemma2 stk';
    
    objects2_equal_lemma 0UL g g';

    assert (color_of_object1 x g == white);
    get_allocated_block_addresses_lemma g g' x 2UL;
    assert (Seq.length st == 0);
    G.push_to_stack_graph_lemma grph vl st x;
    assert (G.push_to_stack_graph grph vl st x == Seq.create 1 x);
    assert (stk' == Seq.create 1 x);
    assert (G.push_to_stack_graph grph vl st x == stk');
    assert (fst (push_to_stack2 g st x) == G.push_to_stack_graph (create_graph_from_heap g) vl st x);
    ()
 )
 else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');

  
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem x st));
  G.snoc_unique_lemma x st;
  assert (G.is_vertex_set st');
  assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  

  assert (forall y. Seq.mem y st' ==> is_valid_header y g);
  assert (forall y. Seq.mem y st' ==> is_valid_header y g');
  assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  assert (heap_remains_same_except_index_v_id x g g');
  assert (Seq.length st > 0);
  G.push_to_stack_graph_lemma1 grph vl st x;
  assert (G.push_to_stack_graph grph vl st x == snoc st x);
  ()
)
                                                                       
#restart-solver 

let push_to_stack_heap_and_push_to_graph_equality_lemma1  (g:heap{well_formed_heap2 g})
                                                          (st: seq Usize.t{G.is_vertex_set st /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                      Seq.mem x st)})
                                                          (x: hp_addr{~(Seq.mem x st) /\
                                                                      (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                       is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                       (Usize.v x % Usize.v mword == 0) /\
                                                                       is_valid_header x g /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                                         (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                         (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                         (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                         (G.is_vertex_set vl) /\
                                                                         (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>
                                                                         Seq.mem x vl)
                                                                       })
                                        : Lemma
                                          (requires (well_formed_allocated_blocks g) /\
                                                    
                                                    (~(Seq.mem x st) /\ ~(Seq.mem x vl)) /\
                                                    (Seq.mem x (get_allocated_block_addresses g)) /\
                                                    (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                    (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                   (ensures (fst (push_to_stack2 g st x) == G.push_to_stack_graph1 vl st x)) = 
  if Seq.length st = 0 then
 (
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
   
    G.is_vertex_set_lemma2 stk';
    
    objects2_equal_lemma 0UL g g';

    assert (color_of_object1 x g == white);
    get_allocated_block_addresses_lemma g g' x 2UL;
    assert (Seq.length st == 0);
    //G.push_to_stack_graph_lemma grph vl st x;
    assert (G.push_to_stack_graph1 vl st x == Seq.create 1 x);
    assert (stk' == Seq.create 1 x);
    assert (G.push_to_stack_graph1 vl st x == stk');
    ()
 )
 else
 ( 
   lemma_tail_snoc st x;
   lemma_mem_snoc st x; 
   let st' = snoc st x in
   let g' = colorHeader1 x g gray in 
   objects2_equal_lemma 0UL g g';
  
   assert (objects2 0UL g ==  objects2 0UL g');
   assert (well_formed_heap2 g');
   assert (G.is_vertex_set st);
   assert (~(Seq.mem x st));
   G.snoc_unique_lemma x st;
   assert (G.is_vertex_set st');
   assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  

   assert (forall y. Seq.mem y st' ==> is_valid_header y g);
   assert (forall y. Seq.mem y st' ==> is_valid_header y g');

   assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
   assert (heap_remains_same_except_index_v_id x g g');
   assert (Seq.length st > 0);
   //G.push_to_stack_graph_lemma1 grph vl st x;
   assert (G.push_to_stack_graph1 vl st x == snoc st x);
   ()
 )

let push_to_stack2_graph_lemma  (g:heap{well_formed_heap2 g})
                                (st: seq Usize.t{G.is_vertex_set st /\
                                                 (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                 (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                 (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==> Seq.mem x st)})                                             
                                (x: hp_addr{~(Seq.mem x st) /\
                                            (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                            is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                            (Usize.v x % Usize.v mword == 0) /\
                                            is_valid_header x g /\ color_of_object1 x g == white /\
                                            (Seq.mem x (get_allocated_block_addresses g))})
                                
                    : Lemma 
                     (requires (well_formed_allocated_blocks g /\
                                well_formed_allocated_blocks (colorHeader1 x g 2UL)))
                     (ensures (create_graph_from_heap g == create_graph_from_heap ((snd (push_to_stack2 g st x))))) = 
if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
    create_graph_from_heap_lemma_gray g x;
    assert (create_graph_from_heap g == create_graph_from_heap g');
    assert (Seq.mem x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');
    objects2_equal_lemma 0UL g g';
    
    assert (objects2 0UL g ==  objects2 0UL g');
                                           
    assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');

    assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');
    assert (heap_remains_same_except_index_v_id x g g');
    ()
)
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';

  create_graph_from_heap_lemma_gray g x;
  assert (create_graph_from_heap g == create_graph_from_heap g');
  assert (objects2 0UL g ==  objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem x st));
  G.snoc_unique_lemma x st;
  assert (G.is_vertex_set st');
  assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
   assert (forall y. Seq.mem y st' ==> is_valid_header y g);
  assert (forall y. Seq.mem y st' ==> is_valid_header y g');
  
  assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  assert (heap_remains_same_except_index_v_id x g g');
  ()
)                                         

#restart-solver
#push-options "--z3rlimit 500"

#restart-solver 

let valid_succ_color_lemma (g:heap{well_formed_heap2 g})
                           (succ:hp_addr{Usize.v succ >= 0 /\ Usize.v succ < heap_size /\
                                    is_valid_header succ g})
                  : Lemma
                    (requires True(*(color_of_block succ g == white \/
                               color_of_block succ g == gray \/
                               color_of_block succ g == black)*))
                    (ensures (color_of_object1 succ g == white ==> ~(isGrayObject1 succ g) /\
                                                                 ~(isBlackObject1 succ g))) = ()

#restart-solver 

let valid_succ_color_lemma1 (g:heap{well_formed_heap2 g})
                            (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                            (vl: seq Usize.t {vl = get_black_block_addresses g (get_allocated_block_addresses g)})
                            (succ:hp_addr{Usize.v succ >= 0 /\ Usize.v succ < heap_size /\
                                    is_valid_header succ g}) 
                  : Lemma
                    (requires ((color_of_object1 succ g == white \/
                               color_of_object1 succ g == gray \/
                               color_of_object1 succ g == black)))  
                    (ensures ~(color_of_object1 succ g == white) ==> Seq.mem succ st \/ Seq.mem succ vl) = ()


#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver

let fieldPush_spec_body   (g:heap{well_formed_heap2 g})
                          (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                         (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                          (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                          is_valid_header h_index g})
                                          
                         (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                         (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                    : Pure (stack_heap_pair)
                      (requires True)
                      (ensures fun st_hp -> well_formed_heap2 (snd st_hp) /\
                                         
                                         G.is_vertex_set (fst st_hp) /\
                                         
                                         (forall x. Seq.mem x (fst st_hp) ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\

                                         (forall x. Seq.mem x (fst st_hp) ==> Usize.v x % Usize.v mword == 0) /\
                                         
                                         (forall x. Seq.mem x (fst st_hp) ==> is_valid_header x (snd st_hp)) /\
                                         
                                         (forall x. Seq.mem x (objects2 0UL (snd st_hp)) /\
                                               isGrayObject1 x (snd st_hp) <==>
                                               Seq.mem x (fst st_hp)) /\
                                               
                                         (forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word (snd st_hp) x)) /\
                                               
                                         (objects2 0UL g ==
                                         objects2 0UL (snd st_hp)) /\ 
                                         
                                         (is_hp_addr (Usize.(h_index +^ (i *^ mword)))) (*/\
                                         (isPointer (Usize.(h_index +^ (i *^ mword))) g /\ 
                                          color_of_object1 (Usize.(h_index +^ (i *^ mword))) g == white ==> 
                                                  heap_remains_same_except_index_v_id (Usize.(h_index +^ (i *^ mword))) g (snd st_hp))*) /\
                                         (*(heap_remains_same_except_index_v_id (read_word g (Usize.(h_index +^ (i *^ mword))))
                                                g (snd st_hp)) /\*)
                                                
                                         (Seq.length g == Seq.length (snd st_hp)) /\
                                         
                                         (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\
                                         
                                         (get_allocated_block_addresses g ==
                                            get_allocated_block_addresses (snd st_hp))) = 
   assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);
       
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));

  if isPointer succ_index g  then
    (
      if color_of_object1 succ g = white  then
      (
       valid_succ_color_lemma g succ;
       assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
       let st', g' = push_to_stack2 g st succ in
       push_to_stack2_heap_state_lemma g st succ;
       push_to_stack2_field_size_lemma g st succ;
       assert (G.is_vertex_set st');
       assert (forall x. Seq.mem x (objects2 0UL g') /\
                                               isGrayObject1 x g' <==>
                                               Seq.mem x st');
       assert (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g');
         
       assert (well_formed_heap2 g');

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 succ g == white);
       push_to_stack2_lemma g st succ;

       assert ( (get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       assert (heap_remains_same_except_index_v_id succ g g');
       assert (isPointer succ_index g /\ color_of_object1 succ g == white ==> heap_remains_same_except_index_v_id succ g g');
       assert (is_valid_header h_index g');
       assert (is_valid_header succ g');
       assert (Usize.v wz <= Usize.v (getWosize (read_word g' h_index)));
       assert ((Seq.length g == Seq.length g'));
       assert (forall x. Seq.mem x st ==> Seq.mem x st');
       
       (st', g')
      )
      else
      (
         (st,g)
      )
    )
  else
   ( 
       (st,g)
   )
     
      
      

#restart-solver


#restart-solver


#restart-solver

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver

let fieldPush_spec_body_fields_lemma   (g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                         (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                         (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                         (G.is_vertex_set st) /\
                                                         (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                               Seq.mem x st)
                                                         })
                                        (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                         (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                         is_valid_header h_index g})
                                          
                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                    :Lemma
                     (requires (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8) /\
                                 
                               (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice (snd (fieldPush_spec_body g st h_index wz i)) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8)
                                )
                     (ensures  (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). 
                             getWosize (read_word g t) == getWosize (read_word (snd (fieldPush_spec_body g st h_index wz i)) t)) /\
                             
                             (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (fieldPush_spec_body g st h_index wz i)) y)) = 
                                                                                  
   assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
       
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
  let succ_index = Usize.add h_index (Usize.mul i mword) in
       
  assert (Usize.v succ_index < heap_size);
 
  max_wosize_times_mword_multiple_of_mword i;
  sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
  assert (Usize.v succ_index % Usize.v mword == 0);
  assert (is_hp_addr succ_index);
       
  let succ = read_word g succ_index in
  assert (succ == read_word g succ_index);
  assert (Seq.mem h_index (objects2 0UL g));

  if isPointer succ_index g  then
    (
      if color_of_object1 succ g = white  then
      (
       valid_succ_color_lemma g succ;
       assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
       let st', g' = push_to_stack2 g st succ in
       push_to_stack2_fields_allocated_blocks_lemma g st succ ;

       assert (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                          getWosize (read_word (snd (fieldPush_spec_body g st h_index wz i)) t));
       assert (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (fieldPush_spec_body g st h_index wz i)) y);
       ()
      )
      else
      (
         ()
      )
    )
  else
   ( 
       ()
   )
     
#reset-options "--z3rlimit 1000"

#push-options "--split_queries"

#restart-solver 

let fieldPush_spec_body_black_nodes_lemma (g:heap{well_formed_heap2 g})
                                           (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (G.is_vertex_set st) /\
                                                             (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)
                                                            })
                         
                                           (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                           (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                           is_valid_header h_index g})
                                           
                                           (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                           (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (ensures G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                   (get_black_block_addresses (snd (fieldPush_spec_body g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body g st h_index wz i))))) = 
assert (well_formed_heap2 g);
 assert (is_valid_header h_index g);  
 assert (Seq.mem h_index (objects2 0UL g));
 assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
 assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);   
 let succ_index = Usize.add h_index (Usize.mul i mword) in
       
 assert (Usize.v succ_index < heap_size);
 
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
       
 let succ = read_word g succ_index in
 assert (succ == read_word g succ_index);
 assert (Seq.mem h_index (objects2 0UL g));
 if isPointer succ_index g then
 (
   if color_of_object1 succ g = white then
   (
       valid_succ_color_lemma g succ;
       assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
       let st', g' = push_to_stack2 g st succ in
       push_to_stack2_heap_state_lemma g st succ;
       push_to_stack2_field_size_lemma g st succ;
       push_to_stack2_lemma_black_nodes1 g st succ;
       assert (G.is_vertex_set st');
       assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st succ)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st succ)))));
       
       assert (forall x. Seq.mem x (objects2 0UL g') /\
                                               isGrayObject1 x g' <==>
                                               Seq.mem x st');
       assert (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g');
         
       assert (well_formed_heap2 g');

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 succ g == white);
       push_to_stack2_lemma g st succ;

       assert ( (get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       assert (heap_remains_same_except_index_v_id succ g g');
       assert (is_valid_header h_index g');
       assert (is_valid_header succ g');
       assert (Usize.v wz <= Usize.v (getWosize (read_word g' h_index)));
       assert ((Seq.length g == Seq.length g'));
       assert (forall x. Seq.mem x st ==> Seq.mem x st');
       
       ()
    )
   else 
    (
       ()
    )
 )
 else
 (
   ()
 )
 

#restart-solver 

let fieldPush_spec_body_black_nodes_mem_lemma (g:heap{well_formed_heap2 g})
                                              (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (G.is_vertex_set st) /\
                                                             (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)
                                                            })
                         
                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                             (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                             is_valid_header h_index g})
                                           
                                             (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                             (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                          Seq.mem y (get_black_block_addresses (snd (fieldPush_spec_body g st h_index wz i)) 
                                                              (get_allocated_block_addresses (snd (fieldPush_spec_body g st h_index wz i)))))) =
 assert (well_formed_heap2 g);
 assert (is_valid_header h_index g);  
 assert (Seq.mem h_index (objects2 0UL g));
 assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
 assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);   
 let succ_index = Usize.add h_index (Usize.mul i mword) in
       
 assert (Usize.v succ_index < heap_size);
 
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
       
 let succ = read_word g succ_index in
 assert (succ == read_word g succ_index);
 assert (Seq.mem h_index (objects2 0UL g));

 if isPointer succ_index g then
  (
  
    if color_of_object1 succ g = white then
    (
       valid_succ_color_lemma g succ;
       assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
       let st', g' = push_to_stack2 g st succ in
       push_to_stack2_heap_state_lemma g st succ;
       push_to_stack2_field_size_lemma g st succ;
       push_to_stack2_lemma_black_nodes1 g st succ;
       assert (G.is_vertex_set st');
       assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st succ)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st succ)))));
       
       assert (forall x. Seq.mem x (objects2 0UL g') /\
                                               isGrayObject1 x g' <==>
                                               Seq.mem x st');
       assert (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g');
         
       assert (well_formed_heap2 g');

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 succ g == white);
       push_to_stack2_lemma g st succ;

       push_to_stack2_mem_lemma_black_nodes g st succ;

       assert ( (get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       assert (heap_remains_same_except_index_v_id succ g g');
       assert (is_valid_header h_index g');
       assert (is_valid_header succ g');
       assert (Usize.v wz <= Usize.v (getWosize (read_word g' h_index)));
       assert ((Seq.length g == Seq.length g'));
       assert (forall x. Seq.mem x st ==> Seq.mem x st');
       
       ()
    )
   else 
    (
       ()
    )
  )
 else
  (
    ()
  )

#restart-solver

#restart-solver

#restart-solver

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver

let fieldPush_spec_body_well_formed_allocated_blocks_lemma  (g:heap{well_formed_heap2 g})
                                                            (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (G.is_vertex_set st) /\
                                                             (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)
                                                            })
                         
                                                            (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                            is_valid_header h_index g})
                                           
                                                            (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                            (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (requires ((Seq.mem h_index (get_allocated_block_addresses g)) /\
                                     (well_formed_allocated_blocks g)))
                                     
                          (ensures (well_formed_allocated_blocks (snd (fieldPush_spec_body g st h_index wz i)))) =
 assert (well_formed_heap2 g);
 assert (is_valid_header h_index g);  
 assert (Seq.mem h_index (objects2 0UL g));
 assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
 assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);   
 let succ_index = Usize.add h_index (Usize.mul i mword) in
       
 assert (Usize.v succ_index < heap_size);
 
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
 lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
 assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
 assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
 assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);     
 
 let succ = read_word g succ_index in
 assert (succ == read_word g succ_index);
 assert (Seq.mem h_index (objects2 0UL g));
 if isPointer succ_index g then
 (
   if color_of_object1 succ g = white then
   (
      valid_succ_color_lemma g succ;
      assert (color_of_object1 succ g == white);
      assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
      assert (~(Seq.mem succ st));
       
      assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                 Seq.mem x st);
      let st', g' = push_to_stack2 g st succ in

      push_to_stack2_well_formed_allocated_blocks_lemma g st succ 2UL;

      assert (well_formed_allocated_blocks g');
       
       push_to_stack2_heap_state_lemma g st succ;
       push_to_stack2_field_size_lemma g st succ;
       
       assert (G.is_vertex_set st');
       
       assert (forall x. Seq.mem x (objects2 0UL g') /\
                                               isGrayObject1 x g' <==>
                                               Seq.mem x st');
       assert (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g');
         
       assert (well_formed_heap2 g');

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 succ g == white);
       push_to_stack2_lemma g st succ;

       push_to_stack2_mem_lemma_black_nodes g st succ;

       assert ( (get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       assert (heap_remains_same_except_index_v_id succ g g');
       assert (is_valid_header h_index g');
       assert (is_valid_header succ g');
       assert (Usize.v wz <= Usize.v (getWosize (read_word g' h_index)));
       assert ((Seq.length g == Seq.length g'));
       assert (forall x. Seq.mem x st ==> Seq.mem x st');
       ()
   )
 else
  ( 
    assert (well_formed_allocated_blocks g);
    assert (well_formed_allocated_blocks (snd (fieldPush_spec_body g st h_index wz i)));
    ()
  )
 )
else
 (
   assert (well_formed_allocated_blocks g);
   assert (well_formed_allocated_blocks (snd (fieldPush_spec_body g st h_index wz i)));
   ()
 )

#reset-options "--z3rlimit 1000"

let fieldPush_spec_body_valid_header_visited_set_lemma  (g:heap{well_formed_heap2 g})
                                                        (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                 (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                 (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                 (G.is_vertex_set st) /\
                                                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==> Seq.mem x st)
                                                                                })
                                                         (h_index:hp_addr {Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                 is_valid_header h_index g})
                                          
                                                         (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                         (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                         (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                 (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                 (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                 (G.is_vertex_set vl) /\
                                                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                })
                            : Lemma
                              (ensures ((forall x. Seq.mem x vl ==> is_valid_header x (snd (fieldPush_spec_body g st h_index wz i))))) = 
 assert (well_formed_heap2 g);
 assert (is_valid_header h_index g);  
 assert (Seq.mem h_index (objects2 0UL g));
 assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
 assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);   
 let succ_index = Usize.add h_index (Usize.mul i mword) in
       
 assert (Usize.v succ_index < heap_size);
 
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
       
 let succ = read_word g succ_index in
 assert (succ == read_word g succ_index);
 assert (Seq.mem h_index (objects2 0UL g));
                            
 if isPointer succ_index g && color_of_object1 succ g = white then
   (
       valid_succ_color_lemma g succ;
       assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
       let st', g' = push_to_stack2 g st succ in
       push_to_stack2_heap_state_lemma g st succ;
       push_to_stack2_field_size_lemma g st succ;
       
       assert (G.is_vertex_set st');
       assert (forall x. Seq.mem x (objects2 0UL g') /\
                                               isGrayObject1 x g' <==>
                                               Seq.mem x st');
       assert (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g');
         
       assert (well_formed_heap2 g');

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 succ g == white);
       push_to_stack2_lemma g st succ;

       assert ( (get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       assert (heap_remains_same_except_index_v_id succ g g');
       assert (is_valid_header h_index g');
       assert (is_valid_header succ g');
       assert (Usize.v wz <= Usize.v (getWosize (read_word g' h_index)));
       assert ((Seq.length g == Seq.length g'));
       assert (forall x. Seq.mem x st ==> Seq.mem x st');
       push_to_stack2_visited_list_valid_header_lemma g st succ vl;
       assert (forall x. Seq.mem x vl ==> is_valid_header x (snd (fieldPush_spec_body g st h_index wz i)));
       ()
    )
   else 
    (
       
      assert (forall x. Seq.mem x vl ==> is_valid_header x (snd (fieldPush_spec_body g st h_index wz i)));  
      ()
          
    )

let fieldPush_spec_body_black_nodes_visited_set_lemma  (g:heap{well_formed_heap2 g})
                                                        (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                 (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                 (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                 (G.is_vertex_set st) /\
                                                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==> Seq.mem x st)
                                                                                })
                                                         (h_index:hp_addr {Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                 is_valid_header h_index g})
                                          
                                                         (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                         (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                         (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                 (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                 (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                 (G.is_vertex_set vl) /\
                                                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                })
                            : Lemma
                              (ensures (forall y. Seq.mem y (objects2 0UL (snd (fieldPush_spec_body g st h_index wz i))) /\ 
                                                  isBlackObject1 y (snd (fieldPush_spec_body g st h_index wz i)) <==>  
                                                                                           Seq.mem y vl)) = 
 assert (well_formed_heap2 g);
 assert (is_valid_header h_index g);  
 assert (Seq.mem h_index (objects2 0UL g));
 assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
 assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);   
 let succ_index = Usize.add h_index (Usize.mul i mword) in
       
 assert (Usize.v succ_index < heap_size);
 
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
       
 let succ = read_word g succ_index in
 assert (succ == read_word g succ_index);
 assert (Seq.mem h_index (objects2 0UL g));
                             

 if isPointer succ_index g && color_of_object1 succ g = white then
   (
       valid_succ_color_lemma g succ;
       assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
       let st', g' = push_to_stack2 g st succ in
       push_to_stack2_heap_state_lemma g st succ;
       push_to_stack2_field_size_lemma g st succ;
       
       assert (G.is_vertex_set st');
       assert (forall x. Seq.mem x (objects2 0UL g') /\
                                               isGrayObject1 x g' <==>
                                               Seq.mem x st');
       assert (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g');
         
       assert (well_formed_heap2 g');

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 succ g == white);
       push_to_stack2_lemma g st succ;

       assert ( (get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       assert (heap_remains_same_except_index_v_id succ g g');
       assert (is_valid_header h_index g');
       assert (is_valid_header succ g');
       assert (Usize.v wz <= Usize.v (getWosize (read_word g' h_index)));
       assert ((Seq.length g == Seq.length g'));
       assert (forall x. Seq.mem x st ==> Seq.mem x st');
       push_to_stack_mem_lemma_black_nodes_visited_list_lemma g st succ vl;
       assert (forall y. Seq.mem y (objects2 0UL (snd (push_to_stack2 g st succ))) /\ isBlackObject1 y (snd (push_to_stack2 g st succ)) <==>  Seq.mem y vl);
       assert (forall y. Seq.mem y (objects2 0UL (snd (fieldPush_spec_body g st h_index wz i))) /\ 
                                                  isBlackObject1 y (snd (fieldPush_spec_body g st h_index wz i)) <==>  
                                                                                           Seq.mem y vl);
       ()
    )
   else 
    (
       
      assert (forall x. Seq.mem x vl ==> is_valid_header x (snd (fieldPush_spec_body g st h_index wz i)));  
      ()
          
    )

#restart-solver 

#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver

#reset-options "--z3rlimit 500"

#restart-solver 

let fieldPush_spec_body_graph_lemma (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (G.is_vertex_set st) /\
                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==> Seq.mem x st)
                                                      })
                                    (h_index:hp_addr {Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                      (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                      is_valid_header h_index g})
                                          
                                    (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (requires ((Seq.mem h_index (get_allocated_block_addresses g)) /\
                                    
                                      (*/\
                                     (all_successors_are_mem_allocated_blocks g h_index (getWosize (Seq.index g (Usize.v h_index))) i)*) 
                                     (well_formed_allocated_blocks g) /\
                                     (well_formed_allocated_blocks (snd (fieldPush_spec_body g st h_index wz i)))))
                                     
                          (ensures (create_graph_from_heap g == create_graph_from_heap (snd (fieldPush_spec_body g st h_index wz i)))) = 

assert (well_formed_heap2 g);
 assert (is_valid_header h_index g);  
 assert (Seq.mem h_index (objects2 0UL g));
 assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
 assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);   
 let succ_index = Usize.add h_index (Usize.mul i mword) in
       
 assert (Usize.v succ_index < heap_size);
 
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
       
 let succ = read_word g succ_index in
 assert (succ == read_word g succ_index);
 assert (Seq.mem h_index (objects2 0UL g));

  if isPointer succ_index g && color_of_object1 succ g = white then
   (
       valid_succ_color_lemma g succ;
       assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
       let st', g' = push_to_stack2 g st succ in
       push_to_stack2_heap_state_lemma g st succ;
       push_to_stack2_field_size_lemma g st succ;
       
       assert (G.is_vertex_set st');
       assert (forall x. Seq.mem x (objects2 0UL g') /\
                                               isGrayObject1 x g' <==>
                                               Seq.mem x st');
       assert (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g');
         
       assert (well_formed_heap2 g');

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 succ g == white);
       push_to_stack2_lemma g st succ;

       assert ( (get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       assert (heap_remains_same_except_index_v_id succ g g');
       assert (is_valid_header h_index g');
       assert (is_valid_header succ g');
       assert (Usize.v wz <= Usize.v (getWosize (read_word g' h_index)));
       assert ((Seq.length g == Seq.length g'));
       assert (forall x. Seq.mem x st ==> Seq.mem x st');
       push_to_stack2_well_formed_allocated_blocks_lemma g st succ 2UL;
       push_to_stack2_graph_lemma g st succ;
        
       ()
    )
   else 
    (
       
         
      ()
          
    )

let rec fieldPush_spec1  (g:heap{well_formed_heap2 g})
                         (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (G.is_vertex_set st) /\
                                                             (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)
                                                            })
                         
                         (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                          (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                          is_valid_header h_index g})
                                           
                          (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                          (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                      
                    
         : Pure (stack_heap_pair)
         (requires True)
         (ensures fun st_hp -> (G.is_vertex_set (fst st_hp)) /\
         
                            (Seq.length g == Seq.length (snd st_hp)) /\
                            
                            (well_formed_heap2 (snd st_hp)) /\
                            
                            (forall x. Seq.mem x (fst st_hp) ==> Usize.v x >= 0 /\ Usize.v x < heap_size)/\

                            (forall x. Seq.mem x (fst st_hp) ==> Usize.v x % Usize.v mword == 0) /\
                            
                            (forall x. Seq.mem x (fst st_hp) ==> is_valid_header x (snd st_hp)) /\
                            
                            (forall x. Seq.mem x (objects2 0UL (snd st_hp)) /\ isGrayObject1 x (snd st_hp) <==>
                                                   Seq.mem x (fst st_hp)) /\
                                                   
                            (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\ (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                            
                            get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))
                              
         (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       st_hp
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body g st h_index wz i in
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header x g'));

       assert ((forall x. Seq.mem x (objects2 0UL g') /\
                               isGrayObject1 x g' <==>
                                         Seq.mem x st'));
       fieldPush_spec1 g' st' h_index wz i'
    )

#restart-solver



#reset-options "--z3rlimit 1000"

#push-options "--split_queries"

#restart-solver 

let rec fieldPush_spec1_fields_lemma1  (g:heap{well_formed_heap2 g})
                                      (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (G.is_vertex_set st) /\
                                                             (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)
                                                            })
                         
                                     (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                          (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                          is_valid_header h_index g})
                                           
                                    (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                      
                    
         :Lemma
          (ensures (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                                   getWosize (read_word (snd (fieldPush_spec1 g st h_index wz i)) t)) /\
                   (forall t y. Seq.mem t (objects2 0UL g) /\ 
                                   Usize.v y >= Usize.v t + Usize.v mword /\
                                   Usize.v y <= Usize.v t + (Usize.v (getWosize (read_word g t)) * Usize.v mword) ==>
                                                             read_word g y == read_word (snd (fieldPush_spec1 g st h_index wz i)) y))
          (decreases ((Usize.v wz + 1) - Usize.v i)) =
 if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body g st h_index wz i in
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header x g'));

       assert ((forall x. Seq.mem x (objects2 0UL g') /\
                               isGrayObject1 x g' <==>
                                         Seq.mem x st'));
       assert ((forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8));

       assert ((forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice g' (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8));

       fieldPush_spec_body_fields_lemma g st h_index wz i;
       let st_hp = fieldPush_spec1 g' st' h_index wz i' in
       
       assert ((forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}).
                                 length (slice (snd st_hp) (Usize.v t) ((Usize.v t) + (Usize.v mword))) = 8));
       fieldPush_spec1_fields_lemma1 g' st' h_index wz i';
       
       ()
    )
    
let fieldPush_fieldPush_spec_body_lemma (g:heap{well_formed_heap2 g})
                                        (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (G.is_vertex_set st) /\
                                                             (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)
                                                            })
                         
                                         (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                          (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                           is_valid_header h_index g})
                                           
                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                        (i':Usize.t{Usize.v i' == Usize.v i + 1})
                       : Lemma
                         (requires True)
                         (ensures (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i')) = ()

let fieldPush_fieldPush_spec_body_lemma1 (g:heap{well_formed_heap2 g})
                                         (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (G.is_vertex_set st) /\
                                                             (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)
                                                            })
                         
                                         (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                         (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                         is_valid_header h_index g})
                                           
                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                                        (i:Usize.t)
                                        
                       : Lemma
                         (requires (Usize.v i == Usize.v wz + 1))
                         (ensures g == snd (fieldPush_spec1 g st h_index wz i) /\
                                  st == fst (fieldPush_spec1 g st h_index wz i)) = ()


#restart-solver

let rec fieldPush_spec1_black_nodes_lemma1   (g:heap{well_formed_heap2 g})
                                             (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (G.is_vertex_set st) /\
                                                             (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)
                                                            })
                         
                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                              is_valid_header h_index g})
                                           
                                            (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                            (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses  (snd (fieldPush_spec1 g st h_index wz i))
                                                                         (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i))))))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 
  if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body g st h_index wz i in

       fieldPush_spec_body_black_nodes_mem_lemma g st h_index wz i;
       fieldPush_spec_body_black_nodes_lemma g st h_index wz i;
       
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header x g'));

       assert ((forall x. Seq.mem x (objects2 0UL g') /\
                               isGrayObject1 x g' <==>
                                         Seq.mem x st'));

      
       assert (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0);
                                                            
                                                             
      fieldPush_spec1_black_nodes_lemma1 g' st' h_index wz i'
    )


#restart-solver 

#restart-solver

let rec fieldPush_spec1_black_nodes_lemma  (g:heap{well_formed_heap2 g})
                                           (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (G.is_vertex_set st) /\
                                                             (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                   Seq.mem x st)
                                                            })
                         
                                            (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                              is_valid_header h_index g})
                                           
                                            (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                            (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (ensures (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (fieldPush_spec1 g st h_index wz i)) 
                                                                               (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i))))))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body g st h_index wz i in

       //fieldPush_spec_body_black_nodes_mem_lemma g st h_index wz i;
       fieldPush_spec_body_black_nodes_lemma g st h_index wz i;

       assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                 (get_black_block_addresses g' (get_allocated_block_addresses g')));
       
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header x g'));

       assert ((forall x. Seq.mem x (objects2 0UL g') /\
                               isGrayObject1 x g' <==>
                                         Seq.mem x st'));

      
       assert (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0);
       assert (Usize.v i' >= 1);   
       assert (Usize.v i' <= Usize.v wz + 1);
       let st'', g'' = fieldPush_spec1 g' st' h_index wz i' in                                                      
       fieldPush_spec1_black_nodes_lemma g' st' h_index wz i';
       assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                 (get_black_block_addresses g'' (get_allocated_block_addresses g'')));
       ()
    
    )

#restart-solver 

let rec fieldPush_spec1_well_formed_allocated_blocks_lemma  (g:heap{well_formed_heap2 g})
                                                            (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                              (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                              (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                              (G.is_vertex_set st) /\
                                                                              (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                            })
                         
                                                            (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                             is_valid_header h_index g})
                                           
                                            (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                            (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                       :  Lemma
                          (requires ((Seq.mem h_index (get_allocated_block_addresses g)) /\
                                     (well_formed_allocated_blocks g)))
                                    
                          (ensures (well_formed_allocated_blocks (snd (fieldPush_spec1 g st h_index wz i))))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) =
if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body g st h_index wz i in

       fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
       
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header x g'));

       assert ((forall x. Seq.mem x (objects2 0UL g') /\
                               isGrayObject1 x g' <==>
                                         Seq.mem x st'));

       let st'', g'' = fieldPush_spec1 g' st' h_index wz i' in
       assert (well_formed_allocated_blocks g');
       assert (get_allocated_block_addresses g' == get_allocated_block_addresses g);
       assert (get_allocated_block_addresses g'' == get_allocated_block_addresses g');
       fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
       ()
    )

#restart-solver 

#restart-solver 

let rec fieldPush_spec1_graph_lemma (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (G.is_vertex_set st) /\
                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                      })
                         
                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                    is_valid_header h_index g})
                                           
                                    (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (requires ((Seq.mem h_index (get_allocated_block_addresses g)) /\
                                     (well_formed_allocated_blocks g) /\
                                     (well_formed_allocated_blocks (snd (fieldPush_spec1 g st h_index wz i)))))
                          
                          (ensures (create_graph_from_heap g == create_graph_from_heap (snd (fieldPush_spec1 g st h_index wz i)))) 
                          (decreases ((Usize.v wz + 1) - Usize.v i)) =  

if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body g st h_index wz i in
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header x g'));

       assert ((forall x. Seq.mem x (objects2 0UL g') /\
                               isGrayObject1 x g' <==>
                                         Seq.mem x st'));
        fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
        fieldPush_spec_body_graph_lemma g st h_index wz i;
        
        fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
        
        fieldPush_spec1_graph_lemma g' st' h_index wz i'
    )
                          

#restart-solver 


//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

let arithmetic_lemma (i:Usize.t)
                     (wz:wosize)
            : Lemma
              (requires (Usize.v i < Usize.v wz + 1))
              (ensures (Usize.v i <= Usize.v wz)) = 
 assert (Usize.v i < Usize.v wz + 1);
 assert (Usize.v i <= Usize.v wz);
 ()

#restart-solver 

let arithmetic_lemma1 (i:Usize.t)
                     (wz:wosize)
            : Lemma
              (requires (Usize.v i <= Usize.v wz))
              (ensures (Usize.v i - 1 < Usize.v wz)) = 
 assert (Usize.v i <= Usize.v wz);
 assert (Usize.v i - 1 < Usize.v wz);
 ()


#restart-solver


let rec graph_successors_create_from_an_index (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))})
                                              (f: seq Usize.t{(f == G.successors (create_graph_from_heap g) h_index) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                              (i:Usize.t {Usize.v i <= Seq.length f}) 
                            
                            : Tot (s_list': seq Usize.t{s_list' == Seq.slice f (Usize.v i) (Seq.length f)})
                              (decreases (Seq.length f - Usize.v i))= 
                              
 if Usize.v i = Seq.length f then
 (
   Seq.empty #Usize.t
 )
 else
 (
   let succ = Seq.index f (Usize.v i) in
   let i' = Usize.add i 1UL in
   let rest_of_list = graph_successors_create_from_an_index g h_index f i' in
   assert (rest_of_list == Seq.slice f (Usize.v i') (Seq.length f));
   lemma_tl  succ rest_of_list;
   let s_list' = Seq.cons succ rest_of_list in
   assert (s_list' == Seq.slice f (Usize.v i) (Seq.length f));
   assert (Seq.head s_list' == succ);
   assert (Seq.head s_list' == Seq.index f (Usize.v i));
   s_list'
 )

let graph_successors_create_from_an_index_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\

                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))})
                                                    (f: seq Usize.t{(f == G.successors (create_graph_from_heap g) h_index) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                    (i:Usize.t {Usize.v i < Seq.length f}) 
                                  : Lemma
                                    (ensures (Seq.head (graph_successors_create_from_an_index g h_index f i) == Seq.index f (Usize.v i))) = ()
#restart-solver 

let graph_successors_create_from_an_index_lemma1 (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))})
                                                    (f: seq Usize.t{(f == G.successors (create_graph_from_heap g) h_index) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                    (i:Usize.t {Usize.v i < Seq.length f}) 
                                                    (i': Usize.t {Usize.v i' == Usize.v i + 1})
                                  : Lemma
                                    (ensures (Seq.tail (graph_successors_create_from_an_index g h_index f i) == (graph_successors_create_from_an_index g h_index f i'))) = ()
                                    
let create_successors_list_for_h_index_from_i_index_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                                                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                                    (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                   : Lemma
                                     (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                     (ensures (isPointer(Usize.add h_index (Usize.mul i mword)) g) ==> Seq.head (create_successors_list_for_h_index g h_index wz i) ==
                                                                                                          (read_word g (Usize.add h_index (Usize.mul i mword)))) = ()

#restart-solver 

let create_successors_list_for_h_index_from_i_index_lemma_tail_helper (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                                                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                                    (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                   
                                    : Lemma
                                      (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\ (isPointer(Usize.add h_index (Usize.mul i mword)) g))
                                      (ensures (create_successors_list_for_h_index g h_index wz i <> Seq.empty) /\ 
                                                 Seq.length (create_successors_list_for_h_index g h_index wz i) > 0) = ()

#restart-solver 

#restart-solver

let create_successors_list_for_h_index_from_i_index_lemma_tail (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                                                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                                    (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                    (i':Usize.t{Usize.v i' == Usize.v i + 1}) 
                                    : Lemma
                                      (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\ (isPointer(Usize.add h_index (Usize.mul i mword)) g) /\
                                                 Seq.length (create_successors_list_for_h_index g h_index wz i) > 0)
                                      (ensures Seq.tail (create_successors_list_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i') = 
 
 if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       ()
 
    )
 else
 (
   
      assert (is_valid_header h_index g);  
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      
       if isPointer succ_index g  then
      (
        assert (succ == read_word g succ_index);
        assert (is_valid_header h_index g);
        assert (Seq.mem h_index (objects2 0UL g));
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        
        test_allocs g h_index wz;
        assert (Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g));
        assert (Seq.mem succ (get_allocated_block_addresses g));
        assert (Seq.mem succ (objects2 0UL g));
        assert (is_valid_header succ g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        
        let s_list' = create_successors_list_for_h_index g h_index wz i' in
        

        lemma_tl succ s_list'; 
        
        let s_list = Seq.cons succ s_list' in 
        
        assert (Seq.head s_list == succ);

        assert (Seq.tail s_list == s_list');

        assert (Seq.tail (create_successors_list_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i');
      
        ()
      )
      else
      (
        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        let s_list = create_successors_list_for_h_index g h_index wz i' in
        assert (Seq.tail (create_successors_list_for_h_index g h_index wz i) == create_successors_list_for_h_index g h_index wz i');
      
        ()
      )
 )
                                                  



let graph_successors_create_from_index_0_equals_graph_successors (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))})
                                        : Lemma
                                          (requires (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v (getWosize (read_word g h_index))))
                                          (ensures (G.successors (create_graph_from_heap g) h_index == 
                                                      graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) 0UL)) = 
  
  let s_list' =  graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) 0UL in
  assert (s_list' == Seq.slice (G.successors (create_graph_from_heap g) h_index) 0 (Seq.length (G.successors (create_graph_from_heap g) h_index)));
  assert (G.successors (create_graph_from_heap g) h_index == Seq.slice (G.successors (create_graph_from_heap g) h_index) 0 (Seq.length (G.successors (create_graph_from_heap g) h_index)));
  ()
                                          
#restart-solver

let graph_successors_from_0_and_heap_field_pointers_from_1_are_equal (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                                     (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))})
                               
                                : Lemma
                                  (requires (is_fields_within_limit1 h_index (getWosize (read_word g h_index)) /\
                                                                       is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g /\
                                                         (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                             (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v (getWosize (read_word g h_index)))))
                                  (ensures graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) = 
 
 graph_successors_create_from_index_0_equals_graph_successors g h_index;
 graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
 ()


#restart-solver 

let create_successors_list_for_h_index_recursing_property_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                                                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                                    (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                                    (i':Usize.t{Usize.v i' == Usize.v i + 1})
                                       : Lemma
                                         (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                         (ensures ~(isPointer(Usize.add h_index (Usize.mul i mword)) g) ==> create_successors_list_for_h_index g h_index wz i == 
                                                                                create_successors_list_for_h_index g h_index wz i') = ()
 
let create_successors_list_for_h_index_recursing_property_lemma1 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                                                 (i':Usize.t{Usize.v i' == Usize.v i + 1})
                                       : Lemma
                                         (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                         (ensures (isPointer(Usize.add h_index (Usize.mul i mword)) g) ==> create_successors_list_for_h_index g h_index wz i == 
                                                   Seq.cons  (read_word g (Usize.add h_index (Usize.mul i mword))) (create_successors_list_for_h_index g h_index wz i')) = ()
                    
let create_successors_list_for_h_index_recursing_property_lemma2 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i == Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                        : Lemma
                                          (ensures create_successors_list_for_h_index g h_index wz i == Seq.empty) = ()



#restart-solver

let create_successors_list_for_h_index_recursing_property_lemma3 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                 (i':Usize.t{Usize.v i' == Usize.v i + 1})
                                        : Lemma
                                          (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                          (ensures (create_successors_list_for_h_index g h_index wz i == Seq.empty) ==> 
                                                      create_successors_list_for_h_index g h_index wz i' == Seq.empty) = ()


let create_successors_list_for_h_index_recursing_property_lemma4 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                                 (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                 (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                
                                        : Lemma
                                          (requires (is_hp_addr (Usize.add h_index (Usize.mul i mword))))
                                          (ensures (create_successors_list_for_h_index g h_index wz i == Seq.empty) ==> 
                                                       ~(isPointer(Usize.add h_index (Usize.mul i mword)) g)) = ()


let create_successors_list_for_h_index_i_equals_wz_plus_one_implies_succ_list_from_j_is_empty (g:heap{well_formed_heap2 g})
                                                                                              (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                                   (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                                   (G.is_vertex_set st) /\
                                                                                                   (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                                          Seq.mem x st)
                                                                                                     })
                         
                                                                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                               is_valid_header h_index g})
                                           
                                                                                             (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                             (i:Usize.t{Usize.v i == Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                             (j:Usize.t)
                                          : Lemma
                                            (requires (well_formed_allocated_blocks g) /\
                                          
                                                      (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                            
                                                     (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                                                     (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
                                                     (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0) /\
                                                     (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v wz) /\
                                                     
                                                     (Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) h_index)) /\
                                                     
                                                      
                                                     (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) ==
                                                     (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i))
                                            (ensures Usize.v j == Seq.length (G.successors (create_graph_from_heap g) h_index)) = 
create_successors_list_for_h_index_recursing_property_lemma2 g h_index wz i;
assert (create_successors_list_for_h_index g h_index wz i == Seq.empty);
assert ((graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) == Seq.empty);
assert (Usize.v j == Seq.length (G.successors (create_graph_from_heap g) h_index));
()

#restart-solver 

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j (g:heap{well_formed_heap2 g})
                                                                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                               is_valid_header h_index g})
                                           
                                                                                             (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                             (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                             (j:Usize.t)
                         
                                                                                           
                                          : Lemma
                                            (requires (well_formed_allocated_blocks g) /\
                                          
                                                      (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                            
                                                     (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                                                     (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
                                                     (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0) /\
                                                     (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v wz) /\
                                                     
                                                     (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) h_index)) /\
                                                     
                                                      
                                                     (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) ==
                                                     (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i))
                                            (ensures (let s_heap_i = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) in
                                                      let s_graph_j =  (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) in
                                                      let hd = Seq.head s_heap_i in
                                                      let hd1 = Seq.head s_graph_j in
                                                      let tl = Seq.tail s_heap_i in
                                                      let tl1 = Seq.tail s_graph_j in
                                                      (hd == hd1) /\ (tl == tl1))) = 
  let s_heap_i = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) in
  let s_graph_j =  (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) in
  assert (s_heap_i == s_graph_j);
  assert (Usize.v i < Usize.v wz + 1);
  assert (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) h_index));
  let hd = Seq.head s_heap_i in
  let hd1 = Seq.head s_graph_j in
  //assert (Seq.index s_heap_i (Usize.v i) == Seq.index s_graph_j (Usize.v j));
  let tl = Seq.tail s_heap_i in
  let tl1 = Seq.tail s_graph_j in
  assert (hd == hd1);
  assert (tl == tl1);
  
  ()

#restart-solver 

#restart-solver

let field_ptr_construct (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                           (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                           (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                           (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1}) =
  (Usize.add h_index (Usize.mul i mword))


let seq_empty_lemma1 (#a:Type)
            : Lemma
              (ensures (Seq.length (Seq.empty #a) == 0)) = ()

let cons_length_lemma3 (#a:Type)
                       (s:seq a)
                       (s_cons:a)
                 : Lemma
                   (ensures (Seq.length (Seq.cons s_cons s) > 0))=
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 assert (Seq.length s' == Seq.length s + 1) ;
 assert (Seq.length s' > 0);
 ()

(*(is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
  (isPointer(Usize.add h_index (Usize.mul i mword)) g)*)
                                                     
#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver


#restart-solver

#push-options "--split_queries"

#restart-solver

#restart-solver

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j1 (g:heap{well_formed_heap2 g})
                                                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                               is_valid_header h_index g})
                                           
                                                                                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                                (j:Usize.t)
                         
                                                                                             
                                          : Lemma
                                            (requires (well_formed_allocated_blocks g) /\
                                          
                                                      (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                            
                                                     (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                                                     (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
                                                     (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0) /\
                                                     (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v wz) /\
                                                     
                                                     (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) h_index)) /\
                                                     
                                                      
                                                     (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) ==
                                                     (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                     (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                     (isPointer(Usize.add h_index (Usize.mul i mword)) g)
                                                     )
                                              (ensures (Seq.index (G.successors (create_graph_from_heap g) h_index) (Usize.v j) == 
                                                        read_word g (Usize.add h_index (Usize.mul i mword)))) = 
 graph_successors_create_from_an_index_lemma g h_index (G.successors (create_graph_from_heap g) h_index) j;
 create_successors_list_for_h_index_from_i_index_lemma g h_index wz i; 
 create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j g h_index wz i j;
 assert (Seq.index (G.successors (create_graph_from_heap g) h_index) (Usize.v j) == 
                                                         read_word g (Usize.add h_index (Usize.mul i mword)));
 ()

#restart-solver 

#restart-solver 

#push-options "--z3rlimit 1000"

#restart-solver

let create_successors_list_for_h_index_pointer_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                           (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                           (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                           (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})

                       : Lemma
                         (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x)))) /\
                                   (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) /\
                                   (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                            (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                            (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                   (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                   (isPointer (field_ptr_construct g h_index wz i) g))
                         (ensures (Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0))
                         
                         (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       seq_empty_lemma1 #UInt64.t;
       assert (Seq.length s_list == 0);
       
       ()
 
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      if isPointer succ_index g  then
      (
        assert (succ == read_word g succ_index);
        assert (is_valid_header h_index g);
        assert (Seq.mem h_index (objects2 0UL g));
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        
        test_allocs g h_index wz;
        assert (Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g));
        assert (Seq.mem succ (get_allocated_block_addresses g));
        assert (Seq.mem succ (objects2 0UL g));
        assert (is_valid_header succ g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        
        let s_list' = create_successors_list_for_h_index g h_index wz i' in
        

        lemma_tl succ s_list'; 
        
        let s_list = Seq.cons succ s_list' in 
        cons_length_lemma3 s_list' succ;
        assert (Seq.length s_list > 0);

        ()
      )
      else
      (
        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        let s_list = create_successors_list_for_h_index g h_index wz i' in
        ()
      )
    )


#pop-options


#push-options "--split_queries"

#restart-solver

#reset-options "--z3rlimit 500 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver

let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j2 (g:heap{well_formed_heap2 g})
                                                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                               is_valid_header h_index g})
                                           
                                                                                                (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                                (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                                (j:Usize.t)
                                                                                               
                                                                                               
                         
                                                                                             
                                          : 
                                          Lemma
                                            (requires (well_formed_allocated_blocks g) /\
                                          
                                                      (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                            
                                                     (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                                                     (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
                                                     (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0) /\
                                                     (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v wz) /\
                                                     
                                                     (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) h_index)) /\
                                                     
                                                      
                                                     (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) ==
                                                     (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                     (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                     (isPointer(Usize.add h_index (Usize.mul i mword)) g)
                                                     )
                                             (ensures (let i' = Usize.add i 1UL in
                                                       let j' = Usize.add j 1UL in
                                                       (graph_successors_create_from_an_index g h_index ((G.successors (create_graph_from_heap g) h_index)) j' == 
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i'))) = 
  let i' = Usize.add i 1UL in
  let j' = Usize.add j 1UL in

  let s_heap_i = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) in
  let s_graph_j =  (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) in

  let sl = (G.successors (create_graph_from_heap g) h_index) in
  assert (s_heap_i == s_graph_j);

  
  field_limits_allocated_blocks_lemma g;
  field_contents_within_limits_allocated_blocks_lemma g;
  fieldaddress_within_limits_lemma_x_all g;

  create_successors_list_for_h_index_pointer_lemma g h_index wz i;
  assert (Seq.length s_heap_i > 0);
  assert (Seq.length s_graph_j > 0);
  
  let tl = Seq.tail s_heap_i in
  let tl1 = Seq.tail s_graph_j in
  create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j g h_index wz i j;
  assert (tl == tl1);
  let s_graph_j1 =  (graph_successors_create_from_an_index g h_index sl j') in
  graph_successors_create_from_an_index_lemma1 g h_index sl j j';
  assert (tl1 == s_graph_j1);

  
  let s_heap_i1 = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i') in
  create_successors_list_for_h_index_from_i_index_lemma_tail g h_index wz i i';
  assert (tl ==  s_heap_i1);
  assert (s_graph_j1 == s_heap_i1);
  assert (graph_successors_create_from_an_index g h_index sl j' == create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');
  ()
 

#reset-options "--z3rlimit 50 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#restart-solver

#restart-solver

//#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

let fieldPush_spec_body_successor_push_body_equivalence_lemma2 (g:heap{well_formed_heap2 g})
                                                               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                 (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                 (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                 (G.is_vertex_set st) /\
                                                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==> Seq.mem x st)
                                                                                })
                                                               (h_index:hp_addr {Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                 is_valid_header h_index g})
                                          
                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                               (j:Usize.t)
                                                               (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                 (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                 (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                 (G.is_vertex_set vl) /\
                                                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                })
                                      : Lemma
                                        (requires (well_formed_allocated_blocks g) /\
                                          
                                                  (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                  
                                                  (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                                                  (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
                                                  (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0) /\
                                                     
                                                  (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v wz) /\
                                                     
                                                  (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) h_index)) /\
                                                  (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                  (isPointer(Usize.add h_index (Usize.mul i mword)) g ==> 
                                                         (Seq.index (G.successors (create_graph_from_heap g) h_index) (Usize.v j) == 
                                                         read_word g (Usize.add h_index (Usize.mul i mword)))) /\
                                                  (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                  (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                                        (ensures (fst (fieldPush_spec_body g st h_index wz i) == 
                                                       ( if (isPointer(Usize.add h_index (Usize.mul i mword)) g) then
                                                                (
                                                                      G.successor_push_body1 (G.successors (create_graph_from_heap g) h_index) (vl) (st) (Usize.v j)
                                                                )
                                                               else
                                                                (
                                                                      st
                                                                )))) = 
  
   assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
   assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);
       
   let succ_index = Usize.add h_index (Usize.mul i mword) in
       
   assert (Usize.v succ_index < heap_size);
 
   max_wosize_times_mword_multiple_of_mword i;
   sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
   assert (Usize.v succ_index % Usize.v mword == 0);
   assert (is_hp_addr succ_index);
  
   lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  

   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
   fieldaddress_within_limits_lemma_x_all g;
   
   let succ = read_word g succ_index in
   let succ1 = Seq.index (G.successors (create_graph_from_heap g) h_index) (Usize.v j) in
   assert (succ == read_word g succ_index);
   if isPointer succ_index g  then
   (
     assert (isPointer(Usize.add h_index (Usize.mul i mword)) g ==> 
                                                         (Seq.index (G.successors (create_graph_from_heap g) h_index) (Usize.v j) == 
                                                         read_word g (Usize.add h_index (Usize.mul i mword))));
     assert (succ == succ1);
     if color_of_object1 succ g = white then
   (
       valid_succ_color_lemma g succ;
       assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
       let st', g' = push_to_stack2 g st succ in
       push_to_stack2_heap_state_lemma g st succ;
       push_to_stack2_field_size_lemma g st succ;
       
       assert (Seq.mem h_index (get_allocated_block_addresses g));

       
       test_allocs g h_index wz;
       
       assert (Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g));
       assert (Seq.mem succ (get_allocated_block_addresses g));
                
       push_to_stack_heap_and_push_to_graph_equality_lemma1 g st succ vl;
       assert (st' == G.push_to_stack_graph1 vl st succ);
       
       
     
       
       objects2_equal_lemma 0UL g g';
       
       push_to_stack2_lemma g st succ;

       
       let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) h_index) vl st (Usize.v j) in
       assert (st'' == G.push_to_stack_graph1 vl st succ);
       //assert (st'' ==  G.push_to_stack_graph1 vl st succ);
       assert (st' == st''); 
       assert (fst (fieldPush_spec_body g st h_index wz i) == ( if (isPointer(Usize.add h_index (Usize.mul i mword)) g) then
                                                                (
                                                                      G.successor_push_body1 (G.successors (create_graph_from_heap g) h_index) (vl) (st) (Usize.v j)
                                                                )
                                                               else
                                                                (
                                                                      st
                                                                )));
                                                                       
       ()
   )
 else
   (
      let st' = st in
      let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) h_index) vl st  (Usize.v j) in
      
      assert (st'' == st);
      assert (fst (fieldPush_spec_body g st h_index wz i) == ( if (isPointer(Usize.add h_index (Usize.mul i mword)) g) then
                                                                (
                                                                      G.successor_push_body1 (G.successors (create_graph_from_heap g) h_index) (vl) (st) (Usize.v j)
                                                                )
                                                               else
                                                                (
                                                                      st
                                                                )));
                                                                       
      ()
   )
    

     
   )
   else
   (
     assert (fst (fieldPush_spec_body g st h_index wz i) == ( if (isPointer(Usize.add h_index (Usize.mul i mword)) g) then
                                                                (
                                                                      G.successor_push_body1 (G.successors (create_graph_from_heap g) h_index) (vl) (st) (Usize.v j)
                                                                )
                                                               else
                                                                (
                                                                      st
                                                                )));
                                                                                          
                                                                                          
                                                                                           
     ()
   )
                                                  


#restart-solver


let fieldPush_spec_body_successor_push_body_equivalence_lemma3 (g:heap{well_formed_heap2 g})
                                                               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                 (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                 (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                 (G.is_vertex_set st) /\
                                                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==> Seq.mem x st)
                                                                                })
                                                               (h_index:hp_addr {Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                 is_valid_header h_index g})
                                          
                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                              
                                                               (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                 (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                 (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                 (G.is_vertex_set vl) /\
                                                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                })
                                      : Lemma
                                        (requires (well_formed_allocated_blocks g) /\
                                          
                                                  (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                  
                                                  (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                                                  (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
                                                  (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0) /\
                                                     
                                                  (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v wz) /\
                                                     
                                                 
                                                  (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                  ~(isPointer(Usize.add h_index (Usize.mul i mword)) g) /\
                                                  
                                                  (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                  (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                                        (ensures (fst (fieldPush_spec_body g st h_index wz i) == st)) = ()
                          
                                                                 
                                                      
                                                                      
                                                               


#restart-solver

#restart-solver 

let rec create_succcessors_for_h_index_lemma1 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                             (wz: wosize{(wz == getWosize (read_word g h_index))})

                                            
                         
                                             (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                                             (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})

                                             (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})

                                             (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })

                                             (wz1: wosize{(wz1 == getWosize (read_word g' h_index))})
                            : Lemma
                          (requires (well_formed_allocated_blocks g') /\
                                    (objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (wz == wz1) /\
                                    (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                    (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g') /\
                                    (forall j x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                    (forall j x.  Seq.mem x (get_allocated_block_addresses g') /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)
                                    )
                          (ensures (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 
  if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       seq_empty_lemma ();
       assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
       ()
    )
  else
   (
     assert (objects2 0UL g == objects2 0UL g');
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g');

     assert (heap_remains_same_except_index_v_id v_id g g');

     field_reads_all_equal_for_all_objects_lemma g g' v_id;

      
      

     assert ((forall x (y:hp_addr{(length (slice g' (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8) /\
                              (length (slice g (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8)}). Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) /\
                                       x <> v_id ==>  read_word g y == read_word g' y));
     field_reads_all_equal_h_index_lemma g g' v_id;

     assert (forall (y:hp_addr{(length (slice g' (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8) /\
                              (length (slice g (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8)}). Usize.v y >= Usize.v h_index + Usize.v mword /\
                                             Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                                   read_word g y == read_word g' y);
     let succ_index = Usize.add h_index (Usize.mul i mword) in

     assert (Usize.v i < Usize.v wz + 1);
     assert (well_formed_allocated_blocks g');

     assert (is_fields_within_limit1 h_index wz);

     assert (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size);

     assert (Usize.v i < Usize.v wz + 1);

     assert (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size);
     
     assert (Usize.v succ_index < heap_size);

     
     //assert (heap_remains_same_except_index_v_id v_id g g');

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
                                       
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);



      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);

      lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8); 
      
      let succ1 = read_word g' succ_index in
      assert (succ1 == read_word g' succ_index);

      assert (Usize.v succ_index >= Usize.v h_index + Usize.v mword /\
             Usize.v succ_index <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword));
      assert (succ == succ1);

      let i' = Usize.(i +^ 1UL) in
      if isPointer succ_index g  then
      (
          let s_list' = create_successors_list_for_h_index g h_index wz i' in
          let s_list'' = create_successors_list_for_h_index g' h_index wz1 i' in
          create_succcessors_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;
          assert (create_successors_list_for_h_index g h_index wz i' == create_successors_list_for_h_index g' h_index wz1 i');

          lemma_tl succ s_list'; 
          lemma_tl succ s_list''; 
        
          let s_list = Seq.cons succ s_list' in 
          let s_list1 = Seq.cons succ s_list'' in 
          assert (s_list == s_list1);
          assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
          ()
      )
      else
      (
        let s_list' = create_successors_list_for_h_index g h_index wz i' in

        create_succcessors_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;

        assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g' h_index wz1 i);
       
        ()
      )
   )

#reset-options "--z3rlimit 1000"

#restart-solver 

let push_to_stack2_create_successors_for_h_index_lemma  (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                        (st: seq Usize.t{G.is_vertex_set st /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                      Seq.mem x st)})
                                                        (x: hp_addr{~(Seq.mem x st) /\
                                                                      (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                       is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                       (Usize.v x % Usize.v mword == 0) /\
                                                                       is_valid_header x g /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                                       (c:color{c == 2UL})

                                                       (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})

                                                       (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))})
                                                       (wz1: wosize{((wz1 == getWosize (read_word (snd (push_to_stack2 g st x)) h_index)) /\ 
                                                                                   is_fields_within_limit1 h_index wz1 /\
                                                                                   is_fields_contents_within_limit2 h_index wz1 (snd (push_to_stack2 g st x)) /\
                                                                                   (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))})

                                                
                                                       (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                      : Lemma
                                        (requires (wz == wz1) /\ well_formed_allocated_blocks (snd (push_to_stack2 g st x)))
                                        (ensures (create_successors_list_for_h_index g h_index wz i == 
                                                     create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i)) =
   if Seq.length st = 0 then
(
    let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g c in 

    assert (well_formed_heap2 g');
    
    objects2_equal_lemma 0UL g g';
    
    get_allocated_block_addresses_lemma g g' x c;
    assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))));
    assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
    colorHeader1_Lemma x g c; 

    assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
    fieldaddress_within_limits_lemma_x_all g;

    assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
    well_formed_allocated_blocks_lemma g x c g';
    

    assert (well_formed_allocated_blocks g');
    
    assert (Seq.mem x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');
    create_succcessors_for_h_index_lemma1 g h_index wz i x c g' wz1;
    assert (create_successors_list_for_h_index g h_index wz i == 
             create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i);
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g c in 

  assert (well_formed_heap2 g');
    
   objects2_equal_lemma 0UL g g';
    
   get_allocated_block_addresses_lemma g g' x c;

   assert ((forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
   colorHeader1_Lemma x g c;

   assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');

   fieldaddress_within_limits_lemma_x_all g;

   assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   well_formed_allocated_blocks_lemma g x c g';
    

   assert (well_formed_allocated_blocks g');

   assert (G.is_vertex_set st);
   assert (~(Seq.mem x st));
  
   G.snoc_unique_lemma x st;
   assert (G.is_vertex_set st');
   create_succcessors_for_h_index_lemma1 g h_index wz i x c g' wz1;
   assert (create_successors_list_for_h_index g h_index wz i == 
             create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i);
   ()
)


#restart-solver

let fieldPush_spec_body_create_successors_for_h_index_lemma  (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                             (st: seq Usize.t{G.is_vertex_set st /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                      Seq.mem x st)})
                                                           
                                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})

                                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))})

                                                            (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                       
                                                            (wz1: wosize{((wz1 == getWosize (read_word (snd (fieldPush_spec_body g st h_index wz i)) h_index)) /\ 
                                                                                   is_fields_within_limit1 h_index wz1 /\
                                                                                   is_fields_contents_within_limit2 h_index wz1 (snd (fieldPush_spec_body g st h_index wz i)) /\
                                                                                   (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))})
                                                            (c:color{c == 2UL})
                                                            (j:Usize.t{Usize.v j <= Usize.v wz + 1 /\ Usize.v j >= 1})
                                                                    
                                      : Lemma
                                        (requires (wz == wz1) /\ well_formed_allocated_blocks (snd (fieldPush_spec_body g st h_index wz i)))
                                        (ensures (create_successors_list_for_h_index g h_index wz j == 
                                                     create_successors_list_for_h_index (snd (fieldPush_spec_body g st h_index wz i)) h_index wz1 j)) = 
 assert (well_formed_heap2 g);
 assert (is_valid_header h_index g);  
 assert (Seq.mem h_index (objects2 0UL g));
 assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
 assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);   
 let succ_index = Usize.add h_index (Usize.mul i mword) in
       
 assert (Usize.v succ_index < heap_size);
 
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
       
 let succ = read_word g succ_index in
 assert (succ == read_word g succ_index);
 assert (Seq.mem h_index (objects2 0UL g));
                            
 if isPointer succ_index g && color_of_object1 succ g = white then
   (
       valid_succ_color_lemma g succ;
       assert (~(isGrayObject1 succ g) /\ ~(isBlackObject1 succ g));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
       let st', g' = push_to_stack2 g st succ in
       push_to_stack2_heap_state_lemma g st succ;
       push_to_stack2_field_size_lemma g st succ;
       
       assert (G.is_vertex_set st');
       assert (forall x. Seq.mem x (objects2 0UL g') /\
                                               isGrayObject1 x g' <==>
                                               Seq.mem x st');
       assert (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g);
       assert (forall x. Seq.mem x st' ==> is_valid_header x g');
         
       assert (well_formed_heap2 g');

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 succ g == white);
       push_to_stack2_lemma g st succ;

       push_to_stack2_create_successors_for_h_index_lemma g st succ c h_index wz wz1 j;
       ()
    )
   else 
    (
       
      ()
          
    )

#restart-solver

#restart-solver

let graph_successors_create_from_an_index_equivalence_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                                (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))})
                                                                                     
                                                                (f: seq Usize.t{(f == G.successors (create_graph_from_heap g) h_index) /\
                                                                                (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                                
                                                                (i:Usize.t {Usize.v i <= Seq.length f}) 
                                                                (st: seq Usize.t{G.is_vertex_set st /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                      Seq.mem x st)})
                                                           
                                                                (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g /\
                                                                                   (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0))})
                                                                
                                                                
                                                                                   
                                                                (j:Usize.t{Usize.v j < Usize.v wz + 1 /\ Usize.v j >= 1})
                                                                (g': heap {well_formed_heap2 g' /\
                                                                            g' == (snd (fieldPush_spec_body g st h_index wz j))})

                                                                (f1: seq Usize.t)

                                                                (wz1: wosize{((wz1 == getWosize (read_word g' h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                                   is_fields_contents_within_limit2 h_index wz g' /\
                                                                                   (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v wz ==> 
                                                                                   (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0))})
                                        : Lemma
                                          (requires well_formed_allocated_blocks g' /\
                                                    (get_allocated_block_addresses g == get_allocated_block_addresses g') /\
                                                    (wz == wz1) /\ (f == f1) /\
                                                    (let grph = create_graph_from_heap g' in
                                                     let l = G.successors grph h_index in
                                                     (f1 == l) /\ (Seq.length f1 <= Usize.v wz1)))
                                          (ensures (graph_successors_create_from_an_index g h_index f i == graph_successors_create_from_an_index g' h_index f1 i)) =()
                               
#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"



#push-options "--split_queries"                                                      
                                           
#restart-solver

let rec fieldPush_spec_successor_push_itr_equivalence_lemma2 (g:heap{well_formed_heap2 g})
                                                             (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })
                         
                                                             (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                               is_valid_header h_index g})
                                           
                                                             (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                             (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                             (j:Usize.t)
                                                             (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (G.is_vertex_set vl) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                }) 
                                        : Lemma
                                          (requires (well_formed_allocated_blocks g) /\
                                          
                                                     (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                     
                                                     (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v wz) /\
                                                     
                                                     (Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) h_index)) /\
                                                     
                                                     (Seq.length (G.successors (create_graph_from_heap g) h_index) <= Usize.v (getWosize (read_word g h_index))) /\
  
                                                     (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                                                     (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
                                                     (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0) /\
                                                      
                                                     (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) ==
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                      
                                                      
                                                                (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                                (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                                          (ensures ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) h_index)
                                                                                                       (vl)
                                                                                                       (st)
                                                                                                      (Usize.v j)))
                                          (decreases ((Usize.v wz + 1) - Usize.v i))  = 
let grph = create_graph_from_heap g in
let l = G.successors grph h_index in
graph_successors_length_lemma g h_index;
graph_successors_mem_lemma g h_index;
assert (forall x. Seq.mem x l ==> Seq.mem x (get_allocated_block_addresses g));
assert (Seq.length l <= Usize.v wz);
if Usize.v i = Usize.v wz + 1 then
(
  create_successors_list_for_h_index_i_equals_wz_plus_one_implies_succ_list_from_j_is_empty g st h_index wz i j;
  assert (Usize.v j == Seq.length (G.successors (create_graph_from_heap g) h_index));
  let st' = G.successor_push_itr1 l vl st (Usize.v j) in
  G.successor_push_itr1_lemma1 l vl st (Usize.v j);
  assert (st' == st);
  assert (fst (fieldPush_spec1 g st h_index wz i) == st);
  assert (G.successor_push_itr1 l vl st (Usize.v j) == st);
  ()
)
else
(
 let i' = Usize.add i 1UL in
 assert (Usize.v i < Usize.v wz + 1);

 assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
 assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);   
 let succ_index = Usize.add h_index (Usize.mul i mword) in
       
 assert (Usize.v succ_index < heap_size);
 
 max_wosize_times_mword_multiple_of_mword i;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
 assert (Usize.v succ_index % Usize.v mword == 0);
 assert (is_hp_addr succ_index);
   
 let st', g' = fieldPush_spec_body g st h_index wz i in
 assert (Usize.v i < Usize.v wz + 1);
 arithmetic_lemma i wz;
 assert (Usize.v i <= Usize.v wz);
 arithmetic_lemma1 i wz;
 assert (Usize.v i - 1 < Usize.v wz);
 assert (Seq.length l <= Usize.v wz);
 assert (Usize.v j <= Seq.length l);
 
 if (Usize.v j = Seq.length l) then
 (
   let l' = (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) in
   assert (l' == Seq.empty);
   length_empty_lemma l';
   assert (Seq.length l' == 0);

   (*This means starting from index i if we scan the fields of h_index, we will not get any field pointers. So even if we call fieldPush_spec_body, it will return the
     stack as unaffected. There is no point in recursively continuing the fieldPush at this point.*)
   assert (Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) == 0);
   create_successors_list_for_h_index_recursing_property_lemma3 g h_index wz i i';
   assert ((create_successors_list_for_h_index g h_index wz i == Seq.empty) ==> 
             (create_successors_list_for_h_index g h_index wz i' == Seq.empty));
   assert ((graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i));

   (*Essential pre-condition to continue the recursive call*)
   (*---------------------------------------------------------------------------------------------------------------------------------------*)
   assert ((graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i'));

   let st_gr = G.successor_push_itr1 l vl st (Usize.v j) in
   G.successor_push_itr1_lemma1 l vl st (Usize.v j);
   assert (st_gr == st);
   
   
   create_successors_list_for_h_index_recursing_property_lemma4  g h_index wz i;

   //This is required to establish that fieldPush_spec_body returns the stack as unchanged as the field value is not a pointer
   //---------------------------------------------------------------------------------------------------------------------------------------
   assert (~(isPointer(Usize.add h_index (Usize.mul i mword)) g));

   fieldPush_spec_body_successor_push_body_equivalence_lemma3 g st h_index wz i vl;
   

   assert (st' == st);
   fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
   fieldPush_spec_body_graph_lemma g st h_index wz i;

       assert (well_formed_allocated_blocks g');
       fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
       let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
       let st2 = G.successor_push_itr1 l vl st (Usize.v j) in
       let wz' = getWosize (read_word g' h_index) in
       assert (wz == wz');
       assert (objects2 0UL g == objects2 0UL g');
       
       fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
       fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;
       
       assert (forall x. Seq.mem x vl ==> is_valid_header x g'); 
       assert (forall x. Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g' <==> Seq.mem x vl);

       (*Essential pre-condition to continue the recursive call*)
       (*---------------------------------------------------------------------------------------------------------------------------------------*)
       assert ((graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i')); 

       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j vl;
       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st (Usize.v j));
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i');
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');
       G.successor_push_itr1_lemma1 l vl st (Usize.v j);
       assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) h_index)
                                                                                                       (vl)
                                                                                                       (st)
                                                                                                       (Usize.v j));
       ()
   
 )
 else
 (
   (*In this branch only, we can invoke (G.successor_push_body1). This is because j should be < Seq.length l *)
   assert (Usize.v j < Seq.length l);
   assert (Usize.v i < Usize.v wz + 1);
   // 2 cases
   //Case 1: (isPointer(Usize.add h_index (Usize.mul i mword)) g)
   
    if (isPointer(Usize.add h_index (Usize.mul i mword)) g) then
    (
       let j' = Usize.add j 1UL in
       create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j1 g h_index wz i j;

       //This is the essential precondition for fieldPush_spec body lemma to get the fact that the fieldPush_body and successor_push_body pushes the same field pointer
       //to the stack
       assert (Seq.index (G.successors (create_graph_from_heap g) h_index) (Usize.v j) == 
                                                         read_word g (Usize.add h_index (Usize.mul i mword)));
       create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j2 g h_index wz i j;

       let st'' = G.successor_push_body1 l vl st (Usize.v j) in

       //fieldPush_spec_body_lemma should ensure that the stack returned by fieldPush_spec_body and successor_push_body are the same
       (*Call fieldPush_spec_body_lemma*)
       fieldPush_spec_body_successor_push_body_equivalence_lemma2 g st h_index wz i j vl;
       assert (st' == st'');
       fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
       fieldPush_spec_body_graph_lemma g st h_index wz i;

       assert (well_formed_allocated_blocks g');
       fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
       let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
       let st2 = G.successor_push_itr1 l vl st' (Usize.v j') in
       let wz' = getWosize (read_word g' h_index) in
       assert (wz == wz');
       assert (objects2 0UL g == objects2 0UL g');
       
       fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
       fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;
       
       assert (forall x. Seq.mem x vl ==> is_valid_header x g'); 
       assert (forall x. Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g' <==> Seq.mem x vl);

      (*Essential pre-condition to continue the recursive call*)
      (*---------------------------------------------------------------------------------------------------------------------------------------*)
       assert (graph_successors_create_from_an_index g h_index ((G.successors (create_graph_from_heap g) h_index)) j' == 
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i');

       assert ((forall x. Seq.mem x st' ==> ~(Seq.mem x vl)) /\
              (forall x. Seq.mem x vl ==> ~(Seq.mem x st')));
       assert (Usize.v j' <= Seq.length l);

       assert (is_fields_within_limit1 h_index (getWosize (read_word g' h_index)));

       assert (well_formed_heap2 g');
       assert (get_allocated_block_addresses g ==  get_allocated_block_addresses g');
       assert (Seq.mem h_index (get_allocated_block_addresses g));
       assert (Seq.mem h_index (get_allocated_block_addresses g'));
       field_contents_within_limits_allocated_blocks_lemma g';
                                           
       
       assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g' h_index)) g');
             
       assert (forall k.  Usize.v k > 0 /\ Usize.v k <= Usize.v (getWosize (read_word g' h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v k  * Usize.v mword)) % Usize.v mword == 0);

       
       graph_successors_create_from_an_index_equivalence_lemma g h_index l j' st wz i g' l wz';  
       assert ((graph_successors_create_from_an_index g h_index l j' == graph_successors_create_from_an_index g' h_index l j'));
       
       
       fieldPush_spec_body_create_successors_for_h_index_lemma g st h_index wz i wz' 2UL i';

       assert ((create_successors_list_for_h_index g h_index wz i' == 
                create_successors_list_for_h_index g' h_index wz' i'));
       
       assert (graph_successors_create_from_an_index g' h_index ((G.successors (create_graph_from_heap g') h_index)) j' == 
                          create_successors_list_for_h_index g' h_index (getWosize (read_word g' h_index)) i');
                          
       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j' vl;

       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st' (Usize.v j'));
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i');
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');
       G.successor_push_itr1_lemma l vl st (Usize.v j);
       assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) h_index)
                                                                                                       (vl)
                                                                                                       (st)
                                                                                                       (Usize.v j));
       ()
    )
   
   //--------------------------------------------------------------------------------------------------------------------------------------------------
   //Case 2: ~(isPointer(Usize.add h_index (Usize.mul i mword)) g) 
   
   else
   (
       //fieldPush_spec_body returns the stack as unchanged as the field value is not a pointer
       //---------------------------------------------------------------------------------------------------------------------------------------
       assert (~(isPointer(Usize.add h_index (Usize.mul i mword)) g));
       create_successors_list_for_h_index_recursing_property_lemma g h_index wz i i';
       assert (create_successors_list_for_h_index g h_index wz i == create_successors_list_for_h_index g h_index wz i');

       //fieldPush_spec_body_lemma should ensure that the stack is returned as unchanged
       (*Call fieldPush_spec_body_lemma*)
       fieldPush_spec_body_successor_push_body_equivalence_lemma2 g st h_index wz i j vl;
       assert (st == st');

       fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
       fieldPush_spec_body_graph_lemma g st h_index wz i;

       assert (well_formed_allocated_blocks g');
       fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
       let st1, g'' = fieldPush_spec1 g' st' h_index wz i' in
       let st2 = G.successor_push_itr1 l vl st (Usize.v j) in
       let wz' = getWosize (read_word g' h_index) in
       assert (wz == wz');
       assert (objects2 0UL g == objects2 0UL g');
       
       fieldPush_spec_body_valid_header_visited_set_lemma g st h_index wz i vl;
       fieldPush_spec_body_black_nodes_visited_set_lemma g st h_index wz i vl;
       
       assert (forall x. Seq.mem x vl ==> is_valid_header x g'); 
       assert (forall x. Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g' <==> Seq.mem x vl);

       (*Essential pre-condition to continue the recursive call*)
       (*---------------------------------------------------------------------------------------------------------------------------------------*)
       assert ((graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) h_index) j) ==
             (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i')); 

       fieldPush_spec_successor_push_itr_equivalence_lemma2 g' st' h_index wz i' j vl;
       assert (st1 == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == st2);
       assert (fst (fieldPush_spec1 g' st' h_index wz i') == G.successor_push_itr1 l vl st (Usize.v j));
       fieldPush_fieldPush_spec_body_lemma g st h_index wz i i';
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 (snd (fieldPush_spec_body g st h_index wz i)) 
                                                                                        (fst (fieldPush_spec_body g st h_index wz i))
                                                                                        h_index 
                                                                                        wz
                                                                                        i');
       assert (fieldPush_spec1 g st h_index wz i == fieldPush_spec1 g' st' h_index wz i');
       G.successor_push_itr1_lemma l vl st (Usize.v j);
       assert ((fst (fieldPush_spec1 g st h_index wz i)) == G.successor_push_itr1 (G.successors (create_graph_from_heap g) h_index)
                                                                                                       (vl)
                                                                                                       (st)
                                                                                                       (Usize.v j));
       ()
   )
 )
)
 
#reset-options "--z3rlimit 500"

#restart-solver 

let stack_less_than_heap_size_when_one_non_gray_exists (g:heap{well_formed_heap2 g})
                                                       (st:seq Usize.t)
                                                       (x:Usize.t)
                                  : Lemma
                                    (requires  (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                               (forall x. Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g == gray) <==>
                                                  Seq.mem x st) /\
                                    
                                               (G.is_vertex_set st) /\
                                    
                                               (Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g <> gray)))
                                    
                                    (ensures (Seq.length st < heap_size)) = 

 assert (Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g <> gray));
 assert (~(Seq.mem x st));
 let blocks = objects2 0UL g in
 get_block_address_length_lemma g;
 assert (Seq.length blocks <= heap_size);
 assert (G.subset_vertices st blocks);
 assert (Seq.length st <= heap_size);
 if Seq.length st < heap_size then ()
 else
   (
     assert (Seq.length st == heap_size);
     G.subset_of_each_other st blocks;
     assert (G.subset_vertices blocks st);
     assert (forall x. Seq.mem x blocks ==> Seq.mem x st);
     assert (Seq.mem x st);
     ()
   )

let all_mem_implies_subset (s1:seq Usize.t)
                           (s2:seq Usize.t)
                   : Lemma
                     (requires (G.is_vertex_set s1 /\
                                G.is_vertex_set s2 /\
                                (forall x. Seq.mem x s1 ==> Seq.mem x s2)))
                     (ensures (G.subset_vertices s1 s2)) = ()

#push-options "--split_queries"

#restart-solver

#restart-solver 


let all_mem_st_mem_st'_in_stack (st:stack)
                                (st':stack) = (forall x. Seq.mem x st ==> Seq.mem x st')

let all_mem_st_mem_st__except_v_id_in_stack (v_id:hp_addr)
                                            (st:stack)
                                            (st':stack) = (forall x. Seq.mem x st' /\ x <> v_id ==> Seq.mem x st)

#restart-solver

let valid_header_lemma1 (g:heap{well_formed_heap2 g})
                        (i:nat)
                        (succ:seq Usize.t { i <= Seq.length succ  ==>
                                     ((forall x. Seq.mem x (Seq.slice succ i (Seq.length succ)) ==> 
                                              Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                      (forall x. Seq.mem x (Seq.slice succ i (Seq.length succ)) ==> 
                                              is_valid_header x g))})
             : Lemma
               (ensures ((i + 1) <= Seq.length succ ==> 
                              ((forall x. Seq.mem x (Seq.slice succ (i + 1) (Seq.length succ)) ==> 
                                              Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                      (forall x. Seq.mem x (Seq.slice succ (i + 1) (Seq.length succ)) ==> 
                                              is_valid_header x g)))) = ()

let color_stack_mem_lemma  (g:heap{well_formed_heap2 g})
                               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                 (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                 (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                 (G.is_vertex_set st) /\
                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                                })
                               (succ:hp_addr{is_valid_header succ g /\
                                                (color_of_object1 succ g == white \/
                                                 color_of_object1 succ g == gray \/
                                                 color_of_object1 succ g == black
                                                )})
                   : Lemma
                     (requires (color_of_object1 succ g == white))
                     (ensures (~(isGrayObject1 succ g) /\
                               ~(isBlackObject1 succ g) /\
                               ~(Seq.mem succ st))) = ()

let slice_mem_helper_lemma (s: seq Usize.t{(Seq.length s) > 0})
                           (s': seq Usize.t{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                           (x:Usize.t)
                  : Lemma
                    (requires (Seq.mem x s'))
                    (ensures (Seq.mem x s)) =
 Seq.lemma_mem_snoc s' (Seq.index s (Seq.length s - 1))
                 
let slice_mem_lemma (s: seq Usize.t{(Seq.length s) > 0})
                    (s': seq Usize.t{Seq.equal s' (Seq.slice s 0 (Seq.length s - 1))})
                : Lemma 
                  (ensures (forall x. Seq.mem x s' ==> Seq.mem x s))=
Classical.forall_intro (Classical.move_requires (slice_mem_helper_lemma s s'))

#restart-solver 

let slice_property_lemma (g:heap{well_formed_heap2 g}) 
                         (st: seq Usize.t)
                         (st_top: Usize.t)
                 : Lemma
                   (requires Usize.v st_top <= Seq.length st /\
                             Usize.v st_top > 0 /\
                             (forall x. Seq.mem x (Seq.slice st 0 (Usize.v st_top)) ==>
                                        Usize.v x >= 0 /\ Usize.v x < heap_size))
                   (ensures (forall x. Seq.mem x (Seq.slice st 0 (Usize.v st_top - 1)) ==>
                                         Usize.v x >= 0 /\ Usize.v x < heap_size)) =
 Seq.lemma_slice_snoc st 0 (Usize.v st_top);
 ()

let slice_coloring_lemma (g:heap{well_formed_heap2 g}) 
                         (g':heap{well_formed_heap2 g'}) 
                         (v_id: hp_addr{is_valid_header v_id g /\
                                      is_valid_header v_id g'})
                         (s: seq Usize.t)
                         (s_top:Usize.t{Usize.v s_top <= Seq.length s}) 
         : Lemma
              (requires (G.is_vertex_set (Seq.slice s 0 (Usize.v s_top)) /\
                        ~(Seq.mem v_id (Seq.slice s 0 (Usize.v s_top))) /\
                         color_of_object1 v_id g' == black /\
                         heap_remains_same_except_index_v_id v_id g g' /\
                         (objects2 0UL g ==
                             objects2 0UL g') /\
                         (get_allocated_block_addresses g == 
                              get_allocated_block_addresses g') /\
                         
                         color_of_object1 v_id g == gray /\
                         (forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) \/
                          (y == v_id) <==> Seq.mem y (objects2 0UL g) /\ isGrayObject1 y g)))
              (ensures ((forall y. Seq.mem y (Seq.slice s 0 (Usize.v s_top)) <==>
                             Seq.mem y (objects2 0UL g') /\ isGrayObject1 y g'))) = ()


let colorHeader1_black_nodes_lemma (g:heap{well_formed_heap2 g}) 
                                   (y:hp_addr{Usize.v y >= 0 /\ Usize.v y < heap_size /\
                                             is_valid_header y g /\
                                             color_of_object1 y g <> black
                                          })
           : Lemma
             (ensures Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (colorHeader1 y g black) (get_allocated_block_addresses (colorHeader1 y g black)))) = 
let g' = colorHeader1 y g black in
let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
 colorHeader1_subset_lemma y g;
 assert (G.subset_vertices blacks blacks');
 assert (is_valid_header y g');
 assert (Seq.mem y blacks');
 assert (~(Seq.mem y blacks));
 assert (Seq.length blacks <= Seq.length blacks');
 if Seq.length blacks < Seq.length blacks' then ()
 else
 (
   assert (Seq.length blacks == Seq.length blacks');
   G.subset_of_each_other blacks blacks';
   assert (G.subset_vertices blacks' blacks);
   assert (forall x. Seq.mem x blacks' ==> Seq.mem x blacks);
   ()
 )

#restart-solver

#restart-solver 

#restart-solver

let mark5_body (g:heap{well_formed_heap2 g}) 
               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
           : Pure (stack_heap_pair)
             (requires (~(G.is_emptySet st)))
             (ensures (fun st_hp -> G.is_vertex_set (fst st_hp) /\
                                (Seq.length g == Seq.length (snd st_hp)) /\
                                well_formed_heap2 (snd st_hp) /\
                                (forall x. Seq.mem x (fst st_hp) ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                (forall x. Seq.mem x (fst st_hp) ==> Usize.v x % Usize.v mword == 0) /\
                                (forall x. Seq.mem x (fst st_hp) ==> is_valid_header x (snd st_hp)) /\
                                (forall x. Seq.mem x (objects2 0UL (snd st_hp)) /\
                                        isGrayObject1 x (snd st_hp) <==>
                                                Seq.mem x (fst st_hp)) /\
                                (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                                (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp)))) = 
   assert (~(G.is_emptySet st));
   let v_id = Seq.index st (Seq.length st - 1) in
   let s = Seq.slice st 0 (Seq.length st - 1) in
   assert (color_of_object1 v_id g == gray);
   
   assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
   assert (well_formed_heap2 g);
   slice_mem_lemma st s;
   assert (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (forall x. Seq.mem x s ==> Seq.mem x st);
   G.is_vertex_set_lemma3 st;
   assert (forall x. Seq.mem x s ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

   assert (forall x. Seq.mem x s ==> color_of_object1 x g == gray);

   assert (is_valid_header v_id g);  
   let g' = colorHeader1 v_id g black in
  
   assert (color_of_object1 v_id g' == black);
   
   let f = objects2 0UL g in
   let f' = objects2 0UL g' in
   assert (f == f');
   get_allocated_block_addresses_lemma g g' v_id black;
   assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
   assert (G.is_vertex_set s);
   G.is_vertex_set_lemma5 st;
   assert (~(Seq.mem v_id s));
   Seq.lemma_mem_snoc s v_id;
   assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem x (objects2 0UL g) /\
                                                        isGrayObject1 x g);
   assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
   assert (color_of_object1 v_id g' == 3UL);
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');
   assert (forall x. Seq.mem x s <==> Seq.mem x (objects2 0UL g') /\
                                                        isGrayObject1 x g');
   let wz = wosize_of_object1 v_id g' in
   assert (is_valid_header v_id g');
   assert (Usize.v wz == Usize.v (getWosize (read_word g v_id)));
   assert (Usize.v wz == Usize.v (getWosize (read_word g' v_id)));
  
   let st1, g1 = fieldPush_spec1 g' s v_id wz 1UL in
   assert (G.is_vertex_set st1);
   assert (Seq.length g == Seq.length g1);
   assert (well_formed_heap2 g1);
   assert (forall x. Seq.mem x st1 ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (forall x. Seq.mem x st1 ==> is_valid_header x g1);
   assert (forall x. Seq.mem x st1 ==> Usize.v x % Usize.v mword == 0);
   assert (forall x. Seq.mem x (objects2 0UL g1) /\ isGrayObject1 x g1 <==>
                                                Seq.mem x st1);
    assert (forall x. Seq.mem x s ==> Seq.mem x st1);
   (*assert (forall x. is_visited x g' ==> is_visited x g1);
   assert (forall x. isGrayBlock x g' ==> isGrayBlock x g1);*)
   assert (get_allocated_block_addresses g' == get_allocated_block_addresses g1);
   assert (objects2 0UL g' == objects2 0UL g1);
   assert (objects2 0UL g == objects2 0UL g1);
   assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
   (st1,g1)


#restart-solver 

#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver

let h_index_field_index_mword_multiple_lemma2 (g:heap{well_formed_heap2 g})
                                             (h_index: hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                                             (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g)})
                                             (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
()
          
let fieldaddress_within_limits_lemma1 (g:heap{well_formed_heap2 g})
                                     (x:hp_addr{is_valid_header x g /\ Seq.mem x (get_allocated_block_addresses g)})
                                     (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))})
                          : Lemma
                            (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                            (ensures (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) = 
 h_index_field_index_mword_multiple_lemma2 g x (getWosize (read_word g x)) i
 
#restart-solver 

let fieldaddress_within_limits_lemma_x_i_all1(g:heap{well_formed_heap2 g})
                                             (x:hp_addr{is_valid_header x g /\ Seq.mem x (get_allocated_block_addresses g)})
                           : Lemma
                             (requires (is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                       is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                             (ensures (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma1 g x))

#restart-solver 

let fieldaddress_within_limits_lemma_x_all1 (g:heap{well_formed_heap2 g})
                                    : Lemma
                                      (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g))
                                      (ensures (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                                        (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)) = 
 Classical.forall_intro (Classical.move_requires (fieldaddress_within_limits_lemma_x_i_all1 g))

#restart-solver

#restart-solver

#restart-solver

let mark5_body_black_nodes_lemma (g:heap{well_formed_heap2 g}) 
                                  (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st) /\
                                    Seq.length st > 0
                                    })
                                
           : Lemma
             (requires (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1))))
                                    
            (ensures Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st))))) = 
assert (~(G.is_emptySet st));
   let v_id = Seq.index st (Seq.length st - 1) in
   let s = Seq.slice st 0 (Seq.length st - 1) in
   assert (color_of_object1 v_id g == gray);
   
   assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
   assert (well_formed_heap2 g);
   slice_mem_lemma st s;
   assert (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (forall x. Seq.mem x s ==> Seq.mem x st);
   G.is_vertex_set_lemma3 st;
   assert (forall x. Seq.mem x s ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

   assert (forall x. Seq.mem x s ==> color_of_object1 x g == gray);

   assert (is_valid_header v_id g);  
   let g' = colorHeader1 v_id g black in
  
   assert (color_of_object1 v_id g' == black);
   
   let f = objects2 0UL g in
   let f' = objects2 0UL g' in
   assert (f == f');
   get_allocated_block_addresses_lemma g g' v_id black;
   assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
   assert (G.is_vertex_set s);
   G.is_vertex_set_lemma5 st;
   assert (~(Seq.mem v_id s));
   Seq.lemma_mem_snoc s v_id;
   assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem x (objects2 0UL g) /\
                                                        isGrayObject1 x g);

   assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
   assert (color_of_object1 v_id g' == 3UL);
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');
   assert (forall x. Seq.mem x s <==> Seq.mem x (objects2 0UL g') /\
                                                        isGrayObject1 x g');
   let wz = wosize_of_object1 v_id g' in
   assert (is_valid_header v_id g');
   assert (Usize.v wz == Usize.v (getWosize (read_word g v_id)));
   assert (Usize.v wz == Usize.v (getWosize (read_word g' v_id)));
   colorHeader1_subset_lemma v_id g;
   
   assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                             (get_black_block_addresses g' (get_allocated_block_addresses g')));

   colorHeader1_black_nodes_lemma  g v_id;

   assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
           Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g')));

   let st1, g1 = fieldPush_spec1 g' s v_id wz 1UL in
   fieldPush_spec1_black_nodes_lemma g' s v_id wz 1UL;
   assert (G.subset_vertices (get_black_block_addresses g' (get_allocated_block_addresses g'))
                             (get_black_block_addresses g1 (get_allocated_block_addresses g1)));

   assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
           Seq.length (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
   ()
 
#restart-solver 

let seq_length_minus_one_is_less_than_seq_length (s:seq Usize.t)
                                 : Lemma
                                   (ensures ((Seq.length s - 1) < Seq.length s)) = ()


#restart-solver


let mark5_body_fieldPush_lemma (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st) /\
                                    Seq.length st > 0
                                    })
                                
                               (v_id:hp_addr{v_id == Seq.index st (Seq.length st - 1) /\ is_valid_header v_id g})
                               (g': heap{g' == colorHeader1 v_id g black})
                               (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                               (wz:wosize{wz == wosize_of_object1 v_id g})
                 : Lemma
                   (requires (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x s ==> is_valid_header x g') /\
                                    (G.is_vertex_set s) /\
                                    (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x s) /\
                             (Usize.v v_id >= 0 /\ Usize.v v_id < heap_size) /\
                               is_valid_header v_id g')
                                                  
                   (ensures fst (mark5_body g st) == fst (fieldPush_spec1 g' s v_id wz 1UL) /\
                            snd (mark5_body g st) == snd (fieldPush_spec1 g' s v_id wz 1UL)) = ()

#restart-solver

#restart-solver

#restart-solver

#restart-solver

let mark5_body_black_nodes_lemma1 (g:heap{well_formed_heap2 g}) 
                               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st) /\
                                    Seq.length st > 0
                                    })
                                
                               (v_id:hp_addr{v_id == Seq.index st (Seq.length st - 1) /\ is_valid_header v_id g})
                               (g': heap{g' == colorHeader1 v_id g black})
                               (s: seq Usize.t {s == (Seq.slice st 0 (Seq.length st - 1))})
                               (wz:wosize{wz == wosize_of_object1 v_id g'})
                 : Lemma
                   (requires (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x s ==> is_valid_header x g') /\
                                    (G.is_vertex_set s) /\
                                    (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x s) /\
                             (Usize.v v_id >= 0 /\ Usize.v v_id < heap_size) /\
                               is_valid_header v_id g')
                   (ensures Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st))))) = 
  assert (Seq.mem v_id st);
  assert (color_of_object1 v_id g <> black);
  
  colorHeader1_subset_lemma v_id g;

  assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                             (get_black_block_addresses g' (get_allocated_block_addresses g')));

  colorHeader1_black_nodes_lemma  g v_id;

  assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
           Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g')));                    
  let st1, g1 = fieldPush_spec1 g' s v_id wz 1UL in
  fieldPush_spec1_black_nodes_lemma g' s v_id wz 1UL;
  assert (G.subset_vertices (get_black_block_addresses g' (get_allocated_block_addresses g'))
                             (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
  assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
           Seq.length (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
  
  mark5_body_fieldPush_lemma g st v_id g' s wz;
  assert (snd (mark5_body g st) == snd (fieldPush_spec1 g' s v_id wz 1UL));
  assert (snd (mark5_body g st) == g1);
  assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
           Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
  ()


#restart-solver 

#restart-solver

#restart-solver

#push-options " --z3rlimit 1000 "// --max_fuel 2 --max_ifuel 4 --using_facts_from 'Prims FStar.Seq'"

#restart-solver 

let stack_slice_only_has_gray_color_lemma (g:heap{well_formed_heap2 g}) 
                                          (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                            (G.is_vertex_set st) /\
                                                            (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                              Seq.mem x st) /\
                                                            Seq.length st > 0
                                                            })
                                          (v_id:hp_addr{v_id == Seq.index st (Seq.length st - 1) /\ is_valid_header v_id g})
                                          (c:color{c == 3UL})
                               : Lemma
                                 (requires (*Usize.v (Seq.index st (Seq.length st - 1)) < heap_size /\  Usize.v (Seq.index st (Seq.length st - 1)) % Usize.v mword == 0*) True)
                                 
                                 (ensures (forall x. Seq.mem x (objects2 0UL  (colorHeader1 v_id(*(Seq.index st (Seq.length st - 1))*) g c) ) /\
                                                  isGrayObject1 x (colorHeader1 v_id(*(Seq.index st (Seq.length st - 1))*) g c)  <==>
                                                  Seq.mem x  (Seq.slice st 0 (Seq.length st - 1)))) = 
let v_id = (Seq.index st (Seq.length st - 1)) in  
let st_slice = Seq.slice st 0 (Seq.length st - 1) in
let g' = colorHeader1 v_id (*(Seq.index st (Seq.length st - 1))*) g c in
assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                              Seq.mem x st);
assert (color_of_object1 v_id g' == 3UL);

slice_mem_lemma st st_slice;
assert (forall x. Seq.mem x st_slice ==> Seq.mem x st);
assert (forall x. Seq.mem x st ==> color_of_object1 x g == gray);
assert (all_mem_st_mem_st__except_v_id_in_stack v_id st st_slice);
assert (color_of_object1 v_id g' == 3UL);
assert (forall x. Seq.mem x st_slice /\ x <> v_id ==> Seq.mem x st);
assert (heap_remains_same_except_index_v_id v_id g g');
assert (forall (x:Usize.t {Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). x <> v_id ==>
           read_word g x == read_word g' x); 
assert (G.is_vertex_set st);
G.is_vertex_set_lemma3 st;
G.is_vertex_set_lemma5 st;
assert (~(Seq.mem v_id st_slice));
assert (forall x. Seq.mem x st_slice ==> color_of_object1 x g' == gray);
Seq.lemma_mem_snoc st_slice v_id;
assert (forall x. Seq.mem x st_slice \/ (x == v_id) <==> Seq.mem x (objects2 0UL g) /\
                                                        isGrayObject1 x g);
objects2_equal_lemma 0UL g g';
assert (objects2 0UL g == objects2 0UL g');
assert (forall x. Seq.mem x st_slice <==> Seq.mem x (objects2 0UL g') /\
                                                        isGrayObject1 x g');
()

let rec mark5 (g:heap{well_formed_heap2 g}) 
               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                                      
          : Pure (heap)
            (requires True)
            (ensures (fun g' -> well_formed_heap2 g))
            (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
  if (G.is_emptySet st) then
   (
      g
   )
 else
   (
      let st', g' = mark5_body g st in
      let v_id = Seq.index st (Seq.length st - 1) in
      assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
      assert (is_valid_header v_id g);

      stack_slice_only_has_gray_color_lemma g st v_id 3UL;

      assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1)));
      
      
      mark5_body_black_nodes_lemma g st;
      
      assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
      
      mark5 g' st'
   )


#restart-solver 

#restart-solver 

let mark_mark_body_lemma (g:heap{well_formed_heap2 g}) 
                         (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                   : Lemma
                     (requires (~(G.is_emptySet st)))
                     (ensures (mark5 g st == mark5 (snd (mark5_body g st)) (fst (mark5_body g st)))) = ()

let mark_mark_body_lemma1 (g:heap{well_formed_heap2 g}) 
                          (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                   : Lemma
                     (requires ((G.is_emptySet st)))
                     (ensures (mark5 g st == g)) = ()

let visited_list_lemma (g:heap{well_formed_heap2 g}) 
                       (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                         (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                         (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                         (G.is_vertex_set vl) /\
                                                                         (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==>
                                                                         Seq.mem x vl)
                                                                       })
                       (x: Usize.t{Usize.v x >= 0 /\ Usize.v x < heap_size /\
                                   (Usize.v x % Usize.v mword == 0) /\
                                 is_valid_header x g /\
                                 isGrayObject1 x g /\
                                 Seq.mem x (get_allocated_block_addresses g) /\
                                 ~(Seq.mem x vl)})
             : Lemma
               (requires (well_formed_allocated_blocks g))
               (ensures (forall y. Seq.mem y (objects2 0UL (colorHeader1 x g black)) /\ isBlackObject1 y (colorHeader1 x g black) <==>
                                                        Seq.mem y (G.insert_to_vertex_set (create_graph_from_heap g) x vl))) = 
let g' = colorHeader1 x g black in  
let grph1 = create_graph_from_heap g in
let vl' = G.insert_to_vertex_set grph1 x vl in
assert (forall x. Seq.mem x vl ==> Seq.mem x vl');
assert (Seq.mem x vl');
assert (isBlackObject1 x g');
assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g ==>
              Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g');
assert (~(exists y. (Seq.mem y vl') /\ ~(Seq.mem y vl) /\ y <> x));
colorHeader1_mem_lemma x g;
assert (~(exists y. (Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g') /\
                ~(Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g) /\
                (x <> y)));
assert (forall y. Seq.mem y (objects2 0UL (colorHeader1 x g black)) /\ isBlackObject1 y (colorHeader1 x g black) <==>
                                                        Seq.mem y (G.insert_to_vertex_set (create_graph_from_heap g) x vl));
()
 


#restart-solver 

#restart-solver
  
let is_vertex_set_slice (g:heap{well_formed_heap2 g}) 
                        (st: seq Usize.t{G.is_vertex_set st /\  (~(G.is_emptySet st)) /\
                                         G.subset_vertices st (get_allocated_block_addresses g)}) 
                         
            : Lemma
              (ensures (G.is_vertex_set (Seq.slice st 0 (Seq.length st - 1)) /\
                        G.subset_vertices (Seq.slice st 0 (Seq.length st - 1)) (get_allocated_block_addresses g))) = 
 G.is_vertex_set_lemma3 st;
 slice_mem_lemma st (Seq.slice st 0 (Seq.length st - 1));
 assert (G.is_vertex_set (Seq.slice st 0 (Seq.length st - 1)));
 ()

#restart-solver 

let is_vertex_set_vl_after_insert (g:heap{well_formed_heap2 g})
                                  (x:Usize.t{Seq.mem x (get_allocated_block_addresses g)})
                                  (vl: seq Usize.t{G.is_vertex_set vl /\
                                                   G.subset_vertices vl (get_allocated_block_addresses g) /\
                                                    ~(Seq.mem x vl)})
                : Lemma
                  (requires (well_formed_allocated_blocks g))
                  (ensures (G.is_vertex_set(G.insert_to_vertex_set (create_graph_from_heap g) x vl) /\
                            Seq.mem x (G.insert_to_vertex_set (create_graph_from_heap g) x vl) /\
                            G.subset_vertices (G.insert_to_vertex_set (create_graph_from_heap g) x vl) (get_allocated_block_addresses g))) = ()




#restart-solver

#restart-solver

let mutual_exclusion_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                           (x:Usize.t{Seq.mem x (get_allocated_block_addresses g)})
                           (st: seq Usize.t{G.is_vertex_set st /\  (~(G.is_emptySet st)) /\
                                         G.subset_vertices st (get_allocated_block_addresses g)}) 
                           (vl: seq Usize.t{G.is_vertex_set vl /\
                                                   G.subset_vertices vl (get_allocated_block_addresses g) /\
                                                    ~(Seq.mem x vl)})
                : Lemma
                  (requires  (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                  (ensures ((forall x. Seq.mem x (Seq.slice st 0 (Seq.length st - 1)) ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x (Seq.slice st 0 (Seq.length st - 1))))))) = 
 let s = Seq.slice st 0 (Seq.length st - 1) in
 assert ((forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
         (forall x. Seq.mem x vl ==> ~(Seq.mem x st))));
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 assert (forall x. Seq.mem x s ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x s));
 ()


#restart-solver 

let mutual_exclusion_lemma1 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                           (x:Usize.t{Seq.mem x (get_allocated_block_addresses g)})
                           (s: seq Usize.t{G.is_vertex_set s /\
                                           G.subset_vertices s (get_allocated_block_addresses g) /\
                                            ~(Seq.mem x s)}) 
                           (vl: seq Usize.t{G.is_vertex_set vl /\
                                            G.subset_vertices vl (get_allocated_block_addresses g) /\
                                             ~(Seq.mem x vl)})
                : Lemma
                  (requires  (forall x. Seq.mem x s ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x s))))
                  (ensures (forall y. Seq.mem y (G.insert_to_vertex_set (create_graph_from_heap g) x vl) ==> ~(Seq.mem x s)) /\
                           (forall y. Seq.mem y s ==> ~(Seq.mem y (G.insert_to_vertex_set (create_graph_from_heap g) x vl)))) = 
let grph = create_graph_from_heap g in
let vl' = G.insert_to_vertex_set (create_graph_from_heap g) x vl in
G.insert_to_vertex_set_mem_negation_lemma grph x vl s;
()      


#restart-solver

#restart-solver 

#restart-solver

#push-options " --z3rlimit 1000"

let dfs_mark_equivalence_body_lemma (g:heap{well_formed_heap2 g}) 
                                    (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })
                                    (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (G.is_vertex_set vl) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                })
                                    (c:color{c == 3UL})

                                    : Lemma
                   (requires G.subset_vertices st (get_allocated_block_addresses g) /\
                             G.subset_vertices vl (get_allocated_block_addresses g) /\
                             (~(G.is_emptySet st)) /\
                             (Seq.length st > 0) /\
                             (well_formed_allocated_blocks g) /\
                             (well_formed_allocated_blocks (snd ( mark5_body g st))) /\
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                             
                   (ensures ((*stack equivalence*) fst ( mark5_body g st) == fst (D.dfs_body (create_graph_from_heap g) st vl) /\
                             
                             (*graph equivalence*)(create_graph_from_heap g == create_graph_from_heap (snd ( mark5_body g st))) /\
                             
                             (*visited list and black nodes set equivalence*)
                              (forall x. Seq.mem x (objects2 0UL (snd (mark5_body g st))) /\
                                    isBlackObject1 x (snd ( mark5_body g st)) <==>
                                                  Seq.mem x (snd (D.dfs_body (create_graph_from_heap g) st vl))))) = 
   assert (~(G.is_emptySet st));
   let v_id = Seq.index st (Seq.length st - 1) in
   let s = Seq.slice st 0 (Seq.length st - 1) in
   assert (color_of_object1 v_id g == gray);
   
   assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
   assert (well_formed_heap2 g);
   slice_mem_lemma st s;
   assert (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (forall x. Seq.mem x s ==> Seq.mem x st);
   G.is_vertex_set_lemma3 st;
   assert (forall x. Seq.mem x s ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

   assert (forall x. Seq.mem x s ==> color_of_object1 x g == gray);

   assert (is_valid_header v_id g);

   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;

   assert (G.subset_vertices st (get_allocated_block_addresses g));
   assert (forall x. Seq.mem x st ==> Seq.mem x (get_allocated_block_addresses g));
   assert (Seq.mem v_id (get_allocated_block_addresses g));
   assert (is_fields_within_limit1 v_id (getWosize (read_word g v_id)));
   
   let g' = colorHeader1 v_id g black in
   assert (well_formed_heap2 g');
   field_limits_allocated_blocks_lemma g';
   field_contents_within_limits_allocated_blocks_lemma g';   
  
   assert (color_of_object1 v_id g' == black);
   let f = objects2 0UL g in
   let f' = objects2 0UL g' in
   assert (f == f');
   get_allocated_block_addresses_lemma g g' v_id black;
   assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
   assert (G.is_vertex_set s);
   G.is_vertex_set_lemma5 st;
   assert (~(Seq.mem v_id s));
   stack_slice_only_has_gray_color_lemma g st v_id c;
   assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g'  <==> Seq.mem x s);
   let wz = wosize_of_object1 v_id g' in
   assert (is_valid_header v_id g');
   assert (Usize.v wz == Usize.v (getWosize (read_word g v_id)));
   assert (Usize.v wz == Usize.v (getWosize (read_word g' v_id)));
  
   let st1, g1 = fieldPush_spec1 g' s v_id wz 1UL in
   assert (G.is_vertex_set st1);
   assert (Seq.length g == Seq.length g1);
   assert (well_formed_heap2 g1); 

   colorHeader1_Lemma v_id g c;

   
   
   assert ((get_allocated_block_addresses g == get_allocated_block_addresses g'));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x)));
   assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
   assert (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
          
            
   fieldaddress_within_limits_lemma_x_all g;
   assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);

   assert  (forall i x.  Seq.mem x (get_allocated_block_addresses g') /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g' x))) ==> 
                                                   (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   well_formed_allocated_blocks_lemma g v_id c g'; 
   assert (well_formed_allocated_blocks g');
   assert (Seq.mem v_id (get_allocated_block_addresses g'));
   assert ((forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                              (forall x. Seq.mem x s ==> is_valid_header x g) /\
                                                                              (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                                                                              (G.is_vertex_set s) /\
                                                                              (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                                                   Seq.mem x s));
   
   assert (Usize.v v_id >= 0 /\ Usize.v v_id < heap_size /\
          (Usize.v v_id % Usize.v mword == 0) /\
           is_valid_header v_id g);                              
                                                                             
   assert (is_valid_header v_id g');  
   assert (Usize.v wz == Usize.v (getWosize (read_word g' v_id)));
           
   fieldPush_spec1_well_formed_allocated_blocks_lemma  g' s v_id wz 1UL;
   mark5_body_fieldPush_lemma g st v_id g' s wz;
   assert (well_formed_allocated_blocks g1);
   assert (well_formed_allocated_blocks (snd (mark5_body g st)));
 
   (*compare with dfs_body---------------------------------------------------------------------------------------------------------------*)
    let grph1 = create_graph_from_heap g in
    let x = G.get_last_elem grph1 st in
    assert (x == Seq.index st (Seq.length st - 1));
    assert (x == v_id);

    let xs = G.get_first grph1 st in
    assert (xs == Seq.slice st 0 (Seq.length st - 1));
    assert (s == xs);

    let grph2 = create_graph_from_heap g' in
             
    (*-----Prove grph1 and grph2 are equal*)
    create_graph_from_heap_lemma g v_id black;
     assert (grph1 == grph2);

    let vl' = G.insert_to_vertex_set grph1 x vl in
    visited_list_lemma g vl x;
    assert (forall y. Seq.mem y (objects2 0UL g') /\ isBlackObject1 y g' <==>
                                                        Seq.mem y vl');

    colorHeader1_subset_lemma v_id g;
           

    let _ = G.get_last_mem_lemma grph1 st in
  

   colorHeader1_black_nodes_lemma  g v_id;

   fieldPush_spec1_graph_lemma g' s v_id wz 1UL;
            
             
   let grph3 = create_graph_from_heap g1 in
   assert (grph2 == grph3);
   fieldPush_spec1_black_nodes_lemma g' s v_id wz 1UL;
   fieldPush_spec1_black_nodes_lemma1 g' s v_id wz 1UL;

   assert (forall y. Seq.mem y (get_black_block_addresses g' (get_allocated_block_addresses g')) <==>
                           Seq.mem y (get_black_block_addresses g1 (get_allocated_block_addresses g1)));
 
   let sl = G.successors grph1 x in
   let _ = G.insert_to_vertex_set_mem_negation_lemma grph1 x vl xs in
   assert (forall x. Seq.mem x (objects2 0UL g1) /\
                                    isBlackObject1 x g1 <==>
                                                  Seq.mem x vl');
             
   assert (grph3 == grph1);
   assert (G.subset_vertices st (get_allocated_block_addresses g));
   is_vertex_set_slice g st;
   
   assert (G.is_vertex_set (Seq.slice st 0 (Seq.length st - 1)));
   assert (G.is_vertex_set s);
   assert (forall x. Seq.mem x st ==> Seq.mem x (get_allocated_block_addresses g));
   assert (forall x. Seq.mem x s ==> Seq.mem x st);
   assert (forall x. Seq.mem x s ==> Seq.mem x (get_allocated_block_addresses g));
   assert (G.subset_vertices s (get_allocated_block_addresses g));
   is_vertex_set_vl_after_insert g x vl;
   assert (G.is_vertex_set vl' /\ G.subset_vertices vl' (get_allocated_block_addresses g));

   mutual_exclusion_lemma g v_id st vl;
   mutual_exclusion_lemma1 g v_id s vl;
   assert (forall x. Seq.mem x s ==> ~(Seq.mem x vl'));
   assert (forall x. Seq.mem x vl' ==> ~(Seq.mem x s));

   let r' = G.successor_push_itr1 sl vl' xs 0 in
   G.successor_push_itr1_subset_lemma grph1 sl vl' xs 0;

   assert (is_fields_within_limit1 v_id (getWosize (read_word g' v_id)));
   assert (is_fields_contents_within_limit2 v_id (getWosize (read_word g' v_id)) g'); 
   assert (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g' v_id)) ==> 
                            (Usize.v v_id  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0);

   assert (well_formed_heap2 g' /\ well_formed_allocated_blocks g');
   assert (is_valid_header v_id g');
   assert (Seq.mem v_id (get_allocated_block_addresses g'));
   
   graph_successors_length_lemma g' v_id;

   assert (Seq.length (G.successors (create_graph_from_heap g') v_id) <= Usize.v (getWosize (read_word g' v_id)));
   
   graph_successors_from_0_and_heap_field_pointers_from_1_are_equal g' v_id;

   assert (graph_successors_create_from_an_index g' v_id (G.successors (create_graph_from_heap g') v_id) 0UL ==
             create_successors_list_for_h_index g' v_id (getWosize (read_word g' v_id)) 1UL);
             
   //fieldPush_spec_successor_push_itr_equivalence_lemma1 g' s v_id wz 1UL vl';
   fieldPush_spec_successor_push_itr_equivalence_lemma2 g' s v_id wz 1UL 0UL vl';
   assert ((fst (fieldPush_spec1 g' s v_id wz 1UL)) == G.successor_push_itr1 (G.successors (create_graph_from_heap g') v_id)
                                                                                                       (vl')
                                                                                                       (s)
                                                                                                        0);
   assert (st1 == r'); 
   assert (fst (D.dfs_body (create_graph_from_heap g) st vl) == r');
   assert (fst ( mark5_body g st) == st1);
   assert (fst ( mark5_body g st) == fst (D.dfs_body (create_graph_from_heap g) st vl));
             
   ()


#restart-solver 

#restart-solver

let well_formed_allocated_blocks_mark5_body_heap (g:heap{well_formed_heap2 g}) 
                                                 (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })
                                                 (c:color{c == 3UL})
                                 : Lemma
                                   (requires (well_formed_allocated_blocks g /\
                                             ~(G.is_emptySet st)))
                                   (ensures (well_formed_allocated_blocks (snd (mark5_body g st)))) = 
 assert (~(G.is_emptySet st));
   let v_id = Seq.index st (Seq.length st - 1) in
   let s = Seq.slice st 0 (Seq.length st - 1) in
   assert (color_of_object1 v_id g == gray);
   
   assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
   assert (well_formed_heap2 g);
   slice_mem_lemma st s;
   assert (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (forall x. Seq.mem x s ==> Seq.mem x st);
   G.is_vertex_set_lemma3 st;
   assert (forall x. Seq.mem x s ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

   assert (forall x. Seq.mem x s ==> color_of_object1 x g == gray);

   assert (is_valid_header v_id g);
   
   let g' = colorHeader1 v_id g black in
  
   assert (color_of_object1 v_id g' == black);
   let f = objects2 0UL g in
   let f' = objects2 0UL g' in
   assert (f == f');
   get_allocated_block_addresses_lemma g g' v_id black;
   assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
   assert (G.is_vertex_set s);
   G.is_vertex_set_lemma5 st;
   assert (~(Seq.mem v_id s));
   stack_slice_only_has_gray_color_lemma g st v_id c;
   assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g'  <==> Seq.mem x s);
   let wz = wosize_of_object1 v_id g' in
   assert (is_valid_header v_id g');
   assert (Usize.v wz == Usize.v (getWosize (read_word g v_id)));
   assert (Usize.v wz == Usize.v (getWosize (read_word g' v_id)));
  
   let st1, g1 = fieldPush_spec1 g' s v_id wz 1UL in
   assert (G.is_vertex_set st1);
   assert (Seq.length g == Seq.length g1);
   assert (well_formed_heap2 g1); 
   assert ((get_allocated_block_addresses g == get_allocated_block_addresses g') /\
            (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
            (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
            (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
            (forall x. Seq.mem x (get_allocated_block_addresses g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g'));                                 

   fieldaddress_within_limits_lemma_x_all g;
   assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);

   (*assert  (forall i x.  Seq.mem x (get_allocated_block_addresses g') /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);*)
   well_formed_allocated_blocks_lemma g v_id c g'; 
   assert (well_formed_allocated_blocks g');
   let st1, g1 = fieldPush_spec1 g' s v_id wz 1UL in
   assert (Seq.mem v_id (get_allocated_block_addresses g'));
   assert ((forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                              (forall x. Seq.mem x s ==> is_valid_header x g) /\
                                                                              (forall x. Seq.mem x s ==> Usize.v x % Usize.v mword == 0) /\
                                                                              (G.is_vertex_set s) /\
                                                                              (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                                                   Seq.mem x s));
   
   assert (Usize.v v_id >= 0 /\ Usize.v v_id < heap_size /\
          (Usize.v v_id % Usize.v mword == 0) /\
           is_valid_header v_id g);                              
                                                                             
   assert (is_valid_header v_id g');  
   assert (Usize.v wz == Usize.v (getWosize (read_word g' v_id)));
           
   fieldPush_spec1_well_formed_allocated_blocks_lemma  g' s v_id wz 1UL;
   mark5_body_fieldPush_lemma g st v_id g' s wz;
   assert (well_formed_allocated_blocks g1);
   assert (well_formed_allocated_blocks (snd (mark5_body g st)));
   ()

#restart-solver 

#restart-solver 

#restart-solver

//#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"

#restart-solver

let rec well_formed_heap2_after_mark5 (g:heap{well_formed_heap2 g}) 
                                  (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                      : Lemma
                        (ensures well_formed_heap2 (mark5 g st))
                        (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
  if (G.is_emptySet st) then
   (
      ()
   )
 else
   (
      let st', g' = mark5_body g st in
      let v_id = Seq.index st (Seq.length st - 1) in
      assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
      assert (is_valid_header v_id g);

      stack_slice_only_has_gray_color_lemma g st v_id 3UL;

      assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1)));
      
      
      mark5_body_black_nodes_lemma g st;
      
      assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
      assert (well_formed_heap2 g');
      
      let g'' = mark5 g' st' in
      well_formed_heap2_after_mark5 g' st';
      assert (well_formed_heap2 g'');
      ()
   )

#restart-solver 

let rec well_formed_allocated_blocks_mark5 (g:heap{well_formed_heap2 g}) 
                                           (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })
                                            (c:color{c == 3UL})
                             : Lemma
                               (requires (well_formed_allocated_blocks g) /\ (well_formed_heap2 (mark5 g st)))
                               (ensures (well_formed_allocated_blocks (mark5 g st))) 
                                (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                                                G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
  if (G.is_emptySet st) then
   (
      ()
   )
 else
   (
      let st', g' = mark5_body g st in
      let v_id = Seq.index st (Seq.length st - 1) in
      assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
      assert (is_valid_header v_id g);

      stack_slice_only_has_gray_color_lemma g st v_id 3UL;

      assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1)));
      
      
      mark5_body_black_nodes_lemma g st;
      
      assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
      assert (well_formed_heap2 g');
      well_formed_allocated_blocks_mark5_body_heap g st c;
      assert (well_formed_allocated_blocks g');
      
      let g'' = mark5 g' st' in
      well_formed_heap2_after_mark5 g' st';
      assert (well_formed_heap2 g'');
      well_formed_allocated_blocks_mark5 g' st' c;
      assert (well_formed_allocated_blocks g'');
      ()
   )

#reset-options "--z3rlimit 2000"

#restart-solver

let rec dfs_mark_equivalence_lemma (g:heap{well_formed_heap2 g}) 
                                   (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })

                                   (*assumes Insertion barrier*)
                                   (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (G.is_vertex_set vl) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                }) 

                                   (c:color{c == 3UL})
                                
                 : Lemma
                   (requires G.subset_vertices st (get_allocated_block_addresses g) /\
                             G.subset_vertices vl (get_allocated_block_addresses g) /\
                             (well_formed_allocated_blocks g) /\
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                             
                   (ensures (forall x. Seq.mem x (objects2 0UL (mark5 g st)) /\ isBlackObject1 x (mark5 g st) <==>
                                  Seq.mem x (D.dfs (create_graph_from_heap g)
                                            st
                                            vl))) 

                    (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st])= 
 if (G.is_emptySet st) then
   (
      ()
   )
 else
   (
     let st', g' = mark5_body g st in
     assert (G.is_vertex_set st' /\
             (Seq.length g == Seq.length g') /\
             (well_formed_heap2 g') /\
             (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
             (forall x. Seq.mem x st' ==> is_valid_header x g') /\
             (forall x. Seq.mem x (objects2 0UL g') /\
                                        isGrayObject1 x g' <==>
                                               Seq.mem x st'));

     assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
     assert (objects2 0UL g == objects2 0UL g');

     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header v_id g);

     stack_slice_only_has_gray_color_lemma g st v_id c;

     assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1)));
                            
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g')) > 
                    Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)));

     let g1 = mark5 g' st' in
     mark_mark_body_lemma g st;
     assert (mark5 g st == mark5 g' st');
     let grph1 = create_graph_from_heap g in
     assert (Seq.equal (grph1.vertices) (get_allocated_block_addresses g));
     assert (G.subset_vertices st (get_allocated_block_addresses g));
     assert (G.subset_vertices st grph1.vertices);
     let _ = G.negation_nonEmpty_implies_empty st in
     assert (G.nonEmpty_set st);
     let st1,vl1 = D.dfs_body grph1 st vl in
     well_formed_allocated_blocks_mark5_body_heap g st c;
     assert (well_formed_allocated_blocks g');
     let grph2 = create_graph_from_heap g' in
     assert (grph1 == grph1);
     
     dfs_mark_equivalence_body_lemma g st vl c;

     assert (st' == st1);
     assert (grph1 == grph2);
     assert (forall x. Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g' <==>
                                                  Seq.mem x vl1);

     let vl2 = D.dfs grph1 st1 vl1 in
     D.dfs_lemma grph1 st vl ;
     assert (D.dfs grph1 st vl == D.dfs grph1 st1 vl1);
     dfs_mark_equivalence_lemma g' st' vl1 c;
     assert (forall x. Seq.mem x (objects2 0UL (mark5 g' st')) /\ isBlackObject1 x (mark5 g' st') <==>
                                  Seq.mem x (D.dfs (create_graph_from_heap g')
                                            st'
                                            vl1));
     assert (forall x. Seq.mem x (objects2 0UL (mark5 g st)) /\ isBlackObject1 x (mark5 g st) <==>
                                  Seq.mem x (D.dfs grph1 st vl));
     ()
   )



#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"


let dfs_reachability_in_heap_forward_lemma (g:heap{well_formed_heap2 g}) 
                                           (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })

                                
                                           (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (G.is_vertex_set vl) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                }) 

                                          

                                          (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                         (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                         (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                         (G.is_vertex_set h_list)})
                   :Lemma
                   (requires (G.subset_vertices st (get_allocated_block_addresses g)) /\
                             (G.subset_vertices vl (get_allocated_block_addresses g)) /\
                             (well_formed_allocated_blocks g) /\
                             
                             (G.subset_vertices h_list (get_allocated_block_addresses g)) /\ 
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))) /\
                             (forall x. Seq.mem x st ==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g) o x z1)) /\ 
                             (forall x. Seq.mem x vl ==> (exists o (z1: G.reach (create_graph_from_heap g) o x). Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g) o x z1)))
                             
                   (ensures (forall x. Seq.mem x (D.dfs (create_graph_from_heap g) st vl) ==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g) o x z1))) = 
 D.dfs_lemma_forward (create_graph_from_heap g) st vl h_list;
 assert (forall x. Seq.mem x (D.dfs (create_graph_from_heap g) st vl) ==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g) o x z1));
 ()     

let mark_reachability_in_heap_forward_lemma (g:heap{well_formed_heap2 g}) 
                                           (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })

                                
                                           (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (G.is_vertex_set vl) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                }) 

                                          (c:color{c == 3UL})

                                          (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                         (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                         (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                         (G.is_vertex_set h_list)})
                   :Lemma
                   (requires (G.subset_vertices st (get_allocated_block_addresses g)) /\
                             (G.subset_vertices vl (get_allocated_block_addresses g)) /\
                             (well_formed_allocated_blocks g) /\
                             (well_formed_heap2 (mark5 g st)) /\
                             (well_formed_allocated_blocks (mark5 g st)) /\
                             (G.subset_vertices h_list (get_allocated_block_addresses g)) /\ 
                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))) /\
                             (forall x. Seq.mem x st ==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g) o x z1)) /\ 
                             (forall x. Seq.mem x vl ==> (exists o (z1: G.reach (create_graph_from_heap g) o x). Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g) o x z1)))
                             
                   (ensures (forall x. Seq.mem x (objects2 0UL (mark5 g st)) /\ isBlackObject1 x (mark5 g st) ==> 
                                               (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g) o x z1))) = 

dfs_mark_equivalence_lemma g st vl c;
dfs_reachability_in_heap_forward_lemma g st vl h_list;
()
                   
let dfs_reachability_in_heap_backward_lemma (g:heap{well_formed_heap2 g}) 
                                            (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })

                                
                                            (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (G.is_vertex_set vl) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                }) 

                                          

                                           (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                         (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                         (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                         (G.is_vertex_set h_list)})
                          : Lemma
                            (requires (G.subset_vertices st (get_allocated_block_addresses g)) /\
                                      (G.subset_vertices vl (get_allocated_block_addresses g)) /\
                                      (well_formed_allocated_blocks g) /\
                             
                                      (G.subset_vertices h_list (get_allocated_block_addresses g)) /\ 
                                      (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                                      (forall x. Seq.mem x vl ==> ~(Seq.mem x st))) /\
                                      (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==> 
                                          (Seq.mem x vl \/ (exists y (z3: G.reach (create_graph_from_heap g) y x). G.reachfunc (create_graph_from_heap g) y x z3 /\ Seq.mem y st))) /\
                                      (forall c b (r_cb: G.reach (create_graph_from_heap g) c b). (Seq.mem c vl /\ G.reachfunc (create_graph_from_heap g) c b r_cb /\ ~(c = b)) ==>
                                           (Seq.mem b vl \/ 
                                            Seq.mem b st \/ 
                                            (exists d. Seq.mem d st /\ Seq.mem d (G.vertices_in_path (create_graph_from_heap g) c b r_cb)))))
                            (ensures (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==> 
                                                        Seq.mem x (D.dfs7 (create_graph_from_heap g) st vl))) = 
D.dfs7_lemma_backward (create_graph_from_heap g) st vl h_list;
()

let dfs_reachability_in_heap_backward_lemma1 (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })

                                
                                             (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (G.is_vertex_set vl) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                }) 

                                          

                                            (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                         (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                         (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                         (G.is_vertex_set h_list)})
                          : Lemma
                            (requires (G.subset_vertices st (get_allocated_block_addresses g)) /\
                                      (G.subset_vertices vl (get_allocated_block_addresses g)) /\
                                      (well_formed_allocated_blocks g) /\
                             
                                      (G.subset_vertices h_list (get_allocated_block_addresses g)) /\ 
                                      (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                                      (forall x. Seq.mem x vl ==> ~(Seq.mem x st))) /\
                                      (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==> 
                                          (Seq.mem x vl \/ (exists y (z3: G.reach (create_graph_from_heap g) y x). G.reachfunc (create_graph_from_heap g) y x z3 /\ Seq.mem y st))) /\
                                      (forall c b (r_cb: G.reach (create_graph_from_heap g) c b). (Seq.mem c vl /\ G.reachfunc (create_graph_from_heap g) c b r_cb /\ ~(c = b)) ==>
                                           (Seq.mem b vl \/ 
                                            Seq.mem b st \/ 
                                            (exists d. Seq.mem d st /\ Seq.mem d (G.vertices_in_path (create_graph_from_heap g) c b r_cb)))))
                            (ensures (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==> 
                                                        Seq.mem x (D.dfs (create_graph_from_heap g) st vl))) = 
dfs_reachability_in_heap_backward_lemma g st vl h_list;
D.dfs_equality_lemma (create_graph_from_heap g) st vl;
()

let mark_reachability_in_heap_backward_lemma1 (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })

                                
                                             (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (G.is_vertex_set vl) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                }) 

                                          

                                            (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                         (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                         (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                         (G.is_vertex_set h_list)})
                                            (c:color{c == 3UL})
                          : Lemma
                            (requires (G.subset_vertices st (get_allocated_block_addresses g)) /\
                                      (G.subset_vertices vl (get_allocated_block_addresses g)) /\
                                      (well_formed_allocated_blocks g) /\
                             
                                      (G.subset_vertices h_list (get_allocated_block_addresses g)) /\ 
                                      (well_formed_heap2 (mark5 g st)) /\
                                      (well_formed_allocated_blocks (mark5 g st)) /\
                                      (forall x. Seq.mem x st ==> ~(Seq.mem x vl) /\
                                      (forall x. Seq.mem x vl ==> ~(Seq.mem x st))) /\
                                      (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==> 
                                          (Seq.mem x vl \/ (exists y (z3: G.reach (create_graph_from_heap g) y x). G.reachfunc (create_graph_from_heap g) y x z3 /\ Seq.mem y st))) /\
                                      (forall c b (r_cb: G.reach (create_graph_from_heap g) c b). (Seq.mem c vl /\ G.reachfunc (create_graph_from_heap g) c b r_cb /\ ~(c = b)) ==>
                                           (Seq.mem b vl \/ 
                                            Seq.mem b st \/ 
                                            (exists d. Seq.mem d st /\ Seq.mem d (G.vertices_in_path (create_graph_from_heap g) c b r_cb)))))
                            (ensures (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==> 
                                              Seq.mem x (objects2 0UL (mark5 g st)) /\ isBlackObject1 x (mark5 g st))) = 
dfs_mark_equivalence_lemma g st vl c;
dfs_reachability_in_heap_backward_lemma1 g st vl h_list;
()

#reset-options "--z3rlimit 500"





/// Sweep Implementation - Without merging of blue blocks.
/// Essential pre-condition - There are no grey objects in the heap.



let wosize_plus_times_mword_multiple_of_mword1 (wz:wosize)
                     :Lemma 
                      (ensures (Usize.v (Usize.mul (Usize.add wz 1UL) mword) % Usize.v mword == 0)) = ()
                      
let noGreyObjects (g:heap{well_formed_heap2 g}) = (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray)) 

let objects2_mem_lemma1_app (h_index: hp_addr)
                            (g:heap)
                           
                      
          : Lemma 
            (requires (Seq.length (objects2 0UL g) > 0 /\ Seq.mem h_index (objects2 0UL g) /\ 
                        Usize.v (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) < heap_size))
            (ensures (Seq.mem (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) (objects2 0UL g))) = 
  
  let s = objects2 0UL g in
  objects2_mem_lemma1 0UL g;
  let h_index_new = Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword) in
  assert (Usize.v h_index_new < heap_size);
  assert (Seq.mem h_index_new s);
  ()

let getNextHeader (g:heap{well_formed_heap2 g})
                  (h_index:hp_addr{is_valid_header h_index g}) 
          : Tot (h_next: hp_addr{ (let wz =  getWosize (read_word g h_index) in
                                  let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                                   h_next == (if (Usize.v h_index_new < heap_size) then 
                                   (
                                        h_index_new
                                   )
                                   else
                                   (
                                        h_index
                                   ))) /\ is_valid_header h_next g}) = 
          
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 wosize_plus_times_mword_multiple_of_mword1 wz;
 sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
 assert (Usize.v h_index_new % Usize.v mword == 0);
 if (Usize.v h_index_new < heap_size) then
 (
    objects2_mem_lemma1_app h_index g;
    assert (is_valid_header h_index_new g);
    h_index_new
 )
 else
 (
   h_index // if the return of getNextHeader g h_index == h_index then there are no next headers, this is the last object in the heap
 )



let noContiguousBlueObjects (g:heap{well_formed_heap2 g}) = 
  ~(forall x y. is_valid_header x g /\ is_valid_header y g /\ x <> y /\ getNextHeader g x == y ==> color_of_object1 x g == blue /\ color_of_object1 y g == blue)

let noContiguousBlueObjects1 (g:heap{well_formed_heap2 g}) = 
~(exists x y. is_valid_header x g /\ is_valid_header y g /\ x <> y /\ getNextHeader g x == y /\ color_of_object1 x g == blue /\ color_of_object1 y g == blue)

#restart-solver 

#restart-solver 

#reset-options "--z3rlimit 500"

#pop-options
#pop-options

#pop-options

#push-options "--z3rlimit 500"

#restart-solver 

//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver 

let update_wosize_of_header (v_id:hp_addr)  
                            (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                            (wz:wosize)
             : Tot (g': heap{Seq.length g == Seq.length g' /\
                            (length (slice g' (Usize.v v_id) ((Usize.v v_id) + (Usize.v mword))) = 8) /\
                             read_word g' v_id == makeHeader (wz) (color_of_object1 v_id g) (tag_of_object1 v_id g) /\
                             heap_remains_same_except_index_v_id v_id g g' /\
                             color_of_object1 v_id g' == color_of_object1 v_id g /\
                             wosize_of_object1 v_id g' == wz /\
                             tag_of_object1 v_id g' == tag_of_object1 v_id g 
                             }) = 
 let c = getColor (read_word g v_id) in
 let tg = getTag (read_word g v_id) in  
 let h = makeHeader wz c tg in
 assert (wz == getWosize h);
 assert (c == getColor h);
 assert (tg == getTag h);
 assert (Usize.v v_id >= 0);
 assert (Usize.v v_id < heap_size);
 assert (Usize.v v_id < Seq.length g);
 assert (well_formed_heap2 g);
 let h_index = v_id in
 assert (Seq.mem h_index (objects2 0UL g));
 assert (Seq.length (objects2 0UL g) > 0);
 lemma_len_slice g (Usize.v h_index) ((Usize.v h_index) + (Usize.v mword));
 
 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 
 assert (forall (x:hp_addr). x <> h_index ==> read_word g x == read_word g' x);
 assert (heap_remains_same_except_index_v_id v_id g g' /\
                             color_of_object1 v_id g' == color_of_object1 v_id g /\
                             wosize_of_object1 v_id g' == wz /\
                             tag_of_object1 v_id g' == tag_of_object1 v_id g);
 assert (Seq.length g == Seq.length g');
 g'


#restart-solver 

#restart-solver 

let rec no_grey_objects_after_mark5 (g:heap{well_formed_heap2 g}) 
                                (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                      : Lemma
                        (requires (well_formed_heap2 (mark5 g st)))
                        (ensures (noGreyObjects (mark5 g st))) 
                         (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
if (G.is_emptySet st) then
   (
      assert (noGreyObjects g);
      ()
   )
 else
   (
      let st', g' = mark5_body g st in
      let v_id = Seq.index st (Seq.length st - 1) in
      assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
      assert (is_valid_header v_id g);

      stack_slice_only_has_gray_color_lemma g st v_id 3UL;

      assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1)));
      
      
      mark5_body_black_nodes_lemma g st;
      
      assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
      assert (well_formed_heap2 g');
      
      let g'' = mark5 g' st' in
      well_formed_heap2_after_mark5 g' st';
      assert (well_formed_heap2 g'');
      no_grey_objects_after_mark5 g' st';
      assert (noGreyObjects g'');
      ()
    )

#restart-solver 

#pop-options

#pop-options

#push-options "--z3rlimit 100"

#push-options "--split_queries"

#restart-solver

let colorHeader1_wosizeLemma  (v_id:hp_addr)  
                              (g:heap{well_formed_heap2 g /\ is_valid_header v_id g}) 
                              (c:color)
                              (h_id:hp_addr)
              : Lemma
                (ensures (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word (colorHeader1 v_id g c) x)) /\
                            (objects2 h_id g == objects2 h_id (colorHeader1 v_id g c))) = 
 let wz = getWosize (read_word g v_id) in
 let tg = getTag (read_word g v_id) in  
 let h = makeHeader wz c tg in
 assert (wz == getWosize h);
 assert (c == getColor h);
 assert (tg == getTag h);
 assert (Usize.v v_id >= 0);
 assert (Usize.v v_id < heap_size);
 assert (Usize.v v_id < Seq.length g);
 assert (well_formed_heap2 g);
 let h_index = v_id in
 assert (Seq.mem h_index (objects2 0UL g));
 assert (Seq.length (objects2 0UL g) > 0);

 let g' = write_word g h_index h in
 write_word_lemma g h_index h;
 assert (forall (x:hp_addr). x <> h_index ==> read_word g x == read_word g' x);
 assert (heap_remains_same_except_index_v_id h_index g g');
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). x <> h_index ==> getWosize (read_word g x) == getWosize (read_word g' x));
 assert (getWosize (read_word g h_index) == getWosize (read_word g' h_index));
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x));
 objects2_equal_lemma h_id g g';
 assert (objects2 h_id g == objects2 h_id g');
 ()


let mutually_exclusive_sets (s1: seq Usize.t {G.is_vertex_set s1})
                            (s2: seq Usize.t {G.is_vertex_set s2}) =
 (forall x. Seq.mem x s1 ==> ~(Seq.mem x s2)) /\
 (forall x. Seq.mem x s2 ==> ~(Seq.mem x s1))
              
#restart-solver 

let push_to_stack_mutual_exclusivity_lemma (g:heap{well_formed_heap2 g}) 
                                           (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                           (h_list_tl: seq Usize.t{(forall x. Seq.mem x h_list_tl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list_tl ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list_tl ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list_tl)}) 
                                          (x: hp_addr{~(Seq.mem x st) /\
                                                     (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                     (Usize.v x % Usize.v mword == 0) /\
                                                     is_valid_header x g})
                     : Lemma
                       (requires ~(Seq.mem x h_list_tl) /\ mutually_exclusive_sets st h_list_tl)
                       (ensures (mutually_exclusive_sets (fst (push_to_stack2 g st x)) h_list_tl)) = ()

#restart-solver

let create_root_stack_and_gray_modified_heap_body (g:heap{well_formed_heap2 g}) 
                                                 (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                 (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)})          
                                                  
      : Pure (stack_heap_pair) 
             (requires (mutually_exclusive_sets st h_list) /\ Seq.length h_list > 0 /\ (G.is_vertex_set (tail h_list)))
             (ensures fun st_hp -> well_formed_heap2 (snd st_hp) /\
                               (objects2 0UL (snd st_hp)) == (objects2 0UL g) /\
                                    (forall x. Seq.mem x (fst st_hp) ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x (fst st_hp) ==> is_valid_header x (snd st_hp)) /\                                                      
                                    (forall x. Seq.mem x (fst st_hp) ==> Usize.v x % Usize.v mword == 0) /\                                                       
                                    (G.is_vertex_set (fst st_hp)) /\
                                    (mutually_exclusive_sets (fst st_hp) (tail h_list)) /\
                                    (forall x. Seq.mem x (objects2 0UL (snd st_hp)) /\ isGrayObject1 x (snd st_hp) <==>  Seq.mem x (fst st_hp))) = 
     assert (Seq.length h_list > 0);
     let hd = Seq.head h_list in
     let tl = Seq.tail h_list in
     
     assert (G.is_vertex_set st);
     assert (G.is_vertex_set h_list);

     assert (~(Seq.mem hd st));
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     assert (mutually_exclusive_sets st tl);

     G.is_vertex_set_lemma4 h_list;
     assert (~(Seq.mem hd tl));
     assert (~(Seq.mem hd st));
     let st', g' = push_to_stack2 g st hd in
     assert (mutually_exclusive_sets st' tl);
     (st',g')
         

let rec create_root_stack_and_gray_modified_heap (g:heap{well_formed_heap2 g}) 
                                                 (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                 (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)})          
                                                  
      : Pure (stack_heap_pair) 
         (requires mutually_exclusive_sets st h_list)
         (ensures fun st_hp ->  well_formed_heap2 (snd st_hp) /\
                             (objects2 0UL (snd st_hp)) == (objects2 0UL g) /\
                                    (forall x. Seq.mem x (fst st_hp) ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x (fst st_hp) ==> is_valid_header x (snd st_hp)) /\                                                      
                                    (forall x. Seq.mem x (fst st_hp) ==> Usize.v x % Usize.v mword == 0) /\                                                       
                                    (G.is_vertex_set (fst st_hp)) /\
                                    (forall x. Seq.mem x (objects2 0UL (snd st_hp)) /\ isGrayObject1 x (snd st_hp) <==>  Seq.mem x (fst st_hp)))
         (decreases (Seq.length h_list)) =
  
  if Seq.length h_list = 0 then 
  (
     (st,g)
  )
  else
  (
     let hd = Seq.head h_list in
     let tl = Seq.tail h_list in
     
     assert (G.is_vertex_set st);
     assert (G.is_vertex_set h_list);

     assert (~(Seq.mem hd st));
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     assert (mutually_exclusive_sets st tl);

     G.is_vertex_set_lemma4 h_list;
     assert (~(Seq.mem hd tl));
     assert (~(Seq.mem hd st));
     let st', g' = push_to_stack2 g st hd in
     assert (mutually_exclusive_sets st' tl);
    
     let st1, g1 = create_root_stack_and_gray_modified_heap g' st' (tail h_list) in
     (st1,g1)
  )

let create_root_stack_and_gray_modified_heap_base_lemma1 (g:heap{well_formed_heap2 g}) 
                                                         (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                        (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)})  
                                                        (i:Usize.t {(Usize.v i == Seq.length h_list) /\ 
                                                                      (forall x. Seq.mem x (Seq.slice h_list (Usize.v i) (Seq.length h_list)) ==> 
                                                                                                       Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x (Seq.slice h_list (Usize.v i) (Seq.length h_list)) ==> 
                                                                                     Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x (Seq.slice h_list (Usize.v i) (Seq.length h_list)) ==> 
                                                                                       is_valid_header x g) /\
                                                                      (G.is_vertex_set (Seq.slice h_list (Usize.v i) (Seq.length h_list)))})
                                                  
      : Lemma
        (requires mutually_exclusive_sets st (Seq.slice h_list (Usize.v i) (Seq.length h_list)))
        (ensures (create_root_stack_and_gray_modified_heap g st (Seq.slice h_list (Usize.v i) (Seq.length h_list)) == (st,g))) = ()

#restart-solver 

let create_root_stack_and_gray_modified_heap_rec_lemma2 (g:heap{well_formed_heap2 g}) 
                                                         (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                        (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)})  
                                                        (i:UInt32.t {(UInt32.v i < Seq.length h_list) /\ 
                                                                      (forall x. Seq.mem x (Seq.slice h_list (UInt32.v i) (Seq.length h_list)) ==> 
                                                                                                       Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x (Seq.slice h_list (UInt32.v i) (Seq.length h_list)) ==> 
                                                                                     Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x (Seq.slice h_list (UInt32.v i) (Seq.length h_list)) ==> 
                                                                                       is_valid_header x g) /\
                                                                      (G.is_vertex_set (Seq.slice h_list (UInt32.v i) (Seq.length h_list)))})
        : Lemma
        (requires mutually_exclusive_sets st (Seq.slice h_list (UInt32.v i) (Seq.length h_list)) /\
                   (forall x. Seq.mem x (Seq.slice h_list (UInt32.v i + 1) (Seq.length h_list)) ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                   (forall x. Seq.mem x (Seq.slice h_list (UInt32.v i + 1) (Seq.length h_list)) ==> Usize.v x % Usize.v mword == 0) /\
                   (forall x. Seq.mem x (Seq.slice h_list (UInt32.v i + 1) (Seq.length h_list)) ==> is_valid_header x g) /\
                   (G.is_vertex_set (Seq.slice h_list (UInt32.v i + 1) (Seq.length h_list))) /\
                   (~(Seq.mem (Seq.index h_list (UInt32.v i)) st)) /\
                   mutually_exclusive_sets ((fst (push_to_stack2 g st (Seq.index h_list (UInt32.v i))))) (Seq.slice h_list (UInt32.v i + 1) (Seq.length h_list))
        )                                                                                                                         
        (ensures  (create_root_stack_and_gray_modified_heap g st (Seq.slice h_list (UInt32.v i) (Seq.length h_list)) == 
                    
                   create_root_stack_and_gray_modified_heap (snd (push_to_stack2 g st (Seq.index h_list (UInt32.v i)))) 
                                                                                             (fst (push_to_stack2 g st (Seq.index h_list (UInt32.v i)))) 
                                                                                             (Seq.slice h_list (UInt32.v i + 1) (Seq.length h_list)))) = ()                    


let create_root_stack_and_gray_modified_heap_base_lemma (g:heap{well_formed_heap2 g}) 
                                                        (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                        (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)}) 
                                    : Lemma
                                      (requires (mutually_exclusive_sets st h_list) /\ Seq.length h_list == 0) 
                                      (ensures (create_root_stack_and_gray_modified_heap g st h_list == (st,g))) = ()





let create_root_stack_and_gray_modified_heap_rec_lemma  (g:heap{well_formed_heap2 g}) 
                                                        (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                        (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)}) 
                                    : Lemma
                                      (requires (mutually_exclusive_sets st h_list) /\ Seq.length h_list < 0)
                                      (ensures (create_root_stack_and_gray_modified_heap g st h_list == 
                                                    create_root_stack_and_gray_modified_heap (snd (push_to_stack2 g st (head h_list))) 
                                                                                             (fst (push_to_stack2 g st (head h_list))) 
                                                                                             (tail h_list))) = ()

let create_root_stack_and_gray_modified_heap_rec_lemma1 (g:heap{well_formed_heap2 g}) 
                                                        (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                        (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)}) 
                                    : Lemma
                                      (requires (mutually_exclusive_sets st h_list) /\ Seq.length h_list < 0)
                                      (ensures (create_root_stack_and_gray_modified_heap g st h_list == 
                                                    create_root_stack_and_gray_modified_heap (snd (push_to_stack2 g st (Seq.index h_list 0))) 
                                                                                             (fst (push_to_stack2 g st (Seq.index h_list 0))) 
                                                                                             (Seq.slice h_list 1 (Seq.length h_list)))) = ()


let rec create_root_stack_and_gray_modified_heap1 (g:heap{well_formed_heap2 g}) 
                                                 (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                 (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)})          
                                                  
      : Pure (stack_heap_pair) 
         (requires mutually_exclusive_sets st h_list)
         (ensures fun st_hp ->  well_formed_heap2 (snd st_hp) /\
                             (objects2 0UL (snd st_hp)) == (objects2 0UL g) /\
                                    (forall x. Seq.mem x (fst st_hp) ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x (fst st_hp) ==> is_valid_header x (snd st_hp)) /\                                                      
                                    (forall x. Seq.mem x (fst st_hp) ==> Usize.v x % Usize.v mword == 0) /\                                                       
                                    (G.is_vertex_set (fst st_hp)) /\
                                    (forall x. Seq.mem x (objects2 0UL (snd st_hp)) /\ isGrayObject1 x (snd st_hp) <==>  Seq.mem x (fst st_hp)))
         (decreases (Seq.length h_list)) =
  
  if Seq.length h_list = 0 then 
  (
     (st,g)
  )
  else
  (
    
     let tl = Seq.tail h_list in
     
   
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     
     let st',g' = create_root_stack_and_gray_modified_heap_body g st h_list in
     let st1, g1 = create_root_stack_and_gray_modified_heap1 g' st' (tail h_list) in
     (st1,g1)
  )

let sweep_body_helper (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                      (h_index:hp_addr{is_valid_header h_index g})
            : Tot (g':heap{let c = getColor (read_word g h_index) in
                            ((color_of_object1 h_index g' = (if c = white then blue
                                                            else
                                                            (
                                                              if c = black then white
                                                              else
                                                              blue
                                                            ))) /\
                             (heap_remains_same_except_index_v_id h_index g g') /\
                             well_formed_heap2 g' /\
                             (objects2 0UL g == objects2 0UL g') /\
                             (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x)) /\
                             (objects2 h_index g == objects2 h_index g'))}) = 
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white) then 
 (
   let g' = colorHeader1 h_index g blue in
   colorHeader1_wosizeLemma h_index g blue h_index;
   assert (objects2 h_index g == objects2 h_index g');
   g'
 )
 else
 (
   if (c = black) then 
   (
      let g' = colorHeader1 h_index g white in
      colorHeader1_wosizeLemma h_index g white h_index;
      assert (objects2 h_index g == objects2 h_index g');
      g'
   )
   else
   (
     assert (c == blue);
     objects2_equal_lemma h_index g g;
     assert (objects2 h_index g == objects2 h_index g);
     g
   )
 )

#restart-solver

#restart-solver 

#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver

let rec sweep (g:heap{well_formed_heap2 g /\ noGreyObjects g})
              (h_index:hp_addr{is_valid_header h_index g /\ (Seq.length (objects2 h_index g) > 0)})
          : Tot (g':heap{(well_formed_heap2 g') /\ 
                         (objects2 0UL g == objects2 0UL g') /\
                         (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x)) /\
                         (objects2 h_index g == objects2 h_index g') /\
                         (forall x. Seq.mem x (objects2 h_index g) /\ color_of_object1 x g == black <==> Seq.mem x (objects2 h_index g') /\ color_of_object1 x g' == white) /\
                         (forall x. Seq.mem x (objects2 h_index g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                               Seq.mem x (objects2 h_index g') /\ color_of_object1 x g' == blue) /\
                         (forall (x:Usize.t{Usize.v x < Usize.v h_index /\ Usize.v x % 8 == 0}). getColor (read_word g x) == getColor (read_word g' x))})
            (decreases (heap_size - Usize.v h_index)) = 
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let g' = sweep_body_helper g h_index in 
 assert (well_formed_heap2 g');
 assert (objects2 0UL g == objects2 0UL g');
 assert (heap_remains_same_except_index_v_id h_index g g');
 assert (color_of_object1 h_index g == white ==> color_of_object1 h_index g' == blue);
 assert (color_of_object1 h_index g == black ==> color_of_object1 h_index g' == white);
 assert (color_of_object1 h_index g == blue ==> color_of_object1 h_index g' == blue);
 assert (color_of_object1 h_index g' <> black);
 if Usize.v h_index_new >= heap_size then
 (
    assert (objects2 h_index g == objects2 h_index g');
    assert (forall x. Seq.mem x (objects2 h_index g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                               Seq.mem x (objects2 h_index g') /\ color_of_object1 x g' == blue);
    assert (forall x. Seq.mem x (objects2 h_index g) /\ color_of_object1 x g == black <==> Seq.mem x (objects2 h_index g') /\ color_of_object1 x g' == white);
    assert (forall (x:Usize.t{Usize.v x < Usize.v h_index /\ Usize.v x % 8 == 0}). getColor (read_word g x) == getColor (read_word g' x));
    g'
 )
 else
 (
      wosize_plus_times_mword_multiple_of_mword1 wz;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);
      objects2_mem_lemma1_app h_index g;
      assert (is_valid_header h_index_new g);
      assert (is_valid_header h_index_new g');
      assert (Seq.mem h_index (objects2 0UL g));
      assert (Seq.length (objects2 0UL g) > 0);
      assert (Seq.length (objects2 h_index g) > 0);
      assert (Seq.length (objects2 h_index g') > 0);
      objects2_length_lemma1 g' h_index h_index_new; 
      assert (Seq.length (objects2 h_index_new g') > 0);
      let g'' = sweep g' h_index_new in
      assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g' x) == getWosize (read_word g'' x));
      assert (objects2 h_index_new g' == objects2 h_index_new g'');
      assert (forall x. Seq.mem x (objects2 h_index_new g') /\ color_of_object1 x g' == black <==> Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white);
      assert (forall x. Seq.mem x (objects2 h_index_new g') /\ (color_of_object1 x g' == white \/ color_of_object1 x g' == blue) <==> 
                               Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == blue);
      assert (forall (x:Usize.t{Usize.v x < Usize.v h_index_new /\ Usize.v x % 8 == 0}). getColor (read_word g' x) == getColor (read_word g'' x));
      assert (well_formed_heap2 g'');
      assert (objects2 0UL g' == objects2 0UL g'');
      assert (objects2 0UL g'' == objects2 0UL g);
      objects2_equal_lemma h_index g' g'';
      assert (objects2 h_index g' == objects2 h_index g'');
      assert (objects2 h_index g == objects2 h_index g'');
      assert (getColor (read_word g' h_index) == getColor (read_word g'' h_index));
      assert (color_of_object1 h_index g'' <> black);
      
      assert (Seq.mem h_index (objects2 h_index g) /\ color_of_object1 h_index g == black <==> Seq.mem h_index (objects2 h_index g') /\ color_of_object1 h_index g' == white);
      assert (Seq.mem h_index (objects2 h_index g) /\ color_of_object1 h_index g == black <==> Seq.mem h_index (objects2 h_index g'') /\ color_of_object1 h_index g'' == white);
      assert (forall x. Seq.mem x (objects2 h_index_new g') /\ color_of_object1 x g' == black <==> Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white);
      assert (forall x. Seq.mem x (objects2 h_index g) /\ color_of_object1 x g == black /\ x <> h_index <==> Seq.mem x (objects2 h_index g') /\ color_of_object1 x g' == black);
      assert (forall x. Seq.mem x (objects2 h_index_new g') /\ color_of_object1 x g' == black <==> Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white);
      objects2_cons_lemma1 h_index g h_index_new;
      objects2_cons_lemma1 h_index g' h_index_new;
      objects2_cons_lemma1 h_index g'' h_index_new;
      assert (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g)));
      assert (forall x. Seq.mem x (objects2 h_index g') <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g')));
      assert (forall x. Seq.mem x (objects2 h_index g'') <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g'')));
      
      objects2_equal_lemma h_index_new g g';
      assert (forall x. Seq.mem x (objects2 h_index_new g) /\ color_of_object1 x g == black <==> Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white);
      assert (forall x. (x == h_index /\  color_of_object1 x g == black) \/ (Seq.mem x (objects2 h_index_new g) /\ color_of_object1 x g == black) <==> 
                   (x == h_index /\  color_of_object1 x g'' == white) \/ (Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == white));
      assert (forall x. (x == h_index \/ Seq.mem x (objects2 h_index_new g)) /\ color_of_object1 x g == black <==> 
                   (x == h_index \/ Seq.mem x (objects2 h_index_new g'')) /\ color_of_object1 x g'' == white);
      assert (forall x. Seq.mem x (objects2 h_index g) /\ color_of_object1 x g == black <==> 
                   Seq.mem x (objects2 h_index g'') /\ color_of_object1 x g'' == white);
          
      assert (forall x. Seq.mem x (objects2 h_index_new g') /\ (color_of_object1 x g' == white \/ color_of_object1 x g' == blue) <==> 
                               Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == blue);
      assert (forall x. Seq.mem x (objects2 h_index_new g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                               Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == blue);

      assert (Seq.mem h_index (objects2 h_index g) /\ (color_of_object1 h_index g == white \/ color_of_object1 h_index g == blue) <==> 
                        Seq.mem h_index (objects2 h_index g') /\ color_of_object1 h_index g' == blue);
      assert (Seq.mem h_index (objects2 h_index g) /\ (color_of_object1 h_index g == white \/ color_of_object1 h_index g == blue) <==> 
                        Seq.mem h_index (objects2 h_index g'') /\ color_of_object1 h_index g'' == blue);

      assert (forall x. (x == h_index /\  (color_of_object1 x g == white \/ color_of_object1 x g == blue)) \/ 
                   (Seq.mem x (objects2 h_index_new g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue)) <==> 
                   (x == h_index /\  color_of_object1 x g'' == blue) \/ (Seq.mem x (objects2 h_index_new g'') /\ color_of_object1 x g'' == blue));

      assert (forall x. (x == h_index \/ Seq.mem x (objects2 h_index_new g)) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                     
                   (x == h_index \/  Seq.mem x (objects2 h_index_new g'')) /\ color_of_object1 x g'' == blue);
      assert (forall x. Seq.mem x (objects2 h_index g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                   Seq.mem x (objects2 h_index g'') /\ color_of_object1 x g'' == blue);
      assert (forall (x:Usize.t{Usize.v x < Usize.v h_index /\ Usize.v x % 8 == 0}). getColor (read_word g x) == getColor (read_word g'' x));
      g''
 )


#restart-solver 


let rec sweep1 (g:heap{well_formed_heap2 g /\ noGreyObjects g})
               (h_index:hp_addr{is_valid_header h_index g /\ (Seq.length (objects2 h_index g) > 0)})
          : Tot (g':heap{(well_formed_heap2 g') /\ 
                         (objects2 0UL g == objects2 0UL g')})
            (decreases (heap_size - Usize.v h_index)) = 
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let g' = sweep_body_helper g h_index in 
 assert (well_formed_heap2 g');
 assert (objects2 0UL g == objects2 0UL g');
 if Usize.v h_index_new >= heap_size then
 (
   g'
 )
 else
 (
      wosize_plus_times_mword_multiple_of_mword1 wz;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);
      
      objects2_mem_lemma1_app h_index g;
      
      assert (is_valid_header h_index_new g);
      assert (is_valid_header h_index_new g');
     
      assert (Seq.mem h_index (objects2 0UL g));
      assert (Seq.length (objects2 0UL g) > 0);
      assert (Seq.length (objects2 h_index g) > 0);
      assert (Seq.length (objects2 h_index g') > 0);
      
      objects2_length_lemma1 g' h_index h_index_new; 
      assert (Seq.length (objects2 h_index_new g') > 0);
      
      let g'' = sweep1 g' h_index_new in
     
      assert (objects2 0UL g' == objects2 0UL g'');
      assert (objects2 0UL g'' == objects2 0UL g);
      g''
 )

#restart-solver 

#restart-solver

#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver 

let rec sweep1_sweep_equivalence_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                       (h_index:hp_addr{is_valid_header h_index g /\ (Seq.length (objects2 h_index g) > 0)})
                        : Lemma 
                          (ensures (sweep1 g h_index == sweep g h_index)) 
                          (decreases (heap_size - Usize.v h_index))= 
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let g' = sweep_body_helper g h_index in 
 assert (well_formed_heap2 g');
 assert (objects2 0UL g == objects2 0UL g');
 if Usize.v h_index_new >= heap_size then
 (
   ()
 )
 else
 (
   wosize_plus_times_mword_multiple_of_mword1 wz;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);
      
      objects2_mem_lemma1_app h_index g;
      
      assert (is_valid_header h_index_new g);
      assert (is_valid_header h_index_new g');
     
      assert (Seq.mem h_index (objects2 0UL g));
      assert (Seq.length (objects2 0UL g) > 0);
      assert (Seq.length (objects2 h_index g) > 0);
      assert (Seq.length (objects2 h_index g') > 0);
      
      objects2_length_lemma1 g' h_index h_index_new; 
      assert (Seq.length (objects2 h_index_new g') > 0);
      
      let g1 = sweep1 g' h_index_new in
      let g2 = sweep g' h_index_new in
      sweep1_sweep_equivalence_lemma g' h_index_new;
      assert (g1 == g2);
      ()
 )

let sweep1_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                 (h_index:hp_addr{is_valid_header h_index g /\ (Seq.length (objects2 h_index g) > 0)})
             : Lemma
               (ensures  (well_formed_heap2 (sweep1 g h_index)) /\ 
                         (objects2 0UL g == objects2 0UL (sweep1 g h_index)) /\
                         (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word (sweep1 g h_index) x)) /\
                         (objects2 h_index g == objects2 h_index (sweep1 g h_index)) /\
                         (forall x. Seq.mem x (objects2 h_index g) /\ color_of_object1 x g == black <==> 
                                Seq.mem x (objects2 h_index (sweep1 g h_index)) /\ color_of_object1 x (sweep1 g h_index) == white) /\
                         (forall x. Seq.mem x (objects2 h_index g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                               Seq.mem x (objects2 h_index (sweep1 g h_index)) /\ color_of_object1 x (sweep1 g h_index) == blue) /\
                         (forall (x:Usize.t{Usize.v x < Usize.v h_index /\ Usize.v x % 8 == 0}). getColor (read_word g x) == getColor (read_word (sweep1 g h_index) x))) = 
 let g1 = sweep g h_index in

 assert (well_formed_heap2 g1); 
 assert (objects2 0UL g == objects2 0UL g1);
 assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g1 x));
 assert (objects2 h_index g == objects2 h_index g1);
 assert(forall x. Seq.mem x (objects2 h_index g) /\ color_of_object1 x g == black <==> 
                             Seq.mem x (objects2 h_index g1) /\ color_of_object1 x g1 == white);
 assert (forall x. Seq.mem x (objects2 h_index g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                               Seq.mem x (objects2 h_index g1) /\ color_of_object1 x g1 == blue);
 assert (forall (x:Usize.t{Usize.v x < Usize.v h_index /\ Usize.v x % 8 == 0}). getColor (read_word g x) == getColor (read_word g1 x));
 let g2 = sweep1 g h_index in
 sweep1_sweep_equivalence_lemma g h_index;
 ()

let only_white_and_blue_blocks (g:heap{well_formed_heap2 g}) = 
   (forall x. Seq.mem x (objects2 0UL g) ==> color_of_object1 x g == blue \/ color_of_object1 x g == white)

#restart-solver

#restart-solver

let noGreyObjects_from_h_index (g:heap{well_formed_heap2 g}) 
                               (h_index:hp_addr{is_valid_header h_index g}) =
(forall x. Seq.mem x (objects2 h_index g) ==> ~(color_of_object1 x g == gray))

let only_white_and_blue_blocks_from_h_index (g:heap{well_formed_heap2 g}) 
                                            (h_index:hp_addr{is_valid_header h_index g}) = 
 (forall x. Seq.mem x (objects2 h_index g) ==> color_of_object1 x g == blue \/ color_of_object1 x g == white)

let noBlackObjects_from_h_index (g:heap{well_formed_heap2 g}) 
                               (h_index:hp_addr{is_valid_header h_index g}) =
(forall x. Seq.mem x (objects2 h_index g) ==> ~(color_of_object1 x g == black))

let noBlackObjects (g:heap{well_formed_heap2 g})=
(forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == black))

#restart-solver 

#restart-solver 

let sweep1_color_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                       (h_index:hp_addr{is_valid_header h_index g /\ (Seq.length (objects2 h_index g) > 0) /\ noGreyObjects_from_h_index g h_index})
             : Lemma
               (requires (well_formed_heap2 (sweep1 g h_index) /\ (is_valid_header h_index (sweep1 g h_index))))
               (ensures (only_white_and_blue_blocks_from_h_index (sweep1 g h_index) h_index) /\
                         (noGreyObjects_from_h_index (sweep1 g h_index) h_index) /\
                         (noBlackObjects_from_h_index (sweep1 g h_index) h_index)) = 
 let g1 = sweep1 g h_index in
 sweep1_lemma g h_index;
 assert (forall x. Seq.mem x (objects2 h_index g) /\ color_of_object1 x g == black <==> 
                   Seq.mem x (objects2 h_index g1) /\ color_of_object1 x g1 == white);
 assert (forall x. Seq.mem x (objects2 h_index g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                               Seq.mem x (objects2 h_index g1) /\ color_of_object1 x g1 == blue);
 assert (well_formed_heap2 g1);
 assert (objects2 h_index g == objects2 h_index g1);
 assert (is_valid_header h_index g1);
 objects2_color_lemma h_index g;
 assert(noGreyObjects g);
 assert (forall x. Seq.mem x (objects2 h_index g) ==> ~(color_of_object1 x g == gray));
 assert (forall x. Seq.mem x (objects2 h_index g) ==> color_of_object1 x g == white \/ color_of_object1 x g == black \/ color_of_object1 x g == blue);
 assert (forall x. Seq.mem x (objects2 h_index g1) ==> color_of_object1 x g1 == blue \/ color_of_object1 x g1 == white);
 assert (only_white_and_blue_blocks_from_h_index g1 h_index);
 assert (forall x. Seq.mem x (objects2 h_index g1) ==> ~(color_of_object1 x g1 == gray));
 assert (forall x. Seq.mem x (objects2 h_index g1) ==> ~(color_of_object1 x g1 == black));
 assert (noGreyObjects_from_h_index g1 h_index);
 assert (noBlackObjects_from_h_index g1 h_index);
 ()

let sweep1_heap_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                 : Lemma
                   (ensures ((forall x. Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == black <==> 
                                Seq.mem x (objects2 0UL (sweep1 g 0UL)) /\ color_of_object1 x (sweep1 g 0UL) == white) /\
                             (forall x. Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g == white \/ color_of_object1 x g == blue) <==> 
                               Seq.mem x (objects2 0UL (sweep1 g 0UL)) /\ color_of_object1 x (sweep1 g 0UL) == blue))) = 
let g1 = sweep1 g 0UL in
sweep1_lemma g 0UL;
()

let sweep1_heap_color_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                   : Lemma
                     (requires (well_formed_heap2 (sweep1 g 0UL)))
                     (ensures (only_white_and_blue_blocks (sweep1 g 0UL)) /\
                              (noGreyObjects (sweep1 g 0UL)) /\
                              (noBlackObjects (sweep1 g 0UL))) = 
let g1 = sweep1 g 0UL in
assert (well_formed_heap2 g1);
sweep1_color_lemma g 0UL;
assert (only_white_and_blue_blocks_from_h_index g1 0UL);
assert (forall x. Seq.mem x (objects2 0UL g1) ==> color_of_object1 x g1 == blue \/ color_of_object1 x g1 == white);
assert (only_white_and_blue_blocks g1);
assert (forall x. Seq.mem x (objects2 0UL g1) ==> ~(color_of_object1 x g1 == gray));
assert (forall x. Seq.mem x (objects2 0UL g1) ==> ~(color_of_object1 x g1 == black));
assert (noGreyObjects g1);
assert (noBlackObjects g1);
()


(*let noGreyObjects (g:heap{well_formed_heap2 g}) = (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray)) *)
(*
  input g --> well_formed_heap2 g /\ 
              well_formed_allocated_blocks g /\  
              noContiguousBlueObjects g /\ 
              noGreyObjects g /\ 
              only_white_and_blue_blocks g
              
  output g' --> well_formed_heap2 g' /\ 
                well_formed_allocated_blocks g' /\  
                noContiguousBlueObjects g' /\ 
                noGreyObjects g' /\ 
                only_white_and_blue_blocks g'
*)

(*Implement sweep with merging to ensure noContiguousBlueObjects property
  noGreyObjects is proved by mark
  well_formed_allocated_blocks property is proved on mark5_body
  only_white_and_blue_blocks property need to be proved*)


let mark_and_sweep_GC (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g /\  noContiguousBlueObjects g /\ noGreyObjects g /\ only_white_and_blue_blocks g})
                      (*root pointers--------------------------------------------------------------------------------------------------------------------------*)
                      (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                           (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                           (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                           (G.is_vertex_set h_list)})
                : Tot (g':heap) = 
 
 (*Mark stack creation-----------------------------------------------------------------------------------------*)
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);

 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in

 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);

 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3 = sweep g2 0UL in
 g3

(*-------------------------------------------------------------------------------------------------------------*)
(*GC without merging in sweep----------------------------------------------------------------------------------*)

let mark_and_sweep_GC1 (g:heap{well_formed_heap2 g /\ 
                                well_formed_allocated_blocks g /\  
                                noGreyObjects g /\ 
                                only_white_and_blue_blocks g /\
                                noBlackObjects g})
                        (*root pointers--------------------------------------------------------------------------------------------------------------------------*)
                        (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                           (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                           (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                           (G.is_vertex_set h_list) /\
                                           (G.subset_vertices h_list (get_allocated_block_addresses g))})
                : Tot (g':heap{well_formed_heap2 g' /\ 
                               noGreyObjects g' /\ 
                               only_white_and_blue_blocks g' /\
                               noBlackObjects g'}) = 
 
 (*Mark stack creation-----------------------------------------------------------------------------------------*)
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);

 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in

 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);

 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3 = sweep1 g2 0UL in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);
 g3

#restart-solver 

#reset-options "--z3rlimit 500"

#restart-solver 

#push-options "--z3rlimit 1000"

#restart-solver

let allocs_of_after_sweep_is_subset_of_allocs_before_sweep (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                          : Lemma
                            (requires (well_formed_allocated_blocks g) /\
                                      (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\ 
                                                 (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                            (ensures (forall x. Seq.mem x (objects2 0UL g) /\ (isWhiteObject1 x (sweep1 g 0UL)) <==> 
                                         Seq.mem x (get_allocated_block_addresses (sweep1 g 0UL))) /\
                                     (G.subset_vertices (get_allocated_block_addresses (sweep1 g 0UL)) (get_allocated_block_addresses g))) =
                                     

assert (well_formed_allocated_blocks g);
let g1 = sweep1 g 0UL in
sweep1_heap_lemma g;
sweep1_heap_color_lemma g;
assert (forall x. Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == black <==> 
                        Seq.mem x (objects2 0UL g1) /\ color_of_object1 x g1 == white);
let allocs = get_allocated_block_addresses g in
let allocs1 = get_allocated_block_addresses g1 in

assert (forall x. Seq.mem x (objects2 0UL g) /\ ((isWhiteObject1 x g) \/ (isBlackObject1 x g)) <==>
                                                               Seq.mem x allocs); 
                                                                                                 

assert (objects2 0UL g == objects2 0UL g1);
assert (forall x. Seq.mem x (objects2 0UL g1) /\ ((isWhiteObject1 x g) \/ (isGrayObject1 x g) \/ (isBlackObject1 x g))==>
                                                               Seq.mem x allocs); 

assert (forall x. Seq.mem x (objects2 0UL g1) ==> color_of_object1 x g1 == blue \/ color_of_object1 x g1 == white);



assert (forall x. Seq.mem x (objects2 0UL g1) /\ (isWhiteObject1 x g1) <==>
                                                               Seq.mem x allocs1); 
assert (forall x. Seq.mem x (objects2 0UL g) /\ (isWhiteObject1 x g1) <==>
                                                               Seq.mem x allocs1); 

assert (forall x. Seq.mem x (objects2 0UL g) /\ (isBlackObject1 x g) <==> 
                        Seq.mem x (objects2 0UL g) /\ (isWhiteObject1 x g1));

assert (forall x. Seq.mem x (objects2 0UL g) /\ (isBlackObject1 x g) <==> Seq.mem x allocs1);
assert (forall x. Seq.mem x (objects2 0UL g) /\ (isWhiteObject1 x g1) <==> Seq.mem x allocs1);
assert (forall x. Seq.mem x (objects2 0UL g) /\ ((isWhiteObject1 x g) \/ (isBlackObject1 x g)) <==>
                                                               Seq.mem x allocs); 

assert (forall x. Seq.mem x allocs1 ==> Seq.mem x allocs);
assert (G.is_vertex_set allocs);
assert (G.is_vertex_set allocs1);
assert (G.subset_vertices allocs1 allocs);
()

#restart-solver 

let push_to_stack2_noBlackObjects_lemma  (g:heap{well_formed_heap2 g /\ noBlackObjects g})
                                         (st: seq Usize.t{G.is_vertex_set st /\
                                                           (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                           (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                           (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                Seq.mem x st)})
                   
                                         (x: hp_addr{~(Seq.mem x st) /\
                                                       (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                       (Usize.v x % Usize.v mword == 0) /\
                                                       is_valid_header x g}) 
                                
            : Lemma
              (ensures noBlackObjects (snd (push_to_stack2 g st x))) = 
if Seq.length st = 0 then
(
   let stk' = Seq.create 1 x in
    assert (noBlackObjects g);
    let g' = colorHeader1 x g gray in 
    assert (noBlackObjects g');
    assert (Seq.mem x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');
    objects2_equal_lemma 0UL g g';
    
    assert (objects2 0UL g == objects2 0UL g');
                                            
    assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');

    assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');
    assert (heap_remains_same_except_index_v_id x g g');
    assert ((forall x. Seq.mem x stk' ==> Usize.v x % Usize.v mword == 0));
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  assert (noBlackObjects g');
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem x st));
  G.snoc_unique_lemma x st;
  assert (G.is_vertex_set st');
  assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  

  assert (forall y. Seq.mem y st' ==> is_valid_header y g);
  assert (forall y. Seq.mem y st' ==> is_valid_header y g');
  
  assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  assert (heap_remains_same_except_index_v_id x g g');
  ()
)




let create_root_stack_and_gray_modified_heap_body_black_objects_lemma (g:heap{well_formed_heap2 g /\ noBlackObjects g}) 
                                                                      (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                        (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                        (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                        (G.is_vertex_set st) /\
                                                                                        (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                        Seq.mem x st)})
                                                                      (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                           (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                                           (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                                           (G.is_vertex_set h_list)})          
                                                   
      :Lemma
       (requires (mutually_exclusive_sets st h_list) /\ Seq.length h_list > 0 /\ (G.is_vertex_set (tail h_list)))
       (ensures noBlackObjects (snd (create_root_stack_and_gray_modified_heap_body g st h_list)))= 
     assert (Seq.length h_list > 0);
     let hd = Seq.head h_list in
     let tl = Seq.tail h_list in
     
     assert (G.is_vertex_set st);
     assert (G.is_vertex_set h_list);

     assert (~(Seq.mem hd st));
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     assert (mutually_exclusive_sets st tl);

     G.is_vertex_set_lemma4 h_list;
     assert (~(Seq.mem hd tl));
     assert (~(Seq.mem hd st));
     assert (noBlackObjects g);
     let st', g' = push_to_stack2 g st hd in
     push_to_stack2_noBlackObjects_lemma g st hd;
     assert (mutually_exclusive_sets st' tl);
     assert (noBlackObjects g');
     ()
         

let rec create_root_stack_and_gray_modified_heap_noBlackObjects_lemma (g:heap{well_formed_heap2 g /\ noBlackObjects g}) 
                                                                      (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                        (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                        (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                        (G.is_vertex_set st) /\
                                                                                        (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                        Seq.mem x st)})
                                                                      (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                           (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                                           (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                                           (G.is_vertex_set h_list)})          
                                                  
      :  Lemma 
         (requires mutually_exclusive_sets st h_list)
         (ensures noBlackObjects (snd (create_root_stack_and_gray_modified_heap g st h_list)))
         (decreases (Seq.length h_list)) =
  
  if Seq.length h_list = 0 then 
  (
     ()
  )
  else
  (
     let hd = Seq.head h_list in
     let tl = Seq.tail h_list in
     
     assert (G.is_vertex_set st);
     assert (G.is_vertex_set h_list);

     assert (~(Seq.mem hd st));
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     assert (mutually_exclusive_sets st tl);

     G.is_vertex_set_lemma4 h_list;
     assert (~(Seq.mem hd tl));
     assert (~(Seq.mem hd st));
     let st', g' = push_to_stack2 g st hd in
     push_to_stack2_noBlackObjects_lemma g st hd;
     assert (mutually_exclusive_sets st' tl);

     assert (noBlackObjects g');
     let st1, g1 = create_root_stack_and_gray_modified_heap g' st' (tail h_list) in
     create_root_stack_and_gray_modified_heap_noBlackObjects_lemma g' st' (tail h_list);
     ()
  )

#restart-solver 

#restart-solver

#restart-solver 

let rec create_root_stack_and_gray_modified_heap_well_formed_allocated_blocks_lemma (g:heap{well_formed_heap2 g}) 
                                                                                    (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                                      (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                                      (G.is_vertex_set st) /\
                                                                                                      (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                                      Seq.mem x st)})
                                                                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> 
                                                                                                            Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                                         (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                                                         (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                                                         (forall x. Seq.mem x h_list ==> color_of_object1 x g == white) /\
                                                                                                         (G.is_vertex_set h_list)}) 
                                                                                    (c:color{c == 2UL})
                                                  
      :  Lemma 
         (requires (mutually_exclusive_sets st h_list) /\ well_formed_allocated_blocks g /\
                   (G.subset_vertices h_list (get_allocated_block_addresses g)))
         (ensures (well_formed_allocated_blocks (snd (create_root_stack_and_gray_modified_heap g st h_list))) /\
                  (get_allocated_block_addresses g == get_allocated_block_addresses (snd (create_root_stack_and_gray_modified_heap g st h_list))) /\
                  (create_graph_from_heap g == create_graph_from_heap (snd (create_root_stack_and_gray_modified_heap g st h_list))))
         (decreases (Seq.length h_list)) = 
if Seq.length h_list = 0 then 
  (
     ()
  )
  else
  (
     let hd = Seq.head h_list in
     let tl = Seq.tail h_list in
     
     assert (G.is_vertex_set st);
     assert (G.is_vertex_set h_list);

     assert (~(Seq.mem hd st));
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     assert (mutually_exclusive_sets st tl);

     G.is_vertex_set_lemma4 h_list;
     assert (~(Seq.mem hd tl));
     assert (~(Seq.mem hd st));
     let st', g' = push_to_stack2 g st hd in
     field_limits_allocated_blocks_lemma g;
     assert (is_fields_within_limit1 hd (getWosize (read_word g hd)));

     assert (well_formed_heap2 g);
     assert (well_formed_allocated_blocks g);
     assert (color_of_object1 hd g == white);
     push_to_stack2_well_formed_allocated_blocks_lemma g st hd c;
     push_to_stack2_lemma g st hd; 
     push_to_stack2_graph_lemma g st hd;
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
     
     assert (mutually_exclusive_sets st' tl);
     assert (well_formed_allocated_blocks g');
     assert (create_graph_from_heap g == create_graph_from_heap g');
     let st1, g1 = create_root_stack_and_gray_modified_heap g' st' (tail h_list) in
     create_root_stack_and_gray_modified_heap_well_formed_allocated_blocks_lemma g' st' (tail h_list) c;
     assert (well_formed_allocated_blocks g1);
     assert (get_allocated_block_addresses g1 == get_allocated_block_addresses g');
     assert (get_allocated_block_addresses g1 == get_allocated_block_addresses g);
     assert (create_graph_from_heap g1 == create_graph_from_heap g');
     assert (create_graph_from_heap g1 == create_graph_from_heap g);
     ()
    )

#restart-solver

#restart-solver 

let push_to_stack2_mem_lemma  (g:heap{well_formed_heap2 g})
                    (st: seq Usize.t{G.is_vertex_set st /\
                                   (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                   (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                   (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)})
                    (x: hp_addr{~(Seq.mem x st) /\
                                (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                (Usize.v x % Usize.v mword == 0) /\
                                is_valid_header x g}) 
                                
           :Lemma 
            (ensures (forall y. Seq.mem y (fst (push_to_stack2 g st x)) ==> y == x \/ Seq.mem y st)) =
if Seq.length st = 0 then
(
   let stk' = Seq.create 1 x in
    let g' = colorHeader1 x g gray in 
    assert (Seq.mem x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');
    objects2_equal_lemma 0UL g g';
    
    assert (objects2 0UL g == objects2 0UL g');
                                            
    assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');

    assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x stk');
    assert (heap_remains_same_except_index_v_id x g g');
    assert ((forall x. Seq.mem x stk' ==> Usize.v x % Usize.v mword == 0));
    assert (forall y. Seq.mem y stk' ==> y == x \/ Seq.mem y st);
    ()
)
    
else
(
  lemma_tail_snoc st x;
  lemma_mem_snoc st x; 
  let st' = snoc st x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem x st));
  G.snoc_unique_lemma x st;
  assert (G.is_vertex_set st');
  assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  

  assert (forall y. Seq.mem y st' ==> is_valid_header y g);
  assert (forall y. Seq.mem y st' ==> is_valid_header y g');
  
  assert (forall x. Seq.mem x (objects2 0UL g') /\ isGrayObject1 x g' <==>
                                                  Seq.mem x st');
  assert (heap_remains_same_except_index_v_id x g g');
  assert (forall y. Seq.mem y st' ==> y == x \/ Seq.mem y st);
  ()
)



let rec create_root_stack_and_gray_modified_heap_mem_lemma (g:heap{well_formed_heap2 g}) 
                                                 (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                 (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)})          
                                                  
      :  Lemma
         (requires mutually_exclusive_sets st h_list)
          
         (ensures (forall x. Seq.mem x (fst (create_root_stack_and_gray_modified_heap g st h_list)) ==> Seq.mem x st \/ Seq.mem x h_list) /\
                  (forall x. Seq.mem x st ==> Seq.mem x (fst (create_root_stack_and_gray_modified_heap g st h_list))) /\
                  (forall x. Seq.mem x h_list ==> Seq.mem x (fst (create_root_stack_and_gray_modified_heap g st h_list))))
         (decreases (Seq.length h_list)) =
  
  if Seq.length h_list = 0 then 
  (
     ()
  )
  else
  (
     let hd = Seq.head h_list in
     let tl = Seq.tail h_list in
     
     assert (G.is_vertex_set st);
     assert (G.is_vertex_set h_list);

     assert (~(Seq.mem hd st));
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     assert (mutually_exclusive_sets st tl);

     G.is_vertex_set_lemma4 h_list;
     assert (~(Seq.mem hd tl));
     assert (~(Seq.mem hd st));
     let st', g' = push_to_stack2 g st hd in
     push_to_stack2_mem_lemma g st hd;
     assert (forall x. Seq.mem x st' ==> x == hd \/ Seq.mem x st);
     assert (mutually_exclusive_sets st' tl);
     assert (Seq.mem hd st');
     let st1, g1 = create_root_stack_and_gray_modified_heap g' st' (tail h_list) in
     create_root_stack_and_gray_modified_heap_mem_lemma g' st' (tail h_list);
     assert (forall x. Seq.mem x (tail h_list) ==> Seq.mem x st1);
     assert (forall x. Seq.mem x st' ==> Seq.mem x st1);
     assert (forall x. Seq.mem x st ==> Seq.mem x st');
     assert (forall x. Seq.mem x st ==> Seq.mem x st1);
     assert (Seq.mem hd st');
     assert (Seq.mem hd st1);
     assert (forall x. Seq.mem x h_list ==> Seq.mem x st1);
     assert (forall x. Seq.mem x st1 ==> Seq.mem x st' \/ Seq.mem x (tail h_list));
     assert (forall x. Seq.mem x st1 ==> x == hd \/ Seq.mem x st \/ Seq.mem x (tail h_list));
     assert (forall x. Seq.mem x st1 ==> Seq.mem x st \/ Seq.mem x h_list);
     ()
  )


#restart-solver 

#restart-solver 

let mark_and_sweep_GC1_safety_lemma1 (g:heap{well_formed_heap2 g /\ 
                                            well_formed_allocated_blocks g /\  
                                            noGreyObjects g /\ 
                                            only_white_and_blue_blocks g /\
                                            noBlackObjects g})
                                    (*root pointers------------------------------------------------------------------------------------------------------------*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (c:color{c == 3UL})
                                    (c1:color{c1 == 2UL})
                        : Lemma
                          (ensures (forall x.  (Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list))) /\
                                               isWhiteObject1 x (mark_and_sweep_GC1 g h_list)  ==>
                                           (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g) o x z1))) = 
 (*Mark stack creation-----------------------------------------------------------------------------------------*)
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);
 assert (forall x. Seq.mem x h_list ==> color_of_object1 x g == white);
 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in
 create_root_stack_and_gray_modified_heap_noBlackObjects_lemma g st h_list;
 assert (noBlackObjects g1);
 let allocs = get_allocated_block_addresses g1 in
 let vl = get_black_block_addresses g1 allocs in
 assert (Seq.length vl == 0);
 assert (Seq.length st == 0);
 create_root_stack_and_gray_modified_heap_mem_lemma g st h_list;
 assert ((forall x. Seq.mem x st ==> Seq.mem x st') /\
                (forall x. Seq.mem x h_list ==> Seq.mem x st'));
 assert (forall x. Seq.mem x st' ==> Seq.mem x st \/ Seq.mem x h_list);
 assert (forall x. Seq.mem x st' ==> Seq.mem x h_list);
 assert (forall x. Seq.mem x st' <==> Seq.mem x h_list);
 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);
 assert (G.is_vertex_set st');
 assert (G.subset_vertices st' (get_allocated_block_addresses g1));
 assert (G.subset_vertices vl (get_allocated_block_addresses g1));
 assert (well_formed_heap2 g2);
 assert (well_formed_allocated_blocks g);

 
 create_root_stack_and_gray_modified_heap_well_formed_allocated_blocks_lemma g st h_list c1;
 
 assert (well_formed_allocated_blocks g1);
 well_formed_allocated_blocks_mark5 g1 st' c;
 assert (well_formed_allocated_blocks g2);
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
 assert (G.subset_vertices h_list (get_allocated_block_addresses g));
 assert (G.subset_vertices h_list (get_allocated_block_addresses g1));
 assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));
 assert (create_graph_from_heap g1 == create_graph_from_heap g);
 G.reflex_lemma_list (create_graph_from_heap g1) h_list;
 assert (forall x. Seq.mem x h_list ==> (exists (r: (G.reach (create_graph_from_heap g1) x x)). (G.reachfunc (create_graph_from_heap g1) x x r)));
 assert (forall x. Seq.mem x st' ==> (exists o (z1: G.reach (create_graph_from_heap g1) o x) . Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g1) o x z1));
 assert (forall x. Seq.mem x vl ==> (exists o (z1: G.reach (create_graph_from_heap g1) o x). Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g1) o x z1));
 mark_reachability_in_heap_forward_lemma g1 st' vl c h_list;
 assert (forall x. Seq.mem x (objects2 0UL g2) /\ isBlackObject1 x g2 ==> 
                                               (exists o (z1: G.reach (create_graph_from_heap g1) o x) . Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g1) o x z1));
 
 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3 = sweep1 g2 0UL in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);
 assert (forall x. Seq.mem x (objects2 0UL g2) /\ color_of_object1 x g2 == black <==> 
                                Seq.mem x (objects2 0UL g3) /\ color_of_object1 x g3 == white);
 assert (forall x. Seq.mem x (objects2 0UL g3) /\ isWhiteObject1 x g3 ==> 
                                               (exists o (z1: G.reach (create_graph_from_heap g1) o x) . Seq.mem o h_list /\
                                                                         G.reachfunc (create_graph_from_heap g1) o x z1));
 assert (create_graph_from_heap g1 == create_graph_from_heap g);
 ()

#restart-solver 

let mark_and_sweep_GC1_safety_lemma2 (g:heap{well_formed_heap2 g /\ 
                                            well_formed_allocated_blocks g /\  
                                            noGreyObjects g /\ 
                                            only_white_and_blue_blocks g /\
                                            noBlackObjects g})
                                    (*root pointers------------------------------------------------------------------------------------------------------------*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (c:color{c == 3UL})
                                    (c1:color{c1 == 2UL})
                : Lemma 
                  (ensures (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                      (Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list))) /\
                                                        isWhiteObject1 x (mark_and_sweep_GC1 g h_list)
                                                       )) = 

 (*Mark stack creation-----------------------------------------------------------------------------------------*)
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);
 assert (forall x. Seq.mem x h_list ==> color_of_object1 x g == white);
 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in
 create_root_stack_and_gray_modified_heap_noBlackObjects_lemma g st h_list;
 assert (noBlackObjects g1);
 let allocs = get_allocated_block_addresses g1 in
 let vl = get_black_block_addresses g1 allocs in
 assert (Seq.length vl == 0);
 assert (Seq.length st == 0);
 create_root_stack_and_gray_modified_heap_mem_lemma g st h_list;
 assert ((forall x. Seq.mem x st ==> Seq.mem x st') /\
                (forall x. Seq.mem x h_list ==> Seq.mem x st'));
 assert (forall x. Seq.mem x st' ==> Seq.mem x st \/ Seq.mem x h_list);
 assert (forall x. Seq.mem x st' ==> Seq.mem x h_list);
 assert (forall x. Seq.mem x st' <==> Seq.mem x h_list);
 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);
 assert (G.is_vertex_set st');
 assert (G.subset_vertices st' (get_allocated_block_addresses g1));
 assert (G.subset_vertices vl (get_allocated_block_addresses g1));
 assert (well_formed_heap2 g2);
 assert (well_formed_allocated_blocks g);

 
 create_root_stack_and_gray_modified_heap_well_formed_allocated_blocks_lemma g st h_list c1;
 
 assert (well_formed_allocated_blocks g1);
 well_formed_allocated_blocks_mark5 g1 st' c;
 assert (well_formed_allocated_blocks g2);
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
 assert (G.subset_vertices h_list (get_allocated_block_addresses g));
 assert (G.subset_vertices h_list (get_allocated_block_addresses g1));
 assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));
 assert (create_graph_from_heap g1 == create_graph_from_heap g);
 G.reflex_lemma_list (create_graph_from_heap g1) h_list;
 assert (forall o x (z2: G.reach (create_graph_from_heap g1) o x). (G.reachfunc (create_graph_from_heap g1) o x z2) /\ Seq.mem o h_list ==> 
                        (Seq.mem x vl \/  
                        (exists y (z3: G.reach (create_graph_from_heap g1) y x). G.reachfunc (create_graph_from_heap g1) y x z3 /\ Seq.mem y st')));                    
                                           
                                          
 
 assert (forall c b (r_cb: G.reach (create_graph_from_heap g1) c b). (Seq.mem c vl /\ G.reachfunc (create_graph_from_heap g1) c b r_cb /\ ~(c = b)) ==>
                                           (Seq.mem b vl \/ 
                                            Seq.mem b st' \/ 
                                            (exists d. Seq.mem d st' /\ Seq.mem d (G.vertices_in_path (create_graph_from_heap g1) c b r_cb))));
 
 mark_reachability_in_heap_backward_lemma1 g1 st' vl h_list c;
 assert (forall o x (z2: G.reach (create_graph_from_heap g1) o x). (G.reachfunc (create_graph_from_heap g1) o x z2) /\ Seq.mem o h_list ==> 
                                              Seq.mem x (objects2 0UL (mark5 g1 st')) /\ isBlackObject1 x (mark5 g1 st'));
 
 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3 = sweep1 g2 0UL in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);
 assert (forall x. Seq.mem x (objects2 0UL g2) /\ color_of_object1 x g2 == black <==> 
                                Seq.mem x (objects2 0UL g3) /\ color_of_object1 x g3 == white);
 
 
 assert (forall o x (z2: G.reach (create_graph_from_heap g1) o x). (G.reachfunc (create_graph_from_heap g1) o x z2) /\ Seq.mem o h_list ==> 
                                     Seq.mem x (objects2 0UL g3) /\ color_of_object1 x g3 == white);
 assert (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                      (Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list))) /\
                                                        isWhiteObject1 x (mark_and_sweep_GC1 g h_list)
                                                       );
 ()

#restart-solver

let rec dfs_mark_equivalence_graph_lemma    (g:heap{well_formed_heap2 g}) 
                                             (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                               (G.is_vertex_set st) /\
                                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                   Seq.mem x st)
                                                                              })

                                
                                             (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x vl ==> is_valid_header x g) /\
                                                                                (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (G.is_vertex_set vl) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isBlackObject1 x g <==> Seq.mem x vl)
                                                                                }) 
                                             (c:color{c == 3UL})

                          : Lemma
                            (requires (G.subset_vertices st (get_allocated_block_addresses g)) /\
                                      (G.subset_vertices vl (get_allocated_block_addresses g)) /\
                                      (well_formed_allocated_blocks g) /\
                                      (well_formed_heap2 (mark5 g st)) /\
                                      (well_formed_allocated_blocks (mark5 g st)) /\
                                      (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                      (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                   (ensures (create_graph_from_heap g == create_graph_from_heap (mark5 g st))) 

                    (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st])= 
 if (G.is_emptySet st) then
   (
      ()
   )
 else
   (
     let st', g' = mark5_body g st in
     assert (G.is_vertex_set st' /\
             (Seq.length g == Seq.length g') /\
             (well_formed_heap2 g') /\
             (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
             (forall x. Seq.mem x st' ==> is_valid_header x g') /\
             (forall x. Seq.mem x (objects2 0UL g') /\
                                        isGrayObject1 x g' <==>
                                               Seq.mem x st'));

     assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
     assert (objects2 0UL g == objects2 0UL g');

     let v_id = Seq.index st (Seq.length st - 1) in
     assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
     assert (is_valid_header v_id g);

     stack_slice_only_has_gray_color_lemma g st v_id c;

      assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1)));
                            
     mark5_body_black_nodes_lemma g st;
     assert (Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g')) > 
                    Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)));

     let g1 = mark5 g' st' in
     mark_mark_body_lemma g st;
     assert (mark5 g st == mark5 g' st');
     let grph1 = create_graph_from_heap g in
     assert (Seq.equal (grph1.vertices) (get_allocated_block_addresses g));
     assert (G.subset_vertices st (get_allocated_block_addresses g));
     assert (G.subset_vertices st grph1.vertices);
     let _ = G.negation_nonEmpty_implies_empty st in
     assert (G.nonEmpty_set st);
     let st1,vl1 = D.dfs_body grph1 st vl in
     well_formed_allocated_blocks_mark5_body_heap g st c;
     assert (well_formed_allocated_blocks g');
     let grph2 = create_graph_from_heap g' in
     assert (grph1 == grph1);
     
     dfs_mark_equivalence_body_lemma g st vl c;

     assert (st' == st1);
     assert (grph1 == grph2);
     assert (forall x. Seq.mem x (objects2 0UL g') /\ isBlackObject1 x g' <==>
                                                  Seq.mem x vl1);

      dfs_mark_equivalence_graph_lemma g' st' vl1 c;
      assert (well_formed_heap2 g1);
      assert (well_formed_allocated_blocks g1);
      let grph3 = create_graph_from_heap g1 in
      assert (grph2 == grph3);
      assert (grph1 == grph3);
      ()
   )


#restart-solver 

#restart-solver

#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver


#restart-solver

#restart-solver
//#reset-options "--z3rlimit 1000" 

#push-options "--z3rlimit 1000"

#restart-solver 

(*let rec create_successors_list_for_h_index_mem_lemma1 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                                     (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                     (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                       : Lemma
                         (ensures (forall x. Seq.mem x (create_successors_list_for_h_index g h_index wz i) ==> 
                                       (exists t. Usize.v t >= Usize.v i /\ Usize.v t <= Usize.v wz /\
                                             (Usize.v (Usize.add h_index (Usize.mul t mword)) % Usize.v mword == 0) /\
                                             (Usize.v (Usize.add h_index (Usize.mul t mword)) < heap_size) /\
                                             (is_hp_addr (Usize.add h_index (Usize.mul t mword))) /\
                                             (isPointer (Usize.add h_index (Usize.mul t mword)) g) /\
                                             (Seq.mem x (get_allocated_block_addresses g)) /\
                                             (x == read_word g (Usize.add h_index (Usize.mul t mword))))))
                         
                         (decreases ((Usize.v wz + 1) - Usize.v i)) = admit()*)

#restart-solver 

#restart-solver

let field_ptrs_mem_successors_list (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                                   (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                   (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                   (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1}) = 
    (forall t.  (Usize.v t >= Usize.v i /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g) /\
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (create_successors_list_for_h_index g h_index wz i))
                                   
                                                    
let field_add (h_index:hp_addr)
              (t:Usize.t{(UInt.fits (Usize.v t * Usize.v mword) Usize.n) /\
                         (UInt.fits (Usize.v h_index + (Usize.v t * Usize.v mword)) Usize.n)}) = Usize.add h_index (Usize.mul t mword)

#restart-solver 

#restart-solver 

#restart-solver

let field_ptrs_mem_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                                     (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                     (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                    (i': Usize.t{Usize.v i' == Usize.v i + 1 /\ (Usize.v i' <= Usize.v wz + 1) /\ (Usize.v i' >= 1)})
                            : Lemma
                              (requires  (forall t.  (Usize.v t >= Usize.v i' /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr (Usize.add h_index (Usize.mul t mword))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g) /\
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (create_successors_list_for_h_index g h_index wz i')) /\
                                         (let s = create_successors_list_for_h_index g h_index wz i in
                                          let succ_index = (Usize.add h_index (Usize.mul i mword)) in
                                                 (is_hp_addr succ_index) /\
                                                  isPointer succ_index g /\
                                                  (Seq.mem (read_word g succ_index) s) /\
                                                  (Seq.mem (read_word g succ_index) (get_allocated_block_addresses g))
                                                  ))
                              (ensures field_ptrs_mem_successors_list g h_index wz i) = 
 assert (Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1);
 assert (Usize.v i' <= Usize.v wz + 1);
 assert (Usize.v i' >= 1);
 let s = create_successors_list_for_h_index g h_index wz i in
 let s' = create_successors_list_for_h_index g h_index wz i' in
 let succ_index = (Usize.add h_index (Usize.mul i mword)) in
 let succ = read_word g succ_index in
 assert (forall t.  (Usize.v t >= Usize.v i' /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g) /\
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) s');
 assert (Seq.mem succ s);
 create_successors_list_for_h_index_recursing_property_lemma1  g h_index wz i i';
 assert (s == cons succ s');
 assert (Usize.v i >= Usize.v i /\ Usize.v i <= Usize.v wz);
 assert  (forall t.  (Usize.v t >= Usize.v i' /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (create_successors_list_for_h_index g h_index wz i'));
        
      
 assert  (forall t.  (Usize.v t >= Usize.v i' /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) s');
 
 assert (forall t.  (Usize.v t >= Usize.v i' /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr (Usize.add h_index (Usize.mul t mword))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g) /\
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) s');

 mem_cons succ s';
 assert (forall x. Seq.mem x s' ==> Seq.mem x s);
 assert  (forall t.  (Usize.v t >= Usize.v i' /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) s);
 
 assert  (forall t.  (Usize.v t >= Usize.v i' /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g))
                                                    );
 
 
 assert  (forall t.  (Usize.v t >= Usize.v i /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) s);
 
 assert  (forall t.  (Usize.v t >= Usize.v i /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g))
                                                    );
 
 assert  (forall t.  (Usize.v t >= Usize.v i /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g)) /\
                                                      Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) s
                                                    );
 assert (field_ptrs_mem_successors_list g h_index wz i);
 ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"
#push-options "--split_queries"

#restart-solver 

let rec create_successors_list_for_h_index_mem_lemma2 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                                     (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                                                     (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                                    

                       : Lemma
                         (ensures field_ptrs_mem_successors_list g h_index wz i)
                         
                         (decreases ((Usize.v wz + 1) - Usize.v i)) = 
  if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in
       ()
 
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_allocated_blocks_lemma g;
      field_contents_within_limits_allocated_blocks_lemma g;
      fieldaddress_within_limits_lemma_x_all g;
        
      (*assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (get_allocated_block_addresses g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);*)
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      if isPointer succ_index g  then
      (
        assert (succ == read_word g succ_index);
        assert (is_valid_header h_index g);
        assert (Seq.mem h_index (objects2 0UL g));
        assert (Seq.mem h_index (get_allocated_block_addresses g));
        
        test_allocs g h_index wz;
        assert (Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g));
        assert (Seq.mem succ (get_allocated_block_addresses g));
        assert (Seq.mem succ (objects2 0UL g));
        assert (is_valid_header succ g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        
        let s_list' = create_successors_list_for_h_index g h_index wz i' in
        create_successors_list_for_h_index_mem_lemma2 g h_index wz i';

        lemma_tl succ s_list'; 
        
        let s_list = Seq.cons succ s_list' in 
        mem_cons succ s_list';
        assert (Seq.mem succ s_list);
        assert (field_ptrs_mem_successors_list g h_index wz i');
        (*assert  (forall t.  (Usize.v t >= Usize.v i' /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (create_successors_list_for_h_index g h_index wz i'));
        
      
         assert  (forall t.  (Usize.v t >= Usize.v i' /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) s_list');
         assert  (forall t.  (Usize.v t >= Usize.v i /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) s_list);*)
         field_ptrs_mem_lemma g h_index wz i i';
         //assert (field_ptrs_mem_successors_list g h_index wz i);
         ()
         
     )
      else
      (
        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        let s_list = create_successors_list_for_h_index g h_index wz i' in
        create_successors_list_for_h_index_mem_lemma2 g h_index wz i';
        assert (field_ptrs_mem_successors_list g h_index wz i');
        (*assert  (forall t.  (Usize.v t >= Usize.v i /\ Usize.v t <= Usize.v wz) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) s_list);*)
        ()
      )
    )


#restart-solver 

#restart-solver 

let create_successors_list_for_h_index_mem_lemma3 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                           : Lemma
                             (requires (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                                       (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
                                       (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                           (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))
                            (ensures ((forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                                                     (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                                     isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                                     (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g)) /\
                                                     (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) 
                                                                 (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL))))) = 
   
 create_successors_list_for_h_index_mem_lemma2 g h_index (getWosize (read_word g h_index)) 1UL;
 ()

#restart-solver 

#restart-solver

#restart-solver

let create_successors_list_for_all_mem_lemma3 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                : Lemma
                                  (requires (forall y. Seq.mem y (get_allocated_block_addresses g) ==> is_fields_within_limit1 y (getWosize (read_word g y))) /\
                                            (forall y . Seq.mem y (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 y (getWosize (read_word g y)) g) /\ 
                                            (forall y. Seq.mem y (get_allocated_block_addresses g) ==> (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g y)) ==> 
                                                                  (Usize.v y  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)))
                                  (ensures  (forall (y:hp_addr). Seq.mem y (get_allocated_block_addresses g) ==> 
                                                   (forall t. is_fields_within_limit1 y (getWosize (read_word g y)) /\
                                                      (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                                   (is_hp_addr ((Usize.add y (Usize.mul t mword)))) /\
                                                   isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                                      (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g)) /\
                                                       (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) 
                                                           (create_successors_list_for_h_index g y (getWosize (read_word g y)) 1UL))))) = 
 Classical.forall_intro (Classical.move_requires (create_successors_list_for_h_index_mem_lemma3 g));
 ()
                                                                 
(*In the above lemma, (y:hp_addr) has to be passed explicitly*)

(*1. After GC, the fields of objects in the input heap g is the same as fields of the output heap, g3.
     a. create_roots_gray --> should not affect fields
        create_edge_list_for_graph g == create_edge_list_for_graph g1
        
     b. mark --> should not affect fields
        create_edge_list_for_graph g1 == create_edge_list_for_graph g2
        
     c. sweep --> should not affect fields
        create_edge_list_for_graph g2 == create_edge_list_for_graph g3
     d. result
        create_edge_list_for_graph g == create_edge_list_for_graph g3
        From, this we can conclude that the edge_list of allocated and reachable objects after sweep (white objects) also remain the same.
        
  2. After GC, the heap is well-formed-allocated blocks heap 
     a. White objects are the only allocated objects after sweep.
     b. White objects fields remain the same from the above lemma.
     c. The field pointers of an allocated object are the edges in the allocated object graph
     d. All the white objects and only the white objects are reachable from roots.
     e. The edges of the white objects are reachable from roots, hence they are white and hence they are pointing to allocated objects.
     f. Hence well-formed-allocated objects heap.
  3. After GC, All the reachable and only the reachable objects form the vertices of the allocated objects graph.
  4. After GC, All the edges between the reachable objects should be preserved
     *)

open FStar.Classical

#reset-options "--z3rlimit 1000"

#restart-solver

let black_object_fields_reach_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                                                 
                                    (g2:heap{well_formed_heap2 g2 /\ well_formed_allocated_blocks g2}) (*---> heap after mark*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (h_index:hp_addr{Seq.mem h_index (get_allocated_block_addresses g)})
                                                                  
               
                :Lemma
                 (requires   (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                             (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\ 
                             (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                             (objects2 0UL g2 == objects2 0UL g) /\
                             (get_allocated_block_addresses g == get_allocated_block_addresses g2) /\
                             (color_of_object1 h_index g2 == black) /\
                             (create_graph_from_heap g == create_graph_from_heap g2) /\
                             (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2) /\
                             (forall x.  (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)))
                 (ensures (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                                 (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                 isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                 (*the below condition is necessary to typecheck*)
                                 (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g2)) /\ 
                                         (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (objects2 0UL g2)) /\ 
                                                                           isBlackObject1 (read_word g (Usize.add h_index (Usize.mul t mword))) g2)) = 
  assert (forall x.  (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
  assert (color_of_object1 h_index g2 == black);
  assert (exists o (z1: G.reach (create_graph_from_heap g) o h_index). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o h_index z1);
                                                                                     
  let _ = exists_elim 
           (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==> 
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o y r1))
           ()
           (fun (o:hp_addr{Seq.mem o h_list /\ 
                         (exists (z1: G.reach (create_graph_from_heap g) o h_index). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o h_index z1)}) -> 

              assert (Seq.mem h_index (get_allocated_block_addresses g));
              assert (G.mem_graph_vertex (create_graph_from_heap g) h_index);
              assert (Seq.mem o (get_allocated_block_addresses g));
              assert (G.mem_graph_vertex (create_graph_from_heap g) o);

              assert (exists (p: (G.reach (create_graph_from_heap g) o h_index)). G.reachfunc (create_graph_from_heap g) o h_index p);
              
              let _ = G.succ_reach_transitive_lemma1 (create_graph_from_heap g) o h_index in
              
              assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==> 
                                                  (exists (r1: G.reach (create_graph_from_heap g) o y).G.reachfunc (create_graph_from_heap g) o y r1));
             
              assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==> 
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o y r1));
              ()) in 
  
   
    assert (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2);
    assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==>  (Seq.mem y (objects2 0UL g2)) /\ isBlackObject1 y g2);
    
    field_limits_allocated_blocks_lemma g;
    field_contents_within_limits_allocated_blocks_lemma g;
    fieldaddress_within_limits_lemma_x_all g;
    graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
    assert (G.successors (create_graph_from_heap g) h_index == 
                                             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
    
    assert (forall y. Seq.mem y (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) ==>  (Seq.mem y (objects2 0UL g2)) /\ isBlackObject1 y g2);
    
    
    create_successors_list_for_h_index_mem_lemma2 g h_index (getWosize (read_word g h_index)) 1UL;
    
    assert (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                  (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                  isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                  Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL));
   
    assert (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                  (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                  isPointer (Usize.add h_index (Usize.mul t mword)) g ==>  (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (objects2 0UL g2)) /\ 
                                                                           isBlackObject1 (read_word g (Usize.add h_index (Usize.mul t mword))) g2);
    ()

#restart-solver 

#restart-solver

#restart-solver

#restart-solver


let white_object_fields_reach_lemma1 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                                                 
                                    (g3:heap{well_formed_heap2 g3}) (*---> heap after mark*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (h_index:hp_addr{Seq.mem h_index (get_allocated_block_addresses g) /\
                                                     Seq.mem h_index (get_allocated_block_addresses g3)})
                                                                  
               
                :Lemma
                 (requires   (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                             (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\ 
                             (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                             (forall x. Seq.mem x (objects2 0UL g3) ==>  Seq.mem x (objects2 0UL g)) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> Seq.mem x (get_allocated_block_addresses g)) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g3) <==> Seq.mem x (objects2 0UL g3) /\ isWhiteObject1 x g3) /\
                             (color_of_object1 h_index g3 == white) /\
                             
                             (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3) /\
                             (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)))
                 (ensures (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                                 (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                 isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                 (*the below condition is necessary to typecheck*)
                                 (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g3)) /\ 
                                         (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (objects2 0UL g3)) /\ 
                                                                           isWhiteObject1 (read_word g (Usize.add h_index (Usize.mul t mword))) g3)) = 
                                                                           
 assert (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
  assert (color_of_object1 h_index g3 == white);
  assert (exists o (z1: G.reach (create_graph_from_heap g) o h_index). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o h_index z1);
                                                                                     
  let _ = exists_elim 
           (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==> 
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o y r1))
           ()
           (fun (o:hp_addr{Seq.mem o h_list /\ 
                         (exists (z1: G.reach (create_graph_from_heap g) o h_index). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o h_index z1)}) -> 

              assert (Seq.mem h_index (get_allocated_block_addresses g));
              assert (G.mem_graph_vertex (create_graph_from_heap g) h_index);
              assert (Seq.mem o (get_allocated_block_addresses g));
              assert (G.mem_graph_vertex (create_graph_from_heap g) o);

              assert (exists (p: (G.reach (create_graph_from_heap g) o h_index)). G.reachfunc (create_graph_from_heap g) o h_index p);
              
              let _ = G.succ_reach_transitive_lemma1 (create_graph_from_heap g) o h_index in
              
              assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==> 
                                                  (exists (r1: G.reach (create_graph_from_heap g) o y).G.reachfunc (create_graph_from_heap g) o y r1));
             
              assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==> 
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o y r1));
              ()) in 
  

 assert (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3);
 assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==>  (Seq.mem y (objects2 0UL g3)) /\ isWhiteObject1 y g3);
 
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 
 graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
 
 assert (G.successors (create_graph_from_heap g) h_index == 
                                             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
    
 assert (forall y. Seq.mem y (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) ==>  
            (Seq.mem y (objects2 0UL g3)) /\ isWhiteObject1 y g3);
    
    
 create_successors_list_for_h_index_mem_lemma2 g h_index (getWosize (read_word g h_index)) 1UL;

 assert (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                  (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                  isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                  Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL));

 assert (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                  (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                  isPointer (Usize.add h_index (Usize.mul t mword)) g ==>  
                            (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g3)) /\
                                                                          (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (objects2 0UL g3)) /\ 
                                                                           isWhiteObject1 (read_word g (Usize.add h_index (Usize.mul t mword))) g3);

()

#restart-solver 

#restart-solver

#restart-solver 

#restart-solver

//#push-options "--z3rlimit 500"


let white_object_fields_reach_lemma3 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                                                 
                                    (g3:heap{well_formed_heap2 g3}) (*---> heap after mark*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (h_index:hp_addr{Seq.mem h_index (get_allocated_block_addresses g) /\
                                                     Seq.mem h_index (get_allocated_block_addresses g3)})
                                                                  
               
                :Lemma
                 (requires   (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                             (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\ 
                             (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) (*/\
                             
                             
                             (is_fields_within_limit1 h_index (getWosize (read_word g3 h_index))) /\
                             (is_fields_contents_within_limit2 h_index (getWosize (read_word g3 h_index)) g3) /\ 
                             (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g3 h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) *)/\
                                                                  
                             (forall x. Seq.mem x (objects2 0UL g3) ==>  Seq.mem x (objects2 0UL g)) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> Seq.mem x (get_allocated_block_addresses g)) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g3) <==> Seq.mem x (objects2 0UL g3) /\ isWhiteObject1 x g3) /\
                             (color_of_object1 h_index g3 == white) /\
                             
                             (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3) /\
                             (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)))
                 (ensures (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                                 (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                                 isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                                 (*the below condition is necessary to typecheck*)
                                 (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g3)) /\ 
                                         (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (objects2 0UL g3)) /\ 
                                                                           isWhiteObject1 (read_word g (Usize.add h_index (Usize.mul t mword))) g3)) = 
                                                                           
 assert (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
  assert (color_of_object1 h_index g3 == white);
  assert (exists o (z1: G.reach (create_graph_from_heap g) o h_index). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o h_index z1);
                                                                                     
  let _ = exists_elim 
           (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==> 
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o y r1))
           ()
           (fun (o:hp_addr{Seq.mem o h_list /\ 
                         (exists (z1: G.reach (create_graph_from_heap g) o h_index). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o h_index z1)}) -> 

              assert (Seq.mem h_index (get_allocated_block_addresses g));
              assert (G.mem_graph_vertex (create_graph_from_heap g) h_index);
              assert (Seq.mem o (get_allocated_block_addresses g));
              assert (G.mem_graph_vertex (create_graph_from_heap g) o);

              assert (exists (p: (G.reach (create_graph_from_heap g) o h_index)). G.reachfunc (create_graph_from_heap g) o h_index p);
              
              let _ = G.succ_reach_transitive_lemma1 (create_graph_from_heap g) o h_index in
              
              assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==> 
                                                  (exists (r1: G.reach (create_graph_from_heap g) o y).G.reachfunc (create_graph_from_heap g) o y r1));
             
              assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==> 
                                                  (exists o (r1: G.reach (create_graph_from_heap g) o y). Seq.mem o h_list /\ G.reachfunc (create_graph_from_heap g) o y r1));
              ()) in 
  

 assert (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3);
 assert (forall y. Seq.mem y (G.successors (create_graph_from_heap g) h_index) ==>  (Seq.mem y (objects2 0UL g3)) /\ isWhiteObject1 y g3);
 
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 
 graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
 
 assert (G.successors (create_graph_from_heap g) h_index == 
                                             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
    
 assert (forall y. Seq.mem y (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) ==>  
            (Seq.mem y (objects2 0UL g3)) /\ isWhiteObject1 y g3);
    
    
 create_successors_list_for_h_index_mem_lemma2 g h_index (getWosize (read_word g h_index)) 1UL;

 assert (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                  (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                  isPointer (Usize.add h_index (Usize.mul t mword)) g ==>
                  Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL));

 assert (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g h_index))) /\
                  (is_hp_addr ((Usize.add h_index (Usize.mul t mword)))) /\
                  isPointer (Usize.add h_index (Usize.mul t mword)) g ==>  
                            (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (get_allocated_block_addresses g3)) /\
                                                                          (Seq.mem (read_word g (Usize.add h_index (Usize.mul t mword))) (objects2 0UL g3)) /\ 
                                                                           isWhiteObject1 (read_word g (Usize.add h_index (Usize.mul t mword))) g3);

()


#restart-solver 

#restart-solver 

#restart-solver

let graph_successors_heap_create_successor_list_equivalence_lemma_all (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                                      (*(h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))})*)
                                : Lemma
                                  (requires ((forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                  is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                  
                                             (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                  is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                                                        
                                             (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                  (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x)) ==> 
                                                                  (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))))
                                  (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                      G.successors (create_graph_from_heap g) x == 
                                                      create_successors_list_for_h_index g x (getWosize (read_word g x)) 1UL)) = 
Classical.forall_intro (Classical.move_requires (graph_successors_heap_create_successor_list_equivalence_lemma g))

#restart-solver 

#restart-solver

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#restart-solver

let white_object_all_fields_reach_lemma1 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                                                 
                                    (g3:heap{well_formed_heap2 g3}) (*---> heap after sweep*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                           :Lemma
                            (requires   
                             (forall y. Seq.mem y (get_allocated_block_addresses g) ==> is_fields_within_limit1 y (getWosize (read_word g y))) /\
                             (forall y . Seq.mem y (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 y (getWosize (read_word g y)) g) /\ 
                             (forall y. Seq.mem y (get_allocated_block_addresses g) ==> (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g y)) ==> 
                                                                  (Usize.v y  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)) /\
                             
                             
                             (forall y. Seq.mem y (get_allocated_block_addresses g3) ==> is_fields_within_limit1 y (getWosize (read_word g3 y))) /\
                             (forall y . Seq.mem y (get_allocated_block_addresses g3) ==> is_fields_contents_within_limit2 y (getWosize (read_word g3 y)) g3) /\ 
                             (forall y. Seq.mem y (get_allocated_block_addresses g3) ==> (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g3 y)) ==> 
                                                                  (Usize.v y  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)) /\
                                                                  
                             (forall x. Seq.mem x (objects2 0UL g3) ==>  Seq.mem x (objects2 0UL g)) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> Seq.mem x (get_allocated_block_addresses g)) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g3) <==> Seq.mem x (objects2 0UL g3) /\ isWhiteObject1 x g3) /\
                             
                             (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3) /\
                             (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)) /\
                             (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                             G.successors (create_graph_from_heap g) y == 
                                             create_successors_list_for_h_index g y (getWosize (read_word g y)) 1UL) /\
                                             
                             (forall y. Seq.mem y (get_allocated_block_addresses g3) /\
                                   Seq.mem y (get_allocated_block_addresses g) ==> 
                                    (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                     (is_hp_addr ((Usize.add y (Usize.mul t mword)))) /\
                                     isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                      Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) 
                                        (create_successors_list_for_h_index g y (getWosize (read_word g y)) 1UL)))
                                        
                             )
                            (ensures (forall y. Seq.mem y (get_allocated_block_addresses g3) /\ 
                                           Seq.mem y (get_allocated_block_addresses g) /\
                                           color_of_object1 y g3 == white ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                           (is_hp_addr ((Usize.add y (Usize.mul t mword)))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3)) /\ 
                                                  (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (objects2 0UL g3)) /\ 
                                                                           isWhiteObject1 (read_word g (Usize.add y (Usize.mul t mword))) g3))) = 
graph_successors_heap_create_successor_list_equivalence_lemma_all g;
create_successors_list_for_all_mem_lemma3 g;
Classical.forall_intro (Classical.move_requires (white_object_fields_reach_lemma3 g g3 h_list));
()

#restart-solver 

#restart-solver

let white_object_all_fields_reach_lemma3 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                                                 
                                    (g3:heap{well_formed_heap2 g3}) (*---> heap after sweep*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                           :Lemma
                            (requires   
                             (forall y. Seq.mem y (get_allocated_block_addresses g) ==> is_fields_within_limit1 y (getWosize (read_word g y))) /\
                             (forall y . Seq.mem y (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 y (getWosize (read_word g y)) g) /\ 
                             (forall y. Seq.mem y (get_allocated_block_addresses g) ==> (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g y)) ==> 
                                                                  (Usize.v y  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)) /\
                             
                             
                             (forall y. Seq.mem y (get_allocated_block_addresses g3) ==> is_fields_within_limit1 y (getWosize (read_word g3 y))) /\
                             (forall y . Seq.mem y (get_allocated_block_addresses g3) ==> is_fields_contents_within_limit2 y (getWosize (read_word g3 y)) g3) /\ 
                             (forall y. Seq.mem y (get_allocated_block_addresses g3) ==> (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g3 y)) ==> 
                                                                  (Usize.v y  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)) /\
                                                                  
                             (forall x. Seq.mem x (objects2 0UL g3) ==>  Seq.mem x (objects2 0UL g)) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> Seq.mem x (get_allocated_block_addresses g)) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g3) <==> Seq.mem x (objects2 0UL g3) /\ isWhiteObject1 x g3) /\
                             
                             (forall y. Seq.mem y (get_allocated_block_addresses g3) /\ 
                                           Seq.mem y (get_allocated_block_addresses g) /\
                                           color_of_object1 y g3 == white ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                           (is_hp_addr ((Usize.add y (Usize.mul t mword)))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3)) /\ 
                                                  (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (objects2 0UL g3)) /\ 
                                                                           isWhiteObject1 (read_word g (Usize.add y (Usize.mul t mword))) g3)) /\
                             (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                         Usize.v (getWosize (read_word g y)) == Usize.v (getWosize (read_word g3 y))) /\
                             (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                     (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                     (is_hp_addr (Usize.add y (Usize.mul t mword))) ==>
                                     Usize.v (read_word g (Usize.add y (Usize.mul t mword))) == 
                                     Usize.v (read_word g3 (Usize.add y (Usize.mul t mword)))))
                             )
                            (ensures (well_formed_allocated_blocks g3)) = 
assert (forall y. Seq.mem y (get_allocated_block_addresses g3) /\ 
                                           Seq.mem y (get_allocated_block_addresses g) /\
                                           color_of_object1 y g3 == white ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                           (is_hp_addr (Usize.add y (Usize.mul t mword))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3)) /\ 
                                                  (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (objects2 0UL g3)) /\ 
                                                                           isWhiteObject1 (read_word g (Usize.add y (Usize.mul t mword))) g3));

assert (forall y. Seq.mem y (get_allocated_block_addresses g3) /\ 
                                           Seq.mem y (get_allocated_block_addresses g) /\
                                           color_of_object1 y g3 == white ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                           (is_hp_addr (Usize.add y (Usize.mul t mword))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3)))); 
                                                 
assert (forall y. Seq.mem y (get_allocated_block_addresses g3) /\
                                           color_of_object1 y g3 == white ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                           (is_hp_addr (Usize.add y (Usize.mul t mword))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3)))); 
assert (forall x. Seq.mem x (get_allocated_block_addresses g3) <==> Seq.mem x (objects2 0UL g3) /\ isWhiteObject1 x g3);
assert (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> Seq.mem x (objects2 0UL g3) /\ isWhiteObject1 x g3);
assert (forall x. Seq.mem x (get_allocated_block_addresses g3) ==>  color_of_object1 x g3 == white);
assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                         Usize.v (getWosize (read_word g y)) == Usize.v (getWosize (read_word g3 y)));

assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                           (is_hp_addr (Usize.add y (Usize.mul t mword))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3))));
assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                           (is_hp_addr (Usize.add y (Usize.mul t mword))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3))));
assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                           (is_hp_addr (Usize.add y (Usize.mul t mword))) ==>
                                            Usize.v (read_word g (Usize.add y (Usize.mul t mword))) == Usize.v (read_word g3 (Usize.add y (Usize.mul t mword)))));

assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                           (is_hp_addr (Usize.add y (Usize.mul t mword))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g3 ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3))));
assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                           (is_hp_addr (Usize.add y (Usize.mul t mword))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g3 ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g3 (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3))));

assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==> 
              (forall i.  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g3 y))) /\
                                                     (is_hp_addr (Usize.add y (Usize.mul i mword))) /\
                                                     isPointer (Usize.add y (Usize.mul i mword)) g3 ==>
                                                     Seq.mem (read_word g3 (Usize.add y (Usize.mul i mword))) (get_allocated_block_addresses g3)));
assert (check_fields_points_to_allocs2 g3 (get_allocated_block_addresses g3));
assert (well_formed_allocated_blocks g3);
()

#reset-options "--z3rlimit 1000"

#push-options "--split_queries"

#restart-solver



#restart-solver

let rec mark5_objects2_lemma (g:heap{well_formed_heap2 g}) 
                             (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                                      
          :Lemma
            (requires (well_formed_heap2 (mark5 g st)))
            (ensures (objects2 0UL g == objects2 0UL (mark5 g st)) /\
                     (get_allocated_block_addresses g == get_allocated_block_addresses (mark5 g st)))
            (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
  if (G.is_emptySet st) then
   (
      assert (objects2 0UL g == objects2 0UL (mark5 g st));
      assert (get_allocated_block_addresses g == get_allocated_block_addresses (mark5 g st));
      ()
   )
 else
   (
      let st', g' = mark5_body g st in
      assert (objects2 0UL g == objects2 0UL g');
      assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
      let v_id = Seq.index st (Seq.length st - 1) in
      assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
      assert (is_valid_header v_id g);

      stack_slice_only_has_gray_color_lemma g st v_id 3UL;

      assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1)));
      
      
      mark5_body_black_nodes_lemma g st;
      
      
      assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
      
      let g'' = mark5 g' st' in
      mark5_objects2_lemma g' st';
      assert (objects2 0UL g' == objects2 0UL g'');
      assert (objects2 0UL g == objects2 0UL g'');
      assert (get_allocated_block_addresses g' == get_allocated_block_addresses g'');
      assert (get_allocated_block_addresses g == get_allocated_block_addresses g'');
      ()
   )
  
#restart-solver

let mark_and_sweep_GC1_well_formed_allocated_blocks1_lemma5 (g:heap{well_formed_heap2 g /\ 
                                                                  well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                         (*root pointers--------------------------------------------------------------------------------------------*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (c:color{c == 3UL})
                                    (c1:color{c1 == 2UL})
                : Lemma
                  (ensures (forall x. Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list)) /\ (isWhiteObject1 x (mark_and_sweep_GC1 g h_list)) <==> 
                                             Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)))) = 
                           
 
(*Mark stack creation-----------------------------------------------------------------------------------------*)
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);

 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in
 create_root_stack_and_gray_modified_heap_noBlackObjects_lemma g st h_list;
 assert (noBlackObjects g1);
 let allocs = get_allocated_block_addresses g1 in
 let vl = get_black_block_addresses g1 allocs in
 assert (Seq.length vl == 0);
 assert (Seq.length st == 0);
 create_root_stack_and_gray_modified_heap_mem_lemma g st h_list;
 assert ((forall x. Seq.mem x st ==> Seq.mem x st') /\
                (forall x. Seq.mem x h_list ==> Seq.mem x st'));
 assert (forall x. Seq.mem x st' ==> Seq.mem x st \/ Seq.mem x h_list);
 assert (forall x. Seq.mem x st' ==> Seq.mem x h_list);
 assert (forall x. Seq.mem x st' <==> Seq.mem x h_list);
 assert (objects2 0UL g == objects2 0UL g1);
 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);
 assert (G.is_vertex_set st');
 assert (G.subset_vertices st' (get_allocated_block_addresses g1));
 assert (G.subset_vertices vl (get_allocated_block_addresses g1));
 assert (well_formed_heap2 g2);
 assert (well_formed_allocated_blocks g);
 mark5_objects2_lemma g1 st';
 assert (objects2 0UL g1 == objects2 0UL g2);
 assert (objects2 0UL g == objects2 0UL g2);
 
 create_root_stack_and_gray_modified_heap_well_formed_allocated_blocks_lemma g st h_list c1;
 
 assert (well_formed_allocated_blocks g1);
 well_formed_allocated_blocks_mark5 g1 st' c;
 assert (well_formed_allocated_blocks g2);
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
 assert (G.subset_vertices h_list (get_allocated_block_addresses g));
 assert (G.subset_vertices h_list (get_allocated_block_addresses g1));
 assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));

 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3 = sweep1 g2 0UL in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);
                                      
 assert (well_formed_allocated_blocks g2);
 
 let allocs_sweep1 = get_allocated_block_addresses g3 in
 field_limits_allocated_blocks_lemma g2;
 field_contents_within_limits_allocated_blocks_lemma g2;
 fieldaddress_within_limits_lemma_x_all g2;
 allocs_of_after_sweep_is_subset_of_allocs_before_sweep g2;
 assert (forall x. Seq.mem x (objects2 0UL g3) /\ (isWhiteObject1 x g3) <==> Seq.mem x allocs_sweep1);

 
 assert (forall x. Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list)) /\ (isWhiteObject1 x (mark_and_sweep_GC1 g h_list)) <==> 
                                             Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)));
 ()


#restart-solver


let create_graph_from_heap_structurelemma (g:heap {well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                   : Lemma
                    (requires True)
                    (ensures (create_graph_from_heap g).vertices == get_allocated_block_addresses g /\
                             (create_graph_from_heap g).edge_set == create_edge_list_for_graph g) = ()


#restart-solver 

let create_edge_list_for_graph_structure_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
               : Lemma
                 (requires  (forall x. Seq.mem x ((get_allocated_block_addresses g))==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                                                                             (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)))
                 (ensures create_edge_list_for_graph g == create_edge_list_from_heap g (get_allocated_block_addresses g)) = ()
  
let  create_edge_list_from_heap_structure_lemma   (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                    : Lemma
                      (requires  (forall x. Seq.mem x ((get_allocated_block_addresses g))==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                                                                             (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)))
                      (ensures  (forall x. Seq.mem x (get_allocated_block_addresses g) ==> G.successors_fn2 x (create_edge_list_from_heap g (get_allocated_block_addresses g)) == 
                                                                                     G.successors_fn2 x (create_edge_pairs_for_h_index g 
                                                                                                         x 
                                                                                                         (getWosize (read_word g x))
                                                                                                         1UL))) = ()
                                                                                 
#restart-solver 

#restart-solver 

let successors_list_remain_same_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                                                 
                                    (g2:heap{well_formed_heap2 g2 /\ well_formed_allocated_blocks g2}) (*---> heap after mark*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (h_index:hp_addr{Seq.mem h_index (get_allocated_block_addresses g)})
                                                                  
               
                :Lemma
                 (requires   (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                             (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\ 
                             (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                             (is_fields_within_limit1 h_index (getWosize (read_word g2 h_index))) /\
                             (is_fields_contents_within_limit2 h_index (getWosize (read_word g2 h_index)) g2) /\ 
                             (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g2 h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                             (get_allocated_block_addresses g == get_allocated_block_addresses g2) /\
                             
                             (create_graph_from_heap g == create_graph_from_heap g2))
                (ensures (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index))
                                             1UL ==
                          create_successors_list_for_h_index g2 h_index (getWosize (read_word g2 h_index))
                                             1UL)) = 
  let grph = create_graph_from_heap g in
  let grph1 = create_graph_from_heap g2 in
  assert (grph == grph1);
  assert (grph.vertices == grph1.vertices);
  assert (grph.edge_set == grph1.edge_set);
  graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
  
 
  
  assert (G.successors (create_graph_from_heap g) h_index == 
                                             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
  field_limits_allocated_blocks_lemma g;
  field_contents_within_limits_allocated_blocks_lemma g;
  fieldaddress_within_limits_lemma_x_all g;

  field_limits_allocated_blocks_lemma g2;
  field_contents_within_limits_allocated_blocks_lemma g2;
  fieldaddress_within_limits_lemma_x_all g2;

  graph_successors_heap_create_successor_list_equivalence_lemma g2 h_index;
  
  create_edge_list_from_heap_structure_lemma g;
  create_edge_list_from_heap_structure_lemma g2;

  assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> G.successors_fn2 x (create_edge_list_from_heap g (get_allocated_block_addresses g)) == 
                                                                                     G.successors_fn2 x (create_edge_pairs_for_h_index g 
                                                                                                         x 
                                                                                                         (getWosize (read_word g x))
                                                                                                         1UL));
  
  
  assert (forall x. Seq.mem x (get_allocated_block_addresses g2) ==> G.successors_fn2 x (create_edge_list_from_heap g2 (get_allocated_block_addresses g2)) == 
                                                                                     G.successors_fn2 x (create_edge_pairs_for_h_index g2 
                                                                                                         x 
                                                                                                         (getWosize (read_word g2 x))
                                                                                                         1UL));
                                                                                                         
  assert (G.successors_fn2 h_index (create_edge_list_from_heap g (get_allocated_block_addresses g)) == 
                                                                                     G.successors_fn2 h_index (create_edge_pairs_for_h_index g 
                                                                                                         h_index 
                                                                                                         (getWosize (read_word g h_index))
                                                                                                         1UL));

  assert (G.successors_fn2 h_index (create_edge_list_from_heap g2 (get_allocated_block_addresses g2)) == 
                                                                                     G.successors_fn2 h_index (create_edge_pairs_for_h_index g2 
                                                                                                         h_index 
                                                                                                         (getWosize (read_word g2 h_index))
                                                                                                         1UL));
                                                                                                         
  create_edge_list_for_graph_structure_lemma g;

  create_edge_list_for_graph_structure_lemma g2;
  assert (G.successors_fn2 h_index (create_edge_list_for_graph g) ==  G.successors_fn2 h_index (create_edge_pairs_for_h_index g 
                                                                                                         h_index 
                                                                                                         (getWosize (read_word g h_index))
                                                                                                         1UL));

  assert (G.successors_fn2 h_index (create_edge_list_for_graph g2) ==  G.successors_fn2 h_index (create_edge_pairs_for_h_index g2 
                                                                                                         h_index 
                                                                                                         (getWosize (read_word g2 h_index))
                                                                                                         1UL));
                                                                                                         
  create_graph_from_heap_structurelemma g;
  create_graph_from_heap_structurelemma g2;
  
  assert (G.successors_fn2 h_index ((create_graph_from_heap g).edge_set) ==  G.successors_fn2 h_index (create_edge_pairs_for_h_index g 
                                                                                                         h_index 
                                                                                                         (getWosize (read_word g h_index))
                                                                                                         1UL));                                                           
                                                                                                                

  assert (G.successors_fn2 h_index (grph.edge_set) ==  G.successors_fn2 h_index (create_edge_pairs_for_h_index g 
                                                                                                         h_index 
                                                                                                         (getWosize (read_word g h_index))
                                                                                                         1UL)); 
                                                                                                         
  assert (G.successors_fn2 h_index ((create_graph_from_heap g2).edge_set) ==  G.successors_fn2 h_index (create_edge_pairs_for_h_index g2 
                                                                                                         h_index 
                                                                                                         (getWosize (read_word g2 h_index))
                                                                                                         1UL)); 
  assert (G.successors_fn2 h_index (grph1.edge_set) ==  G.successors_fn2 h_index (create_edge_pairs_for_h_index g2 
                                                                                                         h_index 
                                                                                                         (getWosize (read_word g2 h_index))
                                                                                                       1UL)); 

  assert (G.successors_fn2 h_index (grph.edge_set) == G.successors_fn2 h_index (grph1.edge_set)); 
   
                                                                                                                                                                                
                                                                                                                                                                            
                                                                                                                                                                                G.successors_successors_fn2_connect_lemma (create_graph_from_heap g) h_index; 

  G.successors_successors_fn2_connect_lemma (create_graph_from_heap g2) h_index; 
  
  assert (G.successors_fn2 h_index ((create_graph_from_heap g).edge_set) == G.successors (create_graph_from_heap g) h_index);
  assert (G.successors_fn2 h_index ((create_graph_from_heap g2).edge_set) == G.successors (create_graph_from_heap g2) h_index);

  assert (G.successors_fn2 h_index (grph.edge_set) == G.successors grph h_index);
  assert (G.successors_fn2 h_index (grph1.edge_set) == G.successors grph1 h_index);

  assert (G.successors grph h_index == G.successors grph1 h_index);
  graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
  graph_successors_heap_create_successor_list_equivalence_lemma g2 h_index;
                                                                                                           
  assert (G.successors grph h_index ==  create_successors_list_for_h_index g h_index (getWosize (read_word g h_index))
                                             1UL);                                                                                                       
                                                                                                        
                                                                                                       
  assert (G.successors grph1 h_index ==  create_successors_list_for_h_index g2 h_index (getWosize (read_word g2 h_index))
                                             1UL); 
  assert (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index))
                                             1UL ==
          create_successors_list_for_h_index g2 h_index (getWosize (read_word g2 h_index))
                                             1UL);
  ()
                
let successors_list_for_all_remain_same_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                                                 
                                              (g2:heap{well_formed_heap2 g2 /\ well_formed_allocated_blocks g2}) (*---> heap after mark*)
                                              (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                   
                 :Lemma
                 (requires   (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\ 
                             (forall x. Seq.mem x (get_allocated_block_addresses g) ==> (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x)) ==> 
                                                                  (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g2) ==> is_fields_within_limit1 x (getWosize (read_word g2 x))) /\
                             (forall x. Seq.mem x (get_allocated_block_addresses g2) ==> is_fields_contents_within_limit2 x (getWosize (read_word g2 x)) g2) /\ 
                             (forall x. Seq.mem x (get_allocated_block_addresses g2) ==> (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g2 x)) ==> 
                                                                  (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)) /\
                             (get_allocated_block_addresses g == get_allocated_block_addresses g2) /\
                             
                             (create_graph_from_heap g == create_graph_from_heap g2))
                (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                 create_successors_list_for_h_index g x (getWosize (read_word g x)) 1UL ==
                                 create_successors_list_for_h_index g2 x (getWosize (read_word g2 x)) 1UL)) =  
Classical.forall_intro (Classical.move_requires (successors_list_remain_same_lemma g g2 h_list))




#restart-solver 

let allocs_property (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                    (h_index: hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                
                 : Lemma 
                   (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                      (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                      (Usize.v (getWosize (read_word g x)) <= Usize.v (getWosize (read_word g x))) /\
                                      (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v  (getWosize (read_word g x)) ==> 
                                             (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)))
                                             
                   (ensures ((forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v  (getWosize (read_word g h_index)))/\
                                   (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
                                   isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                   Seq.mem (read_word g (Usize.add h_index (Usize.mul i mword))) (get_allocated_block_addresses g)))) = 
  test_allocs g h_index (getWosize (read_word g h_index))
    
 #restart-solver 
 
let allocs_all_property (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                   : Lemma 
                   (requires (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                      (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                      (Usize.v (getWosize (read_word g x)) <= Usize.v (getWosize (read_word g x))) /\
                                      (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v  (getWosize (read_word g x)) ==> 
                                             (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)))
                                             
                   (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) ==> (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)))/\
                                   (is_hp_addr ((Usize.add x (Usize.mul i mword)))) /\
                                   isPointer (Usize.add x (Usize.mul i mword)) g ==>
                                                   Seq.mem (read_word g (Usize.add x (Usize.mul i mword))) (get_allocated_block_addresses g)))) = 
 Classical.forall_intro (Classical.move_requires (allocs_property g))



#restart-solver 

let field_limits_objects2_lemma (g:heap{well_formed_heap2 g})
                    : Lemma
                      (ensures (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_within_limit1 x (getWosize (read_word g x)))) = 
 assert (well_formed_heap2 g);
 let objs = objects2 0UL g in
 assert (forall x. Seq.mem x objs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 assert (G.subset_vertices (get_allocated_block_addresses g) objs);
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 assert (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_within_limit1 x (getWosize (read_word g x)));
 ()

let field_contents_within_limits_objects2_lemma (g:heap{well_formed_heap2 g})
                                            : Lemma
                                              (ensures (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)) = 
 assert (well_formed_heap2 g);
 let objs = objects2 0UL g in
 assert (check_all_block_fields_within_limit2 g objs);
 assert ((forall x. Seq.mem x objs ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
 assert (G.subset_vertices (get_allocated_block_addresses g) objs);  
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
 ()

#restart-solver 

let seq_empty_lemma5 ()
            : Lemma
              (ensures (Seq.length (Seq.empty #UInt64.t) == 0)) = ()


#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver 

let rec field_pointers_for_h_index (g:heap{well_formed_heap2 g}) 

                                   (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g (*/\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))*)})
                                           
                                   (wz: wosize{((wz == getWosize (read_word g h_index)) /\ is_fields_within_limit1 h_index wz /\
                                                                       is_fields_contents_within_limit2 h_index wz g /\
                                                         (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                  (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                   (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                       : Tot (seq Usize.t) 
                         
                         (decreases ((Usize.v wz + 1) - Usize.v i)) = 

if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in

       seq_empty_lemma5 ();
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
      
       s_list
 
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_objects2_lemma g;
      field_contents_within_limits_objects2_lemma g;
      fieldaddress_within_limits_lemma_x_all3 g;
        
      assert (forall x. Seq.mem x (objects2 0UL g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (objects2 0UL g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (objects2 0UL g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      if isPointer succ_index g  then
      (
        assert (succ == read_word g succ_index);
        assert (is_valid_header h_index g);
        assert (Seq.mem h_index (objects2 0UL g));
        

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        
        let s_list' = field_pointers_for_h_index g h_index wz i' in
        

        lemma_tl succ s_list'; 
        
        let s_list = Seq.cons succ s_list' in 
        s_list
     )
      else
      (
        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        let s_list = field_pointers_for_h_index g h_index wz i' in
        s_list
      )
    )

let rec field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma (g:heap{well_formed_heap2 g}) 

                                                                                   (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                              (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                               is_valid_header h_index g})
                                                                                             
                                           
                                                                                   (wz: wosize{((wz == getWosize (read_word g h_index)) /\ 
                                                                                            is_fields_within_limit1 h_index wz /\
                                                                                            is_fields_contents_within_limit2 h_index wz g /\
                                                                                            (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v wz ==> 
                                                                                            (Usize.v h_index  + 
                                                                                                (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))})
                         
                                                                                   (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1}) 
                                      :Lemma
                                       (requires (well_formed_allocated_blocks g) /\ (Seq.mem h_index (get_allocated_block_addresses g))) 
                                       (ensures (field_pointers_for_h_index g h_index wz i == create_successors_list_for_h_index g h_index wz i)) 
                                       (decreases ((Usize.v wz + 1) - Usize.v i)) = 
if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in

       seq_empty_lemma5 ();
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
      
       ()
 
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_objects2_lemma g;
      field_contents_within_limits_objects2_lemma g;
      fieldaddress_within_limits_lemma_x_all3 g;
        
      assert (forall x. Seq.mem x (objects2 0UL g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (objects2 0UL g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (objects2 0UL g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      if isPointer succ_index g  then
      (
        assert (succ == read_word g succ_index);
        assert (is_valid_header h_index g);
        assert (Seq.mem h_index (objects2 0UL g));
        

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        
        let s_list' = field_pointers_for_h_index g h_index wz i' in
        

        lemma_tl succ s_list'; 
        
        let s_list = Seq.cons succ s_list' in 
        field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma g h_index wz i';
        ()
     )
      else
      (
        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        let s_list = field_pointers_for_h_index g h_index wz i' in
        field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma g h_index wz i';
        ()
      )
    )

#restart-solver 

let rec field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma1 (g:heap{well_formed_heap2 g}) 
                                                                                    (i:Usize.t)

                                                                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                    is_valid_header h_index g /\
                                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})
                                       :Lemma
                                       (requires (well_formed_allocated_blocks g) /\ 
                                                 
                                                 (Usize.v i <= Usize.v (getWosize (read_word g h_index)) + 1 /\ Usize.v i >= 1) /\
                                                 (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
                                                 (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
                                                  (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                            (Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))
                                                                                                
                                                                                       
                                       (ensures (field_pointers_for_h_index g h_index (getWosize (read_word g h_index)) i == 
                                                    create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i)) 
                                       (decreases ((Usize.v (getWosize (read_word g h_index)) + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v (getWosize (read_word g h_index)) + 1 then
    (
       let s_list = Seq.empty #UInt64.t in

       seq_empty_lemma5 ();
       assert (Seq.length s_list == 0);
       ()
 
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Seq.mem h_index (objects2 0UL g));
      assert (is_fields_within_limit1 h_index (getWosize (read_word g h_index)));
      assert (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g);  

      field_limits_objects2_lemma g;
      field_contents_within_limits_objects2_lemma g;
      fieldaddress_within_limits_lemma_x_all3 g;
        
      assert (forall x. Seq.mem x (objects2 0UL g) ==>
                                      (is_fields_within_limit1 x (getWosize (read_word g x))));
       
      assert (forall x. Seq.mem x (objects2 0UL g) ==>  (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
      
      assert (forall i x.  Seq.mem x (objects2 0UL g) /\
                                  (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                       (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
   
      
      
      let succ_index = Usize.add h_index (Usize.mul i mword) in
       
      assert (Usize.v succ_index < heap_size);
 
      max_wosize_times_mword_multiple_of_mword i;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
      assert (Usize.v succ_index % Usize.v mword == 0);
      assert (is_hp_addr succ_index);

      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);
      assert (Seq.mem h_index (objects2 0UL g));
       
      assert (Usize.v succ_index < heap_size);
      if isPointer succ_index g  then
      (
        assert (succ == read_word g succ_index);
        assert (is_valid_header h_index g);
        assert (Seq.mem h_index (objects2 0UL g));
        

        assert (Usize.v i' > 1);
        
        
        let s_list' = field_pointers_for_h_index g h_index (getWosize (read_word g h_index)) i' in
        

        lemma_tl succ s_list'; 
        
        let s_list = Seq.cons succ s_list' in 
        field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma1 g i' h_index;
        ()
     )
      else
      (
        assert (Usize.v i' > 1);
        
        let s_list = field_pointers_for_h_index g h_index (getWosize (read_word g h_index)) i' in
        field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma1 g i' h_index;
        ()
      )
    )
                                           
#restart-solver 

//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"




let field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma1_all (g:heap{well_formed_heap2 g}) 
                                                                                        
                                       :Lemma
                                       (requires (well_formed_allocated_blocks g) /\ 
                                                 (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                           is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                 (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                                          is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                                  (forall x. Seq.mem x (get_allocated_block_addresses g) ==>
                                                       (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                            (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)))
                                         (ensures (forall x. Seq.mem x (get_allocated_block_addresses g) /\ is_valid_header x g ==>  
                                               field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                                                    create_successors_list_for_h_index g x (getWosize (read_word g x)) 1UL)) = 
 Classical.forall_intro (Classical.move_requires (field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma1 g 1UL))
                                                 
                                                                                              
let rec field_pointers_for_h_index_lemma1 (g:heap{well_formed_heap2 g}) 

                                          (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g 
                                                           })
                                           
                                          (wz: wosize{(wz == getWosize (read_word g h_index))})

                                            
                         
                                          (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})

                                          (v_id:hp_addr{is_valid_header v_id g})

                                          (c:color(*{c == 3UL \/ c == 2UL \/ c == 1UL}*))

                                          (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })

                                          (wz1: wosize{(wz1 == getWosize (read_word g' h_index))})
                                             
                        : Lemma
                          (requires (objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (wz == wz1) /\
                                    
                                    (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                    (forall x. Seq.mem x (objects2 0UL g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
                                    (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                    (forall x. Seq.mem x (objects2 0UL g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g') /\
                                    (forall j x.  Seq.mem x (objects2 0UL g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                    (forall j x.  Seq.mem x (objects2 0UL g') /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)
                                    )
                          (ensures (field_pointers_for_h_index g h_index wz i == field_pointers_for_h_index g' h_index wz1 i))
                          (decreases ((Usize.v wz + 1) - Usize.v i)) = 
if Usize.v i = Usize.v wz + 1 then
    (
       let s_list = Seq.empty #UInt64.t in

       seq_empty_lemma5 ();
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
      
       ()
    )
  else
   (
     assert (objects2 0UL g == objects2 0UL g');
     assert (heap_remains_same_except_index_v_id v_id g g');

     field_reads_all_equal_for_all_objects_lemma g g' v_id;

      
      

     assert ((forall x (y:hp_addr{(length (slice g' (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8) /\
                              (length (slice g (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8)}). 
                               Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) /\
                                       x <> v_id ==>  read_word g y == read_word g' y));
     field_reads_all_equal_h_index_lemma g g' v_id;

     assert (forall (y:hp_addr{(length (slice g' (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8) /\
                              (length (slice g (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8)}). Usize.v y >= Usize.v h_index + Usize.v mword /\
                                             Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                                   read_word g y == read_word g' y);
     let succ_index = Usize.add h_index (Usize.mul i mword) in

     field_limits_objects2_lemma g;
     field_contents_within_limits_objects2_lemma g;
     fieldaddress_within_limits_lemma_x_all3 g;
        
    
                                       
     max_wosize_times_mword_multiple_of_mword i;
     sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
     assert (Usize.v succ_index % Usize.v mword == 0);
     assert (is_hp_addr succ_index);



      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);

      lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8); 
      
      let succ1 = read_word g' succ_index in
      assert (succ1 == read_word g' succ_index);

      assert (Usize.v succ_index >= Usize.v h_index + Usize.v mword /\
             Usize.v succ_index <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword));
      assert (succ == succ1);

      let i' = Usize.(i +^ 1UL) in
      if isPointer succ_index g  then
      (
          let s_list' = field_pointers_for_h_index g h_index wz i' in

          field_pointers_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;
          lemma_tl succ s_list'; 
        
          let s_list = Seq.cons succ s_list' in
          ()
      )
      else
      (
        let s_list = field_pointers_for_h_index g h_index wz i' in

        field_pointers_for_h_index_lemma1 g h_index wz i' v_id c g' wz1;
        ()
        )
   )

let rec field_pointers_for_h_index_lemma3 (g:heap{well_formed_heap2 g}) 
                                          
                                          (i:Usize.t)

                                          (v_id:hp_addr{is_valid_header v_id g})

                                          (c:color(*{c == 3UL \/ c == 2UL \/ c == 1UL}*))

                                          (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })

                                          
                                          (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g 
                                                           })
                                            
                          : Lemma
                          (requires 
                                    (Usize.v i <= Usize.v (getWosize (read_word g h_index)) + 1 /\ Usize.v i >= 1) /\
                                    (getWosize (read_word g h_index) == getWosize (read_word g' h_index)) /\
                                    
                                    (objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    
                                    
                                    (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                    (forall x. Seq.mem x (objects2 0UL g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
                                    (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                    (forall x. Seq.mem x (objects2 0UL g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g') /\
                                    (forall j x.  Seq.mem x (objects2 0UL g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                    (forall j x.  Seq.mem x (objects2 0UL g') /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)
                                    )
                          (ensures (field_pointers_for_h_index g h_index (getWosize (read_word g h_index)) i == 
                                       field_pointers_for_h_index g' h_index (getWosize (read_word g' h_index)) i))
                          (decreases ((Usize.v (getWosize (read_word g h_index)) + 1) - Usize.v i)) = 
if Usize.v i = Usize.v (getWosize (read_word g h_index)) + 1 then
    (
       let s_list = Seq.empty #UInt64.t in

       seq_empty_lemma5 ();
       assert (Seq.length s_list == 0);
       
      
       ()
    )
  else
   (
     assert (objects2 0UL g == objects2 0UL g');
     assert (heap_remains_same_except_index_v_id v_id g g');

     field_reads_all_equal_for_all_objects_lemma g g' v_id;

      
      

     assert ((forall x (y:hp_addr{(length (slice g' (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8) /\
                              (length (slice g (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8)}). 
                               Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                       Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) /\
                                       x <> v_id ==>  read_word g y == read_word g' y));
     field_reads_all_equal_h_index_lemma g g' v_id;

     assert (forall (y:hp_addr{(length (slice g' (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8) /\
                              (length (slice g (Usize.v y) ((Usize.v y) + (Usize.v mword))) = 8)}). Usize.v y >= Usize.v h_index + Usize.v mword /\
                                             Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                                   read_word g y == read_word g' y);
     let succ_index = Usize.add h_index (Usize.mul i mword) in

     field_limits_objects2_lemma g;
     field_contents_within_limits_objects2_lemma g;
     fieldaddress_within_limits_lemma_x_all3 g;
        
    
                                       
     max_wosize_times_mword_multiple_of_mword i;
     sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
       
     assert (Usize.v succ_index % Usize.v mword == 0);
     assert (is_hp_addr succ_index);



      lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8);  
      let succ = read_word g succ_index in
      assert (succ == read_word g succ_index);

      lemma_len_slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
      assert (length (slice g' (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8); 
      
      let succ1 = read_word g' succ_index in
      assert (succ1 == read_word g' succ_index);

      assert (Usize.v succ_index >= Usize.v h_index + Usize.v mword /\
             Usize.v succ_index <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword));
      assert (succ == succ1);

      let i' = Usize.(i +^ 1UL) in
      if isPointer succ_index g  then
      (
          let s_list' = field_pointers_for_h_index g h_index (getWosize (read_word g h_index)) i' in

          field_pointers_for_h_index_lemma3 g i' v_id c g' h_index;
          lemma_tl succ s_list'; 
        
          let s_list = Seq.cons succ s_list' in
          ()
      )
      else
      (
        let s_list = field_pointers_for_h_index g h_index (getWosize (read_word g h_index)) i' in

        field_pointers_for_h_index_lemma3 g  i' v_id c g' h_index;
        ()
        )
   )

let field_pointers_for_h_index_lemma3_all    (g:heap{well_formed_heap2 g}) 
                                              

                                              (v_id:hp_addr{is_valid_header v_id g})

                                              (c:color(*{c == 3UL \/ c == 2UL \/ c == 1UL}*))

                                              (g':heap{(well_formed_heap2 g') /\ Seq.equal g'(colorHeader1 v_id g c) })
                          : Lemma
                          (requires 
                                    (objects2 0UL g == objects2 0UL g') /\
                                    (heap_remains_same_except_index_v_id v_id g g') /\
                                    (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). 
                                            getWosize (read_word g x) == getWosize (read_word g' x)) /\
                                    
                                    (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                    (forall x. Seq.mem x (objects2 0UL g') ==> is_fields_within_limit1 x (getWosize (read_word g' x))) /\
                                    (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                    (forall x. Seq.mem x (objects2 0UL g') ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g') /\
                                    (forall j x.  Seq.mem x (objects2 0UL g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                    (forall j x.  Seq.mem x (objects2 0UL g') /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g' x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)
                                    )
                          (ensures (forall x. Seq.mem x (objects2 0UL g') ==>
                                         field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                                            field_pointers_for_h_index g' x (getWosize (read_word g' x)) 1UL)) = 
Classical.forall_intro (Classical.move_requires (field_pointers_for_h_index_lemma3 g 1UL v_id c g'))
                                          

#reset-options "--z3rlimit 1000"
#push-options "--split_queries"
                                          
                                          
#restart-solver                                            

#restart-solver 


let sweep_body_helper_field_pointers_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                           (h_index:hp_addr{is_valid_header h_index g})
            : Lemma
              
              (ensures ((*field_pointers_for_h_index g h_index (getWosize (read_word g h_index)) 1UL == 
                        field_pointers_for_h_index (sweep_body_helper g h_index) h_index (getWosize (read_word (sweep_body_helper g h_index) h_index)) 1UL)*)
                        (forall x. Seq.mem x (objects2 0UL (sweep_body_helper g h_index)) ==>
                                field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                                 field_pointers_for_h_index (sweep_body_helper g h_index) x (getWosize (read_word (sweep_body_helper g h_index) x)) 1UL))) = 
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white) then 
 (
   let g' = colorHeader1 h_index g blue in
   
   field_limits_objects2_lemma g;
   field_contents_within_limits_objects2_lemma g;
   fieldaddress_within_limits_lemma_x_all3 g;

   field_limits_objects2_lemma g';
   field_contents_within_limits_objects2_lemma g';
   fieldaddress_within_limits_lemma_x_all3 g';
   
   colorHeader1_wosizeLemma h_index g blue h_index;
   assert (objects2 h_index g == objects2 h_index g');

   assert (objects2 0UL g == objects2 0UL g');
   assert (heap_remains_same_except_index_v_id h_index g g');

   let wz = getWosize (read_word g h_index) in
   let wz1 = getWosize (read_word g' h_index) in

   assert (wz == wz1);
  
   field_pointers_for_h_index_lemma3_all  g h_index blue g';
   assert (forall x. Seq.mem x (objects2 0UL g') ==>
                                         field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                                            field_pointers_for_h_index g' x (getWosize (read_word g' x)) 1UL);
   ()
 )
 else
 (
   if (c = black) then 
   (
      let g' = colorHeader1 h_index g white in
      colorHeader1_wosizeLemma h_index g white h_index;
      assert (objects2 h_index g == objects2 h_index g');
      
      field_limits_objects2_lemma g;
      field_contents_within_limits_objects2_lemma g;
      fieldaddress_within_limits_lemma_x_all3 g;

      field_limits_objects2_lemma g';
      field_contents_within_limits_objects2_lemma g';
      fieldaddress_within_limits_lemma_x_all3 g';
   
      assert (objects2 0UL g == objects2 0UL g');
      assert (heap_remains_same_except_index_v_id h_index g g');

      let wz = getWosize (read_word g h_index) in
      let wz1 = getWosize (read_word g' h_index) in

      assert (wz == wz1);
      
      field_pointers_for_h_index_lemma3_all  g h_index white g';
      assert (forall x. Seq.mem x (objects2 0UL g') ==>
                                         field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                                            field_pointers_for_h_index g' x (getWosize (read_word g' x)) 1UL);
      ()
   )
   else
   (
     assert (c == blue);
     objects2_equal_lemma h_index g g;
     assert (objects2 h_index g == objects2 h_index g);
     let wz = getWosize (read_word g h_index) in
     assert (field_pointers_for_h_index g h_index wz 1UL == field_pointers_for_h_index g h_index wz 1UL);
     assert (forall x. Seq.mem x (objects2 0UL g) ==>
                                         field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                                            field_pointers_for_h_index (sweep_body_helper g h_index) x (getWosize (read_word (sweep_body_helper g h_index) x)) 1UL);
     ()
   )
 )




#reset-options "--z3rlimit 1000"
#push-options "--split_queries"

#restart-solver 


#restart-solver 

#restart-solver 

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver


let rec sweep1_field_pointers_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                    (h_index:hp_addr{is_valid_header h_index g /\ (Seq.length (objects2 h_index g) > 0)})
          : Lemma
           (requires (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                      (forall x. Seq.mem x (objects2 0UL (sweep1 g h_index)) ==> is_fields_within_limit1 x (getWosize (read_word (sweep1 g h_index) x))) /\
                      (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                      (forall x. Seq.mem x (objects2 0UL (sweep1 g h_index)) ==> 
                            is_fields_contents_within_limit2 x (getWosize (read_word (sweep1 g h_index) x)) (sweep1 g h_index)) /\
                      (forall j x.  Seq.mem x (objects2 0UL g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                      (forall j x.  Seq.mem x (objects2 0UL (sweep1 g h_index)) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word (sweep1 g h_index) x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))
           
            (ensures 
                 (objects2 h_index g == (objects2 h_index (sweep1 g h_index))) /\
                 (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word (sweep1 g h_index) x)) /\
                 (forall x. Seq.mem x (objects2 0UL (sweep1 g h_index)) ==> 
                             field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                             field_pointers_for_h_index (sweep1 g h_index) x (getWosize (read_word (sweep1 g h_index) x)) 1UL))
            (decreases (heap_size - Usize.v h_index)) = 
 let wz =  getWosize (read_word g h_index) in
 
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let g' = sweep_body_helper g h_index in

 
 sweep_body_helper_field_pointers_lemma g h_index;
 
 assert (well_formed_heap2 g');
 assert (objects2 0UL g == objects2 0UL g');

 field_limits_objects2_lemma g';
 field_contents_within_limits_objects2_lemma g';
 fieldaddress_within_limits_lemma_x_all3 g';
 assert (forall x. Seq.mem x (objects2 0UL g') ==> 
                             field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                             field_pointers_for_h_index g' x (getWosize (read_word g' x)) 1UL);
     
 if Usize.v h_index_new >= heap_size then
 (
   assert (objects2 h_index g == objects2 h_index g');
   assert (objects2 h_index (sweep1 g h_index) == (objects2 h_index (sweep1 g h_index)));
   assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word (sweep1 g h_index) x));
   assert (forall x. Seq.mem x (objects2 h_index g) ==>  getWosize (read_word g x) == getWosize (read_word (sweep1 g h_index) x));
   //assert (forall x. Seq.mem x (objects2 h_index g') ==> field_pointers_for_h_index g x wz 1UL == field_pointers_for_h_index g' x wz 1UL);
   assert (forall x. Seq.mem x (objects2 0UL (sweep1 g h_index)) ==> 
                             field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                             field_pointers_for_h_index (sweep1 g h_index) x (getWosize (read_word (sweep1 g h_index) x)) 1UL);
  ()
 
 )
 else
 (
      wosize_plus_times_mword_multiple_of_mword1 wz;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);
      
      objects2_mem_lemma1_app h_index g;
      
      assert (is_valid_header h_index_new g);
      assert (is_valid_header h_index_new g');
     
      assert (Seq.mem h_index (objects2 0UL g));
      assert (Seq.length (objects2 0UL g) > 0);
      assert (Seq.length (objects2 h_index g) > 0);
      assert (Seq.length (objects2 h_index g') > 0);
      
      objects2_length_lemma1 g' h_index h_index_new; 
      assert (Seq.length (objects2 h_index_new g') > 0);
      
      let g'' = sweep1 g' h_index_new in
      
      field_limits_objects2_lemma g'';
      field_contents_within_limits_objects2_lemma g'';
      fieldaddress_within_limits_lemma_x_all3 g'';

      objects2_cons_lemma1 h_index g h_index_new;
      objects2_cons_lemma1 h_index g' h_index_new;

      sweep1_field_pointers_lemma g' h_index_new ;
      assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g' x) == getWosize (read_word g'' x));
      assert (objects2 h_index_new g' == objects2 h_index_new g'');
      objects2_equal_lemma h_index g' g'';
      objects2_cons_lemma1 h_index g'' h_index_new;
      objects2_equal_lemma h_index_new g g';
      (*assert (objects2 0UL g' == objects2 0UL g'');
      assert (objects2 0UL g'' == objects2 0UL g);*)
      assert (forall x. Seq.mem x (objects2 0UL g'') ==> 
                             field_pointers_for_h_index g' x (getWosize (read_word g' x)) 1UL == 
                             field_pointers_for_h_index g'' x (getWosize (read_word g'' x)) 1UL);
      
      
      
      assert (Seq.length (objects2 h_index g) > 0 /\ 
                        Usize.v h_index_new < heap_size ==> 
                         ((objects2 h_index g) == Seq.cons h_index (objects2 h_index_new g)) /\
                         (forall x. Seq.mem x (objects2 h_index g) <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g))));
      assert (Seq.length (objects2 h_index g') > 0 /\ 
                        Usize.v h_index_new < heap_size ==> 
                         ((objects2 h_index g') == Seq.cons h_index (objects2 h_index_new g')) /\
                         (forall x. Seq.mem x (objects2 h_index g') <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g'))));

      assert (Seq.length (objects2 h_index g'') > 0 /\ 
                        Usize.v h_index_new < heap_size ==> 
                         ((objects2 h_index g'') == Seq.cons h_index (objects2 h_index_new g'')) /\
                         (forall x. Seq.mem x (objects2 h_index g'') <==> x == h_index \/ (Seq.mem x (objects2 h_index_new g''))));
      
      
      assert (forall x. Seq.mem x (objects2 0UL g') ==> 
                             field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                             field_pointers_for_h_index g' x (getWosize (read_word g' x)) 1UL);
                             

     assert (objects2 0UL g == objects2 0UL g');
     assert (objects2 0UL g' == objects2 0UL g'');
     assert (objects2 0UL g == objects2 0UL g'');
     assert (forall x. Seq.mem x (objects2 0UL g'') ==> 
                             field_pointers_for_h_index g x (getWosize (read_word g x)) 1UL == 
                             field_pointers_for_h_index g'' x (getWosize (read_word g'' x)) 1UL);
     ()
 )


#restart-solver

#restart-solver

#restart-solver 

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver 






#reset-options "--z3rlimit 1000"
#push-options "--split_queries"

#restart-solver

let field_equal_pred (g:heap{well_formed_heap2 g})
                     (g':heap{well_formed_heap2 g' /\ (objects2 0UL g) == (objects2 0UL g') /\
                             (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x))}) =
 (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y)

let wosize_equal_pred (g:heap{well_formed_heap2 g})
                      (g':heap{well_formed_heap2 g' /\ (objects2 0UL g) == (objects2 0UL g')}) =
  (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g t) == 
                                                                      getWosize (read_word g' t))

#restart-solver

#restart-solver

let field_equal_trans_lemma (g:heap{well_formed_heap2 g})
                            (g':heap{well_formed_heap2 g' /\ (objects2 0UL g) == (objects2 0UL g') /\
                                     wosize_equal_pred g g'})
                            (g1:heap{well_formed_heap2 g1/\ (objects2 0UL g') == (objects2 0UL g1) /\
                                     wosize_equal_pred g' g1}) 
                : Lemma
                  (requires field_equal_pred g g' /\
                            field_equal_pred g' g1)
                  (ensures wosize_equal_pred g g1 /\ field_equal_pred g g1)= 
 assert (field_equal_pred g g');
 assert (field_equal_pred g' g1);
 assert (wosize_equal_pred g g');
 assert (wosize_equal_pred g' g1);
 assert (wosize_equal_pred g g1);
 assert ((objects2 0UL g) == (objects2 0UL g'));
 assert ((objects2 0UL g') == (objects2 0UL g1));
 assert (objects2 0UL g == objects2 0UL g1);
 assert (field_equal_pred g g1);
 ()

#restart-solver 

#restart-solver 


let mark5_body_fields_lemma1 (g:heap{well_formed_heap2 g}) 
                             (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
           : Lemma
             (requires (~(G.is_emptySet st)) /\
                       (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1))))
             (ensures  wosize_equal_pred g  (snd (mark5_body g st)) /\
                       (field_equal_pred g (snd (mark5_body g st))))= 
   assert (~(G.is_emptySet st));
   let v_id = Seq.index st (Seq.length st - 1) in
   let s = Seq.slice st 0 (Seq.length st - 1) in
   assert (color_of_object1 v_id g == gray);
   
   assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
   assert (well_formed_heap2 g);
   slice_mem_lemma st s;
   assert (forall x. Seq.mem x s ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (forall x. Seq.mem x s ==> Seq.mem x st);
   G.is_vertex_set_lemma3 st;
   assert (forall x. Seq.mem x s ==> Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g);

   assert (forall x. Seq.mem x s ==> color_of_object1 x g == gray);

   assert (is_valid_header v_id g);  
   let g' = colorHeader1 v_id g black in
  
   assert (color_of_object1 v_id g' == black);
   
   let f = objects2 0UL g in
   let f' = objects2 0UL g' in
   assert (f == f');
   get_allocated_block_addresses_lemma g g' v_id black;
   assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
   
   (*colorHeader1_fields_lemma v_id g black;

   assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x));

   assert (forall x y. Seq.mem x (objects2 0UL g) /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                              Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y);*)
   assert (G.is_vertex_set s);
   G.is_vertex_set_lemma5 st;
   assert (~(Seq.mem v_id s));
   Seq.lemma_mem_snoc s v_id;
   assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem x (objects2 0UL g) /\
                                                        isGrayObject1 x g);
   assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
   assert (color_of_object1 v_id g' == 3UL);
   objects2_equal_lemma 0UL g g';
   assert (objects2 0UL g == objects2 0UL g');
   
   assert (forall x. Seq.mem x s <==> Seq.mem x (objects2 0UL g') /\
                                                        isGrayObject1 x g');
   let wz = wosize_of_object1 v_id g' in
   assert (is_valid_header v_id g');
   assert (Usize.v wz == Usize.v (getWosize (read_word g v_id)));
   assert (Usize.v wz == Usize.v (getWosize (read_word g' v_id)));
  
   let st1, g1 = fieldPush_spec1 g' s v_id wz 1UL in
   assert (G.is_vertex_set st1);
   assert (Seq.length g == Seq.length g1);
   assert (well_formed_heap2 g1);
   assert (forall x. Seq.mem x st1 ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
   assert (forall x. Seq.mem x st1 ==> is_valid_header x g1);
   assert (forall x. Seq.mem x st1 ==> Usize.v x % Usize.v mword == 0);
   assert (forall x. Seq.mem x (objects2 0UL g1) /\ isGrayObject1 x g1 <==>
                                                Seq.mem x st1);
   assert (forall x. Seq.mem x s ==> Seq.mem x st1);
   (*assert (forall x. is_visited x g' ==> is_visited x g1);
   assert (forall x. isGrayBlock x g' ==> isGrayBlock x g1);*)
   assert (get_allocated_block_addresses g' == get_allocated_block_addresses g1);
   assert (objects2 0UL g' == objects2 0UL g1);
   assert (objects2 0UL g == objects2 0UL g1);
   assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
   
   colorHeader1_fields_lemma v_id g black;
   assert (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). getWosize (read_word g x) == getWosize (read_word g' x));
   
   assert (field_equal_pred g g');

   fieldPush_spec1_fields_lemma1 g' s v_id wz 1UL;
   
   assert (forall (t:Usize.t{Usize.v t < heap_size /\ Usize.v t % 8 == 0}). getWosize (read_word g' t) == 
                                                                      getWosize (read_word g1 t));
   assert (field_equal_pred g' g1);
   field_equal_trans_lemma g g' g1;
   assert (wosize_equal_pred g g1);
   assert (field_equal_pred g g1);
   ()





#restart-solver


#restart-solver 

#restart-solver

let rec mark5_fields_lemma (g:heap{well_formed_heap2 g}) 
                           (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                                      
          : Lemma 
            (requires (well_formed_heap2 (mark5 g st) /\ (objects2 0UL g == objects2 0UL (mark5 g st))))
            (ensures  (wosize_equal_pred g (mark5 g st)) /\
                      (field_equal_pred g  (mark5 g st)))
            (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
  if (G.is_emptySet st) then
   (
      ()
   )
 else
   (
      let st', g' = mark5_body g st in
      let v_id = Seq.index st (Seq.length st - 1) in
      assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
      assert (is_valid_header v_id g);

      stack_slice_only_has_gray_color_lemma g st v_id 3UL;

      assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1)));
      
      
      mark5_body_black_nodes_lemma g st;
      
      assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
      
      
      mark5_body_fields_lemma1 g st;
      assert (wosize_equal_pred g g');
      assert (field_equal_pred g g');
      let g1 = mark5 g' st' in 
      well_formed_heap2_after_mark5 g' st';
      assert (well_formed_heap2 g1);
      mark5_fields_lemma g' st';
      assert (wosize_equal_pred g' g1);
      assert (field_equal_pred g' g1);
      mark5_objects2_lemma g' st';
      assert (objects2 0UL g' == objects2 0UL g1);
      assert (objects2 0UL g == objects2 0UL g1);
      field_equal_trans_lemma g g' g1;
      assert (wosize_equal_pred g g1);
      assert (field_equal_pred g g1);
      ()
   )

#restart-solver 

let create_root_stack_and_gray_modified_heap_body_fields_lemma (g:heap{well_formed_heap2 g}) 
                                                               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                 (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                 (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                 (G.is_vertex_set st) /\
                                                                                 (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                    Seq.mem x st)})
                                                               (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)})          
                                                  
      : Lemma
             (requires (mutually_exclusive_sets st h_list) /\ Seq.length h_list > 0 /\ (G.is_vertex_set (tail h_list)))
             (ensures  (wosize_equal_pred g (snd (create_root_stack_and_gray_modified_heap_body g st h_list))) /\
                      (field_equal_pred g  (snd (create_root_stack_and_gray_modified_heap_body g st h_list)))) = 
     assert (Seq.length h_list > 0);
     let hd = Seq.head h_list in
     let tl = Seq.tail h_list in
     
     assert (G.is_vertex_set st);
     assert (G.is_vertex_set h_list);

     assert (~(Seq.mem hd st));
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     assert (mutually_exclusive_sets st tl);

     G.is_vertex_set_lemma4 h_list;
     assert (~(Seq.mem hd tl));
     assert (~(Seq.mem hd st));
     let st', g' = push_to_stack2 g st hd in
     push_to_stack2_fields_allocated_blocks_lemma  g st hd;
     assert (mutually_exclusive_sets st' tl);
     assert (objects2 0UL g == objects2 0UL g');
     assert(wosize_equal_pred g g');
     assert (field_equal_pred g g');
     ()

let rec create_root_stack_and_gray_modified_heap_fields_lemma (g:heap{well_formed_heap2 g}) 
                                                              (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                                (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                                                (G.is_vertex_set st) /\
                                                                                (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                                Seq.mem x st)})
                                                              (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list)})          
                                                  
      :  Lemma 
         (requires mutually_exclusive_sets st h_list)
         (ensures (wosize_equal_pred g (snd (create_root_stack_and_gray_modified_heap g st h_list))) /\
                  (field_equal_pred g (snd (create_root_stack_and_gray_modified_heap g st h_list))))
         (decreases (Seq.length h_list)) =
  
  if Seq.length h_list = 0 then 
  (
     ()
  )
  else
  (
     let hd = Seq.head h_list in
     let tl = Seq.tail h_list in
     
     assert (G.is_vertex_set st);
     assert (G.is_vertex_set h_list);

     assert (~(Seq.mem hd st));
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     assert (mutually_exclusive_sets st tl);

     G.is_vertex_set_lemma4 h_list;
     assert (~(Seq.mem hd tl));
     assert (~(Seq.mem hd st));
     let st', g' = push_to_stack2 g st hd in
     assert (mutually_exclusive_sets st' tl);
     push_to_stack2_fields_allocated_blocks_lemma  g st hd;
     assert (mutually_exclusive_sets st' tl);
     assert (objects2 0UL g == objects2 0UL g');
     assert(wosize_equal_pred g g');
     assert (field_equal_pred g g');
    
     let st1, g1 = create_root_stack_and_gray_modified_heap g' st' (tail h_list) in
     assert (objects2 0UL g' == objects2 0UL g1);
     create_root_stack_and_gray_modified_heap_fields_lemma g' st' (tail h_list);
     
     assert(wosize_equal_pred g' g1);
     assert (field_equal_pred g' g1);
     field_equal_trans_lemma g g' g1;
     assert (wosize_equal_pred g g1);
     assert (field_equal_pred g g1);
     ()
  )

let sweep_body_helper_fields_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                   (h_index:hp_addr{is_valid_header h_index g})
            : Lemma
              (ensures (wosize_equal_pred g (sweep_body_helper g h_index)) /\
                       (field_equal_pred g (sweep_body_helper g h_index)))= 
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white) then 
 (
   let g' = colorHeader1 h_index g blue in
   colorHeader1_wosizeLemma h_index g blue h_index;
   assert (objects2 h_index g == objects2 h_index g');
   colorHeader1_fields_lemma h_index g blue;
   assert(wosize_equal_pred g g');
   assert (field_equal_pred g g');
   ()
 )
 else
 (
   if (c = black) then 
   (
      let g' = colorHeader1 h_index g white in
      colorHeader1_wosizeLemma h_index g white h_index;
      assert (objects2 h_index g == objects2 h_index g');
      colorHeader1_fields_lemma h_index g white;
      assert (wosize_equal_pred g g');
      assert (field_equal_pred g g');
      ()
   )
   else
   (
     assert (c == blue);
     objects2_equal_lemma h_index g g;
     assert (objects2 h_index g == objects2 h_index g);
     ()
   )
 )

let rec sweep1_fields_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                            (h_index:hp_addr{is_valid_header h_index g /\ (Seq.length (objects2 h_index g) > 0)})
          : Lemma 
            (ensures (wosize_equal_pred g (sweep1 g h_index)) /\
                     (field_equal_pred g (sweep1 g h_index)))
            (decreases (heap_size - Usize.v h_index)) = 
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let g' = sweep_body_helper g h_index in 
 sweep_body_helper_fields_lemma g h_index; 
 assert (well_formed_heap2 g');
 assert (objects2 0UL g == objects2 0UL g');
 assert (wosize_equal_pred g g');
 assert (field_equal_pred g g');
 if Usize.v h_index_new >= heap_size then
 (
   ()
 )
 else
 (
      wosize_plus_times_mword_multiple_of_mword1 wz;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);
      
      objects2_mem_lemma1_app h_index g;
      
      assert (is_valid_header h_index_new g);
      assert (is_valid_header h_index_new g');
     
      assert (Seq.mem h_index (objects2 0UL g));
      assert (Seq.length (objects2 0UL g) > 0);
      assert (Seq.length (objects2 h_index g) > 0);
      assert (Seq.length (objects2 h_index g') > 0);
      
      objects2_length_lemma1 g' h_index h_index_new; 
      assert (Seq.length (objects2 h_index_new g') > 0);
      
      let g'' = sweep1 g' h_index_new in
      sweep1_fields_lemma g' h_index_new;
     
      assert (objects2 0UL g' == objects2 0UL g'');
      assert (objects2 0UL g'' == objects2 0UL g);
      assert (wosize_equal_pred g' g'');
      assert (field_equal_pred g' g'');
      field_equal_trans_lemma g g' g'';
      assert (wosize_equal_pred g g'');
      assert (field_equal_pred g g'');
      ()
 )

#restart-solver

let allocs_fields (g:heap{well_formed_heap2 g}) =
   (forall y. Seq.mem y (get_allocated_block_addresses g) ==> is_fields_within_limit1 y (getWosize (read_word g y)))
   
let allocs_fields_contents (g:heap{well_formed_heap2 g}) =
   (forall y . Seq.mem y (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 y (getWosize (read_word g y)) g)

let allocs_fields_aligned (g:heap{well_formed_heap2 g}) =
   (forall y. Seq.mem y (get_allocated_block_addresses g) ==> (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g y)) ==> 
                                                                  (Usize.v y  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))

let white_fields_white_pred  (g:heap{well_formed_heap2 g})
                             (g3:heap{well_formed_heap2 g3}) =
   (forall y. Seq.mem y (get_allocated_block_addresses g3) /\ 
                                           Seq.mem y (get_allocated_block_addresses g) /\
                                           color_of_object1 y g3 == white ==>
                                           (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                           (is_hp_addr ((Usize.add y (Usize.mul t mword)))) /\
                                           isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                           (*the below condition is necessary to typecheck*)
                                           (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (get_allocated_block_addresses g3)) /\ 
                                                  (Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) (objects2 0UL g3)) /\ 
                                                                           isWhiteObject1 (read_word g (Usize.add y (Usize.mul t mword))) g3))

let allocs_reads_equal (g:heap{well_formed_heap2 g})
                       (g3:heap{well_formed_heap2 g3}) =
     (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                         Usize.v (getWosize (read_word g y)) == Usize.v (getWosize (read_word g3 y)))

let allocs_field_reads_equal (g:heap{well_formed_heap2 g})
                             (g3:heap{well_formed_heap2 g3}) =
     (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                     (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                     (is_hp_addr ((Usize.add y (Usize.mul t mword))) ==>
                                     Usize.v (read_word g (Usize.add y (Usize.mul t mword))) == 
                                     Usize.v (read_word g3 (Usize.add y (Usize.mul t mword))))))

#restart-solver 

#restart-solver 

let allocs_reads_equal_from_wosize_equal_pred (g:heap{well_formed_heap2 g})
                                              (g3:heap{well_formed_heap2 g3}) 
                        : Lemma
                          (requires (objects2 0UL g == objects2 0UL g3) /\
                                    (wosize_equal_pred g g3))
                          (ensures (allocs_reads_equal g g3)) =
 assert (wosize_equal_pred g g3);
 assert (forall x. Seq.mem x (objects2 0UL g3) ==> Usize.v (getWosize (read_word g x)) == Usize.v (getWosize (read_word g3 x)));
 assert (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> Usize.v (getWosize (read_word g x)) == Usize.v (getWosize (read_word g3 x)));
 ()

#restart-solver 

#restart-solver

let fields_allocated_blocks_helper_lemma  (g:heap{well_formed_heap2 g})
                                                                 
                                          (g3:heap{well_formed_heap2 g3})
                                          (h_index:hp_addr{is_valid_header h_index g})
                                          (y:Usize.t{Usize.v y >= 1 /\
                                                                  Usize.v y <= (Usize.v (getWosize (read_word g h_index))) /\
                                                                  is_hp_addr (Usize.add h_index (Usize.mul y mword))})
                                                       
                        : Lemma
                          (requires (objects2 0UL g == objects2 0UL g3) /\
                                    (forall x. Seq.mem x (objects2 0UL g3) ==> 
                                           (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                                 Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g3 y)))
                          (ensures read_word g (Usize.add h_index (Usize.mul y mword)) == 
                                   read_word g3 (Usize.add h_index (Usize.mul y mword))) = 
 let objs1 = objects2 0UL g in
 let objs2 = objects2 0UL g3 in
 assert (objs1 == objs2);
 assert (Seq.mem h_index objs2);
 assert (is_valid_header h_index g3);
 assert (forall y. Usize.v y >= Usize.v h_index + Usize.v mword /\
              Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword) ==>
                                               read_word g y == read_word g3 y);
 
 let p = Usize.add h_index (Usize.mul y mword) in
 assert (is_hp_addr p);
 assert (Usize.v p >=  Usize.v h_index + Usize.v mword);
 assert (Usize.v p <=  Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword));
 assert (read_word g p == read_word g3 p);
 ()                                   

let fields_allocated_blocks_all_helper_lemma (g:heap{well_formed_heap2 g})
                                                                 
                                             (g3:heap{well_formed_heap2 g3})
                                             (h_index:hp_addr{is_valid_header h_index g})
                                                       
                        : Lemma
                          (requires        (objects2 0UL g == objects2 0UL g3) /\
                                           (forall x. Seq.mem x (objects2 0UL g3) ==> 
                                           (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                                 Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g3 y)))
                                                             
                          (ensures (forall y. (Usize.v y >= 1 /\ Usize.v y <= Usize.v (getWosize (read_word g h_index))) /\
                                                         (is_hp_addr (Usize.add h_index (Usize.mul y mword))) ==>
                                   read_word g (Usize.add h_index (Usize.mul y mword)) == 
                                   read_word g3 (Usize.add h_index (Usize.mul y mword)))) = 
Classical.forall_intro (Classical.move_requires (fields_allocated_blocks_helper_lemma g g3 h_index))

(*(forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                     (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                     (is_hp_addr (Usize.add y (Usize.mul t mword))) ==>
                                     Usize.v (read_word g (Usize.add y (Usize.mul t mword))) == 
                                     Usize.v (read_word g3 (Usize.add y (Usize.mul t mword)))))*)


let fields_allocated_blocks_all_helper_lemma1 (g:heap{well_formed_heap2 g})
                                                                 
                                              (g3:heap{well_formed_heap2 g3})
                          : Lemma
                           (requires (objects2 0UL g == objects2 0UL g3) /\
                                    (forall x. Seq.mem x (objects2 0UL g3) ==> 
                                     (forall y. Usize.v y >= Usize.v x + Usize.v mword /\
                                                 Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                             read_word g y == read_word g3 y)))
                          (ensures (forall x. Seq.mem x (objects2 0UL g3) ==>
                                      (forall y. (Usize.v y >= 1 /\ Usize.v y <= Usize.v (getWosize (read_word g x))) /\
                                                         (is_hp_addr (Usize.add x (Usize.mul y mword))) ==>
                                                         read_word g (Usize.add x (Usize.mul y mword)) == 
                                                         read_word g3 (Usize.add x (Usize.mul y mword))))) = 
Classical.forall_intro (Classical.move_requires (fields_allocated_blocks_all_helper_lemma g g3))

#restart-solver 

#restart-solver 

let object_field_reads_ver1 (g:heap{well_formed_heap2 g})
                                                                 
                            (g3:heap{well_formed_heap2 g3}) =
(forall x. Seq.mem x (objects2 0UL g3) ==>
                                      (forall y. (Usize.v y >= 1 /\ Usize.v y <= Usize.v (getWosize (read_word g x))) /\
                                                         (is_hp_addr (Usize.add x (Usize.mul y mword))) ==>
                                                         read_word g (Usize.add x (Usize.mul y mword)) == 
                                                         read_word g3 (Usize.add x (Usize.mul y mword))))


 
#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options  "--split_queries"

#restart-solver

#restart-solver

#restart-solver

let fields_allocs_equal_pred (g:heap{well_formed_heap2 g})
                                                                 
                             (g3:heap{well_formed_heap2 g3})
                             (x:hp_addr{is_valid_header x g})=
  (forall y. Usize.v y >= 1 /\ Usize.v y <= (Usize.v (getWosize (read_word g x))) /\
                                                         is_hp_addr (Usize.add x (Usize.mul y mword)) ==>
                                                         Usize.v  (read_word g (Usize.add x (Usize.mul y mword))) == 
                                                         Usize.v (read_word g3 (Usize.add x (Usize.mul y mword))))

let object_field_reads_ver1_implies_allocs_field_reads_helper (g:heap{well_formed_heap2 g})
                                                                 
                                                              (g3:heap{well_formed_heap2 g3})
                                                              (h_index:hp_addr{is_valid_header h_index g})
                               : Lemma
                                 (requires (objects2 0UL g == objects2 0UL g3) /\
                                            (Seq.mem h_index (get_allocated_block_addresses g3)) /\
                                            (allocs_reads_equal g g3) /\
                                            (object_field_reads_ver1 g g3))
                                 (ensures fields_allocs_equal_pred g g3 h_index) = 
 assert (Seq.mem h_index (objects2 0UL g3));
 assert (Seq.mem h_index (get_allocated_block_addresses g3));
 assert ( Usize.v (getWosize (read_word g h_index)) == Usize.v (getWosize (read_word g3 h_index)));
 assert (fields_allocs_equal_pred g g3 h_index);
 ()

#restart-solver

#restart-solver 


#restart-solver 

#push-options "--z3rlimit 500"

#push-options  "--split_queries"

#restart-solver

let fields_allocated_blocks_lemma (g:heap{well_formed_heap2 g})
                                                                 
                                  (g3:heap{well_formed_heap2 g3})
                  : Lemma
                    (requires (objects2 0UL g == objects2 0UL g3) /\
                              (wosize_equal_pred g g3) /\
                              (field_equal_pred g g3) /\
                              (allocs_reads_equal g g3) /\
                              
                              (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> 
                                    Seq.mem x (get_allocated_block_addresses g)))
                                                             
                    (ensures (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                         Usize.v (getWosize (read_word g y)) == Usize.v (getWosize (read_word g3 y))) /\
                             (*allocs_field_reads_equal g g3*)
                             
                             (forall x. Seq.mem x (get_allocated_block_addresses g3) ==>
                                      (forall y. (Usize.v y >= 1 /\ Usize.v y <= Usize.v (getWosize (read_word g3 x))) /\
                                                         (is_hp_addr (Usize.add x (Usize.mul y mword))) ==>
                                                        Usize.v (read_word g (Usize.add x (Usize.mul y mword))) == 
                                                         Usize.v (read_word g3 (Usize.add x (Usize.mul y mword)))))) = 
assert (wosize_equal_pred g g3);
assert (objects2 0UL g == objects2 0UL g3);
assert (field_equal_pred g g3);

assert (forall x. Seq.mem x (objects2 0UL g3) ==> getWosize (read_word g x) == getWosize (read_word g3 x));
assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==> getWosize (read_word g y) == getWosize (read_word g3 y));

fields_allocated_blocks_all_helper_lemma1  g g3;
assert (object_field_reads_ver1 g g3);
assert (forall x. Seq.mem x (objects2 0UL g3) ==>
                                      (forall y. (Usize.v y >= 1 /\ Usize.v y <= Usize.v (getWosize (read_word g x))) /\
                                                         (is_hp_addr (Usize.add x (Usize.mul y mword))) ==>
                                                        Usize.v (read_word g (Usize.add x (Usize.mul y mword))) == 
                                                         Usize.v (read_word g3 (Usize.add x (Usize.mul y mword)))));
assert (forall x. Seq.mem x (objects2 0UL g3) ==>
                                      (forall y. (Usize.v y >= 1 /\ Usize.v y <= Usize.v (getWosize (read_word g3 x))) /\
                                                         (is_hp_addr (Usize.add x (Usize.mul y mword))) ==>
                                                        Usize.v (read_word g (Usize.add x (Usize.mul y mword))) == 
                                                         Usize.v (read_word g3 (Usize.add x (Usize.mul y mword)))));
assert (forall x. Seq.mem x (get_allocated_block_addresses g3) ==>
                                      (forall y. (Usize.v y >= 1 /\ Usize.v y <= Usize.v (getWosize (read_word g3 x))) /\
                                                         (is_hp_addr (Usize.add x (Usize.mul y mword))) ==>
                                                        Usize.v (read_word g (Usize.add x (Usize.mul y mword))) == 
                                                         Usize.v (read_word g3 (Usize.add x (Usize.mul y mword)))));

()


(*(forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                     (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                     (is_hp_addr ((Usize.add y (Usize.mul t mword))) ==>
                                     Usize.v (read_word g (Usize.add y (Usize.mul t mword))) == 
                                     Usize.v (read_word g3 (Usize.add y (Usize.mul t mword))))))
                                     
 (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                     (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                     (is_hp_addr ((Usize.add y (Usize.mul t mword))) ==>
                                     Usize.v (read_word g (Usize.add y (Usize.mul t mword))) == 
                                     Usize.v (read_word g3 (Usize.add y (Usize.mul t mword)))))))
 
  (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                     (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                     (is_hp_addr ((Usize.add y (Usize.mul t mword))) ==>
                                     Usize.v (read_word g (Usize.add y (Usize.mul t mword))) == 
                                     Usize.v (read_word g3 (Usize.add y (Usize.mul t mword))))))
 
 *)

#pop-options

#restart-solver 

#restart-solver 

#reset-options "--z3rlimit 1000"
#push-options "--split_queries"

#restart-solver 

(*allocs_field_read_equal
  (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                     (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g3 y))) /\
                                     (is_hp_addr ((Usize.add y (Usize.mul t mword))) ==>
                                     Usize.v (read_word g (Usize.add y (Usize.mul t mword))) == 
                                     Usize.v (read_word g3 (Usize.add y (Usize.mul t mword))))))*)





#restart-solver

#restart-solver 

let mark_and_sweep_GC1_well_formed_allocated_blocks1_lemma7 (g:heap{well_formed_heap2 g /\ 
                                                                  well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                         (*root pointers--------------------------------------------------------------------------------------------*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (c:color{c == 3UL})
                                    (c1:color{c1 == 2UL})
                : Lemma
                  (ensures (well_formed_allocated_blocks (mark_and_sweep_GC1 g h_list))) = 
 
 (*Mark stack creation-----------------------------------------------------------------------------------------*)
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);

 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in
 create_root_stack_and_gray_modified_heap_noBlackObjects_lemma g st h_list;
 assert (noBlackObjects g1);
 let allocs = get_allocated_block_addresses g1 in
 let vl = get_black_block_addresses g1 allocs in
 assert (Seq.length vl == 0);
 assert (Seq.length st == 0);
 create_root_stack_and_gray_modified_heap_mem_lemma g st h_list;
 assert ((forall x. Seq.mem x st ==> Seq.mem x st') /\
                (forall x. Seq.mem x h_list ==> Seq.mem x st'));
 assert (forall x. Seq.mem x st' ==> Seq.mem x st \/ Seq.mem x h_list);
 assert (forall x. Seq.mem x st' ==> Seq.mem x h_list);
 assert (forall x. Seq.mem x st' <==> Seq.mem x h_list);
 assert (objects2 0UL g == objects2 0UL g1);
 create_root_stack_and_gray_modified_heap_fields_lemma g st h_list; 
 assert (wosize_equal_pred g g1);
 assert (field_equal_pred g g1);
 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);
 assert (G.is_vertex_set st');
 assert (G.subset_vertices st' (get_allocated_block_addresses g1));
 assert (G.subset_vertices vl (get_allocated_block_addresses g1));
 assert (well_formed_heap2 g2);
 assert (well_formed_allocated_blocks g);
 mark5_objects2_lemma g1 st';
 assert (objects2 0UL g1 == objects2 0UL g2);
 assert (objects2 0UL g == objects2 0UL g2);
 
 create_root_stack_and_gray_modified_heap_well_formed_allocated_blocks_lemma g st h_list c1;
 
 assert (well_formed_allocated_blocks g1);
 well_formed_allocated_blocks_mark5 g1 st' c;
 assert (well_formed_allocated_blocks g2);
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
 assert (G.subset_vertices h_list (get_allocated_block_addresses g));
 assert (G.subset_vertices h_list (get_allocated_block_addresses g1));
 assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));
 mark5_fields_lemma g1 st';
 assert (wosize_equal_pred g1 g2);
 assert (field_equal_pred g1 g2);
 field_equal_trans_lemma g g1 g2;
 assert (wosize_equal_pred g g2);
 assert (field_equal_pred g g2);
 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3 = sweep1 g2 0UL in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);
 
 mark_and_sweep_GC1_safety_lemma1 g h_list c c1;
 mark_and_sweep_GC1_safety_lemma2 g h_list c c1;
 
 assert (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2);
                                                                          
 assert (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3);
                                                      

 assert (forall x.  (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2  ==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
                                                                                     
 assert (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  ==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
                                               
 
 assert (forall x.  (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)); 
 
 
 assert (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)); 
 
 
 
 
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;

 field_limits_allocated_blocks_lemma g3;
 field_contents_within_limits_allocated_blocks_lemma g3;


 fieldaddress_within_limits_lemma_x_all1 g3;
 
 
 assert (objects2 0UL g3 == objects2 0UL g2);

 assert (noGreyObjects g2);

 field_limits_allocated_blocks_lemma g2;
 field_contents_within_limits_allocated_blocks_lemma g2;
 fieldaddress_within_limits_lemma_x_all g2;

 assert (forall y. Seq.mem y (get_allocated_block_addresses g2) ==> is_fields_within_limit1 y (getWosize (read_word g2 y)));
 assert (forall y . Seq.mem y (get_allocated_block_addresses g2) ==> is_fields_contents_within_limit2 y (getWosize (read_word g2 y)) g2);
 assert (forall y. Seq.mem y (get_allocated_block_addresses g2) ==> (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g2 y)) ==> 
                                                                  (Usize.v y  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0));
 
 assert (forall i x.  Seq.mem x (get_allocated_block_addresses g2) /\ 
                                   (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g2 x))) ==> 
                                   (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);

 assert (well_formed_allocated_blocks g2);

 allocs_of_after_sweep_is_subset_of_allocs_before_sweep g2;
 
 assert (forall x. Seq.mem x (objects2 0UL g3) /\ (isWhiteObject1 x g3) <==> Seq.mem x (get_allocated_block_addresses g3));
                                         
 assert (G.subset_vertices (get_allocated_block_addresses g3) (get_allocated_block_addresses g2));

 graph_successors_heap_create_successor_list_equivalence_lemma_all g;
 create_successors_list_for_all_mem_lemma3 g;
 
 assert (forall y. Seq.mem y (get_allocated_block_addresses g) ==>
                                             G.successors (create_graph_from_heap g) y == 
                                             create_successors_list_for_h_index g y (getWosize (read_word g y)) 1UL);
 
 (*assert (forall y. Seq.mem y (get_allocated_block_addresses g) /\
                                   Seq.mem y (get_allocated_block_addresses g) ==> 
                                    (forall t.  (Usize.v t >= 1 /\ Usize.v t <= Usize.v (getWosize (read_word g y))) /\
                                     (is_hp_addr ((Usize.add y (Usize.mul t mword)))) /\
                                     isPointer (Usize.add y (Usize.mul t mword)) g ==>
                                      Seq.mem (read_word g (Usize.add y (Usize.mul t mword))) 
                                        (create_successors_list_for_h_index g y (getWosize (read_word g y)) 1UL)));*)
 assert (get_allocated_block_addresses g2 == get_allocated_block_addresses g1);
 assert (get_allocated_block_addresses g2 == get_allocated_block_addresses g);
 assert (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> Seq.mem x (get_allocated_block_addresses g));
 
 assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                             G.successors (create_graph_from_heap g) y == 
                                             create_successors_list_for_h_index g y (getWosize (read_word g y)) 1UL);
 
 white_object_all_fields_reach_lemma1 g g3 h_list;

 sweep1_fields_lemma g2 0UL;
 assert (wosize_equal_pred g2 g3);
 assert (field_equal_pred g2 g3);
 field_equal_trans_lemma g g2 g3;
 assert (wosize_equal_pred g g3);
 assert (field_equal_pred g g3);
 allocs_reads_equal_from_wosize_equal_pred g g3;
 assert (forall y. Seq.mem y (get_allocated_block_addresses g3) ==>
                                         Usize.v (getWosize (read_word g y)) == Usize.v (getWosize (read_word g3 y)));
 //dummy_lemma1 g g3;
 fields_allocated_blocks_lemma g g3;
 white_object_all_fields_reach_lemma3 g g3 h_list;
 assert (well_formed_allocated_blocks g3);
 ()


#restart-solver 



(*memory alignment in Aymeric allocator*)
(*free-list implementation without proofs*)


#restart-solver

#restart-solver 

#restart-solver



#restart-solver

#reset-options "--z3rlimit 1000"

#restart-solver

//#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let mark_and_sweep_GC1_well_formed_allocated_blocks1_lemma (g:heap{well_formed_heap2 g /\ 
                                                                  well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                         (*root pointers--------------------------------------------------------------------------------------------*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (c:color{c == 3UL})
                                    (c1:color{c1 == 2UL})
                : Lemma
                  (ensures (forall x.  (Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list))) /\ isWhiteObject1 x (mark_and_sweep_GC1 g h_list)  <==> 
                                            (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)) (*/\
                           (forall x. Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list)) /\ (isWhiteObject1 x (mark_and_sweep_GC1 g h_list)) <==> 
                                             Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)))*)) = 
                           
 
(*Mark stack creation-----------------------------------------------------------------------------------------*)
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);

 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in
 create_root_stack_and_gray_modified_heap_noBlackObjects_lemma g st h_list;
 assert (noBlackObjects g1);
 let allocs = get_allocated_block_addresses g1 in
 let vl = get_black_block_addresses g1 allocs in
 assert (Seq.length vl == 0);
 assert (Seq.length st == 0);
 create_root_stack_and_gray_modified_heap_mem_lemma g st h_list;
 assert ((forall x. Seq.mem x st ==> Seq.mem x st') /\
                (forall x. Seq.mem x h_list ==> Seq.mem x st'));
 assert (forall x. Seq.mem x st' ==> Seq.mem x st \/ Seq.mem x h_list);
 assert (forall x. Seq.mem x st' ==> Seq.mem x h_list);
 assert (forall x. Seq.mem x st' <==> Seq.mem x h_list);
 assert (objects2 0UL g == objects2 0UL g1);
 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);
 assert (G.is_vertex_set st');
 assert (G.subset_vertices st' (get_allocated_block_addresses g1));
 assert (G.subset_vertices vl (get_allocated_block_addresses g1));
 assert (well_formed_heap2 g2);
 assert (well_formed_allocated_blocks g);
 mark5_objects2_lemma g1 st';
 assert (objects2 0UL g1 == objects2 0UL g2);
 assert (objects2 0UL g == objects2 0UL g2);
 
 create_root_stack_and_gray_modified_heap_well_formed_allocated_blocks_lemma g st h_list c1;
 
 assert (well_formed_allocated_blocks g1);
 well_formed_allocated_blocks_mark5 g1 st' c;
 assert (well_formed_allocated_blocks g2);
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
 assert (G.subset_vertices h_list (get_allocated_block_addresses g));
 assert (G.subset_vertices h_list (get_allocated_block_addresses g1));
 assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));

 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3 = sweep1 g2 0UL in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);
 mark_and_sweep_GC1_safety_lemma1 g h_list c c1;
 mark_and_sweep_GC1_safety_lemma2 g h_list c c1;

 assert (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2);
                                                                          
 assert (forall o x (z2: G.reach (create_graph_from_heap g) o x). (G.reachfunc (create_graph_from_heap g) o x z2) /\ Seq.mem o h_list ==>
                                                                          (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3);
                                                      

 assert (forall x.  (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2  ==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
                                                                                     
 assert (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  ==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
                                               
 
 assert (forall x.  (Seq.mem x (objects2 0UL g2)) /\ isBlackObject1 x g2  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)); 
 
 
 assert (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));                                        
 
 assert (well_formed_allocated_blocks g2);
 
 let allocs_sweep1 = get_allocated_block_addresses g3 in
 field_limits_allocated_blocks_lemma g2;
 field_contents_within_limits_allocated_blocks_lemma g2;
 fieldaddress_within_limits_lemma_x_all g2;
 allocs_of_after_sweep_is_subset_of_allocs_before_sweep g2;
 assert (forall x. Seq.mem x (objects2 0UL g3) /\ (isWhiteObject1 x g3) <==> Seq.mem x allocs_sweep1);
 assert (forall x.  (Seq.mem x (objects2 0UL g3)) /\ isWhiteObject1 x g3  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));  
 assert (forall x. Seq.mem x allocs_sweep1  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)); 
 assert (forall x. Seq.mem x (objects2 0UL g2) /\ color_of_object1 x g2 == black <==> 
                                Seq.mem x (objects2 0UL g3) /\ color_of_object1 x g3 == white);
 
 
 
 assert (forall x.  (Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list))) /\ isWhiteObject1 x (mark_and_sweep_GC1 g h_list)  <==> 
                                            (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
 
 assert (forall x. Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list)) /\ (isWhiteObject1 x (mark_and_sweep_GC1 g h_list)) <==> 
                                             Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)));
 ()



#restart-solver 

#restart-solver 

#restart-solver


let  mark_and_sweep_GC1_safety_main_vertices_lemma(g:heap{well_formed_heap2 g /\ 
                                                   well_formed_allocated_blocks g /\  
                                noGreyObjects g /\ 
                                only_white_and_blue_blocks g /\
                                noBlackObjects g})
                        (*root pointers--------------------------------------------------------------------------------------------------------------------------*)
                        (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                           (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                           (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                           (G.is_vertex_set h_list) /\
                                           (G.subset_vertices h_list (get_allocated_block_addresses g))})
                        (c:color{c == 3UL})
                        (c1:color{c1 == 2UL})
                    : Lemma
                      (requires (well_formed_heap2(mark_and_sweep_GC1 g h_list) /\ well_formed_allocated_blocks (mark_and_sweep_GC1 g h_list)))
                      (ensures (forall x.   Seq.mem x ((create_graph_from_heap (mark_and_sweep_GC1 g h_list)).vertices) <==> 
                                     (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1))) =
  let g' = mark_and_sweep_GC1 g h_list in
  let grph = create_graph_from_heap g in
  let grph' = create_graph_from_heap g' in
  mark_and_sweep_GC1_well_formed_allocated_blocks1_lemma g h_list c c1;
  assert (forall x.  (Seq.mem x (objects2 0UL g')) /\ isWhiteObject1 x g'  <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1)); (*-->proved*)
  
  let allocs_GC = get_allocated_block_addresses g' in
 
  assert (forall x. Seq.mem x (objects2 0UL g') /\ (isWhiteObject1 x g') <==> Seq.mem x allocs_GC); (*---> proved*)

  assert (forall x.   Seq.mem x allocs_GC <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
  let vertices_GC = grph'.vertices in
  assert (vertices_GC == allocs_GC);

  assert (forall x.   Seq.mem x vertices_GC <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
  assert (forall x.   Seq.mem x (grph'.vertices) <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
  assert (forall x.   Seq.mem x ((create_graph_from_heap g').vertices) <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
  assert (forall x.   Seq.mem x ((create_graph_from_heap (mark_and_sweep_GC1 g h_list)).vertices) <==> (exists o (z1: G.reach (create_graph_from_heap g) o x) . Seq.mem o h_list /\
                                                                                     G.reachfunc (create_graph_from_heap g) o x z1));
 
  ()


#restart-solver 

#reset-options "--z3rlimit 1000" 

#push-options "--split_queries"

#restart-solver 

#restart-solver 

let mark_and_sweep_GC1_safety_main_edges_lemma1     (g:heap{well_formed_heap2 g /\ 
                                                       well_formed_allocated_blocks g /\  
                                                       noGreyObjects g /\ 
                                                       only_white_and_blue_blocks g /\
                                                       noBlackObjects g})
                                                     
                                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                           (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                           (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                           (G.is_vertex_set h_list) /\
                                                                           (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                                      (c:color{c == 3UL})
                                                      (c1:color{c1 == 2UL}) 
                                         
                    : Lemma
                      (requires (well_formed_heap2(mark_and_sweep_GC1 g h_list)) /\ 
                                (well_formed_allocated_blocks (mark_and_sweep_GC1 g h_list)) /\
                                (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). 
                                    getWosize (read_word g x) == getWosize (read_word (mark_and_sweep_GC1 g h_list) x)) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==> 
                                                      is_fields_within_limit1 x (getWosize (read_word (mark_and_sweep_GC1 g h_list) x))) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==> 
                                             is_fields_contents_within_limit2 x (getWosize (read_word (mark_and_sweep_GC1 g h_list) x)) 
                                                                 (mark_and_sweep_GC1 g h_list)) /\
                                (forall j x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                (forall j x.  Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) /\ 
                                          (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word (mark_and_sweep_GC1 g h_list) x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0))
                                
                               
                   (ensures (forall y. Seq.mem y (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==>  
                                               create_successors_list_for_h_index (mark_and_sweep_GC1 g h_list) y 
                                                                                  (getWosize (read_word (mark_and_sweep_GC1 g h_list) y)) 
                                                                                  1UL ==
                                               create_successors_list_for_h_index g y 
                                                                                 (getWosize (read_word g y)) 
                                                                                  1UL)) = 
     
     
     (*Mark stack creation-----------------------------------------------------------------------------------------*)
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);

 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in
 create_root_stack_and_gray_modified_heap_noBlackObjects_lemma g st h_list;
 assert (noBlackObjects g1);
 let allocs = get_allocated_block_addresses g1 in
 let vl = get_black_block_addresses g1 allocs in
 assert (Seq.length vl == 0);
 assert (Seq.length st == 0);
 create_root_stack_and_gray_modified_heap_mem_lemma g st h_list;
 assert ((forall x. Seq.mem x st ==> Seq.mem x st') /\
                (forall x. Seq.mem x h_list ==> Seq.mem x st'));
 assert (forall x. Seq.mem x st' ==> Seq.mem x st \/ Seq.mem x h_list);
 assert (forall x. Seq.mem x st' ==> Seq.mem x h_list);
 assert (forall x. Seq.mem x st' <==> Seq.mem x h_list);
 assert (objects2 0UL g == objects2 0UL g1);
 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);
 assert (G.is_vertex_set st');
 assert (G.subset_vertices st' (get_allocated_block_addresses g1));
 assert (G.subset_vertices vl (get_allocated_block_addresses g1));
 assert (well_formed_heap2 g2);
 assert (well_formed_allocated_blocks g);
 mark5_objects2_lemma g1 st';
 assert (objects2 0UL g1 == objects2 0UL g2);
 assert (objects2 0UL g == objects2 0UL g2);
 
 create_root_stack_and_gray_modified_heap_well_formed_allocated_blocks_lemma g st h_list c1;
 
 assert (well_formed_allocated_blocks g1);
 well_formed_allocated_blocks_mark5 g1 st' c;
 assert (well_formed_allocated_blocks g2);
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
 assert (G.subset_vertices h_list (get_allocated_block_addresses g));
 assert (G.subset_vertices h_list (get_allocated_block_addresses g1));
 assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));

 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3 = sweep1 g2 0UL in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);
 field_limits_objects2_lemma g2;
 field_contents_within_limits_objects2_lemma g2;
 fieldaddress_within_limits_lemma_x_all3 g2;
 
 field_limits_objects2_lemma g3;
 field_contents_within_limits_objects2_lemma g3;
 fieldaddress_within_limits_lemma_x_all3 g3;

 assert (well_formed_heap2 g2 /\ noGreyObjects g2);
 sweep1_field_pointers_lemma g2 0UL;

 assert (forall x. Seq.mem x (objects2 0UL g3) ==> 
                             field_pointers_for_h_index g2 x (getWosize (read_word g2 x)) 1UL == 
                             field_pointers_for_h_index g3 x (getWosize (read_word g3 x)) 1UL);
 
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;

 field_limits_allocated_blocks_lemma g2;
 field_contents_within_limits_allocated_blocks_lemma g2;
 fieldaddress_within_limits_lemma_x_all g2;

 dfs_mark_equivalence_graph_lemma g1 st' vl c;
 let grph1 = create_graph_from_heap g in
 let grph2 = create_graph_from_heap g1 in
 let grph3 = create_graph_from_heap g2 in
 assert (grph1 == grph2);
 assert (grph2 == grph3);
 assert (grph1 == grph3);
 successors_list_for_all_remain_same_lemma g g2 h_list;
 assert (forall x. Seq.mem x (get_allocated_block_addresses g2) ==> 
                                 create_successors_list_for_h_index g x (getWosize (read_word g x)) 1UL ==
                                 create_successors_list_for_h_index g2 x (getWosize (read_word g2 x)) 1UL);
 
 field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma1_all g2;
 
 field_limits_allocated_blocks_lemma g3;
 field_contents_within_limits_allocated_blocks_lemma g3;
 fieldaddress_within_limits_lemma_x_all g3;
 mark_and_sweep_GC1_well_formed_allocated_blocks1_lemma7 g h_list c c1;
 assert (well_formed_allocated_blocks (mark_and_sweep_GC1 g h_list));
 assert (well_formed_allocated_blocks g3);
 
 
 field_pointers_for_h_index_equals_create_successors_list_for_h_index_lemma1_all g3;
 assert (forall x. Seq.mem x (get_allocated_block_addresses g2) /\ is_valid_header x g2 ==>  
                                               field_pointers_for_h_index g2 x (getWosize (read_word g2 x)) 1UL == 
                                               create_successors_list_for_h_index g2 x (getWosize (read_word g2 x)) 1UL);
 assert (forall x. Seq.mem x (get_allocated_block_addresses g3) /\ is_valid_header x g3 ==>  
                                               field_pointers_for_h_index g3 x (getWosize (read_word g3 x)) 1UL == 
                                               create_successors_list_for_h_index g3 x (getWosize (read_word g3 x)) 1UL);
 
 assert (forall x. Seq.mem x (objects2 0UL g3) ==> 
                             field_pointers_for_h_index g2 x (getWosize (read_word g2 x)) 1UL == 
                             field_pointers_for_h_index g3 x (getWosize (read_word g3 x)) 1UL);
 
 assert (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> 
                             field_pointers_for_h_index g2 x (getWosize (read_word g2 x)) 1UL == 
                             field_pointers_for_h_index g3 x (getWosize (read_word g3 x)) 1UL);
 
 
 assert (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> 
            create_successors_list_for_h_index g2 x (getWosize (read_word g2 x)) 1UL ==
            create_successors_list_for_h_index g3 x (getWosize (read_word g3 x)) 1UL);
 
 allocs_of_after_sweep_is_subset_of_allocs_before_sweep g2;
 assert (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> Seq.mem x (get_allocated_block_addresses g2));
 
 assert (forall x. Seq.mem x (get_allocated_block_addresses g3) ==> 
            create_successors_list_for_h_index g x (getWosize (read_word g x)) 1UL  ==
            create_successors_list_for_h_index g3 x (getWosize (read_word g3 x)) 1UL);
 
 
 assert (forall y. Seq.mem y (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==>  
                                               create_successors_list_for_h_index (mark_and_sweep_GC1 g h_list) y 
                                                                                  (getWosize (read_word (mark_and_sweep_GC1 g h_list) y)) 
                                                                                  1UL ==
                                               create_successors_list_for_h_index g y 
                                                                                 (getWosize (read_word g y)) 
                                                                                  1UL);
 ()

#restart-solver 

#restart-solver 




#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver 

let mark_and_sweep_GC1_subgraph_edge_equivalence_lemma (g:heap{well_formed_heap2 g /\ 
                                                       well_formed_allocated_blocks g /\  
                                                       noGreyObjects g /\ 
                                                       only_white_and_blue_blocks g /\
                                                       noBlackObjects g})
                                                     
                                                      (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                           (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                           (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                           (G.is_vertex_set h_list) /\
                                                                           (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                                      (c:color{c == 3UL})
                                                      (c1:color{c1 == 2UL}) 
                                         
                    : Lemma
                      (requires (well_formed_heap2(mark_and_sweep_GC1 g h_list)) /\ 
                                (well_formed_allocated_blocks (mark_and_sweep_GC1 g h_list)) /\
                                (forall (x:Usize.t{Usize.v x < heap_size /\ Usize.v x % 8 == 0}). 
                                    getWosize (read_word g x) == getWosize (read_word (mark_and_sweep_GC1 g h_list) x)) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==> 
                                                      is_fields_within_limit1 x (getWosize (read_word (mark_and_sweep_GC1 g h_list) x))) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==> 
                                             is_fields_contents_within_limit2 x (getWosize (read_word (mark_and_sweep_GC1 g h_list) x)) 
                                                                 (mark_and_sweep_GC1 g h_list)) /\
                                (forall j x.  Seq.mem x (get_allocated_block_addresses g) /\ (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                (forall j x.  Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) /\ 
                                          (Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word (mark_and_sweep_GC1 g h_list) x))) ==> 
                                                    (Usize.v x  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==> 
                                         create_successors_list_for_h_index g x (getWosize (read_word g x)) 1UL  ==
                                         create_successors_list_for_h_index (mark_and_sweep_GC1 g h_list) x 
                                                                            (getWosize (read_word (mark_and_sweep_GC1 g h_list) x)) 1UL) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                      G.successors (create_graph_from_heap g) x == 
                                                      create_successors_list_for_h_index g x (getWosize (read_word g x)) 1UL) /\
                                (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==> 
                                                      G.successors (create_graph_from_heap (mark_and_sweep_GC1 g h_list)) x == 
                                                      create_successors_list_for_h_index (mark_and_sweep_GC1 g h_list) x 
                                                                                         (getWosize (read_word (mark_and_sweep_GC1 g h_list) x)) 1UL))
                                
                               
                   (ensures (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==>
                                             G.successors (create_graph_from_heap (mark_and_sweep_GC1 g h_list)) x == 
                                             G.successors (create_graph_from_heap g) x)) = 
mark_and_sweep_GC1_safety_main_edges_lemma1 g h_list 3UL 2UL;
assert (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==> 
                                         create_successors_list_for_h_index g x (getWosize (read_word g x)) 1UL  ==
                                         create_successors_list_for_h_index (mark_and_sweep_GC1 g h_list) x 
                                                                            (getWosize (read_word (mark_and_sweep_GC1 g h_list) x)) 1UL);

graph_successors_heap_create_successor_list_equivalence_lemma_all g;
graph_successors_heap_create_successor_list_equivalence_lemma_all (mark_and_sweep_GC1 g h_list);

assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> 
                                                      G.successors (create_graph_from_heap g) x == 
                                                      create_successors_list_for_h_index g x (getWosize (read_word g x)) 1UL);
assert (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==> 
                                                      G.successors (create_graph_from_heap (mark_and_sweep_GC1 g h_list)) x == 
                                                      create_successors_list_for_h_index (mark_and_sweep_GC1 g h_list) x 
                                                                                         (getWosize (read_word (mark_and_sweep_GC1 g h_list) x)) 1UL);
assert (forall x. Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)) ==>
                                             G.successors (create_graph_from_heap (mark_and_sweep_GC1 g h_list)) x == 
                                             G.successors (create_graph_from_heap g) x); 
()

(*Together the below shows sub-graph of reachable objects preservance.*)
(*forall x. Seq.mem x grph'.vertices <==> All reachable objects from the root set in grph.vertices*)
(*forall x. Seq.mem x grph'.vertices ==> Seq.mem x grph.vertices*)
(*forall x. Seq.mem x grph'.vertices ==> G.successors grph' x ==
                                         G.successors grph x*)

#restart-solver 

//#reset-options "--z3rlimit 1000"

//#push-options "--split_queries"

#reset-options "--z3rlimit 1000"

#push-options "--split_queries"

#restart-solver

let mark_and_sweep_GC1_well_formed_allocated_blocks1_lemma1 (g:heap{well_formed_heap2 g /\ 
                                                                  well_formed_allocated_blocks g /\  
                                                                  noGreyObjects g /\ 
                                                                  only_white_and_blue_blocks g /\
                                                                  noBlackObjects g})
                                         (*root pointers--------------------------------------------------------------------------------------------*)
                                    (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                          (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                          (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                          (G.is_vertex_set h_list) /\
                                                          (G.subset_vertices h_list (get_allocated_block_addresses g))})
                                    (c:color{c == 3UL})
                                    (c1:color{c1 == 2UL})
                : Lemma
                  (ensures (forall x. Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list)) /\ (isWhiteObject1 x (mark_and_sweep_GC1 g h_list)) <==> 
                                             Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)))) = 
                           
 
(*Mark stack creation-----------------------------------------------------------------------------------------*)
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);

 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in
 create_root_stack_and_gray_modified_heap_noBlackObjects_lemma g st h_list;
 assert (noBlackObjects g1);
 let allocs = get_allocated_block_addresses g1 in
 let vl = get_black_block_addresses g1 allocs in
 assert (Seq.length vl == 0);
 assert (Seq.length st == 0);
 create_root_stack_and_gray_modified_heap_mem_lemma g st h_list;
 assert ((forall x. Seq.mem x st ==> Seq.mem x st') /\
                (forall x. Seq.mem x h_list ==> Seq.mem x st'));
 assert (forall x. Seq.mem x st' ==> Seq.mem x st \/ Seq.mem x h_list);
 assert (forall x. Seq.mem x st' ==> Seq.mem x h_list);
 assert (forall x. Seq.mem x st' <==> Seq.mem x h_list);
 assert (objects2 0UL g == objects2 0UL g1);
 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);
 assert (G.is_vertex_set st');
 assert (G.subset_vertices st' (get_allocated_block_addresses g1));
 assert (G.subset_vertices vl (get_allocated_block_addresses g1));
 assert (well_formed_heap2 g2);
 assert (well_formed_allocated_blocks g);
 mark5_objects2_lemma g1 st';
 assert (objects2 0UL g1 == objects2 0UL g2);
 assert (objects2 0UL g == objects2 0UL g2);
 
 create_root_stack_and_gray_modified_heap_well_formed_allocated_blocks_lemma g st h_list c1;
 
 assert (well_formed_allocated_blocks g1);
 well_formed_allocated_blocks_mark5 g1 st' c;
 assert (well_formed_allocated_blocks g2);
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
 assert (G.subset_vertices h_list (get_allocated_block_addresses g));
 assert (G.subset_vertices h_list (get_allocated_block_addresses g1));
 assert (forall x. Seq.mem x st' ==> ~(Seq.mem x vl));
 assert (forall x. Seq.mem x vl ==> ~(Seq.mem x st'));

 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3 = sweep1 g2 0UL in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);
                                      
 assert (well_formed_allocated_blocks g2);
 
 let allocs_sweep1 = get_allocated_block_addresses g3 in
 field_limits_allocated_blocks_lemma g2;
 field_contents_within_limits_allocated_blocks_lemma g2;
 fieldaddress_within_limits_lemma_x_all g2;
 allocs_of_after_sweep_is_subset_of_allocs_before_sweep g2;
 assert (forall x. Seq.mem x (objects2 0UL g3) /\ (isWhiteObject1 x g3) <==> Seq.mem x allocs_sweep1);

 
 assert (forall x. Seq.mem x (objects2 0UL (mark_and_sweep_GC1 g h_list)) /\ (isWhiteObject1 x (mark_and_sweep_GC1 g h_list)) <==> 
                                             Seq.mem x (get_allocated_block_addresses (mark_and_sweep_GC1 g h_list)));
 ()


#restart-solver 

let sweep1_structure_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
               (h_index:hp_addr{is_valid_header h_index g /\ (Seq.length (objects2 h_index g) > 0)})
          : Lemma 
            (requires (let wz =  getWosize (read_word g h_index) in
                       let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                        (Usize.v h_index_new <  heap_size ==> is_hp_addr h_index_new /\ 
                                                              is_valid_header h_index_new (sweep_body_helper g h_index) /\
                                                              (Seq.length (objects2 h_index_new (sweep_body_helper g h_index)) > 0))))
            (ensures (let wz =  getWosize (read_word g h_index) in
                      let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
                       (sweep1 g h_index =  (if (Usize.v h_index_new >= heap_size) then
                                              (
                                                sweep_body_helper g h_index
                                              )
                                             else
                                             (
                                                sweep1 (sweep_body_helper g h_index) h_index_new
                                             )))))
            (decreases (heap_size - Usize.v h_index)) = 
let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let g' = sweep_body_helper g h_index in 
 assert (well_formed_heap2 g');
 assert (objects2 0UL g == objects2 0UL g');
 if Usize.v h_index_new >= heap_size then
 (
   ()
 )
 else
 (
      wosize_plus_times_mword_multiple_of_mword1 wz;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);
      
      objects2_mem_lemma1_app h_index g;
      
      assert (is_valid_header h_index_new g);
      assert (is_valid_header h_index_new g');
     
      assert (Seq.mem h_index (objects2 0UL g));
      assert (Seq.length (objects2 0UL g) > 0);
      assert (Seq.length (objects2 h_index g) > 0);
      assert (Seq.length (objects2 h_index g') > 0);
      
      objects2_length_lemma1 g' h_index h_index_new; 
      assert (Seq.length (objects2 h_index_new g') > 0);
      
      let g'' = sweep1 g' h_index_new in
     
      assert (objects2 0UL g' == objects2 0UL g'');
      assert (objects2 0UL g'' == objects2 0UL g);
      ()
 )

#restart-solver 

#restart-solver

let mark_and_sweep_GC1_output_equivalence_lemma (g:heap{well_formed_heap2 g /\ 
                                                        well_formed_allocated_blocks g /\  
                                                        noGreyObjects g /\ 
                                                        only_white_and_blue_blocks g /\
                                                        noBlackObjects g})
                                                (*root pointers---------------------------------------------------------------------------------------------------*)
                                                (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                     (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                     (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                     (G.is_vertex_set h_list) /\
                                                                     (G.subset_vertices h_list (get_allocated_block_addresses g))}) 
                                                
                                                (st: seq Usize.t{st == Seq.empty #Usize.t /\ G.is_vertex_set st})
                                                (g1:heap{
                                                         (g1 == snd (create_root_stack_and_gray_modified_heap g st h_list))})
                                                (st': seq Usize.t { 
                                                                    (st' == fst (create_root_stack_and_gray_modified_heap g st h_list)) /\
                                                                    (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                    (forall x. Seq.mem x st' ==> is_valid_header x g1) /\
                                                                    (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                                    (G.is_vertex_set st') /\
                                                                    (forall x. Seq.mem x (objects2 0UL g1) /\ isGrayObject1 x g1 <==>
                                                                       Seq.mem x st')
                                                                 })
                                                (g2:heap{g2 == mark5 g1 st'})
                         :Lemma
                          (requires (well_formed_heap2 g2) /\ (noGreyObjects g2) /\ (is_valid_header 0UL g2) /\ Seq.length (objects2 0UL g2) > 0)
                          (ensures mark_and_sweep_GC1 g h_list == sweep1 g2 0UL)= 
 let g3 = sweep1 g2 0UL in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 (*assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);*)
 assert (mark_and_sweep_GC1 g h_list == g3);
 ()

let well_formed_objects_lemma (g:heap{well_formed_heap2 g})
                  : Lemma 
                    (ensures (Seq.length (objects2 0UL g) > 0)) = ()


(*(Usize.v y >= Usize.v x + Usize.v mword) /\ (Usize.v y <= Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword)*) 
                                                  
#restart-solver 

let fields_not_mem_objs_lemma (g:heap{well_formed_heap2 g})
                              (g':heap)
                              (h_index:hp_addr{Seq.mem h_index (objects2 0UL g)})
                              (y:hp_addr{Usize.v y >= Usize.v h_index + Usize.v mword /\
                                       Usize.v y <= Usize.v h_index + (Usize.v (getWosize (read_word g h_index)) * Usize.v mword)})
                  : Lemma
                    (ensures ~(Seq.mem y (objects2 0UL g))) = 
assert (~(Seq.mem y (objects2 0UL g)));
()

let objects2_equal_lemma1_app (g:heap{well_formed_heap2 g}) 
                              (g':heap)
                              
                   :   Lemma
                       (requires (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g' p) ==  getWosize (read_word g p)))
                       (ensures (objects2 0UL g == objects2 0UL g'))= 
 objects2_equal_lemma1 g g' 0UL;
 assert (objects2 0UL g == objects2 0UL g');
 ()

let write_word_replacement_lemma1 (byte_array: heap)
                                 (byte_index: hp_addr)
                                 (value: UInt64.t)
            : Lemma
              (ensures (read_word (write_word byte_array byte_index value) byte_index == value)) = ()
                                                  
let write_word_before_start_lemma1 (byte_array: heap)
                                  (byte_index: hp_addr)
                                  (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). Usize.v i >= 0 /\  Usize.v i < Usize.v byte_index /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) = 
 replace_range_before_start_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)

let write_word_after_start_end_lemma1 (byte_array: heap)
                                     (byte_index: hp_addr)
                                     (value: UInt64.t)
                      : Lemma
                        (ensures (forall (i:hp_addr). (Usize.v i >= ((Usize.v byte_index) + Usize.v mword)) /\ (Usize.v i < length byte_array) /\ (Usize.v i % Usize.v mword == 0) ==>
                                                  read_word (write_word byte_array byte_index value) i == read_word byte_array i)) =
 replace_range_after_start_end_all_lemma byte_array byte_index (FStar.Endianness.le_of_uint64 value)

let write_word_lemma1 (byte_array: heap)
                      (byte_index: hp_addr)
                      (value: UInt64.t)
                : Lemma 
                  ((forall (i:hp_addr). read_word (write_word byte_array byte_index value) i == (
                                                           if  byte_index = i then
                                                                  value 
                                                             else 
                                                                read_word byte_array i))) = 
write_word_replacement_lemma1 byte_array byte_index value;  
write_word_before_start_lemma1 byte_array byte_index value;
write_word_after_start_end_lemma1 byte_array byte_index value;
()


#restart-solver 

#restart-solver 

let field_member (g:heap{well_formed_heap2 g})
                 (x:hp_addr{is_valid_header x g})
                 (i:hp_addr) = Usize.v i >= Usize.v x + Usize.v mword /\
                                                      Usize.v i <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword)

#restart-solver

let objects_fields_lemma (g:heap{well_formed_heap2 g})
                         (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                         (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                         (p:hp_addr{is_valid_header p g /\ p <> x})
                         (j:hp_addr{Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword)})
                        
                  : Lemma
                    (ensures (Usize.v j <> Usize.v i)) = 
if (Usize.v p > Usize.v x) then
(
  assert (Usize.v p > Usize.v x);
  assert (Usize.v j > Usize.v x);
  assert (Usize.v j > Usize.v i);
  assert (Usize.v j <> Usize.v i);
  ()
)
else
(
  assert (Usize.v p < Usize.v x);
  assert (Usize.v j <> Usize.v x);
  assert (Usize.v j <> Usize.v i);
  ()
)


let objects_fields_lemma1 (g:heap{well_formed_heap2 g})
                          (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                          (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                          (j:Usize.t{Usize.v j > 1 /\
                                     Usize.v j <= (Usize.v (getWosize (read_word g x)))}) 
                   : Lemma
                    (ensures (Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v i)) = ()

let objects_fields_lemma_all (g:heap{well_formed_heap2 g})
                             (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                             (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                             (p:hp_addr{is_valid_header p g /\ p <> x})
                   : Lemma
                     (ensures (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i)) = 
 Classical.forall_intro (objects_fields_lemma g x i p)

let objects_fields_lemma1_all1 (g:heap{well_formed_heap2 g})
                               (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                               (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                    : Lemma
                      (ensures (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}).Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v i)) = 
 Classical.forall_intro (objects_fields_lemma1 g x i);
 ()

let objects_fields_lemma_all1 (g:heap{well_formed_heap2 g})
                              (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                              (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                            
                   : Lemma
                     (ensures (forall p. is_valid_header p g /\ p <> x ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i))) = 
Classical.forall_intro (objects_fields_lemma_all g x i)  

let objects_color_equivalence_lemma (g:heap{well_formed_heap2 g})
                                    (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                                    (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                                    (p:hp_addr{is_valid_header p g /\  color_of_object1 p g <> blue})
                     : Lemma
                       (ensures p <> x) = () 
 
let objects_color_equivalence_lemma_all (g:heap{well_formed_heap2 g})
                                        (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                                        (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                      : Lemma
                       (ensures (forall p. is_valid_header p g /\  color_of_object1 p g <> blue ==> p <> x)) = 
Classical.forall_intro (objects_color_equivalence_lemma g x i) 

let objects_fields_lemma_all1_app (g:heap{well_formed_heap2 g})
                                  (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                                  (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                     : Lemma
                     (ensures (forall p. is_valid_header p g /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i))) = 
objects_color_equivalence_lemma_all g x i;
objects_fields_lemma_all1 g x i ;
()   

let objects_fields_lemma_all1_app1 (g:heap{well_formed_heap2 g})
                                  (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                                  (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword}) 
                     : Lemma
                     (ensures (forall p. is_valid_header p g /\  p <> x ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i))) = 
objects_fields_lemma_all1 g x i ;
()   

#restart-solver

#restart-solver 

#restart-solver

let h_index_field_index_mword_multiple_lemma5 (g:heap{well_formed_heap2 g})
                                              (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                              (wz: wosize{((wz == getWosize (read_word g h_index)) /\ 
                                                             is_fields_within_limit1 h_index wz) /\
                                                             is_fields_contents_within_limit2 h_index wz g})
                                              (i:Usize.t{ Usize.v i > 0 /\ Usize.v i <= Usize.v wz})
                                : Lemma
                                  (ensures (is_hp_addr (Usize.add h_index (Usize.mul  i mword)))) = 
 
max_wosize_times_mword_multiple_of_mword i;
sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0);
assert ((Usize.v h_index  + (Usize.v i  * Usize.v mword)) < heap_size);
assert (is_hp_addr (Usize.add h_index (Usize.mul  i mword)));
()

let h_index_field_index_all_mword_multiple_lemma5(g:heap{well_formed_heap2 g})
                                                 (h_index: hp_addr{Seq.mem h_index (objects2 0UL g)})
                                                   
                                : Lemma
                                 (ensures (forall (i:Usize.t{Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g h_index))}).
                                          is_hp_addr (Usize.add h_index (Usize.mul i mword)))) = 
Classical.forall_intro (Classical.move_requires (h_index_field_index_mword_multiple_lemma5 g h_index (getWosize (read_word g h_index))));
()

let objects_mem_h_index_field_index_all_mword_multiple5 (g:heap{well_formed_heap2 g})
                                                        
                                        : Lemma
                                          (ensures (forall x. Seq.mem x (objects2 0UL g) ==>
                                                        (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))}). 
                                                            is_hp_addr (Usize.add x (Usize.mul i mword))))) =
Classical.forall_intro (Classical.move_requires (h_index_field_index_all_mword_multiple_lemma5 g));
()

#restart-solver 

#restart-solver 

let write_word_to_blue_object_field_lemma (g:heap{well_formed_heap2 g})
                                          (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                                          (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword (*/\ (isPointer i g ==>  Seq.mem (read_word g i) (objects2 0UL g))*)})
                                           
                                          (v:hp_addr{is_valid_header v g})
                          :Lemma 
                          (ensures (objects2 0UL g == objects2 0UL (write_word g i v)) /\ 
                                   (forall p. Seq.mem p (objects2 0UL g) ==> read_word (write_word g i v) p ==  read_word g p) /\
                                   (forall p. Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g i v) j == read_word g j)) /\
                                   (forall p. is_valid_header p g /\ p <> x ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g i v) j == read_word g j)) /\
                                    (forall (j:hp_addr). Usize.v j > Usize.v x + Usize.v mword /\
                                     Usize.v j < Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                      read_word (write_word g i v) j == read_word g j) /\
                                    (Usize.v (read_word (write_word g i v) i) >= 0 /\ Usize.v (read_word (write_word g i v) i) < heap_size) /\
                                    (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}). is_hp_addr (Usize.add x (Usize.mul j mword))) /\
                                    (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}).
                                                     Usize.v (read_word g (Usize.add x (Usize.mul j mword))) == 
                                                     Usize.v (read_word (write_word g i v) (Usize.add x (Usize.mul j mword))))
                                    ) = 
  let g' = write_word g i v in
  write_word_lemma1 g i v;
  assert (forall (p:hp_addr). read_word (write_word g i v) p == (
                                                           if i = p then
                                                               v 
                                                             else 
                                                               read_word g p));
  
  assert (is_valid_header x g);
  assert (Seq.mem x (objects2 0UL g));
  assert (forall p. Seq.mem p (objects2 0UL g) ==> Usize.v (getWosize (read_word g p)) > 0);
  assert (Usize.v (getWosize (read_word g x)) > 0);
  assert (Usize.v (getWosize (read_word g x)) >= 1);
  fields_not_mem_objs_lemma g g' x i;
  assert (~(Seq.mem i (objects2 0UL g)));
  assert (forall p. Seq.mem p (objects2 0UL g) ==> read_word g' p ==  read_word g p);
  assert (forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g' p) ==  getWosize (read_word g p));
  objects2_equal_lemma1_app g g';
  assert (objects2 0UL g == objects2 0UL g');
  assert (Seq.length (objects2 0UL g) > 0);
  assert (Seq.length (objects2 0UL g') > 0);
  assert (forall (p:hp_addr). p<> i ==> read_word g' p == read_word g p);
  objects_fields_lemma_all1_app g x i;
  assert (forall p. is_valid_header p g /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i));
  
  assert (forall p. is_valid_header p g /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word g' j == read_word g j));
  assert (forall p. Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word g' j == read_word g j));
  objects_fields_lemma_all1_app1 g x i;
  assert (forall p. is_valid_header p g /\  p <> x ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> Usize.v j <> Usize.v i));
  
  assert (forall p. is_valid_header p g /\ p <> x ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word g' j == read_word g j));
  assert (forall (j:hp_addr). Usize.v j > Usize.v x + Usize.v mword /\
                                     Usize.v j < Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                      read_word g' j == read_word g j);
  
  assert (Usize.v v >= 0 /\ Usize.v v < heap_size);
  assert (Usize.v v % Usize.v mword == 0);
  assert (read_word g' i == v);
  assert (Usize.v (read_word g' i) >= 0 /\ Usize.v (read_word g' i) < heap_size);
  objects_fields_lemma1_all1 g x i;
  assert (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}).Usize.v (Usize.add x (Usize.mul j mword)) <> Usize.v i);
  h_index_field_index_all_mword_multiple_lemma5 g x;
  assert (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}).
                                                     Usize.v (read_word g (Usize.add x (Usize.mul j mword))) == 
                                                     Usize.v (read_word g' (Usize.add x (Usize.mul j mword))));
  ()


let fields_points_to_blocks2_objects_lemma (g:heap{well_formed_heap2 g})
                                            : Lemma
                                              (ensures (forall x. Seq.mem x (objects2 0UL g) ==> is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (objects2 0UL g))) = 
 assert (well_formed_heap2 g);
 let objs = objects2 0UL g in
 assert (check_fields_points_to_blocks2 g objs);
 assert (forall x. Seq.mem x objs ==>  is_fields_points_to_blocks2 x g (getWosize (read_word g x)) objs);
 ()


#restart-solver 

val check_all_block_fields_within_limit2_lemma3 :   (g:heap) ->
                                                    (g':heap) ->
                                                    (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                 (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                                 (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g))})->
                                                    (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f'' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g'))})->
                                                    (x:hp_addr{Seq.mem x (objects2 0UL g) /\ color_of_object1 x g == blue})->
                                                          
                                                    (k:hp_addr{Usize.v k == Usize.v x + Usize.v mword})->
                                  Lemma
                                  (requires (f' == f'')  /\
                                            (objects2 0UL g ==
                                             objects2 0UL g') /\
                                            (*(forall p. Seq.mem p (objects2 0UL g) ==> getWosize (read_word g p) ==
                                                                                  getWosize (read_word g' p))*) 
                                            (forall p. Seq.mem p (objects2 0UL g) ==> read_word g p ==
                                                                                  read_word g' p) /\                                     
                                            (forall p. Seq.mem p (objects2 0UL g) ==> is_fields_within_limit1 p  (getWosize (read_word g p))) /\
                                            (forall p. Seq.mem p (objects2 0UL g) ==> 
                                                      (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))}). 
                                                            is_hp_addr (Usize.add x (Usize.mul i mword)))) /\
                                            (forall p. Seq.mem p (objects2 0UL g) /\ p <> x ==> 
                                                   (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                                       Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word g' j == read_word g j)) /\
                                            (*(forall p y. Seq.mem p f' /\  p <> x /\ Usize.v y >= Usize.v p + Usize.v mword /\
                                                      Usize.v y <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==>
                                                             read_word g y == read_word g' y) /\*)
                                            
                                            (forall (i:Usize.t {Usize.v i > 1 /\ Usize.v i <= Usize.v (getWosize (read_word g x))}).
                                                     Usize.v (read_word g (Usize.add x (Usize.mul i mword))) == 
                                                     Usize.v (read_word g' (Usize.add x (Usize.mul i mword)))) /\
                                             (*(Usize.v (read_word g' k) >= 0 /\
                                               Usize.v (read_word g' k) < heap_size) /\
                                             (Usize.v (read_word g k) >= 0 /\
                                               Usize.v (read_word g k) < heap_size)*)
                                              (isPointer k g ==> (Usize.v (read_word g k) >= 0 /\ Usize.v (read_word g k) < heap_size)) /\
                                              (isPointer k g' ==> (Usize.v (read_word g' k) >= 0 /\ Usize.v (read_word g' k) < heap_size)))
                                  
                                  (ensures check_all_block_fields_within_limit2 g f' == true <==>
                                           check_all_block_fields_within_limit2 g' f'' == true)
                                   (decreases length f')
                                   
val check_fields_points_to_blocks2_lemma1 : (g:heap)->
                                            (g':heap)->
                                            (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g)) /\
                                                           check_all_block_fields_within_limit2 g f'}) ->
                                          
                                                           
                                            (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                            (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g')) /\
                                                            check_all_block_fields_within_limit2 g' f''}) ->
                                              (x: hp_addr{Seq.mem x (objects2 0UL g)})->
                                              (k:hp_addr{Usize.v k == Usize.v x + Usize.v mword})->
                                        Lemma
                                          (requires (f' == f'')  /\ (objects2 0UL g == objects2 0UL g') /\
                                                     (forall p. Seq.mem p (objects2 0UL g) ==> read_word g p ==
                                                                                  read_word g' p) /\ 
                                                     (forall p. Seq.mem p f'/\ p <> x ==> 
                                                        (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                                       Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word g' j == read_word g j)) /\
                                                     
                                                     (forall (j:hp_addr). Usize.v j  > Usize.v x + Usize.v mword /\
                                                        Usize.v j <= Usize.v x + (Usize.v (getWosize (read_word g' x)) * Usize.v mword) ==> read_word g j == read_word g' j) /\
                                                     (isPointer k g  ==> Seq.mem (read_word g k) (objects2 0UL g)) /\
                                                     (isPointer k g' ==> Seq.mem (read_word g' k) (objects2 0UL g'))
                                                     
                                               )      
                                          (ensures check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true)
                                          (decreases length f')         

#restart-solver

let hp_addr_is_isPointer  (g:heap)
                          (v:hp_addr)
                          (i:hp_addr{read_word g i == v})
               : Lemma
                 (ensures (isPointer i g)) = 
assert (is_hp_addr v);
assert (Usize.v v % Usize.v mword == 0);
UInt.logand_le #64 (Usize.v v) 1;
assert (Usize.logand v 1UL == 0UL);
()

#restart-solver

#restart-solver

let write_word_to_blue_object_field_lemma1 (g:heap{well_formed_heap2 g})
                                           (x:hp_addr{is_valid_header x g /\ color_of_object1 x g == blue})
                                           (i:hp_addr{Usize.v i == Usize.v x + Usize.v mword (*/\ (isPointer i g ==>  Seq.mem (read_word g i) (objects2 0UL g))*)})
                                           
                                           (v:hp_addr{is_valid_header v g})
                          :Lemma 
                           (ensures well_formed_heap2 (write_word g i v)) = 
 assert (is_valid_header x g);
 assert (check_fields_points_to_blocks2 g (objects2 0UL g));
 assert (isPointer i g ==>  Seq.mem (read_word g i) (objects2 0UL g));
 let g' = write_word g i v in
 write_word_lemma1 g i v;
 write_word_to_blue_object_field_lemma g x i v;
 assert ((objects2 0UL g == objects2 0UL (write_word g i v)) /\ 
                                   (forall p. Seq.mem p (objects2 0UL g) ==> read_word (write_word g i v) p ==  read_word g p) /\
                                   (forall p. Seq.mem p (objects2 0UL g) /\ color_of_object1 p g <> blue ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g i v) j == read_word g j)) /\
                                   (forall p. is_valid_header p g /\ p <> x ==> (forall (j:hp_addr). Usize.v j >= Usize.v p + Usize.v mword /\
                                    Usize.v j <= Usize.v p + (Usize.v (getWosize (read_word g p)) * Usize.v mword) ==> read_word (write_word g i v) j == read_word g j)) /\
                                    (forall (j:hp_addr). Usize.v j > Usize.v x + Usize.v mword /\
                                     Usize.v j < Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                      read_word (write_word g i v) j == read_word g j) /\
                                    Usize.v (read_word (write_word g i v) i) >= 0 /\ Usize.v (read_word (write_word g i v) i) < heap_size);
 
 
 assert (read_word g' i == v);
 hp_addr_is_isPointer g' v i;
 assert (isPointer i g');
 assert (Seq.mem (read_word g' i) (objects2 0UL g'));
 assert (isPointer i g' ==> Seq.mem (read_word g' i) (objects2 0UL g'));
 assert (Seq.length (objects2 0UL g) > 0);
 assert (Seq.length (objects2 0UL g') > 0);
 assert (check_all_block_fields_within_limit2 g (objects2 0UL g));
 assert (check_fields_points_to_blocks2 g (objects2 0UL g));  
 field_limits_objects2_lemma g;
 field_contents_within_limits_objects2_lemma  g;
 fields_points_to_blocks2_objects_lemma  g;
 assert (is_fields_within_limit1 x (getWosize (read_word g x)));
 assert (is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
 assert (is_fields_points_to_blocks2 x g (getWosize (read_word g x)) (objects2 0UL g));
 assert (forall i. (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) /\ 
                                                     (is_hp_addr ((Usize.add x (Usize.mul i mword)))) /\
                                                     isPointer (Usize.add x (Usize.mul i mword)) g  ==>
                                                     Seq.mem (read_word g (Usize.add x (Usize.mul i mword))) (objects2 0UL g));
 //assert (Seq.mem (read_word g i) (objects2 0UL g));
 objects_mem_h_index_field_index_all_mword_multiple5 g;
 (*assert (Usize.v (read_word g i) >= 0 /\  Usize.v (read_word g i) < heap_size);*)
                                              
 assert (forall (j:Usize.t {Usize.v j > 1 /\ Usize.v j <= Usize.v (getWosize (read_word g x))}).
                                                     Usize.v (read_word g (Usize.add x (Usize.mul j mword))) == 
                                                     Usize.v (read_word g' (Usize.add x (Usize.mul j mword))));
 assert (isPointer i g ==> (Usize.v (read_word g i) >= 0 /\ Usize.v (read_word g i) < heap_size));
 assert (isPointer i g' ==> (Usize.v (read_word g' i) >= 0 /\ Usize.v (read_word g' i) < heap_size));
 check_all_block_fields_within_limit2_lemma3 g g' (objects2 0UL g) (objects2 0UL g') x i;
 assert (check_all_block_fields_within_limit2 g' (objects2 0UL g'));
 check_fields_points_to_blocks2_lemma1 g g' (objects2 0UL g) (objects2 0UL g') x i;
 assert (check_fields_points_to_blocks2 g' (objects2 0UL g'));
 
 assert (well_formed_heap2 g');
 ()


(* (isPointer k g ==> (Usize.v (read_word g k) >= 0 /\ Usize.v (read_word g k) < heap_size)) /\
   (isPointer k g' ==> (Usize.v (read_word g' k) >= 0 /\ Usize.v (read_word g' k) < heap_size))*)



(* F*                                            Low*
   sweep with freelist                     <---> sweep with free list       
   mark and sweep GC with freelist change  <---> mark and sweep GC with free list change
   
   (1)all non-blue objects and their pointers remain unchanged between sweep and sweep with free list
   Therefore all non-blue objects and their pointers between mark and sweep GC without freelist and with free list remains the same.
   Only non-blue objects are white objects and therefore the sub-graph of reachable objects remain the same between the two versions.*)

(*sweep_body_with_free_list*)

let heap_heap_addr_pair = heap & hp_addr

#restart-solver 

#restart-solver

(*let objects2_mem_lemma1_app (h_index: hp_addr)
                            (g:heap)
                           
                      
          : Lemma 
            (requires (Seq.length (objects2 0UL g) > 0 /\ Seq.mem h_index (objects2 0UL g) /\ 
                        Usize.v (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) < heap_size))
            (ensures (Seq.mem (Usize.add h_index (Usize.mul (Usize.add (getWosize (read_word g h_index)) 1UL) mword)) (objects2 0UL g))) *)

#restart-solver 

let sweep_body_with_free_list (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                              (h_index:hp_addr{is_valid_header h_index g})
                              (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue (*/\
                                          (isPointer (Usize.add fp mword) g ==>  Seq.mem (read_word g (Usize.add fp mword)) (objects2 0UL g))*)})
            : Tot (p:heap_heap_addr_pair{well_formed_heap2 (fst p) /\ (objects2 0UL g == objects2 0UL (fst p))})
                             = 
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white) then 
 (
   let g' = colorHeader1 h_index g blue in
   colorHeader1_wosizeLemma h_index g blue h_index;
   assert (objects2 h_index g == objects2 h_index g');
   Seq.lemma_eq_intro g' (sweep_body_helper g h_index);
   assert (well_formed_heap2 g');
   let first_field_fp = Usize.add fp mword in
  
   assert (Usize.v first_field_fp < heap_size);
   assert (Usize.v fp % Usize.v mword == 0);
   assert (Usize.v first_field_fp % Usize.v mword == 0);
   let g1 = write_word g' first_field_fp h_index in
   write_word_to_blue_object_field_lemma1 g' fp first_field_fp h_index;
   write_word_to_blue_object_field_lemma g' fp first_field_fp h_index;
   assert (well_formed_heap2 g1);
   assert (Seq.length (objects2 0UL g') > 0);
   //assume (objects2 h_index g1 == objects2 h_index g');
   (g1,h_index)
 )
 else
 (
   if (c = black) then 
   (
      let g' = colorHeader1 h_index g white in
      colorHeader1_wosizeLemma h_index g white h_index;
      assert (objects2 h_index g == objects2 h_index g');
      Seq.lemma_eq_intro g' (sweep_body_helper g h_index);
      assert (well_formed_heap2 g');
      assert (objects2 h_index g == objects2 h_index g');
      (g',fp)
   )
   else
   (
     assert (c == blue);
     objects2_equal_lemma h_index g g;
     assert (objects2 h_index g == objects2 h_index g);
     Seq.lemma_eq_intro g (sweep_body_helper g h_index);
     assert (well_formed_heap2 g);
     assert (objects2 h_index g == objects2 h_index g);
     (g,fp)
   )
 )

#restart-solver

#restart-solver 

let sweep_body_with_free_list_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                    (h_index:hp_addr{is_valid_header h_index g})
                                    (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue (*/\
                                          (isPointer (Usize.add fp mword) g ==>  Seq.mem (read_word g (Usize.add fp mword)) (objects2 0UL g))*)})
            :Lemma (ensures (noGreyObjects (fst (sweep_body_with_free_list g h_index fp)))) =
                             
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white) then 
 (
   let g' = colorHeader1 h_index g blue in
   colorHeader1_wosizeLemma h_index g blue h_index;
   assert (objects2 h_index g == objects2 h_index g');
   Seq.lemma_eq_intro g' (sweep_body_helper g h_index);
   assert (well_formed_heap2 g');
   assert (noGreyObjects g');
   let first_field_fp = Usize.add fp mword in
  
   assert (Usize.v first_field_fp < heap_size);
   assert (Usize.v fp % Usize.v mword == 0);
   assert (Usize.v first_field_fp % Usize.v mword == 0);
   let g1 = write_word g' first_field_fp h_index in
   write_word_to_blue_object_field_lemma1 g' fp first_field_fp h_index;
   write_word_to_blue_object_field_lemma g' fp first_field_fp h_index;
   assert (well_formed_heap2 g1);
   assert (noGreyObjects g1);
   ()
 )
 else
 (
   if (c = black) then 
   (
      let g' = colorHeader1 h_index g white in
      colorHeader1_wosizeLemma h_index g white h_index;
      assert (objects2 h_index g == objects2 h_index g');
      Seq.lemma_eq_intro g' (sweep_body_helper g h_index);
      assert (well_formed_heap2 g');
      assert (noGreyObjects g');
      ()
   )
   else
   (
     assert (c == blue);
     objects2_equal_lemma h_index g g;
     assert (objects2 h_index g == objects2 h_index g);
     Seq.lemma_eq_intro g (sweep_body_helper g h_index);
     assert (well_formed_heap2 g);
     assert (noGreyObjects g);
     ()
   )
 )

#restart-solver 

let sweep_body_with_free_list_lemma1 (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                    (h_index:hp_addr{is_valid_header h_index g})
                                    (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue (*/\
                                          (isPointer (Usize.add fp mword) g ==>  Seq.mem (read_word g (Usize.add fp mword)) (objects2 0UL g))*)})
            :Lemma (ensures (is_valid_header (snd (sweep_body_with_free_list g h_index fp)) (fst (sweep_body_with_free_list g h_index fp)))) =
                             
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white) then 
 (
   let g' = colorHeader1 h_index g blue in
   colorHeader1_wosizeLemma h_index g blue h_index;
   assert (objects2 h_index g == objects2 h_index g');
   Seq.lemma_eq_intro g' (sweep_body_helper g h_index);
   assert (well_formed_heap2 g');
   assert (noGreyObjects g');
   let first_field_fp = Usize.add fp mword in
  
   assert (Usize.v first_field_fp < heap_size);
   assert (Usize.v fp % Usize.v mword == 0);
   assert (Usize.v first_field_fp % Usize.v mword == 0);
   let g1 = write_word g' first_field_fp h_index in
   write_word_to_blue_object_field_lemma1 g' fp first_field_fp h_index;
   write_word_to_blue_object_field_lemma g' fp first_field_fp h_index;
   assert (well_formed_heap2 g1);
   assert (objects2 0UL g == objects2 0UL g');
   assert (objects2 0UL g' == objects2 0UL g1);
   assert (is_valid_header h_index g);
   assert (is_valid_header h_index g');
   assert (is_valid_header h_index g1);
   ()
 )
 else
 (
   if (c = black) then 
   (
      let g' = colorHeader1 h_index g white in
      colorHeader1_wosizeLemma h_index g white h_index;
      assert (objects2 h_index g == objects2 h_index g');
      Seq.lemma_eq_intro g' (sweep_body_helper g h_index);
      assert (well_formed_heap2 g');
      assert (is_valid_header fp g');
      ()
   )
   else
   (
     assert (c == blue);
     objects2_equal_lemma h_index g g;
     assert (objects2 h_index g == objects2 h_index g);
     Seq.lemma_eq_intro g (sweep_body_helper g h_index);
     assert (well_formed_heap2 g);
     assert (is_valid_header fp g);
     ()
   )
 )

#restart-solver 

let sweep_body_with_free_list_lemma2 (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                    (h_index:hp_addr{is_valid_header h_index g})
                                    (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue (*/\
                                          (isPointer (Usize.add fp mword) g ==>  Seq.mem (read_word g (Usize.add fp mword)) (objects2 0UL g))*)})
            :Lemma (ensures (color_of_object1 (snd (sweep_body_with_free_list g h_index fp)) (fst (sweep_body_with_free_list g h_index fp)) == blue)) =
                             
 let c = getColor (read_word g h_index) in
 assert (~(c == gray));
 if (c = white) then 
 (
   let g' = colorHeader1 h_index g blue in
   colorHeader1_wosizeLemma h_index g blue h_index;
   assert (objects2 h_index g == objects2 h_index g');
   Seq.lemma_eq_intro g' (sweep_body_helper g h_index);
   assert (well_formed_heap2 g');
   assert (noGreyObjects g');
   let first_field_fp = Usize.add fp mword in
  
   assert (Usize.v first_field_fp < heap_size);
   assert (Usize.v fp % Usize.v mword == 0);
   assert (Usize.v first_field_fp % Usize.v mword == 0);
   let g1 = write_word g' first_field_fp h_index in
   write_word_to_blue_object_field_lemma1 g' fp first_field_fp h_index;
   write_word_to_blue_object_field_lemma g' fp first_field_fp h_index;
   assert (well_formed_heap2 g1);
   assert (objects2 0UL g == objects2 0UL g');
   assert (objects2 0UL g' == objects2 0UL g1);
   assert (is_valid_header h_index g);
   assert (is_valid_header h_index g');
   assert (is_valid_header h_index g1);
   assert (color_of_object1 h_index g' == blue);
   assert (color_of_object1 h_index g1 == blue); 
   ()
 )
 else
 (
   if (c = black) then 
   (
      let g' = colorHeader1 h_index g white in
      colorHeader1_wosizeLemma h_index g white h_index;
      assert (objects2 h_index g == objects2 h_index g');
      Seq.lemma_eq_intro g' (sweep_body_helper g h_index);
      assert (well_formed_heap2 g');
      assert (color_of_object1 fp g' == blue);
      ()
   )
   else
   (
     assert (c == blue);
     objects2_equal_lemma h_index g g;
     assert (objects2 h_index g == objects2 h_index g);
     Seq.lemma_eq_intro g (sweep_body_helper g h_index);
     assert (well_formed_heap2 g);
     assert (color_of_object1 fp g == blue);
     ()
   )
 )

#restart-solver 

#restart-solver

let rec sweep_with_free_list (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                             (h_index:hp_addr{is_valid_header h_index g (*/\ (Seq.length (objects2 h_index g) > 0)*)})
                             (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue})
          : Tot (p:heap_heap_addr_pair{well_formed_heap2 (fst p) /\ noGreyObjects (fst p) /\
                                       is_valid_header (snd p) (fst p) /\ color_of_object1 (snd p) (fst p) == blue})
            (decreases (heap_size - Usize.v h_index)) = 
 let wz =  getWosize (read_word g h_index) in
 let h_index_new =  Usize.add h_index (Usize.mul (Usize.add wz 1UL) mword) in
 let g', fp' = sweep_body_with_free_list g h_index fp in
 assert (well_formed_heap2 g');
 sweep_body_with_free_list_lemma g h_index fp;
 sweep_body_with_free_list_lemma1 g h_index fp;
 sweep_body_with_free_list_lemma2 g h_index fp;
 assert (noGreyObjects g');
 assert (is_valid_header fp' g');
 assert (color_of_object1 fp' g' == blue);
 assert (well_formed_heap2 g');
 assert (objects2 0UL g == objects2 0UL g');
 if Usize.v h_index_new >= heap_size then
 (
   (g',fp')
 )
 else
 (
      wosize_plus_times_mword_multiple_of_mword1 wz;
      sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul (Usize.add wz 1UL) mword);
      assert (Usize.v h_index_new % Usize.v mword == 0);
      assert (is_hp_addr h_index_new);

      assert (Seq.length (objects2 0UL g') > 0);
      assert (Seq.mem h_index (objects2 0UL g')); 
      assert (Usize.v (h_index_new) < heap_size);
      objects2_mem_lemma1_app h_index g;
      
      assert (is_valid_header h_index_new g);
      assert (is_valid_header h_index_new g');
     
      assert (Seq.mem h_index (objects2 0UL g));
      assert (Seq.length (objects2 0UL g) > 0);
      let g'',fp'' = sweep_with_free_list g' h_index_new fp' in
      assert (well_formed_heap2 g'');
      (g'',fp'')
 )


let rec mark5_allocated_blocks_lemma (g:heap{well_formed_heap2 g}) 
                                    (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st)
                                    })
                      : Lemma
                        (requires (well_formed_heap2 (mark5 g st)))
                        (ensures (get_allocated_block_addresses g == get_allocated_block_addresses (mark5 g st)))
                         (decreases %[G.cardinal1(get_allocated_block_addresses g) - 
                         G.cardinal1 (get_black_block_addresses g (get_allocated_block_addresses g));
                         Seq.length st]) = 
if (G.is_emptySet st) then
   (
      ()
   )
 else
   (
      let st', g' = mark5_body g st in
      assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
      let v_id = Seq.index st (Seq.length st - 1) in
      assert (Usize.v v_id < heap_size /\ Usize.v v_id % Usize.v mword == 0);
      assert (is_valid_header v_id g);

      stack_slice_only_has_gray_color_lemma g st v_id 3UL;

      assert (forall x. Seq.mem x (objects2 0UL (colorHeader1 (Seq.index st (Seq.length st - 1)) g black)) /\ 
                                   isGrayObject1 x (colorHeader1 (Seq.index st (Seq.length st - 1)) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1)));
      
      
      mark5_body_black_nodes_lemma g st;
      
      assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st)))));
      assert (well_formed_heap2 g');
      
      let g'' = mark5 g' st' in
      well_formed_heap2_after_mark5 g' st';
      assert (well_formed_heap2 g'');
      mark5_allocated_blocks_lemma g' st';
      ()
    )

#restart-solver 

let rec create_root_stack_and_gray_modified_heap_allocs_lemma (g:heap{well_formed_heap2 g}) 
                                                 (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x st ==> is_valid_header x g) /\
                                                               (G.is_vertex_set st) /\
                                                               (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                                  Seq.mem x st)})
                                                 (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                      (G.is_vertex_set h_list) /\
                                                                      (G.subset_vertices h_list (get_allocated_block_addresses g)) /\
                                                                      (forall x. Seq.mem x h_list ==> color_of_object1 x g == white)})          
                                                  
      :  Lemma
         (requires mutually_exclusive_sets st h_list)
          (ensures (get_allocated_block_addresses g == get_allocated_block_addresses (snd (create_root_stack_and_gray_modified_heap g st h_list))))
         (decreases (Seq.length h_list)) =
  if Seq.length h_list = 0 then 
  (
     ()
  )
  else
  (
     let hd = Seq.head h_list in
     let tl = Seq.tail h_list in
     
     assert (G.is_vertex_set st);
     assert (G.is_vertex_set h_list);

     assert (~(Seq.mem hd st));
     G.is_vertex_set_lemma h_list;
     assert (G.is_vertex_set tl);
     assert (mutually_exclusive_sets st tl);

     G.is_vertex_set_lemma4 h_list;
     assert (~(Seq.mem hd tl));
     assert (~(Seq.mem hd st));
     let st', g' = push_to_stack2 g st hd in
     assert (mutually_exclusive_sets st' tl);
     assert (color_of_object1 hd g == white);
     push_to_stack2_lemma g st hd;
     assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
     create_root_stack_and_gray_modified_heap_allocs_lemma g' st' tl;
     () 
  )

#restart-solver

let sweep_with_free_list_lemma (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                   (h_index:hp_addr{is_valid_header h_index g })
                                   (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue})
                                   (h_index_new:hp_addr{h_index_new == Usize.add h_index (Usize.mul (Usize.add ( getWosize (read_word g h_index)) 1UL) mword)})
                    : Lemma
                      (requires  (Usize.v h_index_new >= heap_size))
                      (ensures (snd (sweep_with_free_list g h_index fp) == snd (sweep_body_with_free_list g h_index fp)) /\
                               (fst (sweep_with_free_list g h_index fp) == fst (sweep_body_with_free_list g h_index fp))) = ()

#restart-solver 

#restart-solver 

let mark_and_sweep_GC1_output_equivalence_lemma1 (g:heap{well_formed_heap2 g /\ 
                                                        well_formed_allocated_blocks g /\  
                                                        noGreyObjects g /\ 
                                                        only_white_and_blue_blocks g /\
                                                        noBlackObjects g})
                                                (*root pointers---------------------------------------------------------------------------------------------------*)
                                                (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                     (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                                                     (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                                                     (G.is_vertex_set h_list) /\
                                                                     (G.subset_vertices h_list (get_allocated_block_addresses g))}) 
                                                
                                                (st: seq Usize.t{st == Seq.empty #Usize.t /\ G.is_vertex_set st})
                                                (g1:heap{
                                                         (g1 == snd (create_root_stack_and_gray_modified_heap g st h_list))})
                                                (st': seq Usize.t { 
                                                                    (st' == fst (create_root_stack_and_gray_modified_heap g st h_list)) /\
                                                                    (forall x. Seq.mem x st' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                    (forall x. Seq.mem x st' ==> is_valid_header x g1) /\
                                                                    (forall x. Seq.mem x st' ==> Usize.v x % Usize.v mword == 0) /\
                                                                    (G.is_vertex_set st') /\
                                                                    (forall x. Seq.mem x (objects2 0UL g1) /\ isGrayObject1 x g1 <==>
                                                                       Seq.mem x st')
                                                                 })
                                                (g2:heap{g2 == mark5 g1 st'})
                                                (h_index:hp_addr{Usize.v h_index == 0})
                         :Lemma
                          (requires (well_formed_heap2 g2) /\ (noGreyObjects g2) /\ (is_valid_header h_index g2) /\ Seq.length (objects2 h_index g2) > 0)
                          (ensures mark_and_sweep_GC1 g h_list == sweep1 g2 h_index)= 
 let g3 = sweep1 g2 h_index in
 sweep1_heap_lemma g2;
 sweep1_heap_color_lemma g2;
 assert (g3 == sweep1 g2 0UL);
 (*assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 assert (noBlackObjects g3);
 assert (only_white_and_blue_blocks g3);*)
 assert (mark_and_sweep_GC1 g h_list == g3);
 ()


let sweep_with_free_list_lemma1 (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                   (h_index:hp_addr{is_valid_header h_index g })
                                   (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue})
                                   (h_index_new:hp_addr{h_index_new == Usize.add h_index (Usize.mul (Usize.add ( getWosize (read_word g h_index)) 1UL) mword)})
                    : Lemma
                      (requires  (Usize.v h_index_new < heap_size) /\ 
                                 well_formed_heap2 ((fst (sweep_body_with_free_list g h_index fp))) /\ 
                                 noGreyObjects (fst (sweep_body_with_free_list g h_index fp)) /\
                                 is_valid_header h_index_new (fst (sweep_body_with_free_list g h_index fp)) /\
                                 is_valid_header (snd (sweep_body_with_free_list g h_index fp)) (fst (sweep_body_with_free_list g h_index fp))  /\
                                 color_of_object1 (snd (sweep_body_with_free_list g h_index fp)) (fst (sweep_body_with_free_list g h_index fp)) == blue
                       )
                      (ensures (snd (sweep_with_free_list g h_index fp) == snd (sweep_with_free_list (fst (sweep_body_with_free_list g h_index fp))
                                                                                                 h_index_new
                                                                                                 (snd (sweep_body_with_free_list g h_index fp))))) = ()

                      
let sweep_with_free_list_lemma2 (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                   (h_index:hp_addr{is_valid_header h_index g })
                                   (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue})
                                   (h_index_new:hp_addr{h_index_new == Usize.add h_index (Usize.mul (Usize.add ( getWosize (read_word g h_index)) 1UL) mword)})
                    : Lemma
                      
                      (ensures(Usize.v h_index_new >= heap_size) ==>  ((snd (sweep_with_free_list g h_index fp) == snd (sweep_body_with_free_list g h_index fp)) /\
                               (fst (sweep_with_free_list g h_index fp) == fst (sweep_body_with_free_list g h_index fp)))) = ()

let sweep_with_free_list_lemma3 (g:heap{well_formed_heap2 g /\ noGreyObjects g})
                                   (h_index:hp_addr{is_valid_header h_index g })
                                   (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue})
                                   (h_index_new:hp_addr{h_index_new == Usize.add h_index (Usize.mul (Usize.add ( getWosize (read_word g h_index)) 1UL) mword)})
                    : Lemma
                      (requires   
                                 well_formed_heap2 ((fst (sweep_body_with_free_list g h_index fp))) /\ 
                                 noGreyObjects (fst (sweep_body_with_free_list g h_index fp)) /\
                                 is_valid_header h_index_new (fst (sweep_body_with_free_list g h_index fp)) /\
                                 is_valid_header (snd (sweep_body_with_free_list g h_index fp)) (fst (sweep_body_with_free_list g h_index fp))  /\
                                 color_of_object1 (snd (sweep_body_with_free_list g h_index fp)) (fst (sweep_body_with_free_list g h_index fp)) == blue
                       )
                      (ensures (Usize.v h_index_new < heap_size) ==> ((snd (sweep_with_free_list g h_index fp) == snd (sweep_with_free_list (fst (sweep_body_with_free_list g h_index fp))
                                                                                                 h_index_new
                                                                                                 (snd (sweep_body_with_free_list g h_index fp)))))) = ()


let test_helper_lemma (g:heap{well_formed_heap2 g})
                      (fp:hp_addr{is_valid_header fp g})
              : Lemma 
                (requires (~(Seq.mem fp (get_allocated_block_addresses g))))
                (ensures (color_of_object1 fp g == blue)) = 
objects2_color_lemma 0UL g;
assert (forall x. Seq.mem x (objects2 0UL g) ==> color_of_object1 x g == white \/ color_of_object1 x g == black \/ color_of_object1 x g == gray \/
                                                               color_of_object1 x g == blue);
assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> color_of_object1 x g == white \/ color_of_object1 x g == black \/ color_of_object1 x g == gray);
assert (color_of_object1 fp g <> white);
assert (color_of_object1 fp g <> black);
assert (color_of_object1 fp g <> gray);
assert (Seq.mem fp (objects2 0UL g));
assert (color_of_object1 fp g == blue);
()
                 
#restart-solver 

let test_helper_lemma1 (g:heap{well_formed_heap2 g})
                       (g1:heap{well_formed_heap2 g1})
                      (fp:hp_addr{is_valid_header fp g /\ is_valid_header fp g1}) 
              : Lemma
                (requires (get_allocated_block_addresses g == get_allocated_block_addresses g1) /\  (~(Seq.mem fp (get_allocated_block_addresses g))))
                (ensures  (~(Seq.mem fp (get_allocated_block_addresses g1)))) = ()

#restart-solver 

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

let test23_lemma (g:heap{well_formed_heap2 g})
                 (g1:heap{well_formed_heap2 g1})
                 (fp:hp_addr{is_valid_header fp g /\ is_valid_header fp g1  /\ color_of_object1 fp g == blue})
        : Lemma
          (requires (objects2 0UL g == objects2 0UL g1) /\
                    (get_allocated_block_addresses g == get_allocated_block_addresses g1))
          (ensures  (color_of_object1 fp g1 == blue)) = 
 assert (~(Seq.mem fp (get_allocated_block_addresses g)));
 test_helper_lemma1 g g1 fp;
 assert (~(Seq.mem fp (get_allocated_block_addresses g1)));
 test_helper_lemma g1 fp;
 assert (color_of_object1 fp g1 == blue);
 ()
 
#reset-options "--z3rlimit 1000"
#push-options "--split_queries"


let mark_and_sweep_GC3 (g:heap{well_formed_heap2 g /\ 
                                well_formed_allocated_blocks g /\  
                                noGreyObjects g /\ 
                                only_white_and_blue_blocks g /\
                                noBlackObjects g})
                        (*root pointers--------------------------------------------------------------------------------------------------------------------------*)
                        (h_list: seq Usize.t{(forall x. Seq.mem x h_list ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                           (forall x. Seq.mem x h_list ==> Usize.v x % Usize.v mword == 0) /\
                                           (forall x. Seq.mem x h_list ==> is_valid_header x g) /\
                                           (G.is_vertex_set h_list) /\
                                           (G.subset_vertices h_list (get_allocated_block_addresses g)) /\
                                           (forall x. Seq.mem x h_list ==> color_of_object1 x g == white)})
                        (fp:hp_addr{is_valid_header fp g /\ color_of_object1 fp g == blue})
                : Tot (p:heap_heap_addr_pair{well_formed_heap2 (fst p) /\ 
                               noGreyObjects (fst p) (*/\ 
                               only_white_and_blue_blocks g' /\
                               noBlackObjects g'*)}) = 
 
 (*Mark stack creation-----------------------------------------------------------------------------------------*)
 assert (~(Seq.mem fp (get_allocated_block_addresses g)));
 let st = Seq.empty #Usize.t in
 assert (forall x. Seq.mem x (objects2 0UL g) ==> ~(color_of_object1 x g == gray));
 assert (~(exists x.  Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g));
 assert (Seq.length st == 0);
 assert (forall x. Seq.mem x (objects2 0UL g) /\ isGrayObject1 x g <==>
                                                  Seq.mem x st);
 assert (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header x g);

 G.is_vertex_set_lemma1 st;
 assert (G.is_vertex_set st);

 (*Root graying-------------------------------------------------------------------------------------------------*)
 
 let st', g1 = create_root_stack_and_gray_modified_heap g st h_list in
 create_root_stack_and_gray_modified_heap_noBlackObjects_lemma g st h_list;
 assert (noBlackObjects g1);
 let allocs = get_allocated_block_addresses g1 in
 let vl = get_black_block_addresses g1 allocs in
 assert (Seq.length vl == 0);
 assert (Seq.length st == 0);
 create_root_stack_and_gray_modified_heap_mem_lemma g st h_list;
 assert ((forall x. Seq.mem x st ==> Seq.mem x st') /\
                (forall x. Seq.mem x h_list ==> Seq.mem x st'));
 assert (forall x. Seq.mem x st' ==> Seq.mem x st \/ Seq.mem x h_list);
 assert (forall x. Seq.mem x st' ==> Seq.mem x h_list);
 assert (forall x. Seq.mem x st' <==> Seq.mem x h_list);
 create_root_stack_and_gray_modified_heap_allocs_lemma g st h_list;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g1);
 test23_lemma g g1 fp;
 assert (color_of_object1 fp g1 == blue);
 (*marking------------------------------------------------------------------------------------------------------*)
 let g2 = mark5 g1 st' in
 well_formed_heap2_after_mark5 g1 st';
 no_grey_objects_after_mark5 g1 st';
 assert (Seq.length (objects2 0UL g2) > 0);
 assert (Seq.mem 0UL ((objects2 0UL g2)));
 assert (is_valid_header 0UL g2);
 mark5_objects2_lemma g1 st';
 assert (objects2 0UL g1 == objects2 0UL g2);
 assert (objects2 0UL g == objects2 0UL g2);
 assert (is_valid_header fp g2);
 mark5_allocated_blocks_lemma g1 st';
 assert (get_allocated_block_addresses g1 == get_allocated_block_addresses g2);
 test23_lemma g1 g2 fp;
 assert (color_of_object1 fp g2 == blue);
 (*sweeping---------------------------------------------------------------------------------------------------*)
 let g3,fp3 = sweep_with_free_list g2 0UL fp in
 
 assert (well_formed_heap2 g3);
 assert (noGreyObjects g3);
 (g3,fp3)


