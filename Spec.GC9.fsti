module Spec.GC9

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


(*No object size exceeds the heap limit*)
(*h_index + (wz + 1) * mword takes to the next header. Therefore, (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) will take us to the last index of the
   byte array which marks the end of the last field of the object. That should be less than heap size.*)
val is_fields_within_limit1  : (h_index: hp_addr) ->
                               (wz: wosize)->
              Tot (b:bool{b == true <==> (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size)})

val is_fields_contents_within_limit2 : (h_index: hp_addr) ->
                                       (wz: wosize{is_fields_within_limit1 h_index wz}) ->
                                       (g:heap) ->
                            Tot (b:bool{b == true <==> (forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}).isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                          (Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) >= Usize.v mword /\
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) < heap_size) /\
                                                          is_hp_addr (read_word g (Usize.add h_index (Usize.mul i mword))))})
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

/// Given the start address of an object, which is the address of the first field of the object, hd_address gets the header address of that object
let hd_address (st_index: hp_addr{UInt.fits (Usize.v st_index - Usize.v mword) Usize.n})
          : Tot (h:hp_addr{Usize.v h == Usize.v st_index - Usize.v mword}) = 
  let h_index = Usize.sub st_index mword in
  assert (Usize.v h_index % Usize.v mword == 0);
  assert (Usize.v h_index >= 0);
  assert (is_hp_addr h_index);
  h_index

#restart-solver 

/// Given the header address of an object, the f_address finds the address of the first field of the object
let f_address (h_index: hp_addr{UInt.fits (Usize.v h_index + Usize.v mword) Usize.n /\ (Usize.v h_index + Usize.v mword < heap_size)}) 
         : Tot (f:hp_addr{Usize.v f == Usize.v h_index + Usize.v mword})=
  let f_index = Usize.add h_index mword in
  assert (Usize.v f_index % Usize.v mword == 0);
  assert (Usize.v f_index >= 0);
  assert (is_hp_addr f_index);
  f_index

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
                                                              (forall x. Seq.mem x f' ==> Usize.v x % Usize.v mword == 0) /\
                                                               (forall x. Seq.mem x f' ==> 
                                                                 Seq.mem x (objects2 0UL g)) /\
                                                               (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g x)))})->
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
                                                                 (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g)) /\
                                                                  
                                                                 (forall x. Seq.mem x f' ==> is_fields_within_limit1 x (getWosize (read_word g x)))})->
                                                (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                  (forall x. Seq.mem x f'' ==> Usize.v x % Usize.v mword == 0) /\
                                                                  (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g')) /\
                                                                   
                                                                  (forall x. Seq.mem x f'' ==> is_fields_within_limit1 x (getWosize (read_word g x)))})->
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

#restart-solver

let test21  (h_index: hp_addr) 
            (g:heap)
            (wz: wosize{(is_fields_within_limit1 h_index wz /\
                         is_fields_contents_within_limit2 h_index wz g)})
            (f':seq Usize.t { (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                    (forall x. Seq.mem x f' ==> 
                                                     Seq.mem x (objects2 0UL g))}) 
            (j:Usize.t {(Usize.v j > 0 /\ Usize.v j <= Usize.v wz) /\ isPointer (Usize.add h_index (Usize.mul j mword)) g}) = 
 
 assert (is_fields_contents_within_limit2 h_index wz g);
 assert ((forall (i:Usize.t {Usize.v i > 0 /\ Usize.v i <= Usize.v wz}).isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) >= Usize.v mword /\
                                                          Usize.v (read_word g (Usize.add h_index (Usize.mul i mword))) < heap_size));
 
 
 assert (Usize.v (read_word g (Usize.add h_index (Usize.mul j mword))) >= Usize.v mword /\
         Usize.v (read_word g (Usize.add h_index (Usize.mul j mword))) < heap_size);

 let f_val = read_word g (Usize.add h_index (Usize.mul j mword)) in
 assert (UInt.fits (Usize.v f_val - Usize.v mword) Usize.n);
 assert (is_hp_addr f_val);
 let h_index' = hd_address (f_val) in
 admit()

#restart-solver 

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
                                                    
                                                     Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (objects2 0UL g))}) 

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


val check_fields_points_to_blocks2_lemma : (g:heap)->
                                              (g':heap) ->
                                              (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g))  /\
                                                           (forall x. Seq.mem x f' ==> 
                                                                   is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)(*/\
                                                           check_all_block_fields_within_limit2 g f'*)})->
                                          
                                                           
                                              (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                            (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g'))  /\
                                                           (forall x. Seq.mem x f'' ==> 
                                                                   is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g')(*/\
                                                            check_all_block_fields_within_limit2 g' f''*)})->
                                          
                                          Lemma
                                           (requires (f' == f'')  /\ (objects2 0UL g == objects2 0UL g') /\
                               
                                                     (forall (x:Usize.t{Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). 
                                                               getWosize (read_word g x) == getWosize (read_word g' x)) /\ 
                                                    (forall i x.  Seq.mem x f' /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                     (forall x y. Seq.mem x f' /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                                                            Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                              read_word g y == read_word g' y))
                                           
                                           (ensures check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true)
                                           (decreases length f')


#restart-solver 

#restart-solver

#restart-solver

let rec check_fields_points_to_blocks2_lemma1  (g:heap)
                                              (g':heap) 
                                              (f':seq Usize.t {(forall x. Seq.mem x f' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x f' ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x f' ==> Seq.mem x (objects2 0UL g))  /\
                                                           (forall x. Seq.mem x f' ==> 
                                                                   is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)(*/\
                                                           check_all_block_fields_within_limit2 g f'*)})
                                          
                                                           
                                              (f'':seq Usize.t {(forall x. Seq.mem x f'' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x f'' ==> is_hp_addr x) /\
                                                            (forall x. Seq.mem x f'' ==> Seq.mem x (objects2 0UL g'))  /\
                                                           (forall x. Seq.mem x f'' ==> 
                                                                   is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g')(*/\
                                                            check_all_block_fields_within_limit2 g' f''*)})
                                          
                                         : Lemma
                                           (requires (f' == f'')  /\ (objects2 0UL g == objects2 0UL g') /\
                               
                                                     (forall (x:Usize.t{Usize.v x < heap_size /\ (Usize.v x % Usize.v mword == 0)}). 
                                                               getWosize (read_word g x) == getWosize (read_word g' x)) /\ 
                                                    (forall i x.  Seq.mem x f' /\ (Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x))) ==> 
                                                    (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0) /\
                                                     (forall x y. Seq.mem x f' /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                                                            Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                              read_word g y == read_word g' y))
                                           
                                           (ensures check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true)
                                           (decreases length f') = 
 match length f' with
   | 0 -> ()
   | _ -> assert (length f' > 0);
         let hd = Seq.head f' in
         let hd' = Seq.head f'' in
         let tl = Seq.tail f' in
         let tl' = Seq.tail f'' in
         assert (hd == hd');
         assert (tl == tl');
         let wz = getWosize (read_word g hd) in
         let wz1 = getWosize (read_word g' hd) in
         assert (wz == wz1);
         assert (Seq.mem hd f');
         if Usize.v wz = 0 then
         (
           assert ((forall x. Seq.mem x tl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                           (forall x. Seq.mem x tl ==> is_hp_addr x) /\
                                                           (forall x. Seq.mem x tl ==> Seq.mem x (objects2 0UL g))  /\
                                                           (forall x. Seq.mem x tl ==> 
                                                                   is_fields_contents_within_limit2 x (getWosize (read_word g x)) g));
           assert ((forall x. Seq.mem x tl' ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                            (forall x. Seq.mem x tl' ==> is_hp_addr x) /\
                                                            (forall x. Seq.mem x tl' ==> Seq.mem x (objects2 0UL g')));
                                                         
           assert (forall x. Seq.mem x f'' ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');
           assert (forall x. Seq.mem x tl' ==> is_fields_contents_within_limit2 x (getWosize (read_word g' x)) g');  
           assert (forall x y. Seq.mem x tl /\ Usize.v y >= Usize.v x + Usize.v mword /\
                                                                            Usize.v y <= Usize.v x + (Usize.v (getWosize (read_word g x)) * Usize.v mword) ==>
                                                              read_word g y == read_word g' y);
           check_fields_points_to_blocks2_lemma1 g g' tl tl'
         )
         else
          (
            assert (Usize.v wz > 0);
            assert (is_fields_contents_within_limit2 hd (getWosize (read_word g hd)) g);
            is_fields_points_to_blocks2_lemma hd g wz (objects2 0UL g) g' wz1 (objects2 0UL g');
            assert (is_fields_points_to_blocks2 hd g wz (objects2 0UL g) == true <==>
                                            is_fields_points_to_blocks2 hd g' wz1 (objects2 0UL g') == true);
            if (is_fields_points_to_blocks2 hd g wz (objects2 0UL g)) then
             (
              assert (is_fields_points_to_blocks2 hd g wz (objects2 0UL g));
              assert (is_fields_points_to_blocks2 hd g' wz1 (objects2 0UL g'));
              let _ = check_fields_points_to_blocks2_lemma1 g g' tl tl' in
              assert(check_fields_points_to_blocks2 g tl == true <==> check_fields_points_to_blocks2 g' tl' == true);
              
              assert (check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true);
              ()
             )
            else
             (
               assert (~(is_fields_points_to_blocks2 hd g (getWosize (read_word g hd)) (objects2 0UL g)));
               assert (check_fields_points_to_blocks2 g f' == true <==> check_fields_points_to_blocks2 g' f'' == true);
               ()
               
             )
          )
         
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

#restart-solver 

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
                                                     Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) f')})
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
           if (Seq.mem (hd_address succ) f') then
           (
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
                                                    Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g))}) = 
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
                                                   Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g)))) =
 assert (well_formed_allocated_blocks g);
 assert (check_fields_points_to_allocs2 g (get_allocated_block_addresses g));
 assert (forall x. Seq.mem x (get_allocated_block_addresses g) ==> is_fields_points_to_f g x (getWosize (read_word g x)) (get_allocated_block_addresses g));
 assert (Seq.mem h_index (get_allocated_block_addresses g));  
 assert (is_fields_points_to_f g h_index (getWosize (read_word g h_index)) (get_allocated_block_addresses g));
 assert (forall i.  (Usize.v i > 0 /\ Usize.v i <= Usize.v wz) /\
               (is_hp_addr ((Usize.add h_index (Usize.mul i mword)))) /\
               isPointer (Usize.add h_index (Usize.mul i mword)) g ==>
                                                     Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
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
           if (Seq.mem (hd_address succ) f') then
           (
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

#restart-solver 

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
       //assert ((Usize.v i < Usize.v wz + 1) /\ Seq.length s_list > 0 ==> Seq.index s_list (Usize.v i - 1) == read_word g ( Usize.add h_index (Usize.mul i mword)));
       s_list
 
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
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
        assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (objects2 0UL g));
        assert (is_valid_header (hd_address succ) g);

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
        (*assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);*)
        let s_list = create_successors_list_for_h_index g h_index wz i' in
        s_list
      )
    )

#restart-solver

#restart-solver

#restart-solver 

(*/// Given the start address of an object, which is the address of the first field of the object, hd_address gets the header address of that object
let hd_address (st_index: hp_addr{UInt.fits (Usize.v st_index - Usize.v mword) Usize.n})
          : Tot (h:hp_addr{Usize.v h == Usize.v st_index - Usize.v mword}) = 
  let h_index = Usize.sub st_index mword in
  assert (Usize.v h_index % Usize.v mword == 0);
  assert (Usize.v h_index >= 0);
  assert (is_hp_addr h_index);
  h_index

#restart-solver 

/// Given the header address of an object, the f_address finds the address of the first field of the object
let f_address (h_index: hp_addr{UInt.fits (Usize.v h_index + Usize.v mword) Usize.n /\ (Usize.v h_index + Usize.v mword < heap_size)}) 
         : Tot (f:hp_addr{Usize.v f == Usize.v h_index + Usize.v mword})=
  let f_index = Usize.add h_index mword in
  assert (Usize.v f_index % Usize.v mword == 0);
  assert (Usize.v f_index >= 0);
  assert (is_hp_addr f_index);
  f_index*)

let f_address_hp_address_lemma (h_index: hp_addr{UInt.fits (Usize.v h_index + Usize.v mword) Usize.n /\ (Usize.v h_index + Usize.v mword < heap_size)})
                         : Lemma (hd_address (f_address h_index) == h_index) = ()

#restart-solver 

#restart-solver

#restart-solver

//let pair = p:hp_addr{UInt.fits (Usize.v p - Usize.v mword) Usize.n} & q:hp_addr{UInt.fits (Usize.v q - Usize.v mword) Usize.n}
                                
let pair = UInt64.t & UInt64.t

let sub_op (x:UInt64.t{UInt.fits (Usize.v x - 2) Usize.n}) =
   let d = Usize.sub x 2UL in
   d

let test_prop' (s':seq UInt64.t)
              (s:seq pair {forall x y. Seq.mem (x,y) s ==> 
                                                Seq.mem (sub_op x) s'}) = admit()
                                                
let test_prop (s':seq UInt64.t)
              (s:seq pair {forall (x:pair). Seq.mem x s ==> (UInt.fits (Usize.v (fst x) - 2) Usize.n) /\
                                                Seq.mem (sub_op (fst x)) s'}) = admit()

#restart-solver 

#restart-solver 

let cons_property_lemma3 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                         (h_index:hp_addr{Seq.mem h_index (get_allocated_block_addresses g)})
                         (s:seq G.edge{(forall p q. Seq.mem (p,q) s ==> is_hp_addr p /\ (UInt.fits (Usize.v p - Usize.v mword) Usize.n) /\
                                                            is_hp_addr q /\ (UInt.fits (Usize.v q - Usize.v mword) Usize.n) /\
                                                            Seq.mem (hd_address p) (get_allocated_block_addresses g) /\
                                                            Seq.mem (hd_address q) (get_allocated_block_addresses g)) /\
                                        (forall p q. Seq.mem (p,q) s ==> hd_address p == h_index)})
                         
                         (s_cons:G.edge{is_hp_addr (fst s_cons) /\ (UInt.fits (Usize.v (fst s_cons) - Usize.v mword) Usize.n) /\
                                        is_hp_addr (snd s_cons) /\ (UInt.fits (Usize.v (snd s_cons) - Usize.v mword) Usize.n) /\
                                       Seq.mem (hd_address (fst s_cons)) (get_allocated_block_addresses g) /\
                                       Seq.mem (hd_address (snd s_cons)) (get_allocated_block_addresses g) /\
                                       hd_address (fst s_cons) == h_index})
                 : Lemma
                   (ensures (forall x y. Seq.mem (x,y) (Seq.cons s_cons s) ==>  is_hp_addr x /\ (UInt.fits (Usize.v x - Usize.v mword) Usize.n) /\
                                                                           is_hp_addr y /\ (UInt.fits (Usize.v y - Usize.v mword) Usize.n) /\
                                                                           Seq.mem (hd_address x) (get_allocated_block_addresses g) /\
                                                                           Seq.mem (hd_address y) (get_allocated_block_addresses g)) /\
                            (forall x y. Seq.mem (x,y) (Seq.cons s_cons s) ==> hd_address x == h_index)) = 
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 ()

let cons_property_lemma5 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                         (h_index:hp_addr{Seq.mem h_index (get_allocated_block_addresses g)})
                         (s:seq G.edge{(forall (p:G.edge). Seq.mem p s ==> is_hp_addr (fst p) /\ (UInt.fits (Usize.v (fst p) - Usize.v mword) Usize.n) /\
                                                            is_hp_addr (snd p) /\ (UInt.fits (Usize.v (snd p) - Usize.v mword) Usize.n) /\
                                                            Seq.mem (hd_address (fst p)) (get_allocated_block_addresses g) /\
                                                            Seq.mem (hd_address (snd p)) (get_allocated_block_addresses g)) /\
                                        (forall (p:G.edge). Seq.mem p s ==> hd_address (fst p) == h_index) /\
                                        (forall (p:G.edge). Seq.mem p s ==> (fst p) == f_address h_index)})
                         
                         (s_cons:G.edge{is_hp_addr (fst s_cons) /\ (UInt.fits (Usize.v (fst s_cons) - Usize.v mword) Usize.n) /\
                                        is_hp_addr (snd s_cons) /\ (UInt.fits (Usize.v (snd s_cons) - Usize.v mword) Usize.n) /\
                                       Seq.mem (hd_address (fst s_cons)) (get_allocated_block_addresses g) /\
                                       Seq.mem (hd_address (snd s_cons)) (get_allocated_block_addresses g) /\
                                       hd_address (fst s_cons) == h_index /\
                                       fst s_cons == f_address h_index})
                 : Lemma
                   (ensures (forall (x:G.edge). Seq.mem x (Seq.cons s_cons s) ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                           is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                           Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                           Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                            (forall (x:G.edge). Seq.mem x (Seq.cons s_cons s) ==> hd_address (fst x) == h_index) /\
                            (forall (x:G.edge). Seq.mem x (Seq.cons s_cons s) ==> (fst x) == f_address h_index)) = 
 lemma_tl s_cons s;
 let s' = Seq.cons s_cons s in
 ()

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

                       : Tot (f':seq (G.edge) {
                       
                                               (forall (x:G.edge). Seq.mem x f' ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                               (forall (x:G.edge). Seq.mem x f' ==> hd_address (fst x) == h_index) /\
                                               (forall (x:G.edge). Seq.mem x f' ==> (fst x) == f_address h_index)}) 
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
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
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
        assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (objects2 0UL g));
        assert (is_valid_header (hd_address succ) g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);

        let e' = create_edge_pairs_for_h_index g h_index wz i' in
        assert ((forall (x:G.edge). Seq.mem x e' ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                               (forall (x:G.edge). Seq.mem x e' ==> hd_address (fst x) == h_index));
        

       let f_index = f_address h_index in
       f_address_hp_address_lemma h_index;
       assert (hd_address f_index == h_index);
       let edge_pair = (f_index,succ) in
       assert (hd_address (fst edge_pair) == h_index);
       assert (fst edge_pair == f_index);
       assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
       assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
       lemma_tl edge_pair e'; 
       
       let e = Seq.cons edge_pair e' in 
      
       cons_property_lemma5 g h_index e' edge_pair;

       assert ((forall (x:G.edge). Seq.mem x e ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
              (forall (x:G.edge). Seq.mem x e ==> hd_address (fst x) == h_index));
      
       
       e
        
      )
      else
      (
        //assert (Usize.v i' > 1);
        //assert (Usize.v i < Usize.v wz + 1);
        //assert (Usize.v i' <= Usize.v wz + 1);
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
      assert (Usize.v i' > 1);
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
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
        assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (objects2 0UL g));
        assert (is_valid_header (hd_address succ) g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);

        let e' = create_edge_pairs_for_h_index g h_index wz i' in
        create_edge_pairs_for_h_index_length_lemma g h_index wz i';
        

       let f_index = f_address h_index in
       f_address_hp_address_lemma h_index;
       assert (hd_address f_index == h_index);
       let edge_pair = (f_index,succ) in
       assert (hd_address (fst edge_pair) == h_index);
       assert (Seq.mem (hd_address (fst edge_pair)) (get_allocated_block_addresses g));
       assert (Seq.mem (hd_address (snd edge_pair)) (get_allocated_block_addresses g));
       lemma_tl edge_pair e'; 
       
       let e = Seq.cons edge_pair e' in 
      
       cons_property_lemma5 g h_index e' edge_pair;

      
      
       
       ()
        
      )
      else
      (
        //assert (Usize.v i' > 1);
        //assert (Usize.v i < Usize.v wz + 1);
        //assert (Usize.v i' <= Usize.v wz + 1);
        let e = create_edge_pairs_for_h_index g h_index wz i' in
        create_edge_pairs_for_h_index_length_lemma g h_index wz i';
        ()
      )
    )
                                                  
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
                               (ensures (
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz 1UL) ==> 
                                                                                is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                                is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                                Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                                Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                         (forall (x:G.edge). Seq.mem x (create_edge_pairs_for_h_index g h_index wz 1UL) ==> 
                                                        (hd_address (fst x) == h_index) /\
                                                        (fst x == f_address h_index)) /\
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

#restart-solver 

#restart-solver 

#restart-solver

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
                         (f': seq (G.edge){(forall (x:G.edge). Seq.mem x f' ==> 
                                                                    is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                    is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                    Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                    Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g)) /\
                                                                    
                                            (forall (x:G.edge). Seq.mem x f' ==> Seq.mem (hd_address (fst x)) f) /\
                                            
                                            (forall x. Seq.mem x f ==> 
                                                                 G.successors_fn2 (f_address x) f' == 
                                                                 G.successors_fn2 (f_address x) 
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
   
   
   let rest_of_f = create_edge_list_from_heap g tl in
   assert (forall (x:G.edge). Seq.mem x rest_of_f ==> Seq.mem (hd_address (fst x)) tl);
  

   assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (hd_address (fst x)) == hd));
   
   let wz = getWosize (read_word g hd) in
   
   let edge_pairs_for_hd = create_edge_pairs_for_h_index g hd wz 1UL in
   assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> 
                                                        is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                        is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                        Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                        Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
                                                        
   assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (hd_address (fst x)) == hd);

   

    let f_id = f_address hd in
    assert (hd_address f_id == hd);
   
    assert (forall (x:G.edge). Seq.mem x edge_pairs_for_hd ==> (fst x == f_id));
    assert (~(Seq.mem hd tl));
    assert (forall y. Seq.mem y tl ==> hd <> y);
    assert (forall y. Seq.mem y tl ==> f_address hd <> f_address y);
    assert (forall (x:G.edge) y. Seq.mem y tl /\ Seq.mem x edge_pairs_for_hd ==> (fst x <> f_address y));
    assert (forall x. Seq.mem x tl ==> ~(exists (y:G.edge). Seq.mem y edge_pairs_for_hd /\ (fst y == (f_address x))));
    
    G.successors_fn2_pick_second_lemma f_id edge_pairs_for_hd;
   
   assert (G.successors_fn2 f_id edge_pairs_for_hd == G.pick_second edge_pairs_for_hd);
   let f' = Seq.append (edge_pairs_for_hd) (rest_of_f) in
  
   
   Seq.lemma_mem_append (edge_pairs_for_hd) (rest_of_f);
   
   
   assert (~(exists (x:G.edge). Seq.mem x rest_of_f /\ (fst x) == f_id));
   G.successors_fn2_e2_is_successors_fn2_e_if_no_fst_i_in_e1 f_id (edge_pairs_for_hd) (rest_of_f) f';
   assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (edge_pairs_for_hd));
   assert (G.successors_fn2 f_id f' == G.successors_fn2 f_id (create_edge_pairs_for_h_index g hd 
                                                                                          (getWosize (read_word g hd))
                                                                                          1UL));
   assert (cons hd tl == f);
   assert (forall x. Seq.mem x tl ==> G.successors_fn2 (f_address x) (rest_of_f) == 
                                                                 G.successors_fn2 (f_address x) 
                                                                                  (create_edge_pairs_for_h_index g 
                                                                                                                 x 
                                                                                                                 (getWosize (read_word g x))
                                                                                                                 1UL));
   
   assert ((forall x. Seq.mem x tl ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                       (forall x. Seq.mem x tl ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                       (forall x. Seq.mem x tl ==> Usize.v x % Usize.v mword == 0) /\
                                                     
                                                        (forall x. Seq.mem x tl ==> is_valid_header x g) /\
                                                       (G.is_vertex_set tl) /\
                                                       (forall x. Seq.mem x tl ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                                                                             (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0)));
   
  
   
   G.successors_fn2_e2_is_successors_fn2_e1_if_no_fst_tl_in_e'' tl (edge_pairs_for_hd) (rest_of_f) f';
   assert (forall x. Seq.mem x tl ==> G.successors_fn2 (f_address x) f' == G.successors_fn2 (f_address x) rest_of_f);
   assert (forall x. Seq.mem x tl ==> G.successors_fn2 (f_address x) f' == 
                                                                 G.successors_fn2 (f_address x) 
                                                                                  (create_edge_pairs_for_h_index g 
                                                                                                                 x 
                                                                                                                 (getWosize (read_word g x))
                                                                                                                 1UL));
   assert (forall x. Seq.mem x f ==> G.successors_fn2 (f_address x) f' == 
                                                G.successors_fn2 (f_address x) 
                                                                 (create_edge_pairs_for_h_index g 
                                                                 x 
                                                                (getWosize (read_word g x))
                                                                 1UL));                                               
                                                                 
   f'
 )


#restart-solver 

#restart-solver

#restart-solver 

let within_heap_all (f: seq Usize.t)
 = (forall x. Seq.mem x f ==> Usize.v x < heap_size)

let multiple_of_mword_all (f: seq Usize.t)
=  (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0)

let all_valid_headers (f: seq Usize.t)
                      (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})=
 (forall x. Seq.mem x f ==> is_valid_header x g)

let all_objects_and_their_field_pointers_are_within_heap_size (f: seq Usize.t)
                                                              (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})=
 (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                      is_fields_contents_within_limit2 x (getWosize (read_word g x)) g)

let all_field_address_are_word_aligned (f: seq Usize.t)
                                       (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})=
  (forall x. Seq.mem x f ==> (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))

let all_mem_of_allocated_blocks (f: seq Usize.t)
                                (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) =
 (forall x. Seq.mem x f ==> Seq.mem x (get_allocated_block_addresses g))
 
#restart-solver 

(*Try to do is make sure that the function names are mapping to the names in the paper
 1. Start address change
 2. Closure
 3. Infix tags
 F* switch
 OCaml switch
 Build OCaml compiler
 First run byte code interpreter.
 Do it first immediately
 3 commands. ./configure Choose 4.14 branch from the repo*)

#restart-solver

let can_be_shifted_forward (f: seq Usize.t)
  = forall x. mem x f ==> Usize.v x + Usize.v mword < heap_size

let can_be_shifted_backward (f: seq Usize.t)
  = forall x. mem x f ==> Usize.v x > 0

#restart-solver

let rec first_field_addresses_of_allocated_blocks   (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                    (f: seq Usize.t 
                                                      { 
                                                       (all_mem_of_allocated_blocks f g) /\
                                                       (within_heap_all f) /\
                                                       (multiple_of_mword_all f) /\
                                                       (all_valid_headers f g) /\
                                                       (G.is_vertex_set f) /\
                                                       (all_objects_and_their_field_pointers_are_within_heap_size f g) /\
                                                       (all_field_address_are_word_aligned f g) /\
                                                       (can_be_shifted_forward f)
                                                       }
                                                     ) 
                       : Tot (f':seq Usize.t{(within_heap_all f') /\
                                             (multiple_of_mword_all f') /\
                                             (can_be_shifted_backward f')  /\
                                             (forall x. Seq.mem x f' <==> Seq.mem (hd_address x) f) /\
                                             (forall x. Seq.mem x f <==> Seq.mem (f_address x) f') /\
                                             (Seq.length f == Seq.length f') /\
                                             (G.is_vertex_set f') /\
                                             (forall x. Seq.mem x f' ==> Seq.mem (hd_address x) (get_allocated_block_addresses g))}) 
                         (decreases Seq.length f) = 
 if length f = 0 then 
 (
   let f' = Seq.empty #Usize.t in
   G.is_vertex_set_lemma1 f';
   f'
 )
 else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));
   
   let rest_of_f = first_field_addresses_of_allocated_blocks g tl in
  
   let f_id = f_address hd in
   assert (hd_address f_id == hd);

   lemma_tl f_id rest_of_f;
   let f' = Seq.cons f_id rest_of_f in
   assert (within_heap_all f);
   assert (within_heap_all rest_of_f);
   assert (within_heap_all f');
   let hd' = Seq.head f' in
   let tl' = Seq.tail f' in
   assert (hd' == f_id);
   assert (tl' == rest_of_f);
   assert (~(mem (head f') (tail f')));
   G.is_vertex_set_cons f_id rest_of_f;
   assert (G.is_vertex_set f');
   assert (forall x. Seq.mem x f' <==> Seq.mem (hd_address x) f);
   assert (forall x. Seq.mem x f <==> Seq.mem (f_address x) f');
   assert (can_be_shifted_backward f');
   assert (forall x. Seq.mem x f' ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));
   f'
  
 )

#restart-solver 

#restart-solver 

let rec first_field_addresses_of_allocated_blocks_lemma   (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                          (f: seq Usize.t 
                                                             { 
                                                               (all_mem_of_allocated_blocks f g) /\
                                                               (within_heap_all f) /\
                                                               (multiple_of_mword_all f) /\
                                                               (all_valid_headers f g) /\
                                                               (G.is_vertex_set f) /\
                                                               (all_objects_and_their_field_pointers_are_within_heap_size f g) /\
                                                               (all_field_address_are_word_aligned f g) /\
                                                               (can_be_shifted_forward f)
                                                             }
                                                           )
                                                           (g':heap{well_formed_heap2 g' /\ well_formed_allocated_blocks g'})
                                                           (f': seq Usize.t 
                                                             { 
                                                               (all_mem_of_allocated_blocks f' g') /\
                                                               (within_heap_all f') /\
                                                               (multiple_of_mword_all f') /\
                                                               (all_valid_headers f' g') /\
                                                               (G.is_vertex_set f') /\
                                                               (all_objects_and_their_field_pointers_are_within_heap_size f' g') /\
                                                               (all_field_address_are_word_aligned f' g') /\
                                                               (can_be_shifted_forward f')
                                                             }
                                                           )
                            : Lemma
                              (requires f == f')
                              (ensures first_field_addresses_of_allocated_blocks g f == first_field_addresses_of_allocated_blocks g' f') 
                              (decreases Seq.length f) =
 if length f = 0 then 
 (
   let f' = Seq.empty #Usize.t in
   G.is_vertex_set_lemma1 f';
   ()
 )
 else
 (
   let hd = Seq.head f in
   let tl = Seq.tail f in
   G.is_vertex_set_lemma f;
   assert (G.is_vertex_set tl);
   
   G.is_vertex_set_lemma4 f;
   assert (~(Seq.mem hd tl));

   let hd' = Seq.head f' in
   let tl' = Seq.tail f' in
   G.is_vertex_set_lemma f';
   assert (G.is_vertex_set tl');
   
   G.is_vertex_set_lemma4 f';
   assert (~(Seq.mem hd tl'));
   let rest_of_f = first_field_addresses_of_allocated_blocks g tl in
   
   assert (tl == tl');
   assert (hd == hd');
   assert ((all_mem_of_allocated_blocks tl' g') /\
                                                               (within_heap_all tl') /\
                                                               (multiple_of_mword_all tl') /\
                                                               (all_valid_headers tl' g') /\
                                                               (G.is_vertex_set tl') /\
                                                               (all_objects_and_their_field_pointers_are_within_heap_size tl' g') /\
                                                               (all_field_address_are_word_aligned tl' g'));
   
   assert (can_be_shifted_forward tl');
   let rest_of_f' = first_field_addresses_of_allocated_blocks g' tl' in
   
   first_field_addresses_of_allocated_blocks_lemma g tl g' tl';
   
   assert (rest_of_f == rest_of_f');
  
   let f_id = f_address hd in
   let f_id' = f_address hd' in
   assert (hd_address f_id == hd);
   assert (f_id == f_id');

   lemma_tl f_id rest_of_f;
   let f1 = Seq.cons f_id rest_of_f in
   
   lemma_tl f_id' rest_of_f';
   let f2 = Seq.cons f_id' rest_of_f' in

   assert (f1 == f2);
   ()
 )
 
#reset-options "--z3rlimit 1000"

#restart-solver

#restart-solver


let create_edge_list_for_graph (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
               : Tot
                 (f': seq (G.edge){(forall (x:G.edge). Seq.mem x f' ==> is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                                                   is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                                                   Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                                                   Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g))}) =
  let allocs = get_allocated_block_addresses g in
  assert ((forall x. Seq.mem x allocs ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                       (forall x. Seq.mem x allocs ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                       (forall x. Seq.mem x allocs ==> Usize.v x % Usize.v mword == 0) /\
                                                       (forall x. Seq.mem x allocs ==> is_valid_header x g) /\
                                                       (G.is_vertex_set allocs));
  assert (forall x. Seq.mem x allocs ==> is_fields_within_limit1 x (getWosize (read_word g x)));
  assert (forall x. Seq.mem x allocs ==> is_fields_contents_within_limit2 x (getWosize (read_word g x)) g);
  fieldaddress_within_limits_lemma_x_all g;
  assert (forall x. Seq.mem x allocs ==> (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0));
  let f' = create_edge_list_from_heap g allocs in
  assert (forall (x:G.edge). Seq.mem x f' ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                           is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                           Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                           Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));                                               
                                                                   
                                                                    
                                           
  f'

#restart-solver 


let edge_list_membership_in_ff_allocs_lemma (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                      : Lemma
                        (ensures True) = 
 let allocs = get_allocated_block_addresses g in
 fieldaddress_within_limits_lemma_x_all g;
 let f' = create_edge_list_from_heap g allocs in
 assert (forall (x:G.edge). Seq.mem x f' ==>  is_hp_addr (fst x) /\ (UInt.fits (Usize.v (fst x) - Usize.v mword) Usize.n) /\
                                           is_hp_addr (snd x) /\ (UInt.fits (Usize.v (snd x) - Usize.v mword) Usize.n) /\
                                           Seq.mem (hd_address (fst x)) (get_allocated_block_addresses g) /\
                                           Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));  
 
 
 let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) ff_allocs);
 assert (forall (x:G.edge). Seq.mem x f' ==> Seq.mem (hd_address (fst x)) allocs);
 assert (forall (x:G.edge). Seq.mem x f' ==> Seq.mem (f_address (hd_address (fst x))) ff_allocs);
 assert (forall (x:G.edge). Seq.mem x f' ==> Seq.mem (fst x) ff_allocs);
 assert (forall (x:G.edge). Seq.mem x f' ==> Seq.mem (hd_address (snd x)) allocs);
 assert (forall (x:G.edge). Seq.mem x f' ==> Seq.mem (f_address (hd_address (snd x))) ff_allocs);
 assert (forall (x:G.edge). Seq.mem x f' ==> Seq.mem (snd x) ff_allocs);
 admit()

let create_graph_from_heap (g:heap {well_formed_heap2 g /\ well_formed_allocated_blocks g}) 
                   : Pure (G.graph_state #unit #unit)
                    (requires all_field_address_are_word_aligned (get_allocated_block_addresses g) g)
                    (ensures fun f -> (G.is_vertex_set f.vertices) /\
                                   (Seq.equal (f.vertices) (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)))) = 
  
  let f = get_allocated_block_addresses g in 
  assert ((all_mem_of_allocated_blocks f g) /\
          (within_heap_all f) /\
          (multiple_of_mword_all f) /\
          (all_valid_headers f g) /\
          (G.is_vertex_set f));
  assert (can_be_shifted_forward f);
  fieldaddress_within_limits_lemma_x_all g;
  assert (all_objects_and_their_field_pointers_are_within_heap_size f g);
  assert (all_field_address_are_word_aligned f g);                                               
  let ff_allocs = first_field_addresses_of_allocated_blocks g f in  
  assert (forall x. Seq.mem x ff_allocs ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));
  let e = create_edge_list_for_graph g in
  
  assert (forall x. Seq.mem x f <==> Seq.mem (f_address x) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (hd_address (fst x)) f);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (f_address (hd_address (fst x))) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (fst x) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (hd_address (snd x)) f);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (f_address (hd_address (snd x))) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (snd x) ff_allocs);
  assert (forall (x:G.edge). Seq.mem x e ==> Seq.mem (fst x) ff_allocs /\
                                       Seq.mem (snd x) ff_allocs);
  {
    vertices  = ff_allocs;//get_allocated_block_addresses g;
    edge_set  = e;//create_edge_list_for_graph g;
  }

(*All successors of a valid address (header address) in graph formed from g are members of allocated blocks ---> when the id is header address
  All hd_address of successors of a f_address (header address) in graph formed from g are members of allocated blocks*)

#restart-solver 

#restart-solver 

#push-options "--z3rlimit 100"

#restart-solver

let graph_successors_mem_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                               (h_index:hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g))
                                  (ensures (forall x. Seq.mem x  (G.successors (create_graph_from_heap g) (f_address h_index)) ==> 
                                                         Seq.mem (hd_address x) (get_allocated_block_addresses g))) = 
 let allocs = get_allocated_block_addresses g in
 fieldaddress_within_limits_lemma_x_all g;
 let grph = create_graph_from_heap g in
 let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
 assert (Seq.equal (grph.vertices) ff_allocs);
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) ff_allocs);
 assert (Seq.mem (f_address h_index) (ff_allocs));
 let f_h_index = f_address h_index in 
 G.successors_successors_fn2_connect_lemma grph f_h_index;  
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index grph.edge_set);
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_for_graph g));
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_from_heap g allocs));
 assert (Seq.mem h_index allocs);                                                         

 let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL in 
 assert (G.successors_fn2 f_h_index (create_edge_list_from_heap g allocs) == 
     G.successors_fn2 f_h_index    h_index_edge_list);                                                                                                                            
                                                                                                                           
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index h_index_edge_list);
 assert (forall (x:G.edge). Seq.mem x h_index_edge_list ==> (fst x) == f_h_index);                                                       
                                                                                           
 G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;

 assert (G.successors_fn2 f_h_index h_index_edge_list ==
                G.pick_second h_index_edge_list);                                                                                                

 create_edge_pairs_for_h_index_length_mem_lemma g h_index (getWosize (read_word g h_index));
 assert (forall (x:G.edge). Seq.mem x h_index_edge_list ==> Seq.mem (hd_address (snd x)) (get_allocated_block_addresses g));
 G.pick_second_mem_lemma grph h_index_edge_list;

 assert (forall x. Seq.mem x (G.pick_second h_index_edge_list) ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));

 assert (forall x. Seq.mem x (G.successors_fn2 f_h_index h_index_edge_list) ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));

 assert (forall x. Seq.mem x (G.successors grph f_h_index) ==> Seq.mem (hd_address x) (get_allocated_block_addresses g));
 ()

#restart-solver 

let graph_successors_length_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                  (h_index:hp_addr{is_valid_header h_index g /\ Seq.mem h_index (get_allocated_block_addresses g)})
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g))
                                  (ensures (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index)))) =
 let allocs = get_allocated_block_addresses g in
 fieldaddress_within_limits_lemma_x_all g;
 let grph = create_graph_from_heap g in
 let ff_allocs = first_field_addresses_of_allocated_blocks g allocs in 
 assert (Seq.equal (grph.vertices) ff_allocs);
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) ff_allocs);
 assert (Seq.mem (f_address h_index) (ff_allocs));
 let f_h_index = f_address h_index in 
 G.successors_successors_fn2_connect_lemma grph f_h_index;  
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index grph.edge_set);
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_for_graph g));
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_from_heap g allocs));
 assert (Seq.mem h_index allocs);  
 
 
 
 assert (G.successors_fn2 f_h_index (create_edge_list_from_heap g allocs) == G.successors_fn2 f_h_index 
                                                                                            (create_edge_pairs_for_h_index g 
                                                                                                                           h_index 
                                                                                                                           (getWosize (read_word g h_index)) 
                                                                                                                           1UL));
 
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index
                                                        (create_edge_pairs_for_h_index g 
                                                                                       h_index 
                                                                                       (getWosize (read_word g h_index)) 
                                                                                       1UL));
                                                                                           
 
 let h_index_edge_list = create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL in 
 assert (G.successors_fn2 f_h_index (create_edge_list_from_heap g allocs) == 
     G.successors_fn2 f_h_index    h_index_edge_list);                                                                                                                            
                                                                                                                           
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index h_index_edge_list);
 assert (forall (x:G.edge). Seq.mem x h_index_edge_list ==> (fst x) == f_h_index);                                                       
                                                                                           
 G.successors_fn2_pick_second_lemma f_h_index h_index_edge_list;

 assert (G.successors_fn2 f_h_index h_index_edge_list ==
                G.pick_second h_index_edge_list);   


 
 G.pick_second_length_lemma (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);
 
 assert (Seq.length (G.pick_second (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL)) == 
         Seq.length (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL));

 create_edge_pairs_for_h_index_length_mem_lemma g h_index (getWosize (read_word g h_index));

 assert (Seq.length (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) <= Usize.v (getWosize (read_word g h_index)));

 assert (Seq.length (G.pick_second (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL)) <= Usize.v (getWosize (read_word g h_index)));

 assert (Seq.length (G.successors_fn2 f_h_index (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL)) <= Usize.v (getWosize (read_word g h_index)));
 assert (Seq.length (G.successors grph f_h_index) <= Usize.v (getWosize (read_word g h_index)));
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
                    (ensures (Usize.v (Usize.add h_index (Usize.mul i mword))< heap_size)) =  ()

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
      
          let f_index = f_address h_index in
          f_address_hp_address_lemma h_index;
          assert (hd_address f_index == h_index);
          let edge_pair = (f_index,succ) in
          let edge_pair' = (f_index,succ1) in
          assert (edge_pair == edge_pair');
          lemma_tl edge_pair e'; 
       
          let e = Seq.cons edge_pair e' in 

          lemma_tl edge_pair' e'; 
       
          let e1 = Seq.cons edge_pair' e' in 

          assert (e == e1);
          (*let edge_pair = (h_index,succ) in
          let edge_pair' = (h_index,succ1) in

          assert (edge_pair == edge_pair');

          lemma_tl edge_pair e'; 
          let e = Seq.cons edge_pair e' in 

          lemma_tl edge_pair' e'; 
          let e1 = Seq.cons edge_pair' e' in 

          assert (e == e1);
          assert (create_edge_pairs_for_h_index g h_index wz i == create_edge_pairs_for_h_index g' h_index wz1 i);
      
          ()*)
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

#restart-solver 

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
                                           
                                           (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                                           
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

#restart-solver 

let create_edge_list_for_graph_lemma (g:heap{well_formed_heap2 g}) 
                                     (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})
                                     (c:color{c == 3UL \/ c== 2UL \/ c == 1UL})
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

#restart-solver 

#restart-solver

#push-options "--z3rlimit 100"

#restart-solver

let can_be_shift_forward_lemma (wz:Usize.t{Usize.v wz > 0})
               (x:Usize.t{Usize.v x + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size})
          : Lemma
            (ensures (Usize.v x + Usize.v mword < heap_size)) = 
assert (Usize.v wz > 0);
assert (Usize.v x + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size);
assert (Usize.v x + Usize.v mword < heap_size);
()

let can_be_shift_forward_lemma1 (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                (f: seq Usize.t { (forall x. Seq.mem x f ==> Seq.mem x (get_allocated_block_addresses g)) /\
                                                       (forall x. Seq.mem x f ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                       (forall x. Seq.mem x f ==> Usize.v x % Usize.v mword == 0) /\
                                                       (forall x. Seq.mem x f ==> is_valid_header x g) /\
                                                       (G.is_vertex_set f) /\
                                                       (forall x. Seq.mem x f ==> is_fields_within_limit1 x (getWosize (read_word g x)) /\
                                                                             is_fields_contents_within_limit2 x (getWosize (read_word g x)) g /\
                                                                             (forall i.  Usize.v i > 0 /\ Usize.v i <= Usize.v (getWosize (read_word g x)) ==> 
                                                                                  (Usize.v x  + (Usize.v i  * Usize.v mword)) % Usize.v mword == 0))}) 
                           : Lemma
                             (ensures  (forall x. Seq.mem x f ==> Usize.v x + Usize.v mword < heap_size)) = 
 assert (forall x. Seq.mem x f ==> Usize.v (getWosize (read_word g x)) > 0);
 assert (forall x. Seq.mem x f ==> Usize.v x + (((Usize.v (getWosize (read_word g x)) + 1) * Usize.v mword) - 1) < heap_size);
 assert (forall x. Seq.mem x f ==> Usize.v x + Usize.v mword < heap_size);
 ()

#restart-solver 

let create_graph_from_heap_lemma (g:heap {well_formed_heap2 g})
                                 (v_id:hp_addr{is_valid_header v_id g /\ Seq.mem v_id (get_allocated_block_addresses g)})
                                 (c:color{c == 3UL \/ c == 2UL \/ c == 1UL})
                         : Lemma 
                           (requires (well_formed_allocated_blocks g /\
                                      well_formed_allocated_blocks (colorHeader1 v_id g c) /\
                                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)))
                           (ensures (create_graph_from_heap g == create_graph_from_heap (colorHeader1 v_id g c))) = 
 let f = get_allocated_block_addresses g in 
 assert ((all_mem_of_allocated_blocks f g) /\
          (within_heap_all f) /\
          (multiple_of_mword_all f) /\
          (all_valid_headers f g) /\
          (G.is_vertex_set f));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 can_be_shift_forward_lemma1 g f;
 assert (can_be_shifted_forward f);
 assert (all_objects_and_their_field_pointers_are_within_heap_size f g);
 assert (all_field_address_are_word_aligned f g); 
 let ff_allocs = first_field_addresses_of_allocated_blocks g f in 

 let g' = colorHeader1 v_id g c in
 let f' = get_allocated_block_addresses g' in
 get_allocated_block_addresses_lemma g g' v_id c;
 assert (f == f');

 field_limits_allocated_blocks_lemma g';
 field_contents_within_limits_allocated_blocks_lemma g';
 fieldaddress_within_limits_lemma_x_all g';
 can_be_shift_forward_lemma1 g' f';
 assert (can_be_shifted_forward f');
 let ff_allocs' = first_field_addresses_of_allocated_blocks g' f' in 
 first_field_addresses_of_allocated_blocks_lemma g f g' f';
 assert (ff_allocs == ff_allocs');
 
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
                                   well_formed_allocated_blocks (colorHeader1 v_id g 2UL) /\
                                   (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)))
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

        let f_index = f_address h_index in
        f_address_hp_address_lemma h_index;
        assert (hd_address f_index == h_index);
        let edge_pair = (f_index,succ) in
        
        //let edge_pair = (h_index,succ) in
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

#restart-solver

#restart-solver

let graph_successors_heap_create_successor_list_equivalence_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                                  (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))})
                                : Lemma
                                  (requires (is_fields_within_limit1 h_index (getWosize (read_word g h_index)) /\
                                                                       is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g /\
                                                         (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                                                                  (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0) /\
                                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g)))
                                  (ensures G.successors (create_graph_from_heap g) (f_address h_index) == 
                                             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) = 
 
 let grph = create_graph_from_heap g in
 let allocs = get_allocated_block_addresses g in

 let f_h_index = f_address h_index in
 
 G.successors_successors_fn2_connect_lemma grph f_h_index;
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index grph.edge_set);
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_for_graph g));
 field_limits_allocated_blocks_lemma g;
 field_contents_within_limits_allocated_blocks_lemma g;
 fieldaddress_within_limits_lemma_x_all g;
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_list_from_heap g allocs));
 assert (Seq.mem h_index allocs);
 assert (G.successors_fn2 f_h_index (create_edge_list_from_heap g allocs) ==  
           G.successors_fn2 f_h_index (create_edge_pairs_for_h_index g  h_index (getWosize (read_word g h_index)) 1UL));
                                                                                                                
 
 assert (grph.vertices == (first_field_addresses_of_allocated_blocks g (get_allocated_block_addresses g)));
 assert (grph.vertices == (first_field_addresses_of_allocated_blocks g allocs));
 assert (forall x. Seq.mem x allocs <==> Seq.mem (f_address x) (first_field_addresses_of_allocated_blocks g allocs));
 assert (forall x. Seq.mem x allocs ==> Seq.mem (f_address x) (first_field_addresses_of_allocated_blocks g allocs));
 assert (Seq.mem f_h_index (first_field_addresses_of_allocated_blocks g allocs));
 assert (Seq.mem f_h_index grph.vertices);
 assert (G.successors grph f_h_index == G.successors_fn2 f_h_index (create_edge_pairs_for_h_index g  h_index (getWosize (read_word g h_index)) 1UL));                                                                                                                
                                                                                 
 G.successors_fn2_pick_second_lemma f_h_index (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);   

 assert (G.successors_fn2 f_h_index (create_edge_pairs_for_h_index g  h_index (getWosize (read_word g h_index)) 1UL) ==
              G.pick_second (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL));
                                                                
 create_successors_pick_second_lemma g h_index (getWosize (read_word g h_index)) 1UL;

 assert (G.pick_second (create_edge_pairs_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) == 
           create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);

 assert (G.successors_fn2 f_h_index (create_edge_pairs_for_h_index g  h_index (getWosize (read_word g h_index)) 1UL) ==
             create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);

 assert (G.successors grph f_h_index ==  create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL);

 assert (G.successors (create_graph_from_heap g) f_h_index == 
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

type stack = s:seq Usize.t {forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size}

type stack_heap_pair = stack & heap


#reset-options "--z3rlimit 500"

#push-options "--z3rlimit 50"

#restart-solver

#push-options "--split_queries"

let push_to_stack2  (g:heap{well_formed_heap2 g})
                    (st: seq Usize.t{G.is_vertex_set st /\
                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st)})
                                    
                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                (Usize.v x % Usize.v mword == 0) /\
                                 is_valid_header x g /\
                                ~(Seq.mem (f_address x) st)
                               }) 
                                
            : Tot (st': stack_heap_pair{well_formed_heap2 (snd st') /\
                                  (forall x. Seq.mem x st ==> Seq.mem x (fst st')) /\
                                  
                                  Seq.mem (f_address x) (fst st') /\
                                  
                                  (G.is_vertex_set (fst st')) /\
                                  
                                  Seq.length (fst st') == Seq.length st + 1 /\
                                  
                                  (forall y. Seq.mem y (fst st') ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

                                  (forall y. Seq.mem y (fst st') ==> Usize.v y % Usize.v mword == 0) /\
                                  
                                  (forall y. Seq.mem y (fst st') ==> is_valid_header (hd_address y) (snd st')) /\
                                  
                                  (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                               isGrayObject1 (hd_address x) (snd st') <==>
                                               Seq.mem x (fst st')) /\
                                               
                                  (forall x. Seq.mem (hd_address x) (objects2 0UL (snd st')) /\
                                               isGrayObject1 (hd_address x) (snd st') <==>
                                               Seq.mem x (fst st'))}) = 
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
                                            
   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x stk');

   assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x stk');
   assert (heap_remains_same_except_index_v_id x g g');
   assert (forall x. Seq.mem x stk' ==> Usize.v x % Usize.v mword == 0);
   (stk', g')
)
    
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st');
  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x st');
  

  assert (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g);
  assert (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g');
  
  assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                  Seq.mem x st');
  assert (heap_remains_same_except_index_v_id x g g');
  (st',g')
)

let push_to_stack2_heap_state_lemma  (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                (Usize.v x % Usize.v mword == 0) /\
                                                is_valid_header x g /\
                                                ~(Seq.mem (f_address x) st)
                                               }) 
                  : Lemma  
                    (ensures (heap_remains_same_except_index_v_id x g (snd (push_to_stack2 g st x)))) = ()

#restart-solver 

#restart-solver 

let push_to_stack2_field_size_lemma (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                (Usize.v x % Usize.v mword == 0) /\
                                                is_valid_header x g /\
                                                ~(Seq.mem (f_address x) st)
                                               })
                  : Lemma  
                    (ensures (forall (y:Usize.t{Usize.v y < heap_size /\  Usize.v y % Usize.v mword == 0}). (getWosize (read_word g y)) ==
                                               (getWosize (read_word (snd (push_to_stack2 g st x)) y)))) = ()

let push_to_stack2_lemma (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                (Usize.v x % Usize.v mword == 0) /\
                                                is_valid_header x g /\
                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                               })
                   : Lemma
                     (ensures (get_allocated_block_addresses g == get_allocated_block_addresses (snd (push_to_stack2 g st x)))) =
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   get_allocated_block_addresses_lemma g g' x 2UL;
   ()
)
    
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  get_allocated_block_addresses_lemma g g' x 2UL;
  ()
)

let push_to_stack2_lemma_block_address (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                (Usize.v x % Usize.v mword == 0) /\
                                                is_valid_header x g /\
                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                               })
                   : Lemma
                     (ensures (objects2 0UL g == objects2 0UL (snd (push_to_stack2 g st x)))) =
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
  
   ()
)
    
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  
  ()
)

let push_to_stack2_lemma_valid_header  (g:heap{well_formed_heap2 g})
                                     (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                (Usize.v x % Usize.v mword == 0) /\
                                                is_valid_header x g /\
                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                               }) 
                   : Lemma
                     (ensures (forall y. is_valid_header y g ==> is_valid_header y (snd (push_to_stack2 g st x)))) =
  push_to_stack2_lemma_block_address g st x;
  ()

#restart-solver 

#restart-solver 

let push_to_stack2_visited_list_valid_header_lemma  (g:heap{well_formed_heap2 g})
                                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                                   (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                                              }) 
                                                    (vl: seq Usize.t {(G.is_vertex_set vl) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl)
                                                                      
                                                                      
                                                                    }) 
                        : Lemma
                          (ensures (forall y. Seq.mem y vl ==> is_valid_header (hd_address y) (snd (push_to_stack2 g st x)))) = 
 push_to_stack2_lemma_valid_header g st x; 
 ()

let push_to_stack2_lemma_gray_nodes (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                                              })
                   : Lemma
                     (ensures (forall y. is_valid_header y g /\ isGrayObject1 y g /\ x <> y ==> is_valid_header y (snd (push_to_stack2 g st x)) /\
                                                                                      isGrayObject1 y (snd (push_to_stack2 g st x)))) = 
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
  
   ()
)
    
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  
  ()
)

#restart-solver 

#reset-options "--z3rlimit 1000" 

#push-options "--split_queries"

#restart-solver

let push_to_stack2_fields_allocated_blocks_lemma  (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st)
                                                              })
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
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   colorHeader1_fields_lemma x g gray;
   ()
)
    
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  colorHeader1_fields_lemma x g gray;
  ()
)

let push_to_stack2_lemma_black_nodes (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white
                                                              })
                   : Lemma
                     (ensures (forall y. is_valid_header y g /\ isBlackObject1 y g /\ x <> y ==> 
                                    is_valid_header y (snd (push_to_stack2 g st x)) /\ isBlackObject1 y (snd (push_to_stack2 g st x)))) = 
 if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   get_allocated_block_addresses_lemma g g' x 2UL;
   ()
)
    
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
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

#restart-solver 

#push-options "--z3rlimit 1000 --max_fuel 2 --max_ifuel 4" 


#restart-solver

let push_to_stack2_lemma_black_nodes1 (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                (*Introduction of the below condition was needed to typecheck*)
                                                                is_fields_within_limit1 x (getWosize (read_word g x))}) 
                                                              
                   : Lemma 
                     (ensures G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                                (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x))))) = 
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
   colorHeader1_color_Lemma x g 2UL;

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
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  colorHeader1_color_Lemma x g 2UL;

  get_allocated_block_addresses_lemma g g' x 2UL;

  assert ((get_allocated_block_addresses g) == (get_allocated_block_addresses g'));
    
  let blacks = get_black_block_addresses g (get_allocated_block_addresses g) in
  let blacks' = get_black_block_addresses g' (get_allocated_block_addresses g') in
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

#restart-solver 

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

#restart-solver 

let push_to_stack2_mem_lemma_black_nodes (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                 (is_fields_within_limit1 x (getWosize (read_word g x)))}) 
                   : Lemma 
                     (ensures (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                               Seq.mem y (get_black_block_addresses (snd (push_to_stack2 g st x)) 
                                                                               (get_allocated_block_addresses (snd (push_to_stack2 g st x)))))) = 
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
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
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
  colorHeader1_color_Lemma x g 2UL;
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
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                 (is_fields_within_limit1 x (getWosize (read_word g x)))}) 
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
assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  
                                         Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y g1);

assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  
                                         Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ isBlackObject1 y (snd (push_to_stack2 g st x)));                             
()

let push_to_stack_mem_lemma_black_nodes_visited_list_lemma (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                    (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                         (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                         (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                         (G.is_vertex_set vl) /\
                                                                         (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==>
                                                                         Seq.mem x vl)
                                                                       })
                                : Lemma
                                  (ensures (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                            isBlackObject1 (hd_address y) (snd (push_to_stack2 g st x)) <==>  
                                                   Seq.mem y vl)) = 
 assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl));
 push_to_stack2_mem_lemma_black_nodes_for_visited_list  g st x;
 assert (forall y. Seq.mem y (objects2 0UL g) /\ isBlackObject1 y g <==>  Seq.mem y (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                                       isBlackObject1 y (snd (push_to_stack2 g st x)));  
 assert (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (push_to_stack2 g st x))) /\ 
                                                       isBlackObject1 (hd_address y) (snd (push_to_stack2 g st x)) <==> Seq.mem y vl);
                                                                        
 ()

#restart-solver 

let push_to_stack2_well_formed_allocated_blocks_lemma  (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                                       (c:color{c == 2UL})
                                   : Lemma
                                     (requires well_formed_allocated_blocks g)
                                     (ensures (well_formed_allocated_blocks (snd (push_to_stack2 g st x)))) = 

if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in
   let g' = colorHeader1 x g gray in 
   assert (Seq.mem f_x stk');
   G.is_vertex_set_lemma2 stk';
   assert (G.is_vertex_set stk');
   objects2_equal_lemma 0UL g g';
    
   assert (objects2 0UL g == objects2 0UL g');
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
   ()
 )
 else
 (
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  objects2_equal_lemma 0UL g g';
  
  assert (objects2 0UL g == objects2 0UL g');
  assert (well_formed_heap2 g');
  assert (G.is_vertex_set st);
  assert (~(Seq.mem (f_address x) st));
  G.snoc_unique_lemma f_x st;
  assert (G.is_vertex_set st'); 
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
    
   ()
 )



#restart-solver

#restart-solver

#restart-solver

let push_to_stack_heap_and_push_to_graph_equality_lemma1  (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                    (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                         (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                         (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                         (G.is_vertex_set vl) /\
                                                                         (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==>
                                                                         Seq.mem x vl)
                                                                       })
                                        : Lemma
                                          (requires (well_formed_allocated_blocks g) /\
                                                    
                                                    (~(Seq.mem (f_address x) st) /\ ~(Seq.mem (f_address x) vl)) /\
                                                    (Seq.mem x (get_allocated_block_addresses g)) /\
                                                    (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                    (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                   (ensures (fst (push_to_stack2 g st x) == G.push_to_stack_graph1 vl st (f_address x))) = 
  if Seq.length st = 0 then
 (
    let f_x = f_address x in
    let stk' = Seq.create 1 f_x in
    let g' = colorHeader1 x g gray in 
    
   
    G.is_vertex_set_lemma2 stk';
    
    objects2_equal_lemma 0UL g g';

    assert (color_of_object1 x g == white);
    get_allocated_block_addresses_lemma g g' x 2UL;
    assert (Seq.length st == 0);
    //G.push_to_stack_graph_lemma grph vl st x;
    assert (G.push_to_stack_graph1 vl st f_x  == Seq.create 1 f_x);
    assert (stk' == Seq.create 1 f_x);
    assert (G.push_to_stack_graph1 vl st f_x == stk');
    ()
 )
 else
 ( 
   let f_x = f_address x in
   lemma_tail_snoc st f_x;
   lemma_mem_snoc st f_x; 
   let st' = snoc st f_x in
   let g' = colorHeader1 x g gray in 
   objects2_equal_lemma 0UL g g';
  
   assert (objects2 0UL g ==  objects2 0UL g');
   assert (well_formed_heap2 g');
   assert (G.is_vertex_set st);
   assert (~(Seq.mem (f_address x) st));
   G.snoc_unique_lemma f_x st;
   assert (G.is_vertex_set st'); 
   
   assert (Seq.length st > 0);
   //G.push_to_stack_graph_lemma1 grph vl st x;
   assert (G.push_to_stack_graph1 vl st f_x == snoc st f_x);
   ()
 )

#restart-solver

let push_to_stack2_graph_lemma  (g:heap{well_formed_heap2 g})
                                (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                    : Lemma 
                     (requires (well_formed_allocated_blocks g /\
                                well_formed_allocated_blocks (colorHeader1 x g 2UL) /\
                                (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) (*/\
                                (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (push_to_stack2 g st x))) (snd (push_to_stack2 g st x)))*)))
                     (ensures (create_graph_from_heap g == create_graph_from_heap ((snd (push_to_stack2 g st x))))) = 
if Seq.length st = 0 then
(
    let f_x = f_address x in
    let stk' = Seq.create 1 f_x in
    let g' = colorHeader1 x g gray in
    create_graph_from_heap_lemma_gray g x;
    assert (create_graph_from_heap g == create_graph_from_heap g');
    assert (Seq.mem f_x stk');
   
    ()
)
else
(
  let f_x = f_address x in
  lemma_tail_snoc st f_x;
  lemma_mem_snoc st f_x; 
  let st' = snoc st f_x in
  let g' = colorHeader1 x g gray in 
  create_graph_from_heap_lemma_gray g x;
  assert (create_graph_from_heap g == create_graph_from_heap g');
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
                            (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                            (*(vl: seq Usize.t {vl = get_black_block_addresses g (get_allocated_block_addresses g)})*)
                            (vl: seq Usize.t {(forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                         (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                         (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                         (G.is_vertex_set vl) /\
                                                                         (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==>
                                                                         Seq.mem x vl)
                                                                       })
                            (succ:hp_addr{Usize.v succ >= 0 /\ Usize.v succ < heap_size /\
                                    is_valid_header succ g}) 
                   : Lemma
                    (requires ((color_of_object1 succ g == white \/
                               color_of_object1 succ g == gray \/
                               color_of_object1 succ g == black)))  
                    (ensures ~(color_of_object1 succ g == white) ==> Seq.mem (f_address succ) st \/ Seq.mem (f_address succ) vl) = ()


#restart-solver

#push-options "--z3rlimit 1000"

#restart-solver

let fieldPush_spec_body   (g:heap{well_formed_heap2 g})
                          (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                         (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                          (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                          is_valid_header h_index g})
                                          
                         (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                         (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                    : Pure (stack_heap_pair)
                      (requires True)
                      (ensures fun st_hp -> well_formed_heap2 (snd st_hp) /\
                                         
                                         G.is_vertex_set (fst st_hp) /\
                                         
                                         (forall x. Seq.mem x (fst st_hp) ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\

                                         (forall x. Seq.mem x (fst st_hp) ==> Usize.v x % Usize.v mword == 0) /\
                                         
                                         (forall x. Seq.mem x (fst st_hp) ==> is_valid_header (hd_address x) (snd st_hp)) /\
                                         
                                         (forall x. Seq.mem (hd_address x) (objects2 0UL (snd st_hp)) /\
                                               isGrayObject1 (hd_address x) (snd st_hp) <==>
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
      let h_addr_succ = hd_address succ in
      if color_of_object1 h_addr_succ g = white  then
      (
        assert (is_valid_header h_addr_succ g);
        valid_succ_color_lemma g h_addr_succ;
      
       assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
       assert (~(Seq.mem (f_address h_addr_succ) st));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
       
       let st', g' = push_to_stack2 g st  h_addr_succ in
       push_to_stack2_heap_state_lemma g st h_addr_succ;
       push_to_stack2_field_size_lemma g st h_addr_succ;
       assert (G.is_vertex_set st');
       assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
              (Seq.mem succ st') /\
                                  
              Seq.length st' == Seq.length st + 1 /\
                                  
              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\
                                  
              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\
                                  
              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\
                                               
              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 h_addr_succ g == white);
       push_to_stack2_lemma g st h_addr_succ;

       assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       //assert (heap_remains_same_except_index_v_id h_addr_succ g g');
      
       assert ((Seq.length g == Seq.length g'));
     
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

#reset-options "--z3rlimit 100 --max_fuel 1 --max_ifuel 1 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver

let fieldPush_spec_body_fields_lemma   (g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
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
      let h_addr_succ = hd_address succ in
      if color_of_object1 h_addr_succ g = white  then
      (
        assert (is_valid_header h_addr_succ g);
        valid_succ_color_lemma g h_addr_succ;
      
       assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
       assert (~(Seq.mem (f_address h_addr_succ) st));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
       
       let st', g' = push_to_stack2 g st  h_addr_succ in
       push_to_stack2_heap_state_lemma g st h_addr_succ;
       push_to_stack2_field_size_lemma g st h_addr_succ;
       push_to_stack2_fields_allocated_blocks_lemma g st h_addr_succ ;
       assert (G.is_vertex_set st');
       assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
              (Seq.mem succ st') /\
                                  
              Seq.length st' == Seq.length st + 1 /\
                                  
              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\
                                  
              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\
                                  
              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\
                                               
              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 h_addr_succ g == white);
       push_to_stack2_lemma g st h_addr_succ;

       assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       //assert (heap_remains_same_except_index_v_id h_addr_succ g g');
      
       assert ((Seq.length g == Seq.length g'));
     
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
                                          (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
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
      let h_addr_succ = hd_address succ in
      if color_of_object1 h_addr_succ g = white  then
      (
        assert (is_valid_header h_addr_succ g);
        valid_succ_color_lemma g h_addr_succ;
      
       assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
       assert (~(Seq.mem (f_address h_addr_succ) st));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
       
       let st', g' = push_to_stack2 g st  h_addr_succ in
       push_to_stack2_heap_state_lemma g st h_addr_succ;
       push_to_stack2_field_size_lemma g st h_addr_succ;
       push_to_stack2_lemma_black_nodes1 g st h_addr_succ;
       assert (G.is_vertex_set st');
       assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
              (Seq.mem succ st') /\
                                  
              Seq.length st' == Seq.length st + 1 /\
                                  
              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\
                                  
              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\
                                  
              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\
                                               
              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 h_addr_succ g == white);
       push_to_stack2_lemma g st h_addr_succ;

       assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       //assert (heap_remains_same_except_index_v_id h_addr_succ g g');
      
       assert ((Seq.length g == Seq.length g'));
     
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

let fieldPush_spec_body_black_nodes_mem_lemma (g:heap{well_formed_heap2 g})
                                              (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
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
      let h_addr_succ = hd_address succ in
      if color_of_object1 h_addr_succ g = white  then
      (
        assert (is_valid_header h_addr_succ g);
        valid_succ_color_lemma g h_addr_succ;
      
       assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
       assert (~(Seq.mem (f_address h_addr_succ) st));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
       
       let st', g' = push_to_stack2 g st  h_addr_succ in
       push_to_stack2_heap_state_lemma g st h_addr_succ;
       push_to_stack2_field_size_lemma g st h_addr_succ;
       push_to_stack2_lemma_black_nodes1 g st h_addr_succ;
       assert (G.is_vertex_set st');
       assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
              (Seq.mem succ st') /\
                                  
              Seq.length st' == Seq.length st + 1 /\
                                  
              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\
                                  
              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\
                                  
              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\
                                               
              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 h_addr_succ g == white);
       push_to_stack2_lemma g st h_addr_succ;
       push_to_stack2_mem_lemma_black_nodes g st h_addr_succ;

       assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       //assert (heap_remains_same_except_index_v_id h_addr_succ g g');
      
       assert ((Seq.length g == Seq.length g'));
     
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

//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#push-options "--split_queries"

#restart-solver

let fieldPush_spec_body_well_formed_allocated_blocks_lemma  (g:heap{well_formed_heap2 g})
                                                            (st: seq Usize.t{G.is_vertex_set st /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                                  Seq.mem x st)})
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
      let h_addr_succ = hd_address succ in
      if color_of_object1 h_addr_succ g = white  then
      (
        assert (is_valid_header h_addr_succ g);
        valid_succ_color_lemma g h_addr_succ;
      
       assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
       assert (~(Seq.mem (f_address h_addr_succ) st));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
       
       let st', g' = push_to_stack2 g st  h_addr_succ in
       push_to_stack2_heap_state_lemma g st h_addr_succ;
       push_to_stack2_field_size_lemma g st h_addr_succ;
       push_to_stack2_well_formed_allocated_blocks_lemma g st h_addr_succ 2UL;
       assert (G.is_vertex_set st');
       assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
              (Seq.mem succ st') /\
                                  
              Seq.length st' == Seq.length st + 1 /\
                                  
              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\
                                  
              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\
                                  
              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\
                                               
              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 h_addr_succ g == white);
       push_to_stack2_lemma g st h_addr_succ;

       assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       //assert (heap_remains_same_except_index_v_id h_addr_succ g g');
      
       assert ((Seq.length g == Seq.length g'));
     
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

let fieldPush_spec_body_valid_header_visited_set_lemma  (g:heap{well_formed_heap2 g})
                                                        (st: seq Usize.t{G.is_vertex_set st /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                                  Seq.mem x st)})
                                                        (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                             is_valid_header h_index g})
                                          
                                                        (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                        (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                        (vl: seq Usize.t {(G.is_vertex_set vl) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl)
                                                                      
                                                                      
                                                                    }) 
                            : Lemma
                              (ensures ((forall y. Seq.mem y vl ==> is_valid_header (hd_address y) (snd (fieldPush_spec_body g st h_index wz i))))) = 
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
      let h_addr_succ = hd_address succ in
      if color_of_object1 h_addr_succ g = white  then
      (
        assert (is_valid_header h_addr_succ g);
        valid_succ_color_lemma g h_addr_succ;
      
       assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
       assert (~(Seq.mem (f_address h_addr_succ) st));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
       
       let st', g' = push_to_stack2 g st  h_addr_succ in
       push_to_stack2_heap_state_lemma g st h_addr_succ;
       push_to_stack2_field_size_lemma g st h_addr_succ;
       assert (G.is_vertex_set st');
       assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
              (Seq.mem succ st') /\
                                  
              Seq.length st' == Seq.length st + 1 /\
                                  
              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\
                                  
              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\
                                  
              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\
                                               
              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 h_addr_succ g == white);
       push_to_stack2_lemma g st h_addr_succ;
       push_to_stack2_visited_list_valid_header_lemma g st h_addr_succ vl;

       assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       //assert (heap_remains_same_except_index_v_id h_addr_succ g g');
      
       assert ((Seq.length g == Seq.length g'));
     
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


let fieldPush_spec_body_black_nodes_visited_set_lemma  (g:heap{well_formed_heap2 g})
                                                       (st: seq Usize.t{G.is_vertex_set st /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                                  Seq.mem x st)})
                                                       (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                             is_valid_header h_index g})
                                          
                                                       (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                       (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                       (vl: seq Usize.t {(G.is_vertex_set vl) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl)
                                                                      
                                                                      
                                                                    }) 
                            : Lemma
                              (ensures (forall y. Seq.mem (hd_address y) (objects2 0UL (snd (fieldPush_spec_body g st h_index wz i))) /\ 
                                                  isBlackObject1 (hd_address y) (snd (fieldPush_spec_body g st h_index wz i)) <==>  
                                                                                           Seq.mem y vl)) = 
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
      let h_addr_succ = hd_address succ in
      if color_of_object1 h_addr_succ g = white  then
      (
        assert (is_valid_header h_addr_succ g);
        valid_succ_color_lemma g h_addr_succ;
      
       assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
       assert (~(Seq.mem (f_address h_addr_succ) st));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
       
       let st', g' = push_to_stack2 g st  h_addr_succ in
       push_to_stack2_heap_state_lemma g st h_addr_succ;
       push_to_stack2_field_size_lemma g st h_addr_succ;
       assert (G.is_vertex_set st');
       assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
              (Seq.mem succ st') /\
                                  
              Seq.length st' == Seq.length st + 1 /\
                                  
              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\
                                  
              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\
                                  
              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\
                                               
              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 h_addr_succ g == white);
       push_to_stack2_lemma g st h_addr_succ;

       assert (G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st));
                                                             
       
       assert ((forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                         (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                         (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                         (G.is_vertex_set vl) /\
                                                                         (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==>
                                                                         Seq.mem x vl));
                                                                         
       push_to_stack_mem_lemma_black_nodes_visited_list_lemma g st h_addr_succ vl;
       assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       //assert (heap_remains_same_except_index_v_id h_addr_succ g g');
      
       assert ((Seq.length g == Seq.length g'));
     
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

//#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

//#push-options "--split_queries"

#restart-solver

//#reset-options "--z3rlimit 500"

#restart-solver

let fieldPush_spec_body_graph_lemma (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                                  Seq.mem x st)})
                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                             is_valid_header h_index g})
                                          
                                    (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                    (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (requires ((Seq.mem h_index (get_allocated_block_addresses g)) /\
                                     (well_formed_allocated_blocks g) /\
                                     (well_formed_allocated_blocks (snd (fieldPush_spec_body g st h_index wz i))) /\
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) (*/\
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (fieldPush_spec_body g st h_index wz i))) 
                                               (snd (fieldPush_spec_body g st h_index wz i)))*))) 
                                     
                          (ensures (create_graph_from_heap g == create_graph_from_heap (snd (fieldPush_spec_body g st h_index wz i)))) = 

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
      let h_addr_succ = hd_address succ in
      if color_of_object1 h_addr_succ g = white  then
      (
        assert (is_valid_header h_addr_succ g);
        valid_succ_color_lemma g h_addr_succ;
      
       assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
       assert (~(Seq.mem (f_address h_addr_succ) st));
       assert (~(Seq.mem succ st));
       
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st);
       
       let st', g' = push_to_stack2 g st  h_addr_succ in
       push_to_stack2_heap_state_lemma g st h_addr_succ;
       push_to_stack2_field_size_lemma g st h_addr_succ;
       assert (G.is_vertex_set st');
       assert (well_formed_heap2 g' /\
              (forall x. Seq.mem x st ==> Seq.mem x st') /\
                                  
              (Seq.mem succ st') /\
                                  
              Seq.length st' == Seq.length st + 1 /\
                                  
              (forall y. Seq.mem y st' ==> Usize.v y >= Usize.v mword /\ Usize.v y < heap_size) /\

              (forall y. Seq.mem y st' ==> Usize.v y % Usize.v mword == 0) /\
                                  
              (forall y. Seq.mem y st' ==> is_valid_header (hd_address y) g') /\
                                  
              (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st') /\
                                               
              (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                                  isGrayObject1 (hd_address x) g' <==>
                                  Seq.mem x st'));

       assert(forall (x:hp_addr{Usize.v x < heap_size}). getWosize (read_word g x) ==
                                               getWosize (read_word g' x));
     
       
       objects2_equal_lemma 0UL g g';
       assert (objects2 0UL g == objects2 0UL g');

       assert (color_of_object1 h_addr_succ g == white);
       push_to_stack2_lemma g st h_addr_succ;

       assert (G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st));
                                                             
       
       
                                                                         
       
       assert ((get_allocated_block_addresses g ==
                                            get_allocated_block_addresses g'));
                                            
       //assert (heap_remains_same_except_index_v_id h_addr_succ g g');
      
       assert ((Seq.length g == Seq.length g'));
       push_to_stack2_well_formed_allocated_blocks_lemma g st h_addr_succ 2UL;
       push_to_stack2_graph_lemma g st h_addr_succ;
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


let rec fieldPush_spec1   (g:heap{well_formed_heap2 g})
                          (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                         
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
                            
                            (forall x. Seq.mem x (fst st_hp) ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size)/\

                            (forall x. Seq.mem x (fst st_hp) ==> Usize.v x % Usize.v mword == 0) /\
                            
                            (forall x. Seq.mem x (fst st_hp) ==> is_valid_header (hd_address x) (snd st_hp)) /\
                            
                            (forall x. Seq.mem (hd_address x) (objects2 0UL (snd st_hp)) /\ isGrayObject1 (hd_address x) (snd st_hp) <==>
                                                   Seq.mem x (fst st_hp)) /\
                                                   
                            (forall x. Seq.mem x st ==> Seq.mem x (fst st_hp)) /\ (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                            
                            get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp))
                              
         (decreases ((Usize.v wz + 1) - Usize.v i)) = 
 if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

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
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));
       fieldPush_spec1 g' st' h_index wz i'
    )

#restart-solver 

#restart-solver

#restart-solver



#reset-options "--z3rlimit 1000"

#push-options "--split_queries"

#restart-solver

let rec fieldPush_spec1_fields_lemma1  (g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                         
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
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

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
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));
       fieldPush_spec_body_fields_lemma g st h_index wz i;
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st_hp = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec1_fields_lemma1 g' st' h_index wz i';
       ()
    )

let fieldPush_fieldPush_spec_body_lemma (g:heap{well_formed_heap2 g})
                                       (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                         
                                       
                         
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
                                         (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                         
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

#restart-solver



#restart-solver

#reset-options "--z3rlimit 1000"

#push-options "--split_queries"

#restart-solver

let rec fieldPush_spec1_black_nodes_lemma1   (g:heap{well_formed_heap2 g})
                                         (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                         
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
       
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       let st', g' = fieldPush_spec_body g st h_index wz i in
       

       fieldPush_spec_body_black_nodes_mem_lemma g st h_index wz i;
       fieldPush_spec_body_black_nodes_lemma g st h_index wz i;
       assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                          Seq.mem y (get_black_block_addresses g' 
                                                              (get_allocated_block_addresses g')));
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st_hp = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec1_black_nodes_lemma1 g' st' h_index wz i';
       assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses (snd st_hp) (get_allocated_block_addresses (snd st_hp))));
                                                                         
       
       
       assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses (snd (fieldPush_spec1 g' st' h_index wz i')) 
                                                      (get_allocated_block_addresses (snd (fieldPush_spec1 g' st' h_index wz i')))));
       
       assert (forall y. Seq.mem y (get_black_block_addresses g (get_allocated_block_addresses g)) <==>
                                         Seq.mem y (get_black_block_addresses (snd (fieldPush_spec1 g st h_index wz i)) 
                                                      (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i)))));
       ()
    )


                                                              
#restart-solver 

#restart-solver

#restart-solver 

let rec fieldPush_spec1_black_nodes_lemma (g:heap{well_formed_heap2 g})
                                          (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                         
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
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i >= 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st', g' = fieldPush_spec_body g st h_index wz i in
       fieldPush_spec_body_black_nodes_lemma g st h_index wz i;
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));
       
       let st'', g'' = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec1_black_nodes_lemma g' st' h_index wz i';
       assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                                 (get_black_block_addresses g'' (get_allocated_block_addresses g'')));
       ()
    )

#restart-solver 

#restart-solver

let rec fieldPush_spec1_well_formed_allocated_blocks_lemma  (g:heap{well_formed_heap2 g})
                                                            (st: seq Usize.t{G.is_vertex_set st /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                            Seq.mem x st)})
                         
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
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i >= 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st', g' = fieldPush_spec_body g st h_index wz i in
       fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
       
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
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
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                            Seq.mem x st)})
                         
                         
                                    (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                    is_valid_header h_index g})
                                           
                                    (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                    (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                        : Lemma
                          (requires ((Seq.mem h_index (get_allocated_block_addresses g)) /\
                                     (well_formed_allocated_blocks g) /\
                                     (well_formed_allocated_blocks (snd (fieldPush_spec1 g st h_index wz i))) /\
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                     (all_field_address_are_word_aligned (get_allocated_block_addresses (snd (fieldPush_spec1 g st h_index wz i))) 
                                                    (snd (fieldPush_spec1 g st h_index wz i)))))
                          
                          (ensures (create_graph_from_heap g == create_graph_from_heap (snd (fieldPush_spec1 g st h_index wz i)))) 
                          (decreases ((Usize.v wz + 1) - Usize.v i)) =  
 if Usize.v i = Usize.v wz + 1 then
    (
       let st_hp = (st,g) in
       assert(Seq.length g == Seq.length (snd st_hp));
       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st);

       assert (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g ==>
                                                  Seq.mem x st);
       assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

       assert (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp));
       ()
    )
  else
    (
       let i' = Usize.(i +^ 1UL) in
       assert (Usize.v i < Usize.v wz + 1);
       assert (Usize.v i >= 1);
       assert (Usize.v i' == Usize.v i + 1);
       assert (Usize.v i' <= Usize.v wz + 1);
       assert (Usize.v i' >= 1);
       let st', g' = fieldPush_spec_body g st h_index wz i in
       
       
       assert ((G.is_vertex_set st') /\
              (Seq.length g == Seq.length g') /\
               (well_formed_heap2 g') /\
               (forall x. Seq.mem x st' ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
               (forall x. Seq.mem x st' ==> is_valid_header (hd_address x) g'));

       assert ((forall x. Seq.mem (hd_address x) (objects2 0UL g') /\
                               isGrayObject1 (hd_address x) g' <==>
                                         Seq.mem x st'));
       
       let st'', g'' = fieldPush_spec1 g' st' h_index wz i' in
       fieldPush_spec_body_well_formed_allocated_blocks_lemma g st h_index wz i;
       fieldPush_spec_body_graph_lemma g st h_index wz i;
        
       fieldPush_spec1_well_formed_allocated_blocks_lemma g' st' h_index wz i';
       assert (all_field_address_are_word_aligned (get_allocated_block_addresses g'') g'');
       fieldPush_spec1_graph_lemma g' st' h_index wz i';
       ()
     
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

#restart-solver 

let h_index_within_limits (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                          (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g))}) = 
 (is_fields_within_limit1 h_index (getWosize (read_word g h_index))) /\
 (is_fields_contents_within_limit2 h_index (getWosize (read_word g h_index)) g) /\
   (forall j.  Usize.v j > 0 /\ Usize.v j <= Usize.v (getWosize (read_word g h_index)) ==> 
                          (Usize.v h_index  + (Usize.v j  * Usize.v mword)) % Usize.v mword == 0)                                                            
                                                                       
                                                                       
#restart-solver 

#restart-solver 

let rec graph_successors_create_from_an_index (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                                                     h_index_within_limits g h_index})
                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
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
   assert (s_list' == Seq.slice (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v i) (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))));
   s_list'
 )
                                                              
let graph_successors_create_from_an_index_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                                                     h_index_within_limits g h_index})
                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                    (i:Usize.t {Usize.v i < Seq.length f}) 
                                  : Lemma
                                    (ensures (Seq.head (graph_successors_create_from_an_index g h_index f i) == Seq.index f (Usize.v i))) = ()                            
                           
#restart-solver 

let graph_successors_create_from_an_index_lemma1 (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                                                     h_index_within_limits g h_index})
                                              (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
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
       
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
       ()
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
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
        assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (objects2 0UL g));
        assert (is_valid_header (hd_address succ) g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        
        let s_list' = create_successors_list_for_h_index g h_index wz i' in
        

        lemma_tl succ s_list'; 
        
        let s_list = Seq.cons succ s_list' in 
        
        assert (Seq.head s_list == succ);

        
      
        ()
      )
      else
      (
        assert (Usize.v i' > 1);
        (*assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);*)
        let s_list = create_successors_list_for_h_index g h_index wz i' in
        ()
      )
    )

#restart-solver 

#restart-solver 

#restart-solver

let slice_lemma (#a:Type)
                (s:seq a)
       : Lemma 
         (ensures s == Seq.slice s 0 (Seq.length s)) = ()


#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

let graph_successors_create_from_index_0_equals_graph_successors (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                                 (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                                                     h_index_within_limits g h_index})
                                                                 
                                        : Lemma
                                          (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                    (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                    (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
                                                    0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)))
                                          (ensures G.successors (create_graph_from_heap g) (f_address h_index) == 
                                                    graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL) = 
let s_list' =  graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL in
assert (s_list' == Seq.slice (G.successors (create_graph_from_heap g) (f_address h_index)) 0 (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))));
slice_lemma (G.successors (create_graph_from_heap g) (f_address h_index));
assert (G.successors (create_graph_from_heap g) (f_address h_index) == 
         Seq.slice (G.successors (create_graph_from_heap g) (f_address h_index)) 0 (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))));
assert (G.successors (create_graph_from_heap g) (f_address h_index) == 
         graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL);
()
                                          
let graph_successors_from_0_and_heap_field_pointers_from_1_are_equal (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                                     (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                                                     h_index_within_limits g h_index})
                               
                                : Lemma
                                  (requires (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                    (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                    (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v (getWosize (read_word g h_index))) /\
                                                    0 <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)))
                                  (ensures graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) 0UL ==
                                                create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) 1UL) = 
graph_successors_create_from_index_0_equals_graph_successors g h_index;
graph_successors_heap_create_successor_list_equivalence_lemma g h_index;
()

#reset-options "--z3rlimit 500"
#push-options "--split_queries"

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

#restart-solver 

let graph_successors_create_from_an_index_empty_lemma (g: heap {well_formed_heap2 g /\ well_formed_allocated_blocks g})
                                                      (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                     (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                     is_valid_header h_index g /\
                                                                                     (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                                                     h_index_within_limits g h_index})
                                                      (f: seq Usize.t{(all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                              (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                              (f == G.successors (create_graph_from_heap g) (f_address h_index)) /\
                                                              (Seq.length f <= Usize.v (getWosize (read_word g h_index)))})
                                                      (i:Usize.t {Usize.v i <= Seq.length f})
                            : Lemma
                              (ensures (graph_successors_create_from_an_index g h_index f i) == Seq.empty ==>
                                             Usize.v i == Seq.length f) = ()



#reset-options "--z3rlimit 50 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Seq'"

#restart-solver

let create_successors_list_for_h_index_i_equals_wz_plus_one_implies_succ_list_from_j_is_empty (g:heap{well_formed_heap2 g})
                                                                                              (st: seq Usize.t{G.is_vertex_set st /\
                                                                                                   (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                                                   (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                                                   (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                                (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                            Seq.mem x st)})
                         
                                                                                               (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                               is_valid_header h_index g
                                                                                                               })
                                           
                                                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                               (i:Usize.t{Usize.v i == Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                               (j:Usize.t)
                                          : Lemma
                                            (requires (well_formed_allocated_blocks g) /\
                                          
                                                      (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                      
                                            
                                                       h_index_within_limits g h_index /\
                                                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                       (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                       (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                       (Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                       (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i))
                                            (ensures Usize.v j == Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) = 
create_successors_list_for_h_index_recursing_property_lemma2 g h_index wz i;
assert (create_successors_list_for_h_index g h_index wz i == Seq.empty);
assert ((graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) == Seq.empty);
graph_successors_create_from_an_index_empty_lemma g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j;
assert (Usize.v j == Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)));
()

#restart-solver




let create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j (g:heap{well_formed_heap2 g})
                                                                                              (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                                               (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                                               is_valid_header h_index g
                                                                                                               })
                                           
                                                                                              (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                                                              (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                                                              (j:Usize.t) 
                                               : Lemma
                                                 (requires (well_formed_allocated_blocks g) /\
                                          
                                                      (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                      
                                            
                                                       h_index_within_limits g h_index /\
                                                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                       (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                       (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                       (Usize.v j <= Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                       (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                       Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0)
                                            (ensures (let s_heap_i = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) in
                                                      let s_graph_j = (graph_successors_create_from_an_index g h_index 
                                                                          (G.successors (create_graph_from_heap g) (f_address h_index)) j) in
                                                       let hd = Seq.head s_heap_i in
                                                       let hd1 = Seq.head s_graph_j in
                                                      
                                                       let tl = Seq.tail s_heap_i in
                                                       let tl1 = Seq.tail s_graph_j in
                                                       (hd == hd1) /\ (tl == tl1))) = ()


#push-options "--z3rlimit 1000"

#reset-options "--z3rlimit 1000"

#restart-solver

let field_ptr_construct (g:heap{well_formed_heap2 g /\ well_formed_allocated_blocks g}) 

                        (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                            (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                            is_valid_header h_index g /\
                                                            (Seq.mem h_index (get_allocated_block_addresses g))})
                                           
                        (wz: wosize{wz == getWosize (read_word g h_index) /\ h_index_within_limits g h_index})
                         
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
                                            
                                                       h_index_within_limits g h_index /\
                                                       (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                       (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                       (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                       (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                       (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                       
                                                       (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                        (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                        (isPointer(Usize.add h_index (Usize.mul i mword)) g) /\
                                                        Seq.length (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) > 0
                                                     )
                                              (ensures (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                        read_word g (Usize.add h_index (Usize.mul i mword)))) = 
 graph_successors_create_from_an_index_lemma g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j;
 create_successors_list_for_h_index_from_i_index_lemma g h_index wz i; 
 create_successors_list_for_h_index_i_index_equals_graph_successors_create_from_an_index_j g h_index wz i j;
 assert (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         read_word g (Usize.add h_index (Usize.mul i mword)));
 ()



#reset-options "--z3rlimit 1000"
#restart-solver


#restart-solver

#push-options "--split_queries"

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
       
       assert (Seq.length s_list == 0);
       assert (Seq.length s_list == (Usize.v wz + 1) - Usize.v i);
      
       ()
    )
  else
    (
      let i' = Usize.(i +^ 1UL) in
      assert (is_valid_header h_index g);  
      assert (Usize.v i < Usize.v wz + 1);
      assert (Usize.v i' <= Usize.v wz + 1);
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
        assert (Seq.mem (hd_address (read_word g (Usize.add h_index (Usize.mul i mword)))) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (get_allocated_block_addresses g));
        assert (Seq.mem (hd_address succ) (objects2 0UL g));
        assert (is_valid_header (hd_address succ) g);

        assert (well_formed_allocated_blocks g);
        assert (Seq.mem h_index (get_allocated_block_addresses g));

        assert (Usize.v i' > 1);
        assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);
        
        let s_list' = create_successors_list_for_h_index g h_index wz i' in
        

        lemma_tl succ s_list'; 
        
        let s_list = Seq.cons succ s_list' in 
        
        assert (Seq.head s_list == succ);

        
      
        ()
      )
      else
      (
        assert (Usize.v i' > 1);
        (*assert (Usize.v i < Usize.v wz + 1);
        assert (Usize.v i' <= Usize.v wz + 1);*)
        let s_list = create_successors_list_for_h_index g h_index wz i' in
        ()
      )
    )

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
                                            
                                                      (h_index_within_limits g h_index) /\
                                                      (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                      (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                      
                                                      (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                      (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                     
                                                      
                                                      (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) ==
                                                      (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) /\
                                                      (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                      (isPointer(Usize.add h_index (Usize.mul i mword)) g)
                                                     )
                                             (ensures (let i' = Usize.add i 1UL in
                                                       let j' = Usize.add j 1UL in
                                                       (graph_successors_create_from_an_index g h_index ((G.successors (create_graph_from_heap g) (f_address h_index))) j' == 
                                                        create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i')))  = 
 let i' = Usize.add i 1UL in
 let j' = Usize.add j 1UL in

 let s_heap_i = (create_successors_list_for_h_index g h_index (getWosize (read_word g h_index)) i) in
 let s_graph_j =  (graph_successors_create_from_an_index g h_index (G.successors (create_graph_from_heap g) (f_address h_index)) j) in
 
 let sl = (G.successors (create_graph_from_heap g) (f_address h_index)) in
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

#restart-solver 

#reset-options "--z3rlimit 100 --max_fuel 2 --max_ifuel 4 --using_facts_from '* -FStar.Seq'"


#restart-solver

#restart-solver


#restart-solver



let fieldPush_spec_body_successor_push_body_equivalence_lemma2 (g:heap{well_formed_heap2 g})
                                                               (st: seq Usize.t{G.is_vertex_set st /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                                  Seq.mem x st)})
                                                               (h_index:hp_addr {Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                 is_valid_header h_index g})
                                          
                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                               (j:Usize.t)
                                                               (vl: seq Usize.t {(G.is_vertex_set vl) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl)
                                                                      
                                                                      
                                                                    }) 
                                        : Lemma
                                        (requires (well_formed_allocated_blocks g) /\
                                          
                                                  (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                  
                                                  
                                            
                                                  (h_index_within_limits g h_index) /\
                                                  (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                                  (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                      
                                                     
                                                  (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                  (Usize.v j < Seq.length (G.successors (create_graph_from_heap g) (f_address h_index))) /\
                                                  (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                                  (isPointer(Usize.add h_index (Usize.mul i mword)) g ==> 
                                                         (Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) == 
                                                         read_word g (Usize.add h_index (Usize.mul i mword)))) /\
                                                  (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                                  (forall x. Seq.mem x vl ==> ~(Seq.mem x st)))
                                          
                                          (ensures (fst (fieldPush_spec_body g st h_index wz i) == 
                                                       ( if (isPointer(Usize.add h_index (Usize.mul i mword)) g) then
                                                                (
                                                                      G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) 
                                                                                              (vl) 
                                                                                              (st) 
                                                                                              (Usize.v j)
                                                                )
                                                               else
                                                                (
                                                                      st
                                                                )))) = 
   assert (well_formed_heap2 g);
       
   field_limits_allocated_blocks_lemma g;
   field_contents_within_limits_allocated_blocks_lemma g;
       
   fieldaddress_within_limits_lemma_x_all g;
       
   let succ_index = Usize.add h_index (Usize.mul i mword) in
       
   max_wosize_times_mword_multiple_of_mword i;
   sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);

   assert (Usize.v succ_index % Usize.v mword == 0);
   assert (is_hp_addr succ_index);

   lemma_len_slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = ((Usize.v succ_index) + (Usize.v mword)) - (Usize.v succ_index));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = (Usize.v mword));
   assert (length (slice g (Usize.v succ_index) ((Usize.v succ_index) + (Usize.v mword))) = 8); 
   
   let succ = read_word g succ_index in
   let succ1 = Seq.index (G.successors (create_graph_from_heap g) (f_address h_index)) (Usize.v j) in
   assert (succ == read_word g succ_index);
   
   if isPointer succ_index g  then
    (
       assert (succ == succ1);
       let h_addr_succ = hd_address succ in
       
       if color_of_object1 h_addr_succ g = white  then
       (
         valid_succ_color_lemma g h_addr_succ;
         assert (~(isGrayObject1 h_addr_succ g) /\ ~(isBlackObject1 h_addr_succ g));
         assert (~(Seq.mem (f_address h_addr_succ) st));
         assert (~(Seq.mem succ st));
         let st', g' = push_to_stack2 g st  h_addr_succ in
         push_to_stack2_heap_state_lemma g st h_addr_succ;
         push_to_stack2_field_size_lemma g st h_addr_succ;
         assert (~(Seq.mem (f_address h_addr_succ) vl));
         assert (f_address h_addr_succ == succ);
         test_allocs g h_index wz;
         assert (Seq.mem h_addr_succ (get_allocated_block_addresses g));
         push_to_stack_heap_and_push_to_graph_equality_lemma1 g st h_addr_succ vl;
         let st1 = G.push_to_stack_graph1 vl st succ in
         assert (st' == G.push_to_stack_graph1 vl st succ);
         //objects2_equal_lemma 0UL g g';
         //push_to_stack2_lemma g st h_addr_succ;
         let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j) in
         assert (st'' == G.push_to_stack_graph1 vl st succ);
         assert (st'' == st1);
         assert (st' == st1);
         assert (st' == st'');
         assert (fst (push_to_stack2 g st h_addr_succ) == st'');
         assert (fst (fieldPush_spec_body g st h_index wz i) == st'');
         assert (fst (fieldPush_spec_body g st h_index wz i) == G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st (Usize.v j));
         assert (isPointer(Usize.add h_index (Usize.mul i mword)) g);
         ()
       )
       else
       (
         let st' = st in
         let st'' = G.successor_push_body1 (G.successors (create_graph_from_heap g) (f_address h_index)) vl st  (Usize.v j) in
         assert (st'' == st);
         assert (st'' == st');
         ()
       )
    )
   else
   (
      ()
   )


let fieldPush_spec_body_successor_push_body_equivalence_lemma3 (g:heap{well_formed_heap2 g})
                                                               (st: seq Usize.t{G.is_vertex_set st /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                            (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                                            (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                                            (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                                  Seq.mem x st)})
                                                               (h_index:hp_addr {Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                 is_valid_header h_index g})
                                          
                                                               (wz:wosize{Usize.v wz == Usize.v (getWosize (read_word g h_index))})
                         
                                                               (i:Usize.t{Usize.v i < Usize.v wz + 1 /\ Usize.v i >= 1})
                                                               
                                                               (vl: seq Usize.t {(G.is_vertex_set vl) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                                      (forall x. Seq.mem x vl ==> Usize.v x % Usize.v mword == 0) /\
                                                                      (forall x. Seq.mem x vl ==> is_valid_header (hd_address x) g) /\
                                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isBlackObject1 (hd_address x) g <==> Seq.mem x vl)
                                                                      
                                                                      
                                                                    }) 
                                : Lemma
                                  (requires ((well_formed_allocated_blocks g) /\
                                          
                                             (Seq.mem h_index (get_allocated_block_addresses g)) /\
                                                  
                                             (h_index_within_limits g h_index) /\
                                             (all_field_address_are_word_aligned (get_allocated_block_addresses g) g) /\
                                             (Seq.mem (f_address h_index) (create_graph_from_heap g).vertices) /\
                                                      
                                                     
                                             (Seq.length (G.successors (create_graph_from_heap g) (f_address h_index)) <= Usize.v wz) /\
                                                     
                                                 
                                             (is_hp_addr (Usize.add h_index (Usize.mul i mword))) /\
                                             ( ~(isPointer(Usize.add h_index (Usize.mul i mword)) g)) /\
                                                  
                                             (forall x. Seq.mem x st ==> ~(Seq.mem x vl)) /\
                                             (forall x. Seq.mem x vl ==> ~(Seq.mem x st))))
                                        (ensures (fst (fieldPush_spec_body g st h_index wz i) == st)) = ()   
                                            
                                            
#restart-solver

#restart-solver 

#push-options "--split_queries"

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
     field_reads_all_equal_for_all_objects_lemma g g' v_id;
     field_reads_all_equal_h_index_lemma g g' v_id;
     let succ_index = Usize.add h_index (Usize.mul i mword) in

     assert (Usize.v i < Usize.v wz + 1);
     assert (well_formed_allocated_blocks g');

     assert (is_fields_within_limit1 h_index wz);

     assert (Usize.v h_index + (((Usize.v wz + 1) * Usize.v mword) - 1) < heap_size);

     assert (Usize.v i < Usize.v wz + 1);

     assert (Usize.v h_index + (Usize.v i * Usize.v mword) < heap_size);
     
     assert (Usize.v succ_index < heap_size);
     
     field_limits_allocated_blocks_lemma g;
     field_contents_within_limits_allocated_blocks_lemma g;
     fieldaddress_within_limits_lemma_x_all g;
     
     max_wosize_times_mword_multiple_of_mword i;
     sum_of_multiple_of_mword_is_multiple_of_mword h_index (Usize.mul i mword);

     //assert (Usize.v succ_index < heap_size);
     
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

#push-options "--split_queries"

#restart-solver


let push_to_stack2_create_successors_for_h_index_lemma  (g:heap{well_formed_heap2 g (*/\ well_formed_allocated_blocks g*)})
                                                        (st: seq Usize.t{G.is_vertex_set st /\
                                                             (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                             (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                             (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                             (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                                Seq.mem x st)})
                                    
                    
                                                        (x: hp_addr{
                                                                      (Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                       
                                                                       (Usize.v x % Usize.v mword == 0) /\
                                                                       is_valid_header x g /\ 
                                                                       ~(Seq.mem (f_address x) st)
                                                                       })
                                                       (c:color{c == 2UL})

                                                       (h_index:hp_addr{Usize.v h_index >= 0 /\ Usize.v h_index < heap_size /\
                                                                                    (Usize.v h_index % Usize.v mword == 0) /\
                                         
                                                                                    is_valid_header h_index g /\
                                                                                    (Seq.mem h_index (get_allocated_block_addresses g))})

                                                       (wz: wosize{wz == getWosize (read_word g h_index)})
                                                       (wz1: wosize{(wz1 == getWosize (read_word (snd (push_to_stack2 g st x)) h_index))})

                                                
                                                       (i:Usize.t{Usize.v i <= Usize.v wz + 1 /\ Usize.v i >= 1})
                                     : Lemma
                                        (requires (wz == wz1) /\ 
                                                  (is_fields_within_limit1 x (getWosize (read_word g x))) /\
                                                  (color_of_object1 x g == white) /\
                                                  (Seq.mem x (get_allocated_block_addresses g)) /\
                                                  well_formed_allocated_blocks g /\
                                                  well_formed_allocated_blocks (snd (push_to_stack2 g st x)) /\
                                                  (h_index_within_limits g h_index) /\
                                                  (h_index_within_limits (snd (push_to_stack2 g st x)) h_index))
                                        (ensures create_successors_list_for_h_index g h_index wz i == 
                                                   create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i) = 
if Seq.length st = 0 then
(
   let f_x = f_address x in
   let stk' = Seq.create 1 f_x in

   
   let g' = colorHeader1 x g gray in 

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
    

    (*assert (well_formed_allocated_blocks g');
    
    assert (Seq.mem x stk');
    G.is_vertex_set_lemma2 stk';
    assert (G.is_vertex_set stk');*)
    (*create_succcessors_for_h_index_lemma1 g h_index wz i x c g' wz1;
    assert (create_successors_list_for_h_index g h_index wz i == 
             create_successors_list_for_h_index (snd (push_to_stack2 g st x)) h_index wz1 i);
    ()*)
    admit()
)
    
else
(

  admit()
)


(*let push_to_stack2_well_formed_allocated_blocks_lemma  (g:heap{well_formed_heap2 g})
                                    (st: seq Usize.t{G.is_vertex_set st /\
                                                      (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                                      (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                                      (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                                      (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                             Seq.mem x st)})
                                    
                                    (x: hp_addr{(Usize.v x >= 0 /\ Usize.v x < heap_size) /\
                                                                (Usize.v x % Usize.v mword == 0) /\
                                                                is_valid_header x g /\
                                                                ~(Seq.mem (f_address x) st) /\ color_of_object1 x g == white /\
                                                                       (Seq.mem x (get_allocated_block_addresses g))})
                                                       (c:color{c == 2UL})
                                   : Lemma
                                     (requires well_formed_allocated_blocks g)
                                     (ensures (well_formed_allocated_blocks (snd (push_to_stack2 g st x)))) = *)

(*Lemma for test purpose*)
let rec subset_of_each_other1_helper (s1: seq Usize.t{G.is_vertex_set s1})
                              (s2:  seq Usize.t{G.is_vertex_set s2})
           :Lemma 
            (requires (length s1 > 0) /\
                      (forall x. Seq.mem x s1 ==> is_hp_addr x) /\
                      (forall x. Seq.mem x s1 ==> UInt.fits (Usize.v x - Usize.v mword) Usize.n) /\
                      (forall x. Seq.mem x s1 ==> Seq.mem (hd_address x) s2)) 
            (ensures True) = 
 assert (Seq.mem (hd_address (head s1)) s2);
 assert (forall x. Seq.mem x (tail s1) ==> Seq.mem (hd_address x) s2);
 admit()

#restart-solver 

#restart-solver 

#restart-solver

let stack_less_than_heap_size_when_one_non_gray_exists (g:heap{well_formed_heap2 g})
                                                       (st:seq Usize.t)
                                                       (x:Usize.t)
                                  : Lemma
                                    (requires  (forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                               (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                               (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                               (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ (color_of_object1 (hd_address x) g == gray) <==>
                                                  Seq.mem x st) /\
                                    
                                               (G.is_vertex_set st) /\
                                    
                                               (Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g <> gray)))
                                    
                                    (ensures (Seq.length st < heap_size)) = 

 assert (Seq.mem x (objects2 0UL g) /\ (color_of_object1 x g <> gray));
 assert (~(Seq.mem (f_address x) st));
 let blocks = objects2 0UL g in
 get_block_address_length_lemma g;
 assert (Seq.length blocks <= heap_size);
 assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) blocks);
 //assert (G.subset_vertices st blocks);
 assert (G.is_vertex_set st);
 assert (G.is_vertex_set blocks);
 assert (forall x. Seq.mem x st ==> UInt.fits (Usize.v x - Usize.v mword) Usize.n);
 assert (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g); 
 assert (forall x. Seq.mem x st ==> Seq.mem (hd_address x) blocks); 
 assert (G.subset_vertices_variant st blocks);
 G.subset_variant_lemma st blocks;
 assert (Seq.length st <= Seq.length blocks);
 assert (Seq.length st <= heap_size);
 if Seq.length st < heap_size then ()
 else
   (
     assert (Seq.length st == heap_size);
     assert (Seq.length st == Seq.length blocks);
     assert  (forall x. Seq.mem x st ==> Seq.mem (hd_address x) blocks);
     assert (forall x. Seq.mem x st ==> is_hp_addr x);
     G.subset_of_each_other1 st blocks;
     assert (forall x. Seq.mem x blocks ==> Seq.mem (f_address x) st);
     assert (Seq.mem (f_address x) st);
     ()
   )

let all_mem_implies_subset (s1:seq Usize.t)
                           (s2:seq Usize.t)
                   : Lemma
                     (requires (G.is_vertex_set s1 /\
                                G.is_vertex_set s2 /\
                                (forall x. Seq.mem x s1 ==> Seq.mem x s2)))
                     (ensures (G.subset_vertices s1 s2)) = ()

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
                               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
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

#restart-solver

let mark5_body (g:heap{well_formed_heap2 g}) 
               (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                    (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st)
                                    })
           : Pure (stack_heap_pair)
             (requires (~(G.is_emptySet st)))
             (ensures (fun st_hp -> G.is_vertex_set (fst st_hp) /\
                                (Seq.length g == Seq.length (snd st_hp)) /\
                                well_formed_heap2 (snd st_hp) /\
                                (forall x. Seq.mem x (fst st_hp) ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                (forall x. Seq.mem x (fst st_hp) ==> Usize.v x % Usize.v mword == 0) /\
                                (forall x. Seq.mem x (fst st_hp) ==> is_valid_header (hd_address x) (snd st_hp)) /\
                                (forall x. Seq.mem (hd_address x) (objects2 0UL (snd st_hp)) /\
                                        isGrayObject1 (hd_address x) (snd st_hp) <==>
                                                Seq.mem x (fst st_hp)) /\
                                (objects2 0UL g == objects2 0UL (snd st_hp)) /\
                                (get_allocated_block_addresses g == get_allocated_block_addresses (snd st_hp)))) = 
 assert (~(G.is_emptySet st));
 let v_id = Seq.index st (Seq.length st - 1) in
 let s = Seq.slice st 0 (Seq.length st - 1) in
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
   
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 G.is_vertex_set_lemma3 st;
 assert (forall x. Seq.mem x s ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 let g' = colorHeader1 h_v_id g black in
 assert (color_of_object1 h_v_id g' == black);
   
 let f = objects2 0UL g in
 let f' = objects2 0UL g' in
 assert (f == f');
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 Seq.lemma_mem_snoc s v_id;
 assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem (hd_address x) (objects2 0UL g) /\
                                                        isGrayObject1 (hd_address x) g);
 
 assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
 assert (color_of_object1 h_v_id g' == 3UL);
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (forall x. Seq.mem x s <==> Seq.mem (hd_address x) (objects2 0UL g') /\
                                                        isGrayObject1 (hd_address x) g');
 
 let wz = wosize_of_object1 h_v_id g' in
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));
 assert (Usize.v wz == Usize.v (getWosize (read_word g' h_v_id)));
 assert (well_formed_heap2 g');
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                             Seq.mem x s);
 assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size);
 assert (Usize.v h_v_id % Usize.v mword == 0);
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));
 let st1, g1 = fieldPush_spec1 g' s h_v_id wz 1UL in
 assert (G.is_vertex_set st1);
 assert (Seq.length g == Seq.length g1);
 assert (well_formed_heap2 g1);
 assert (forall x. Seq.mem x st1 ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st1 ==> is_valid_header (hd_address x) g1);
 assert (forall x. Seq.mem x st1 ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g1) /\ isGrayObject1 (hd_address x) g1 <==>
                                                Seq.mem x st1);
 assert (forall x. Seq.mem x s ==> Seq.mem x st1);
  
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
                                  (st: seq Usize.t {(forall x. Seq.mem x st ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size) /\
                                    (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g) /\
                                    (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0) /\
                                    (G.is_vertex_set st) /\
                                    (forall x. Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g <==>
                                                  Seq.mem x st) /\
                                    Seq.length st > 0
                                    })
                                
           : Lemma
             (requires 
                       (forall x. Seq.mem (hd_address x) (objects2 0UL (colorHeader1 (hd_address (Seq.index st (Seq.length st - 1))) g black)) /\ 
                                   isGrayObject1 (hd_address x) (colorHeader1 (hd_address (Seq.index st (Seq.length st - 1))) g black) <==>
                                          Seq.mem x (Seq.slice st 0 (Seq.length st - 1))))
                                    
            (ensures Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
                      Seq.length (get_black_block_addresses (snd (mark5_body g st)) (get_allocated_block_addresses (snd (mark5_body g st))))) = 
 assert (~(G.is_emptySet st));
 let v_id = Seq.index st (Seq.length st - 1) in
 let s = Seq.slice st 0 (Seq.length st - 1) in
 let h_v_id = hd_address v_id in
 assert (color_of_object1 h_v_id g == gray);
   
 assert (Seq.equal s (Seq.slice st 0 (Seq.length st - 1)));

  
 assert (well_formed_heap2 g);
 slice_mem_lemma st s;
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x s ==> Seq.mem x st);
 G.is_vertex_set_lemma3 st;
 assert (forall x. Seq.mem x s ==> Seq.mem (hd_address x) (objects2 0UL g) /\ isGrayObject1 (hd_address x) g);

 assert (forall x. Seq.mem x s ==> color_of_object1 (hd_address x) g == gray);
 assert (is_valid_header h_v_id g); 
 let g' = colorHeader1 h_v_id g black in
 assert (color_of_object1 h_v_id g' == black);
   
 let f = objects2 0UL g in
 let f' = objects2 0UL g' in
 assert (f == f');
 get_allocated_block_addresses_lemma g g' h_v_id black;
 assert (get_allocated_block_addresses g == get_allocated_block_addresses g');
 
 assert (G.is_vertex_set s);
 G.is_vertex_set_lemma5 st;
 assert (~(Seq.mem v_id s));
 Seq.lemma_mem_snoc s v_id;
 assert (forall x. Seq.mem x s \/ (x == v_id) <==> Seq.mem (hd_address x) (objects2 0UL g) /\
                                                        isGrayObject1 (hd_address x) g);
 
 assert (all_mem_st_mem_st__except_v_id_in_stack v_id st s);
 assert (color_of_object1 h_v_id g' == 3UL);
 objects2_equal_lemma 0UL g g';
 assert (objects2 0UL g == objects2 0UL g');
 assert (forall x. Seq.mem x s <==> Seq.mem (hd_address x) (objects2 0UL g') /\
                                                        isGrayObject1 (hd_address x) g');
 
 let wz = wosize_of_object1 h_v_id g' in
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));
 assert (Usize.v wz == Usize.v (getWosize (read_word g' h_v_id)));
 assert (well_formed_heap2 g');
 assert (forall x. Seq.mem x s ==> Usize.v x >= Usize.v mword /\ Usize.v x < heap_size);
 assert (forall x. Seq.mem x st ==> Usize.v x % Usize.v mword == 0);
 assert (forall x. Seq.mem x st ==> is_valid_header (hd_address x) g');
 assert (forall x. Seq.mem (hd_address x) (objects2 0UL g') /\ isGrayObject1 (hd_address x) g' <==>
                                                             Seq.mem x s);
 assert (Usize.v h_v_id >= 0 /\ Usize.v h_v_id < heap_size);
 assert (Usize.v h_v_id % Usize.v mword == 0);
 assert (is_valid_header h_v_id g');
 assert (Usize.v wz == Usize.v (getWosize (read_word g h_v_id)));
 let st1, g1 = fieldPush_spec1 g' s h_v_id wz 1UL in  
 colorHeader1_subset_lemma h_v_id g;
 assert (G.subset_vertices (get_black_block_addresses g (get_allocated_block_addresses g))
                             (get_black_block_addresses g' (get_allocated_block_addresses g')));

 colorHeader1_black_nodes_lemma  g h_v_id;

 assert (Seq.length (get_black_block_addresses g (get_allocated_block_addresses g)) <
           Seq.length (get_black_block_addresses g' (get_allocated_block_addresses g')));
 admit()

