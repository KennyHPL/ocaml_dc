(* $Id: bigint.ml,v 1.5 2014-11-11 15:06:24-08 - - $ *)
(*Kenny Luu*)
(*kepluu@ucsc.edu*)
(*asg2*)

open Printf

module Bigint = struct

    type sign     = Pos | Neg
    type bigint   = Bigint of sign * int list
    let  radix    = 10
    let  radixlen =  1

    let car       = List.hd
    let cdr       = List.tl
    let map       = List.map
    let reverse   = List.rev
    let strcat    = String.concat
    let strlen    = String.length
    let strsub    = String.sub
    let zero      = Bigint (Pos, [])

   
    let charlist_of_string str = 
        let last = strlen str - 1
        in  let rec charlist pos result =
            if pos < 0
            then result
            else charlist (pos - 1) (str.[pos] :: result)
        in  charlist last []

    let bigint_of_string str =
        let len = strlen str
        in  let to_intlist first =
                let substr = strsub str first (len - first) in
                let digit char = int_of_char char - int_of_char '0' in
                map digit (reverse (charlist_of_string substr))
            in  if   len = 0
                then zero
                else if   str.[0] = '_'
                     then Bigint (Neg, to_intlist 1)
                     else Bigint (Pos, to_intlist 0)

    let string_of_bigint (Bigint (sign, value)) =
        match value with
        | []    -> "0"
        | value -> let reversed = reverse value
                   in  strcat ""
                       ((if sign = Pos then "" else "-") ::
                        (map string_of_int reversed))

(*Removes the trailing zeroes (canonicalize)*)
    let canon list =
        let rec canon' list' = match list' with
            | []       -> []
            | [0]      -> []
            | car::cdr ->
                 let cdr' = canon' cdr
                 in  match car, cdr' with
                     | 0, [] -> []
                     | car, cdr' -> car::cdr'
        in canon' list

(*Comparison function*)
(*Returns -1 if l1 < l2*)
    let rec cmp list1 list2 =
        if (List.length list1) > (List.length list2) then 1
        else if (List.length list1) < (List.length list2) then -1
        else match (list1,list2) with
        | [],[]          -> 0 
        | list1,[]       -> 1
        | [],list2       -> -1
        | list1,list2    ->
            let list1' = reverse list1 in
            let list2' = reverse list2 in
                if (car list1') > (car list2') then 1
                else if (car list1') < (car list2') then -1
                else cmp (reverse(cdr list1')) (reverse (cdr list2'))

    let rec add' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0       -> list1
        | [], list2, 0       -> list2
        | list1, [], carry   -> add' list1 [carry] 0
        | [], list2, carry   -> add' [carry] list2 0
        | car1::cdr1, car2::cdr2, carry ->
          let sum = car1 + car2 + carry
          in  sum mod radix :: add' cdr1 cdr2 (sum / radix)


    let rec sub' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0       -> list1
        | [], list2, 0       -> list2
        | list1, [], carry   -> canon(sub' list1 [carry] 0)
        | [], list2, carry   -> canon(sub' [carry] list2 0)
        | car1::cdr1, car2::cdr2, carry ->
          if (car1 - carry) < car2
          then let diff = (radix + car1) - (car2 + carry)
               in  diff mod radix ::canon(sub' cdr1 cdr2 1)
          else let diff = car1 - car2 - carry
               in  diff mod radix ::canon(sub' cdr1 cdr2 0)
    
    let add (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if neg1 = neg2
        then Bigint (neg1, add' value1 value2 0)
        else let comp = cmp value1 value2 in
            if comp > 0 
               then Bigint(neg1, canon(sub' value1 value2 0))
            else if comp < 0 
               then Bigint(neg2, canon(sub' value2 value1 0)) 
            else zero 

    let sub (Bigint (neg1, value1)) (Bigint (neg2, value2)) = 
        if neg1 = neg2
        then (if (cmp value1 value2) > 0
             then Bigint (Pos, canon (sub' value1 value2 0))
             else Bigint (Neg, canon (sub' value2 value1 0)))
        else if neg2 = Neg
             then Bigint (Pos, add' value1 value2 0)
        else if neg1 = Neg
             then Bigint (Neg, add' value1 value2 0)
        else zero

(*doubles the number*)     
    let double list1 =
        add' list1 list1 0

(*Multiplication using egyptian algorithm*)
    let rec mul' (multiplier, powerof2, multiplicand') =
        if cmp multiplier powerof2 < 0
        then multiplier, [0]
        else let remainder, product =
            mul'(multiplier,double powerof2, double multiplicand')
            in if cmp remainder powerof2 < 0
            then remainder, product
            else sub' remainder powerof2 0, add' product multiplicand' 0

(*Multiplication fnc returns an int list * int list*)
    let mul (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        let sign = if neg1 = neg2 then Pos else Neg in
        let _, product = mul' (value1, [1], value2)
        in Bigint(sign,product)

(*Multiplication fnc returns an int list*)
    let mulInt value1 value2 =
        let _, product = mul' (value1, [1], value2)
        in product

(*Division using egyptian algorithm*)
    let rec divrem' (dividend, powerof2, divisor') =
        if cmp dividend divisor' < 0 
        then [0], dividend
        else let quotient, remainder =
                 divrem' (dividend, double powerof2, double divisor')
             in if cmp remainder divisor' < 0
               then quotient, remainder
               else add' quotient powerof2 0, sub' remainder  divisor' 0

(*Helper function *)
    let divrem (value1, value2) = 
        if value2 = [0] then failwith "ocamldc: divide by 0"
        else divrem' (value1, [1], value2)            

    let div (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        let sign = if neg1 = neg2 then Pos else Neg in
        let quotient, _ = divrem (value1, value2)
        in Bigint(sign, quotient)

(*Division fnc returns an int list*)
    let divInt value1 value2 =
        let quotient, _ = divrem (value1, value2)
        in quotient

    let rem (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        let sign = if neg1 = neg2 then Pos else Neg in
        let _, remainder = divrem (value1, value2)
        in Bigint(sign, remainder)

(*Mod fnc returns an int list*)
    let remInt value1 value2 =
        let _, remainder = divrem (value1, value2)
        in remainder

(*Checks if the number is even*)
    let even number = 
        if remInt number [2] = [0] then true
        else false 

(*Exponentiation*)
    let rec power' (base, expt, result) = match expt with
        | [0]                  -> result
        | expt when even expt  ->
            power' ((mulInt base base), (divInt expt [2]), result)
        | expt                 -> 
            power' (base, (sub' expt [1] 0), (mulInt base result))

    let pow (Bigint (neg1, value1)) (Bigint (neg2, value2)) =
        if neg2 = Neg then zero
        else Bigint(neg1 ,power' (value1, value2, [1]))

end
