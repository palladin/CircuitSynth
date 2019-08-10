#load "Init.fsx"

open Init
open System

let swap (a: _[]) x y =
    let tmp = a.[x]
    a.[x] <- a.[y]
    a.[y] <- tmp

let isPrime : int -> bool = fun n ->
    let rec check i =
        i > n/2 || (n % i <> 0 && check (i + 1))
    if n < 2 then false else check 2
let isPowerOfTwo : int -> bool = fun x -> 
    (x <> 0) && ((x &&& (x - 1)) = 0)

let xor : bool -> bool -> bool = fun a b -> (a || b) && (not a || not b)
let xors : bool [] -> bool = fun bits ->
    bits |> Array.reduce xor


let rndBit () = rand.Next() % 2 = 0

let (|SeqEmpty|SeqCons|) xs = 
  if Seq.isEmpty xs then SeqEmpty
  else SeqCons(Seq.head xs, Seq.skip 1 xs)

let rec merge : seq<'a> -> seq<'a> -> seq<'a> = 
    fun xs ys -> 
        seq {
          match xs, ys with
          | SeqCons(x, xs), SeqCons(y, ys) -> 
            yield x
            yield y
            yield! merge xs ys
          | SeqEmpty, SeqCons(y, ys) -> 
            yield y
            yield! merge xs ys
          | SeqCons(x, xs), SeqEmpty -> 
            yield x
            yield! merge xs ys
          | SeqEmpty, SeqEmpty -> ()
        }

let merge' : seq<seq<'a>> -> seq<'a> = 
    fun xss ->
        xss |> Seq.fold merge Seq.empty 

let take' : int -> seq<'a> -> seq<'a> = 
    fun n xs -> System.Linq.Enumerable.Take(xs, n)

let randoms : int -> int -> int -> seq<int> = fun seed min max ->
    let random = new Random(seed)
    seq { while true do
            yield random.Next(min, max + 1) }

let getSample : (int -> bool) -> int [] -> int -> int [] = 
    fun verify baseSample numOfSamples ->
        let sample =
            (baseSample |> Seq.filter verify, baseSample |> Seq.filter (not << verify))
            ||> merge
            |> Seq.take numOfSamples
            |> Seq.toArray  
        sample