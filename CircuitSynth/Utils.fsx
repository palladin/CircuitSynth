#load "Init.fsx"

open Init
open System
open System.Collections.Generic

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

let merge : seq<'a> -> seq<'a> -> seq<'a> = 
    fun xs ys -> 
        let rec run' : IEnumerator<'a> -> IEnumerator<'a> -> seq<'a> = fun xs ys ->
            seq {
              match xs.MoveNext(), ys.MoveNext() with
              | true, true -> 
                yield xs.Current
                yield ys.Current
                yield! run' xs ys
              | true, false -> 
                  yield xs.Current
                  yield! run' xs ys
              | false, true -> 
                yield ys.Current
                yield! run' xs ys
              | false, false -> ()
            }
        run' (xs.GetEnumerator()) (ys.GetEnumerator())


let merge' : seq<seq<'a>> -> seq<'a> = 
    fun xss ->
        xss |> Seq.fold merge Seq.empty 

let take' : int -> seq<'a> -> seq<'a> = 
    fun n xs -> System.Linq.Enumerable.Take(xs, n)

let randoms : int -> int -> seq<int> = fun min max ->
    seq { while true do
            yield rand.Next(min, max + 1) }

let randomize<'a> : 'a [] -> 'a []  = fun xs -> 
    randoms 0 (xs.Length - 1) |> Seq.distinct |> Seq.take xs.Length |> Seq.map (fun i -> xs.[i]) |> Seq.toArray

let getSample : (int -> bool) -> int [] -> int -> int [] = 
    fun verify baseSample numOfSamples ->
        let sample =
            (baseSample |> Seq.filter verify, baseSample |> Seq.filter (not << verify))
            ||> merge
            |> Seq.take numOfSamples
            |> Seq.toArray  
        sample


let tryWith : (unit -> 'T) -> 'T -> 'T = fun f e ->
    try
        f ()
    with
    | _ -> e


let rec split : int -> seq<int * int> = fun n -> 
    seq { for i in {0..n} -> (i, n - i) }


let rec iterate f value = 
  seq { yield value; 
        yield! iterate f (f value) }

let fixedPoint f initial = 
    iterate f initial 
    |> Seq.pairwise 
    |> Seq.pick (fun (first, second) -> 
        if first = second then Some first else None)