# smalltt

- See [Demo.stt](Demo.stt) for notes on usage, goals and benchmarks.
- See [krakow-pres.pdf](krakow-pres.pdf) for a presentation I previously gave about this system.

**NOTE**: as of november 2020, the implementation here is obsolete in some respects. The evaluator can be greatly simplified along the lines of [this](https://gist.github.com/AndrasKovacs/a0e0938113b193d6b9c1c0620d853784). Here's also a [video](https://www.youtube.com/watch?v=ZEWjnmkfgxE) where I talk about conversion checking using the simplified glued evaluator. I might update this repo at some point to reflect newer best practices.

## Some benchmarks

Benchmarks are informal and unfortunately not yet automated or easily reproducible. Loading [Demo.stt](Demo.stt) causes `smalltt` benchmark times (but not memory usage) to be displayed, but there's no equivalent for Agda and Coq now.

Setup:
- smalltt is compiled with GHC 8.6.2, with -O2 -fllvm
- GHC 8.6.2 is likewise used for GHC/GHCI benchmarks.
- Coq 8.8.2 for Coq, with -type-in-type
- Agda 2.6.0-master, built in 2018 september, is used for Agda,
  again with --type-in-type
- System: Core i7 3770, 8GB RAM, Ubuntu 16.04
- Timings and memory usage measured wth "time" util and process monitoring, or
  by using a stopwatch in the case of Agda normalization.
- Files used for benchmarking: [smalltt](Demo.stt), [Agda](bench/Bench.agda), [Coq](bench/Bench.v), [GHC](bench/Bench.hs)

#### Large length-indexed vector expression elaboration

|  | Time | Space
| --- | :--- | :--- |
| smalltt | 17ms  | 6.3 MB  |
| Coq | 300ms | 280 MB  |
| Agda | ~3s |  330 MB  |

#### Large embedded STLC term elaboration

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 22ms  | 6   MB |
| Coq     | 270ms | 240 MB |
| Agda    | 2.5s  | 120 MB |

#### Evaluation performance: forcing Church-encoded 10m-sized numeral

| | Time | Space
| --- | :--- | :--- |
| GHC -O2 -fllvm            |  14ms   |  0 MB |
| Coq (Eval vm_compute)     |  0.23s  |  82 MB |
| smalltt                   |  0.53s  |  6.3 MB |
| runghc                    |  1.1s   |  22 MB |
| Coq (Eval cbv)            |  1.1s   |  270 MB |
| Coq (Eval lazy)           |  2.8s   |  290 MB |
| Agda                      |  ~5.5s  |  ~635 MB |
| Coq (Eval native_compute) |  failed to compile |

#### Conversion checking 100k-sized Church numerals

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 27ms  | 6.2 MB |
| Agda    | 0.6s  | 57 MB |
| Coq     | 1s    | 340 MB |

#### Conversion checking 1m-sized Church numerals

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 0.27s  | 6.2 MB |
| Agda    | 3.5s  | 1 GB |
| Coq     | stack overflow  |

#### Conversion checking 10m-sized Church numerals

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 2.71s  | 6.2 MB |
| Agda    | out of memory |
| Coq     | stack overflow  |

#### Conversion checking 10k-sized Church numerals with metavariables

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 2.2ms  | 6 MB |
| Coq     | 0.1s  | 220 MB |
| Agda    | out of memory |

#### Conversion checking 1m-sized Church numerals with metavariables

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 0.28s  | 6 MB |
| Coq     | stack overflow |
| Agda    | out of memory |

#### Conversion checking 1m-sized iterated function types

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 1.2s  | 900 MB |
| Agda    | 8.5s | 3.5 GB |
| Coq     | stack overflow |
