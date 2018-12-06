# smalltt

See [Demo.stt](Demo.stt) for notes on usage, goals and benchmarks.

## Some benchmarks

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
| smalltt | 3.7ms  | 6.3 MB  |
| Coq | 300ms | 280 MB  |
| Agda | ~3s |  330 MB  |

#### Large embedded STLC term elaboration

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 37ms  | 6   MB |
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
| smalltt | 0.31s  | 6.2 MB |
| Agda    | 3.5s  | 1 GB |
| Coq     | stack overflow  |

#### Conversion checking 10m-sized Church numerals

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 2.7s  | 6.2 MB |
| Agda    | out of memory |
| Coq     | stack overflow  |

#### Conversion checking 10k-sized Church numerals with metavariables

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 3.5ms  | 6 MB |
| Coq     | 0.1s  | 220 MB |
| Agda    | out of memory |

#### Conversion checking 1m-sized Church numerals with metavariables

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 0.31s  | 6 MB |
| Coq     | stack overflow |
| Agda    | out of memory |

#### Conversion checking 1m-sized iterated function types

| | Time | Space |
| --- | :--- | :--- |
| smalltt | 1.33s  | 925 MB |
| Agda    | 8.5s | 3.5 GB |
| Coq     | stack overflow |
