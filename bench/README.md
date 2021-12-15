
# build commands

- agda: agda FILE -vprofile:7 +RTS -M10G
- coq:  time coqtop -l FILE -batch -type-in-type -time
- lean:
  - grab the correct Lean path with `elan which lean`
  - `su`
  - `ulimit -s unlimited`
  - `lean FILE --profile` where `lean` is the path we got
