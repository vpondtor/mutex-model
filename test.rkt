#lang forge
--#lang forge "electrum_lab1" "anon email here"
option problem_type temporal

var sig File {}
one sig Trash {
  var bin : set File
}

pred init {
  no bin
}

pred empty {
  some bin and             -- guard: this has to be true before the event
  after no bin and         -- effect on bin
  File' = File - Trash.bin -- effect on File
}

pred delete [f : File] {
    f in File -- might not be necessary
    not f in bin
    bin' = bin + f
    File' = File
}

pred restore [f : File] {
  -- what must be true before the file is restored?
  -- what is the effect on bin, if any?
  -- what is the effect on File, if any?
  f in bin
  bin' = bin - f
  File' = File
}

pred traces {
  init
  always (empty or (some f : File | delete[f] or restore[f]))
}

run traces
