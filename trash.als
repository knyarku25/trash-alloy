var sig File {}
var sig Trash in File {}

fact init {
  no Trash
}

pred empty {
  some Trash and
  after no Trash and
  File' = File - Trash
}

pred delete [f : File] {
  f not in Trash
  Trash' = Trash + f
  File' = File
}

pred restore [f : File] {
  f in Trash
  Trash' = Trash - f
  File' = File
}

pred permanentDelete[f : File] {
  f in Trash                 // guard
  Trash' = Trash - f         // remove from Trash
  File' = File - f           // remove from all Files
}

fact trans {
  always (
    empty
    or (some f : File |
        delete[f]
        or restore[f]
        or permanentDelete[f]   // added here
    )
  )
}

// Beginning assertion to verify permanent deletion;
// see permanentGone for continuance of this property
assert deletedStaysInTrash{
  always (all f : File |
    f not in File' implies after always (f not in File)
  )
}

// We're looking to verify that files intended to be
// permanently gone are actually permanently gone (i.e.
// unaffected by restore)
assert permanentGone {
  always (
    all f : File |
      (f not in File)
      implies always (f not in File)
  )
}

run example {}
check deletedStaysInTrash for 5 but 6 steps
check permanentGone for 5 but 6 steps
