module

public import Hypercube.StrongerBounds

@[expose] public section

/-! Instances of the audited diameter-preserving hypercube certificate. -/
namespace Hypercube.DraftThree

theorem four : 20 ≤ f 4 := by
  simpa using theorem14_from_cert 4 3 6 (by decide)

theorem five : 39 ≤ f 5 := by
  simpa using theorem14_from_cert 5 6 22 (by decide)

theorem six : 76 ≤ f 6 := by
  simpa using theorem14_from_cert 6 11 54 (by decide)

theorem seven : 148 ≤ f 7 := by
  simpa using theorem14_from_cert 7 19 140 (by decide)

theorem eight : 294 ≤ f 8 := by
  simpa using theorem14_from_cert 8 37 554 (by decide)


end Hypercube.DraftThree
