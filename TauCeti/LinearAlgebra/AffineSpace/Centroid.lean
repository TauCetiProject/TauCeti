/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Centroid

/-!
# Displacements to the centroid of a finite family

For a nonempty finite family of points `p i`, `i ∈ s`, in an affine space over a division ring of
characteristic zero, the vector from any point `q` to the centroid `s.centroid k p` is the average
of the vectors from `q` to the points `p i`. This is the `Finset` analogue of Mathlib's
`Affine.Simplex.centroid_vsub_eq`.

## Main results

* `Finset.centroid_vsub_eq_smul_sum_vsub`: the vector from a point to the centroid is the average
  of the vectors from that point to the members of the family.
-/

public section

namespace Finset

variable (k : Type*) {V P ι : Type*} [DivisionRing k] [CharZero k] [AddCommGroup V] [Module k V]
  [AddTorsor V P] {s : Finset ι} {p : ι → P}

/-- The vector from any point to the centroid of a nonempty family is the average of the vectors
from that point to the members of the family. -/
theorem centroid_vsub_eq_smul_sum_vsub (hs : s.Nonempty) (q : P) :
    s.centroid k p -ᵥ q = (#s : k)⁻¹ • ∑ i ∈ s, (p i -ᵥ q) := by
  rw [s.centroid_vsub_const k hs, centroid_def,
    affineCombination_eq_linear_combination (hw := s.sum_centroidWeights_eq_one_of_nonempty k hs)]
  simp [smul_sum]

end Finset
