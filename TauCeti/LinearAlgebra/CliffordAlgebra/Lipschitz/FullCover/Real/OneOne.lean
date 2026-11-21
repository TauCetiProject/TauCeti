/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover.Even
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.OneOne

/-!
# The volume element of `Cliff(1, 1)` in the full Clifford cover

In `Cliff(1, 1)`, the volume element `z = e₁ e₂` (`TauCeti.realCliffordOneOneVolume`) is the
product of the generators `e₁` and `e₂`, of norms `1` and `-1`. So it lies in the normalized full
Clifford cover, with reverse norm `reverse z * z = -1`, and in its even part. Since `z ^ 2 = 1` and
`z` anticommutes with the vectors, it acts on the split plane by `-1`, an element of `SO(1, 1)`.

## Main definitions

* `CliffordAlgebra.realCliffordOneOneVolumeFullCover`: the volume element as an element of the full
  cover.

## Main results

* `CliffordAlgebra.cliffordNorm_realCliffordOneOneVolumeFullCover`: its reverse norm is `-1`.
* `CliffordAlgebra.realCliffordOneOneVolumeFullCover_mem_cliffordFullCoverEven`: it is even.
* `CliffordAlgebra.cliffordFullCoverToOrthogonal_realCliffordOneOneVolumeFullCover`: it acts by
  `-1`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

/-- The volume element `z = e₁ e₂` of `Cliff(1, 1)` as an element of the full cover: it is the
product of the generators `e₁` and `e₂`, of norms `1` and `-1`, so its reverse norm is `-1`. -/
def realCliffordOneOneVolumeFullCover : cliffordFullCover (realCliffordForm 1 1) :=
  letI : Invertible (realCliffordForm 1 1 (Pi.single 0 1)) := invertibleOfNonzero (by simp)
  letI : Invertible (realCliffordForm 1 1 (Pi.single 1 1)) := invertibleOfNonzero (by simp)
  ⟨⟨unitι _ (Pi.single 0 1), unitι_mem_lipschitzGroup _⟩ *
      ⟨unitι _ (Pi.single 1 1), unitι_mem_lipschitzGroup _⟩,
    (mem_cliffordFullCover_iff _ _).2 <| Or.inr <| by
      rw [map_mul, cliffordNorm_unitι, cliffordNorm_unitι, Units.ext_iff]
      simp⟩

/-- The underlying Clifford element of `realCliffordOneOneVolumeFullCover` is the volume element
`z = e₁ e₂`. -/
@[simp]
theorem coe_realCliffordOneOneVolumeFullCover :
    (((realCliffordOneOneVolumeFullCover : lipschitzGroup (realCliffordForm 1 1)) :
      (CliffordAlgebra (realCliffordForm 1 1))ˣ) : CliffordAlgebra (realCliffordForm 1 1)) =
      realCliffordOneOneVolume := by
  simp [realCliffordOneOneVolumeFullCover, coe_unitι, realCliffordOneOneVolume_def]

/-- The volume element of `Cliff(1, 1)` has reverse norm `reverse z * z = -z ^ 2 = -1`. -/
@[simp]
theorem cliffordNorm_realCliffordOneOneVolumeFullCover :
    cliffordNorm (realCliffordForm 1 1) realCliffordOneOneVolumeFullCover = -1 := by
  apply Units.ext
  apply algebraMap_injective (realCliffordForm 1 1)
  rw [← reverse_mul_self_eq_algebraMap_cliffordNorm, coe_realCliffordOneOneVolumeFullCover,
    reverse_realCliffordOneOneVolume, neg_mul, realCliffordOneOneVolume_mul_self, Units.val_neg,
    Units.val_one, map_neg, map_one]

/-- The volume element of `Cliff(1, 1)` lies in the even part of the full cover. -/
theorem realCliffordOneOneVolumeFullCover_mem_cliffordFullCoverEven :
    realCliffordOneOneVolumeFullCover ∈ cliffordFullCoverEven (realCliffordForm 1 1) := by
  rw [mem_cliffordFullCoverEven_iff, coe_realCliffordOneOneVolumeFullCover]
  exact realCliffordOneOneVolume_mem_even

/-- **The volume element of `Cliff(1, 1)` acts by `-1`.** It anticommutes with the vectors and
squares to `1`, so conjugation by it negates every vector. -/
theorem cliffordFullCoverToOrthogonal_realCliffordOneOneVolumeFullCover :
    cliffordFullCoverToOrthogonal (realCliffordForm 1 1) realCliffordOneOneVolumeFullCover =
      (realCliffordForm 1 1).negOrthogonal := by
  set Q := realCliffordForm 1 1
  set x := realCliffordOneOneVolumeFullCover
  have hinv : ((((x : lipschitzGroup Q) : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q) = realCliffordOneOneVolume :=
    Units.inv_eq_of_mul_eq_one_right (by
      rw [coe_realCliffordOneOneVolumeFullCover, realCliffordOneOneVolume_mul_self])
  refine Subtype.ext (LinearEquiv.ext fun m ↦ ι_injective Q ?_)
  rw [cliffordFullCoverToOrthogonal_apply, coe_lipschitzToOrthogonal_apply,
    ι_lipschitzVectorAction_apply, hinv, coe_realCliffordOneOneVolumeFullCover,
    involute_realCliffordOneOneVolume, QuadraticMap.coe_negOrthogonal, LinearEquiv.neg_apply,
    map_neg]
  -- In the matrix model, `z` is the swap matrix and `ι m` is `!![m 0, m 1; -m 1, -m 0]`.
  apply realCliffordOneOneEquivMatrix.injective
  rw [map_mul, map_mul, map_neg, realCliffordOneOneVolume_def,
    realCliffordOneOneEquivMatrix_e₀_mul_e₁, realCliffordOneOneEquivMatrix_ι]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end CliffordAlgebra
