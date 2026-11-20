/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.FullCover
public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm.OneOne
import Mathlib.FieldTheory.IsRealClosed.Real
import TauCeti.FieldTheory.SquareClassGroup.Real
import TauCeti.LinearAlgebra.CliffordAlgebra.Lipschitz.FullCover.RankOne
import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Real
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.SpinorNorm
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

/-!
# The real full Clifford cover, the Pin group and the Spin group

For a nondegenerate real quadratic space, the normalized full Clifford cover
`CliffordAlgebra.cliffordFullCover Q`, the Lipschitz elements of reverse norm `±1`, covers `O(Q)`
with kernel `{±1}` in positive dimension, trivial in dimension zero, and its even part covers
`SO(Q)`. This file compares it with the Pin group, of `star` norm `1`, and the Spin group, of even
elements of reverse norm `1`.

For a definite form the Spin group is the whole even part of the full cover, while for an
indefinite form it has index two there, its image being the kernel of the spinor norm on `SO(Q)`.
The Pin group is the whole full cover exactly when the form takes no positive value.

The low-rank checks show the sign conventions at work.

* In `Cliff(0, 1)`, where `e ^ 2 = -1`, the full cover is `{±1, ±e}`, cyclic of order four, and the
  Pin group is all of it.
* In `Cliff(1, 0)`, where `e ^ 2 = 1`, the full cover is again a group of order four, but it is not
  cyclic, and the Pin group is only `{±1}`. So the two covers of `O(1)` are not isomorphic.
* In `Cliff(1, 1)`, the volume element `z = e₁ e₂` has `z ^ 2 = 1` and `reverse z * z = -1`. It lies
  in the even part of the full cover but not in the Spin group, and it acts on the plane by `-1`, an
  element of `SO(1, 1)` that the Spin group does not reach.

## Main results

* `CliffordAlgebra.range_spinToCliffordFullCover_eq_cliffordFullCoverEven_of_posDef` and
  `CliffordAlgebra.range_spinToCliffordFullCover_eq_cliffordFullCoverEven_of_negDef`: for a
  definite form the Spin group is the even part of the full cover.
* `CliffordAlgebra.relIndex_range_spinToCliffordFullCover_of_indefinite`: for an indefinite form
  it has index two there.
* `CliffordAlgebra.pinToCliffordFullCover_surjective_iff`: the Pin group is the whole full cover
  exactly when the form takes no positive value.
* `CliffordAlgebra.isCyclic_cliffordFullCover_realCliffordForm_zero_one` and
  `CliffordAlgebra.not_isCyclic_cliffordFullCover_realCliffordForm_one_zero`: the full covers of
  `Cliff(0, 1)` and `Cliff(1, 0)`.
* `CliffordAlgebra.negOrthogonal_notMem_range_spinToOrthogonal_realCliffordForm_one_one`: the
  Spin group of signature `(1, 1)` does not reach `-1 ∈ SO(1, 1)`, which the volume element of the
  even full cover realizes.

## References

* J. Gallier, *Clifford algebras, Clifford groups, and a generalization of the quaternions*,
  arXiv:0805.0311v3, Definition 1.6 and Proposition 1.21.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

universe v

/-- `-1` is not a square in `ℝ`. -/
private theorem not_isSquare_neg_one_real : ¬IsSquare (-1 : ℝ) :=
  fun h ↦ by linarith [h.nonneg]

section Signature

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **For a positive definite form, Spin is the even full cover.** The spinor norm is trivial, so
every even element of the full cover has reverse norm `1`. -/
theorem range_spinToCliffordFullCover_eq_cliffordFullCoverEven_of_posDef (Q : QuadraticForm ℝ V)
    (hQ : Q.PosDef) :
    (spinToCliffordFullCover Q).range = cliffordFullCoverEven Q := by
  refine le_antisymm (range_spinToCliffordFullCover_le_cliffordFullCoverEven Q) ?_
  rw [← Subgroup.relIndex_eq_one, relIndex_range_spinToCliffordFullCover
    hQ.anisotropic.nondegenerate not_isSquare_neg_one_real IsRealClosed.isSquare_or_isSquare_neg,
    spinorNorm_eq_one_of_posDef Q hQ, MonoidHom.range_one, Subgroup.card_bot]

/-- **For a negative definite form, Spin is the even full cover.** The spinor norm is the
determinant square class, trivial on `SO(Q)`, so every even element of the full cover has reverse
norm `1`. -/
theorem range_spinToCliffordFullCover_eq_cliffordFullCoverEven_of_negDef (Q : QuadraticForm ℝ V)
    (hneg : (-Q).PosDef) :
    (spinToCliffordFullCover Q).range = cliffordFullCoverEven Q := by
  refine le_antisymm (range_spinToCliffordFullCover_le_cliffordFullCoverEven Q) ?_
  rw [← Subgroup.relIndex_eq_one, relIndex_range_spinToCliffordFullCover
    ((QuadraticMap.nondegenerate_neg Q).mp hneg.anisotropic.nondegenerate)
    not_isSquare_neg_one_real IsRealClosed.isSquare_or_isSquare_neg,
    spinorNorm_eq_one_of_negDef Q hneg, MonoidHom.range_one, Subgroup.card_bot]

/-- **For an indefinite form, Spin has index two in the even full cover.** The spinor norm then
takes both signs on `SO(Q)`, so the even part of the full cover contains elements of reverse norm
`-1`. -/
theorem relIndex_range_spinToCliffordFullCover_of_indefinite (Q : QuadraticForm ℝ V)
    (hQ : Q.Nondegenerate) (hpos : ∃ v, 0 < Q v) (hneg : ∃ v, Q v < 0) :
    (spinToCliffordFullCover Q).range.relIndex (cliffordFullCoverEven Q) = 2 := by
  rw [relIndex_range_spinToCliffordFullCover hQ not_isSquare_neg_one_real
      IsRealClosed.isSquare_or_isSquare_neg,
    MonoidHom.range_eq_top.2 (spinorNorm_surjective_of_indefinite Q hQ hpos hneg),
    Subgroup.card_top, natCard_units_quotient_square_real]

/-- **The Pin group is the whole full cover** of a nondegenerate real quadratic space exactly when
the form takes no positive value. -/
theorem pinToCliffordFullCover_surjective_iff (Q : QuadraticForm ℝ V) (hQ : Q.Nondegenerate) :
    Function.Surjective (pinToCliffordFullCover Q) ↔ ∀ v, Q v ≤ 0 := by
  rw [← pinToOrthogonal_surjective_iff Q hQ, ← MonoidHom.range_eq_top, ← MonoidHom.range_eq_top,
    ← comap_range_pinToOrthogonal hQ not_isSquare_neg_one_real]
  constructor
  · intro h
    rw [eq_top_iff]
    intro g _
    obtain ⟨x, rfl⟩ :=
      cliffordFullCoverToOrthogonal_surjective hQ IsRealClosed.isSquare_or_isSquare_neg g
    rw [← Subgroup.mem_comap, h]
    exact Subgroup.mem_top x
  · intro h
    rw [h, Subgroup.comap_top]

end Signature

/-! ### Rank one: `Cliff(0, 1)` and `Cliff(1, 0)` -/

section RankOne

/-- The signature forms of rank one live on a line. -/
private theorem finrank_realCliffordForm {p q : ℕ} (hpq : p + q = 1) :
    Module.finrank ℝ (Fin (p + q) → ℝ) = 1 := by
  rw [Module.finrank_fin_fun, hpq]

/-- **The full covers in rank one have order four**: those of `Cliff(1, 0)` and `Cliff(0, 1)` are
both extensions of `O(1) = {±1}` by `{±1}`. -/
theorem card_cliffordFullCover_realCliffordForm {p q : ℕ} (hpq : p + q = 1) :
    Nat.card (cliffordFullCover (realCliffordForm p q)) = 4 :=
  card_cliffordFullCover_of_finrank_eq_one (nondegenerate_realCliffordForm p q)
    (finrank_realCliffordForm hpq) not_isSquare_neg_one_real IsRealClosed.isSquare_or_isSquare_neg

/-- **The full cover of `Cliff(0, 1)` is cyclic**: the generator `e`, with `e ^ 2 = -1`, has order
four. -/
theorem isCyclic_cliffordFullCover_realCliffordForm_zero_one :
    IsCyclic (cliffordFullCover (realCliffordForm 0 1)) :=
  (isCyclic_cliffordFullCover_iff_of_finrank_eq_one (nondegenerate_realCliffordForm 0 1)
    (finrank_realCliffordForm rfl) not_isSquare_neg_one_real
    IsRealClosed.isSquare_or_isSquare_neg).2 ⟨Pi.single 0 1, by simp⟩

/-- **The full cover of `Cliff(1, 0)` is not cyclic**: `1`, `-1` and the generator `e`, with
`e ^ 2 = 1`, all square to `1`. -/
theorem not_isCyclic_cliffordFullCover_realCliffordForm_one_zero :
    ¬IsCyclic (cliffordFullCover (realCliffordForm 1 0)) := by
  rw [isCyclic_cliffordFullCover_iff_of_finrank_eq_one (nondegenerate_realCliffordForm 1 0)
    (finrank_realCliffordForm rfl) not_isSquare_neg_one_real IsRealClosed.isSquare_or_isSquare_neg]
  rintro ⟨v, hv⟩
  linarith [(posDef_realCliffordForm_zero 1).nonneg v]

/-- **The Pin group of `Cliff(0, 1)` is the whole full cover**: the generator `e` has
`e * star e = -e ^ 2 = 1`. -/
theorem pinToCliffordFullCover_surjective_realCliffordForm_zero_one :
    Function.Surjective (pinToCliffordFullCover (realCliffordForm 0 1)) := by
  refine (pinToCliffordFullCover_surjective_iff _ (nondegenerate_realCliffordForm 0 1)).2 fun v ↦ ?_
  rw [realCliffordForm_apply]
  refine Finset.sum_nonpos fun i _ ↦ ?_
  rw [realCliffordWeight_of_le (Nat.zero_le _)]
  nlinarith [mul_self_nonneg (v i)]

/-- **The Pin group of `Cliff(1, 0)` is only `{±1}`**: its image `SO(1)` is trivial, so it is the
kernel of the full-cover action. -/
theorem range_pinToCliffordFullCover_realCliffordForm_one_zero :
    (pinToCliffordFullCover (realCliffordForm 1 0)).range =
      (cliffordFullCoverToOrthogonal (realCliffordForm 1 0)).ker := by
  have hQ := nondegenerate_realCliffordForm 1 0
  have hbot : (pinToOrthogonal (realCliffordForm 1 0)).range = ⊥ := by
    have h := Subgroup.card_mul_index (pinToOrthogonal (realCliffordForm 1 0)).range
    rw [index_range_pinToOrthogonal _ hQ ⟨Pi.single 0 1, by simp⟩,
      QuadraticMap.card_orthogonalGroup_of_finrank_eq_one hQ.ne_zero
        (finrank_realCliffordForm rfl)] at h
    exact Subgroup.eq_bot_of_card_eq _ (by omega)
  rw [← comap_range_pinToOrthogonal hQ not_isSquare_neg_one_real, hbot, MonoidHom.comap_bot]

/-- The Pin group of `Cliff(1, 0)` has order two. -/
theorem card_range_pinToCliffordFullCover_realCliffordForm_one_zero :
    Nat.card (pinToCliffordFullCover (realCliffordForm 1 0)).range = 2 := by
  have : Nontrivial (Fin (1 + 0) → ℝ) :=
    Module.nontrivial_of_finrank_eq_succ (finrank_realCliffordForm rfl)
  rw [range_pinToCliffordFullCover_realCliffordForm_one_zero,
    card_ker_cliffordFullCoverToOrthogonal (nondegenerate_realCliffordForm 1 0)
      not_isSquare_neg_one_real]

end RankOne

/-! ### Signature `(1, 1)`: the volume element -/

section OneOne

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

/-- The volume element of `Cliff(1, 1)` is not in the Spin group: its reverse norm is `-1`. -/
theorem realCliffordOneOneVolumeFullCover_notMem_range_spinToCliffordFullCover :
    realCliffordOneOneVolumeFullCover ∉ (spinToCliffordFullCover (realCliffordForm 1 1)).range := by
  rw [mem_range_spinToCliffordFullCover_iff, cliffordNorm_realCliffordOneOneVolumeFullCover]
  exact fun h ↦ by norm_num [Units.ext_iff] at h

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

/-- **The Spin group of `Cliff(1, 1)` does not reach `-1`.** The isometry `-1` of the split plane
lies in `SO(1, 1)` and is the action of the volume element of the even full cover, but the only
elements of the full cover acting by it are `±z`, of reverse norm `-1`. -/
theorem negOrthogonal_notMem_range_spinToOrthogonal_realCliffordForm_one_one :
    (realCliffordForm 1 1).negOrthogonal ∉ (spinToOrthogonal (realCliffordForm 1 1)).range := by
  rw [← cliffordFullCoverToOrthogonal_realCliffordOneOneVolumeFullCover, ← Subgroup.mem_comap,
    comap_range_spinToOrthogonal (nondegenerate_realCliffordForm 1 1) not_isSquare_neg_one_real]
  exact realCliffordOneOneVolumeFullCover_notMem_range_spinToCliffordFullCover

end OneOne

end CliffordAlgebra
