/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Pin.Range
public import Mathlib.Basic.Real.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic
import TauCeti.FieldTheory.SquareClassGroup.Real

/-!
# The orthogonal image of the real Pin group

Let `Q` be a nondegenerate quadratic form on a finite-dimensional real vector space. The image of
Mathlib's Pin group `pinGroup Q` in `O(Q)` is the kernel of the norm-sign character
`g ↦ θ(g) · [det g]` (`CliffordAlgebra.range_pinToOrthogonal`), where `θ` is the spinor norm. On a
reflection `τ_v` this character is the sign of `-Q v`, so `τ_v` is the action of a Pin element
exactly when `Q v < 0`. This splits the image by signature:

* if `Q` takes a positive value, the image has index two in `O(Q)`, since the character is then
  onto the two real square classes;
* if `Q` takes a negative value, the image is not `SO(Q)`, since it contains the reflection in a
  negative vector;
* the image is all of `O(Q)` exactly when `Q` takes no positive value, as for a negative definite
  form;
* for a positive definite form the spinor norm is trivial, the image is exactly `SO(Q)`, and every
  Pin element is even, so Mathlib's Pin and Spin groups coincide.

For an indefinite form, the image is therefore an index-two subgroup of `O(Q)` other than `SO(Q)`.
The image of the Spin group, the even part of the Pin group, is all of `SO(Q)` for a definite form
of either sign and has index two in `SO(Q)` for an indefinite form
(`CliffordAlgebra.index_range_spinToSpecialOrthogonal_of_indefinite`). In contrast, the even part
of the normalized full Clifford cover covers all of `SO(Q)` in every signature
(`CliffordAlgebra.exists_cliffordFullCoverToOrthogonal_eq_and_mem_even_iff`, with
`IsRealClosed.isSquare_or_isSquare_neg`).

## Main results

* `CliffordAlgebra.reflectionOrthogonal_mem_range_pinToOrthogonal_iff_neg`: a reflection `τ_v`
  is the action of a Pin element exactly when `Q v < 0`.
* `CliffordAlgebra.index_range_pinToOrthogonal`: if `Q` takes a positive value, the Pin image
  has index two in `O(Q)`.
* `CliffordAlgebra.range_pinToOrthogonal_ne_specialOrthogonalWithin`: if `Q` takes a negative
  value, the Pin image is not `SO(Q)`.
* `CliffordAlgebra.pinToOrthogonal_surjective_iff` and
  `CliffordAlgebra.pinToOrthogonal_surjective_of_negDef`: the Pin action is onto `O(Q)` exactly
  when `Q` takes no positive value, in particular for a negative definite form.
* `CliffordAlgebra.range_pinToOrthogonal_eq_specialOrthogonalWithin_of_posDef` and
  `CliffordAlgebra.pinGroup_eq_spinGroup_of_posDef`: for a positive definite form the Pin image is
  `SO(Q)` and the Pin group is the Spin group.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe v

variable {V : Type v} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **Reflections in the real Pin image.** For a nondegenerate real quadratic form, the reflection
in an anisotropic vector `v` is the action of a Pin element exactly when `Q v < 0`. -/
theorem reflectionOrthogonal_mem_range_pinToOrthogonal_iff_neg (Q : QuadraticForm ℝ V)
    (hQ : Q.Nondegenerate) (v : V) [Invertible (Q v)] :
    QuadraticMap.reflectionOrthogonal Q v ∈ (pinToOrthogonal Q).range ↔ Q v < 0 := by
  rw [reflectionOrthogonal_mem_range_pinToOrthogonal_iff Q hQ, Units.isSquare_iff_pos,
    Units.val_neg, val_unitOfInvertible, neg_pos]

/-- **The real Pin image has index two** in `O(Q)` as soon as `Q` takes a positive value: the
norm-sign character then takes both signs. -/
theorem index_range_pinToOrthogonal (Q : QuadraticForm ℝ V) (hQ : Q.Nondegenerate)
    (hpos : ∃ v, 0 < Q v) :
    (pinToOrthogonal Q).range.index = 2 := by
  obtain ⟨w, hw⟩ := hpos
  let _ : Invertible (Q w) := invertibleOfNonzero hw.ne'
  have hsurj : Function.Surjective (orthogonalSpinorNorm Q hQ * orthogonalDetSquareClass Q) := by
    intro x
    rcases eq_one_or_eq_squareClassHom_neg_one x with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨QuadraticMap.reflectionOrthogonal Q w, ?_⟩
      rw [orthogonalSpinorNorm_mul_orthogonalDetSquareClass_reflectionOrthogonal,
        squareClassHom_eq_iff, Units.squareClass_eq_squareClass_neg_one_iff_neg, Units.val_neg,
        val_unitOfInvertible, neg_neg_iff_pos]
      exact hw
  rw [range_pinToOrthogonal Q hQ, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj,
    Subgroup.card_top, natCard_units_quotient_square_real]

/-- If `Q` takes a negative value, the real Pin image is not `SO(Q)`: it contains the reflection in
a negative vector, which has determinant `-1`. -/
theorem range_pinToOrthogonal_ne_specialOrthogonalWithin (Q : QuadraticForm ℝ V)
    (hQ : Q.Nondegenerate) (hneg : ∃ v, Q v < 0) :
    (pinToOrthogonal Q).range ≠ QuadraticMap.specialOrthogonalWithin Q := by
  obtain ⟨v, hv⟩ := hneg
  let _ : Invertible (Q v) := invertibleOfNonzero hv.ne
  intro h
  have hmem := (reflectionOrthogonal_mem_range_pinToOrthogonal_iff_neg Q hQ v).2 hv
  rw [h, QuadraticMap.mem_specialOrthogonalWithin_iff, QuadraticMap.coe_reflectionOrthogonal,
    QuadraticMap.det_reflection] at hmem
  norm_num [Units.ext_iff] at hmem

/-- **The real Pin action is onto `O(Q)`** exactly when `Q` takes no positive value: the
reflections, which generate `O(Q)`, are then all in the image. -/
theorem pinToOrthogonal_surjective_iff (Q : QuadraticForm ℝ V) (hQ : Q.Nondegenerate) :
    Function.Surjective (pinToOrthogonal Q) ↔ ∀ v, Q v ≤ 0 := by
  rw [← MonoidHom.range_eq_top]
  constructor
  · intro h v
    by_contra hv
    let _ : Invertible (Q v) := invertibleOfNonzero (ne_of_gt (not_le.mp hv))
    have hmem := (reflectionOrthogonal_mem_range_pinToOrthogonal_iff_neg Q hQ v).1
      (h ▸ Subgroup.mem_top _)
    exact hv hmem.le
  · intro h
    refine QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ _ fun v _ ↦ ?_
    exact (reflectionOrthogonal_mem_range_pinToOrthogonal_iff_neg Q hQ v).2
      (lt_of_le_of_ne (h v) (Invertible.ne_zero (Q v)))

/-- For a negative definite real quadratic form the Pin action is onto `O(Q)`. -/
theorem pinToOrthogonal_surjective_of_negDef (Q : QuadraticForm ℝ V) (hneg : (-Q).PosDef) :
    Function.Surjective (pinToOrthogonal Q) := by
  refine (pinToOrthogonal_surjective_iff Q
    ((QuadraticMap.nondegenerate_neg Q).mp hneg.anisotropic.nondegenerate)).2 fun v ↦ ?_
  simpa using hneg.nonneg v

/-- For a positive definite real quadratic form the Pin image is exactly `SO(Q)`: the spinor norm
is trivial, and the determinant square class detects `SO(Q)`. -/
theorem range_pinToOrthogonal_eq_specialOrthogonalWithin_of_posDef (Q : QuadraticForm ℝ V)
    (hQ : Q.PosDef) :
    (pinToOrthogonal Q).range = QuadraticMap.specialOrthogonalWithin Q := by
  rw [range_pinToOrthogonal Q hQ.anisotropic.nondegenerate,
    orthogonalSpinorNorm_eq_one_of_posDef Q hQ, one_mul,
    ker_orthogonalDetSquareClass hQ.anisotropic.nondegenerate]
  exact fun h ↦ by linarith [h.nonneg]

/-- **For a positive definite real form, Pin is Spin.** Every Pin element acts with
determinant one, hence is even. -/
theorem pinGroup_eq_spinGroup_of_posDef (Q : QuadraticForm ℝ V) (hQ : Q.PosDef) :
    pinGroup Q = spinGroup Q := by
  refine le_antisymm (fun x hx ↦ spinGroup.mem_iff.mpr ⟨hx, ?_⟩)
    fun x hx ↦ (spinGroup.mem_iff.mp hx).1
  have hdet : pinToOrthogonal Q ⟨x, hx⟩ ∈ QuadraticMap.specialOrthogonalWithin Q := by
    rw [← range_pinToOrthogonal_eq_specialOrthogonalWithin_of_posDef Q hQ]
    exact ⟨_, rfl⟩
  exact mem_even_of_det_pinToOrthogonal_eq_one Q ⟨x, hx⟩
    (QuadraticMap.mem_specialOrthogonalWithin_iff.mp hdet)

end CliffordAlgebra
