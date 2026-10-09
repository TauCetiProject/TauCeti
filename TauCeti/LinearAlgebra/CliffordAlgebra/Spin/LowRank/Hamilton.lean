/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.Three
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Range
import Mathlib.Tactic.NormNum.IsSquare
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic

/-!
# Norm-one quaternions, the spinor kernel, and the sum of three squares

For a nondegenerate ternary quadratic form over a field of characteristic not two, the even
Clifford algebra is a quaternion algebra with reversal as conjugation, and Spin is its group of
norm-one quaternions (`CliffordAlgebra.spinGroupEquivQuaternionUnitary`). Read through such a
model, the Spin action is a homomorphism from the norm-one quaternions to `SO(Q)` with kernel
`{±1}` and image the kernel of the spinor norm.

For the sum of three squares `x² + y² + z²` the model is the Hamilton quaternions
`ℍ[R] = (-1, -1)_R`, over any commutative ring. Over a field the image of the norm-one Hamilton
quaternions is all of `SO(x² + y² + z²)` exactly when every nonzero sum of three squares is a
square. Over `ℚ` this fails, since `2 = 1² + 1² + 0²` is not a square: the rational points of
`SO(x² + y² + z²)` are **not** the quotient of the norm-one rational Hamilton quaternions by `±1`,
although the kernel of the map is exactly `{±1}`.

## Main results

* `CliffordAlgebra.quaternionUnitaryToSpecialOrthogonal`: in dimension three, the homomorphism
  from the norm-one quaternions of a model of `C₀` to `SO(Q)`, with kernel `{±1}`
  (`CliffordAlgebra.mem_ker_quaternionUnitaryToSpecialOrthogonal_iff`) and image the spinor kernel
  (`CliffordAlgebra.range_quaternionUnitaryToSpecialOrthogonal`).
* `CliffordAlgebra.exists_evenQuaternionEquiv_weightedSumSquares_one`: the even Clifford algebra of
  `x² + y² + z²` is `ℍ[R]`, with reversal as conjugation, over any commutative ring.
* `CliffordAlgebra.spinToSpecialOrthogonal_weightedSumSquares_one_surjective_iff`: the Spin action
  on `SO(x² + y² + z²)` is surjective exactly when every nonzero sum of three squares is a square.
* `CliffordAlgebra.exists_quaternionUnitaryHom_range_ne_top_rat`: over `ℚ`, the image of the
  norm-one Hamilton quaternions is the spinor kernel, a proper subgroup of `SO(x² + y² + z²)`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §55.
* J. Voight, *Quaternion Algebras* (2021), §2.4 and Chapter 4.
-/

public section

open scoped Quaternion
open QuadraticMap TauCeti

namespace CliffordAlgebra

section CommRing

variable {R : Type*} [CommRing R]

/-- **The even Clifford algebra of a sum of three squares is the Hamilton quaternions.** There is
an algebra isomorphism from the even Clifford algebra of `x² + y² + z²` to `ℍ[R]` carrying Clifford
reversal to quaternion conjugation. -/
theorem exists_evenQuaternionEquiv_weightedSumSquares_one :
    ∃ e : even (weightedSumSquares R ![(1 : R), 1, 1]) ≃ₐ[R] ℍ[R],
      ∀ x, e (reverseEven _ x) = star (e x) := by
  -- The explicit model `evenWeightedSumSquaresThreeQuaternionEquiv` has the symbols
  -- `-1⁻¹ * 1`, which are equal but not definitionally equal to the symbols `-1` of `ℍ[R]`.
  have hsym : -(↑(1 : Rˣ)⁻¹ : R) * 1 = -1 := by simp
  obtain ⟨φ, hφ⟩ : ∃ φ : ℍ[R, -(↑(1 : Rˣ)⁻¹ : R) * 1, 0, -(↑(1 : Rˣ)⁻¹ : R) * 1] ≃ₐ[R] ℍ[R],
      ∀ y, φ (star y) = star (φ y) := by
    rw [hsym]
    exact ⟨AlgEquiv.refl, fun _ ↦ by simp⟩
  exact ⟨(evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 1).trans φ, fun x ↦
    (congrArg φ (evenWeightedSumSquaresThreeQuaternionEquiv_reverseEven (1 : R) 1 1 x)).trans
      (hφ _)⟩

end CommRing

variable {K : Type*} [Field K] [Invertible (2 : K)]

section Ternary

variable {V : Type*} [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) (hV : Module.finrank K V = 3) {a b : K}
  (e : even Q ≃ₐ[K] ℍ[K,a,0,b]) (he : ∀ x, e (reverseEven Q x) = star (e x))

/-- The Spin action on a nondegenerate ternary quadratic space, read through a quaternion model
`e` of the even Clifford algebra carrying reversal to conjugation: a homomorphism from the
norm-one quaternions to `SO(Q)`. -/
noncomputable def quaternionUnitaryToSpecialOrthogonal :
    unitary ℍ[K,a,0,b] →* QuadraticMap.specialOrthogonalGroup Q :=
  (spinToSpecialOrthogonal Q).comp (spinGroupEquivQuaternionUnitary Q hQ hV e he).symm.toMonoidHom

/-- A norm-one quaternion acts on `V` as the Spin element it corresponds to under the model. -/
theorem quaternionUnitaryToSpecialOrthogonal_apply (q : unitary ℍ[K,a,0,b]) :
    quaternionUnitaryToSpecialOrthogonal Q hQ hV e he q =
      spinToSpecialOrthogonal Q ((spinGroupEquivQuaternionUnitary Q hQ hV e he).symm q) :=
  (rfl)

/-- The kernel of the norm-one quaternions acting on a ternary quadratic space is `{±1}`. -/
theorem mem_ker_quaternionUnitaryToSpecialOrthogonal_iff [FiniteDimensional K V]
    (q : unitary ℍ[K,a,0,b]) :
    q ∈ (quaternionUnitaryToSpecialOrthogonal Q hQ hV e he).ker ↔ q = 1 ∨ q = -1 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  let E := spinGroupEquivQuaternionUnitary Q hQ hV e he
  have hE : E.symm (-1) = spinGroup.negOne Q hQ.ne_zero := Subtype.ext <| by
    simp [E, coe_spinGroupEquivQuaternionUnitary_symm_apply, Unitary.coe_neg]
  exact (mem_ker_spinToSpecialOrthogonal_iff Q hQ (E.symm q)).trans (by simp [← hE])

/-- **Norm-one quaternions cover the spinor kernel in dimension three.** The image of the
norm-one quaternions in `SO(Q)` is the kernel of the spinor norm. -/
theorem range_quaternionUnitaryToSpecialOrthogonal [FiniteDimensional K V] :
    (quaternionUnitaryToSpecialOrthogonal Q hQ hV e he).range = (spinorNorm Q hQ).ker := by
  rw [quaternionUnitaryToSpecialOrthogonal, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (MulEquiv.surjective _), ← MonoidHom.range_eq_map,
    range_spinToSpecialOrthogonal_eq_ker_spinorNorm]

end Ternary

/-- The Spin action on the special orthogonal group of `x² + y² + z²` is surjective exactly when
every nonzero sum of three squares in `K` is a square. -/
theorem spinToSpecialOrthogonal_weightedSumSquares_one_surjective_iff :
    Function.Surjective (spinToSpecialOrthogonal (weightedSumSquares K ![(1 : K), 1, 1])) ↔
      ∀ x y z : K, x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 → IsSquare (x ^ 2 + y ^ 2 + z ^ 2) := by
  have happ (v : Fin 3 → K) :
      weightedSumSquares K ![(1 : K), 1, 1] v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    simp [weightedSumSquares_apply, Fin.sum_univ_three, _root_.sq]
  have h1 : (1 : Kˣ) ∈ unitValueSet (weightedSumSquares K ![(1 : K), 1, 1]) :=
    mem_unitValueSet.2 ((represents_iff _ _).2 ⟨![1, 0, 0], by simp [happ]⟩)
  rw [spinToSpecialOrthogonal_surjective_iff_isSquare_of_one_mem _
    (nondegenerate_weightedSumSquares fun i ↦ by fin_cases i <;> exact isRegular_one) h1]
  constructor
  · intro h x y z hs
    have := h (Units.mk0 _ hs) (mem_unitValueSet.2 ((represents_iff _ _).2 ⟨![x, y, z], by
      simp [happ]⟩))
    rwa [← isSquare_units_val_iff, Units.val_mk0] at this
  · intro h a ha
    obtain ⟨v, hv⟩ := (represents_iff _ _).1 (mem_unitValueSet.1 ha)
    rw [← isSquare_units_val_iff, ← hv, happ]
    exact h _ _ _ (by rw [← happ, hv]; exact a.ne_zero)

/-- The Spin action on the special orthogonal group of the rational sum of three squares is not
surjective on rational points: `2 = 1² + 1² + 0²` is not a rational square. -/
theorem not_surjective_spinToSpecialOrthogonal_weightedSumSquares_one_rat :
    ¬ Function.Surjective (spinToSpecialOrthogonal (weightedSumSquares ℚ ![(1 : ℚ), 1, 1])) := by
  rw [spinToSpecialOrthogonal_weightedSumSquares_one_surjective_iff]
  intro h
  have := h 1 1 0 (by norm_num)
  norm_num at this

/-- **The rational sum of three squares.** The homomorphism from the norm-one rational Hamilton
quaternions to `SO(x² + y² + z²)(ℚ)` has kernel `{±1}` and image the spinor kernel, and that image
is a proper subgroup: `SO(x² + y² + z²)(ℚ)` is not the quotient of the norm-one quaternions by
`±1`. -/
theorem exists_quaternionUnitaryHom_range_ne_top_rat :
    ∃ f : unitary ℍ[ℚ] →*
        QuadraticMap.specialOrthogonalGroup (weightedSumSquares ℚ ![(1 : ℚ), 1, 1]),
      (∀ q, q ∈ f.ker ↔ q = 1 ∨ q = -1) ∧
        (∀ hQ, f.range = (spinorNorm (weightedSumSquares ℚ ![(1 : ℚ), 1, 1]) hQ).ker) ∧
          f.range ≠ ⊤ := by
  obtain ⟨e, he⟩ := exists_evenQuaternionEquiv_weightedSumSquares_one (R := ℚ)
  have hQ : (weightedSumSquares ℚ ![(1 : ℚ), 1, 1]).Nondegenerate :=
    nondegenerate_weightedSumSquares fun i ↦ by fin_cases i <;> exact isRegular_one
  let f := quaternionUnitaryToSpecialOrthogonal _ hQ (Module.finrank_fin_fun ℚ) e he
  have hrange : f.range = (spinorNorm _ hQ).ker := range_quaternionUnitaryToSpecialOrthogonal ..
  refine ⟨f, fun q ↦ mem_ker_quaternionUnitaryToSpecialOrthogonal_iff .., fun _ ↦ hrange, fun htop ↦
    not_surjective_spinToSpecialOrthogonal_weightedSumSquares_one_rat ?_⟩
  rw [← MonoidHom.range_eq_top, range_spinToSpecialOrthogonal_eq_ker_spinorNorm _ hQ, ← hrange,
    htop]

end CliffordAlgebra
