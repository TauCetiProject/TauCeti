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
import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement
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

* `CliffordAlgebra.evenHamiltonEquivWeightedSumSquaresOne` is the canonical Hamilton-quaternion
  model of the even Clifford algebra of `x² + y² + z²`, with its reversal and norm equations.
* `CliffordAlgebra.pureHamiltonEquivWeightedSumSquaresOne` identifies the underlying quadratic
  space with the pure Hamilton quaternions.
* `CliffordAlgebra.spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne_action` identifies the
  Spin action in these coordinates with quaternion conjugation.
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

private abbrev hamiltonOneSymbol : R := -(↑(1 : Rˣ)⁻¹ : R) * 1

private def hamiltonOneSymbolToHamiltonBasis :
    QuaternionAlgebra.Basis ℍ[R] (hamiltonOneSymbol (R := R)) (0 : R)
      (hamiltonOneSymbol (R := R)) where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by ext <;> simp [hamiltonOneSymbol]
  j_mul_j := by ext <;> simp [hamiltonOneSymbol]
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

private def hamiltonToHamiltonOneSymbolBasis :
    QuaternionAlgebra.Basis
      ℍ[R,hamiltonOneSymbol (R := R),0,hamiltonOneSymbol (R := R)]
      (-1 : R) (0 : R) (-1 : R) where
  i := ⟨0, 1, 0, 0⟩
  j := ⟨0, 0, 1, 0⟩
  k := ⟨0, 0, 0, 1⟩
  i_mul_i := by ext <;> simp [hamiltonOneSymbol]
  j_mul_j := by ext <;> simp [hamiltonOneSymbol]
  i_mul_j := by ext <;> simp
  j_mul_i := by ext <;> simp

/-- The coordinate-preserving identification between the quaternion symbol produced by the
ternary Clifford model at coefficients `1, 1, 1` and the Hamilton quaternions. -/
private def hamiltonOneSymbolEquivHamilton :
    ℍ[R,hamiltonOneSymbol (R := R),0,hamiltonOneSymbol (R := R)] ≃ₐ[R] ℍ[R] :=
  AlgEquiv.ofAlgHom (hamiltonOneSymbolToHamiltonBasis (R := R)).liftHom
    (hamiltonToHamiltonOneSymbolBasis (R := R)).liftHom
    (by
      apply QuaternionAlgebra.hom_ext <;> ext <;>
        simp [QuaternionAlgebra.Basis.lift, hamiltonOneSymbolToHamiltonBasis,
          hamiltonToHamiltonOneSymbolBasis])
    (by
      apply QuaternionAlgebra.hom_ext <;> ext <;>
        simp [QuaternionAlgebra.Basis.lift, hamiltonOneSymbolToHamiltonBasis,
          hamiltonToHamiltonOneSymbolBasis])

private theorem hamiltonOneSymbolEquivHamilton_apply
    (q : ℍ[R,hamiltonOneSymbol (R := R),0,hamiltonOneSymbol (R := R)]) :
    hamiltonOneSymbolEquivHamilton q = ⟨q.re, q.imI, q.imJ, q.imK⟩ := by
  ext <;> simp [hamiltonOneSymbolEquivHamilton, hamiltonOneSymbolToHamiltonBasis,
    QuaternionAlgebra.Basis.lift]

private theorem hamiltonOneSymbolEquivHamilton_star
    (q : ℍ[R,hamiltonOneSymbol (R := R),0,hamiltonOneSymbol (R := R)]) :
    hamiltonOneSymbolEquivHamilton (star q) = star (hamiltonOneSymbolEquivHamilton q) := by
  rw [hamiltonOneSymbolEquivHamilton_apply, hamiltonOneSymbolEquivHamilton_apply]
  rfl

/-- The even Clifford algebra of the sum of three squares is canonically the Hamilton quaternion
algebra. This is the explicit model underlying
`exists_evenQuaternionEquiv_weightedSumSquares_one`. -/
noncomputable def evenHamiltonEquivWeightedSumSquaresOne :
    even (weightedSumSquares R ![(1 : R), 1, 1]) ≃ₐ[R] ℍ[R] :=
  (evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ)).trans
    hamiltonOneSymbolEquivHamilton

/-- The Hamilton coordinates of a product of two generators in the even Clifford algebra of the
sum of three squares. -/
theorem evenHamiltonEquivWeightedSumSquaresOne_ι (x y : Fin 3 → R) :
    evenHamiltonEquivWeightedSumSquaresOne
        ((even.ι (weightedSumSquares R ![(1 : R), 1, 1])).bilin x y) =
      -((⟨x 2, x 0, x 1, 0⟩ : ℍ[R]) * ⟨-y 2, y 0, y 1, 0⟩) := by
  -- Expose the defining composite so the generic ternary-coordinate theorem applies.
  change hamiltonOneSymbolEquivHamilton
      (evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ)
        ((even.ι (weightedSumSquares R ![(1 : R), 1, 1])).bilin x y)) = _
  have h := evenWeightedSumSquaresThreeQuaternionEquiv_ι
    (R := R) (1 : R) 1 (1 : Rˣ) x y
  change evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ)
      ((even.ι (weightedSumSquares R ![(1 : R), 1, 1])).bilin x y) = _ at h
  rw [h, hamiltonOneSymbolEquivHamilton_apply]
  ext <;> simp [QuaternionAlgebra.mk_mul_mk]

/-- The canonical Hamilton model carries Clifford reversal to quaternion conjugation. -/
@[simp]
theorem evenHamiltonEquivWeightedSumSquaresOne_reverseEven
    (x : even (weightedSumSquares R ![(1 : R), 1, 1])) :
    evenHamiltonEquivWeightedSumSquaresOne (reverseEven _ x) =
      star (evenHamiltonEquivWeightedSumSquaresOne x) := by
  -- Expose the defining composite to transport reversal through its two factors.
  change hamiltonOneSymbolEquivHamilton
      (evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ) (reverseEven _ x)) =
    star (hamiltonOneSymbolEquivHamilton
      (evenWeightedSumSquaresThreeQuaternionEquiv (1 : R) 1 (1 : Rˣ) x))
  rw [evenWeightedSumSquaresThreeQuaternionEquiv_reverseEven,
    hamiltonOneSymbolEquivHamilton_star]

/-- In the canonical Hamilton model, the reverse norm is the quaternion norm-square. -/
theorem evenHamiltonEquivWeightedSumSquaresOne_reverseEven_mul_self
    (x : even (weightedSumSquares R ![(1 : R), 1, 1])) :
    evenHamiltonEquivWeightedSumSquaresOne (reverseEven _ x * x) =
      Quaternion.normSq (evenHamiltonEquivWeightedSumSquaresOne x) := by
  rw [map_mul, evenHamiltonEquivWeightedSumSquaresOne_reverseEven,
    Quaternion.star_mul_self]

/-- The sum-of-three-squares quadratic space in the coordinates compatible with the canonical
Hamilton even-Clifford model. Its image is the pure Hamilton quaternions. -/
@[expose] noncomputable def pureHamiltonEquivWeightedSumSquaresOne :
    (weightedSumSquares R ![(1 : R), 1, 1]).IsometryEquiv
      (QuaternionAlgebra.pureNormForm (-1 : R) (-1 : R)) where
  toFun v := ⟨⟨0, -v 1, v 0, -v 2⟩, by simp⟩
  invFun q := ![(q : ℍ[R]).imJ, -(q : ℍ[R]).imI, -(q : ℍ[R]).imK]
  left_inv v := by ext i; fin_cases i <;> simp
  right_inv q := by
    apply Subtype.ext
    have hre : (q : ℍ[R]).re = 0 := q.2
    ext <;> simp [hre]
  map_add' _ _ := by apply Subtype.ext; ext <;> simp <;> abel
  map_smul' _ _ := by apply Subtype.ext; ext <;> simp
  map_app' v := by
    rw [QuaternionAlgebra.pureNormForm_apply_coordinates]
    simp [weightedSumSquares_apply, Fin.sum_univ_three]
    ring

/-- The pure Hamilton quaternion corresponding to a vector in the sum-of-three-squares model. -/
@[simp]
theorem coe_pureHamiltonEquivWeightedSumSquaresOne_apply (v : Fin 3 → R) :
    (pureHamiltonEquivWeightedSumSquaresOne v : ℍ[R]) =
      ⟨0, -v 1, v 0, -v 2⟩ := rfl

/-- The vector coordinates recovered from a pure Hamilton quaternion. -/
@[simp]
theorem pureHamiltonEquivWeightedSumSquaresOne_symm_apply
    (q : LinearMap.ker (QuaternionAlgebra.reₗ (-1 : R) (0 : R) (-1 : R))) :
    pureHamiltonEquivWeightedSumSquaresOne.symm q =
      ![(q : ℍ[R]).imJ, -(q : ℍ[R]).imI, -(q : ℍ[R]).imK] := rfl

/-- **The even Clifford algebra of a sum of three squares is the Hamilton quaternions.** There is
an algebra isomorphism from the even Clifford algebra of `x² + y² + z²` to `ℍ[R]` carrying Clifford
reversal to quaternion conjugation. -/
theorem exists_evenQuaternionEquiv_weightedSumSquares_one :
    ∃ e : even (weightedSumSquares R ![(1 : R), 1, 1]) ≃ₐ[R] ℍ[R],
      ∀ x, e (reverseEven _ x) = star (e x) := by
  exact ⟨evenHamiltonEquivWeightedSumSquaresOne,
    evenHamiltonEquivWeightedSumSquaresOne_reverseEven⟩

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

/-! ### The explicit Hamilton action for the sum of three squares -/

private abbrev hamiltonThreeForm := weightedSumSquares K ![(1 : K), 1, 1]

/-- The Spin group of the sum of three squares is the group of unit Hamilton quaternions. -/
noncomputable def spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne :
    spinGroup (weightedSumSquares K ![(1 : K), 1, 1]) ≃* unitary ℍ[K] :=
  spinGroupEquivQuaternionUnitary _
    (nondegenerate_weightedSumSquares fun i ↦ by fin_cases i <;> exact isRegular_one)
    (Module.finrank_fin_fun K) evenHamiltonEquivWeightedSumSquaresOne
    evenHamiltonEquivWeightedSumSquaresOne_reverseEven

/-- The Hamilton quaternion attached to a Spin element is obtained by applying the canonical
even-Clifford equivalence to its Clifford value. -/
@[simp]
theorem coe_spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne_apply
    (s : spinGroup (weightedSumSquares K ![(1 : K), 1, 1])) :
    (spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne s : ℍ[K]) =
      evenHamiltonEquivWeightedSumSquaresOne
        (evenUnitaryGroupEvenPart _ (spinGroupToEvenUnitary _ s)) := by
  exact coe_spinGroupEquivQuaternionUnitary_apply _ _ _ _ _ s

/-- The inverse Hamilton equivalence recovers a Spin element through the inverse even-Clifford
model. -/
@[simp]
theorem coe_spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne_symm_apply
    (q : unitary ℍ[K]) :
    ((spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne.symm q :
        spinGroup (weightedSumSquares K ![(1 : K), 1, 1])) :
          CliffordAlgebra (weightedSumSquares K ![(1 : K), 1, 1])) =
      (evenHamiltonEquivWeightedSumSquaresOne.symm (q : ℍ[K]) :
        even (weightedSumSquares K ![(1 : K), 1, 1])) := by
  exact coe_spinGroupEquivQuaternionUnitary_symm_apply _ _ _ _ _ q

/-- The Hamilton quaternion corresponding to a Spin element has norm-square one. -/
theorem normSq_spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne
    (s : spinGroup (weightedSumSquares K ![(1 : K), 1, 1])) :
    Quaternion.normSq
        (spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne s : ℍ[K]) = 1 :=
  Quaternion.normSq_coe_unitary_eq_one _

private noncomputable abbrev hamiltonBasisVector (i : Fin 3) : Fin 3 → K :=
  Pi.basisFun K (Fin 3) i

private noncomputable def hamiltonBasisList : List (Fin 3 → K) :=
  [hamiltonBasisVector 0, hamiltonBasisVector 1, hamiltonBasisVector 2]

omit [Invertible (2 : K)] in
private theorem hamiltonBasisList_pairwise :
    (hamiltonBasisList (K := K)).Pairwise (hamiltonThreeForm (K := K)).IsOrtho := by
  simp [hamiltonBasisList, hamiltonBasisVector, QuadraticMap.isOrtho_def,
    hamiltonThreeForm, weightedSumSquares_apply, Fin.sum_univ_three, Pi.basisFun_apply]

omit [Invertible (2 : K)] in
private theorem hamiltonBasisList_span :
    Submodule.span K {x | x ∈ hamiltonBasisList (K := K)} = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun K (Fin 3)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [hamiltonBasisList, hamiltonBasisVector]

private noncomputable def hamiltonVolume : CliffordAlgebra (hamiltonThreeForm (K := K)) :=
  (hamiltonBasisList (K := K)).map (CliffordAlgebra.ι (hamiltonThreeForm (K := K))) |>.prod

omit [Invertible (2 : K)] in
private theorem hamiltonVolume_mem_center :
    hamiltonVolume (K := K) ∈
      Subalgebra.center K (CliffordAlgebra (hamiltonThreeForm (K := K))) := by
  apply prod_map_ι_mem_center_of_odd_length (hamiltonBasisList_pairwise (K := K))
    (by change Odd 3; decide) (hamiltonBasisList_span (K := K))

private noncomputable def hamiltonVectorEven :
    (Fin 3 → K) →ₗ[K] even (hamiltonThreeForm (K := K)) where
  toFun v :=
    v 0 • (even.ι (hamiltonThreeForm (K := K))).bilin
        (hamiltonBasisVector 1) (hamiltonBasisVector 2) +
      v 1 • (even.ι (hamiltonThreeForm (K := K))).bilin
        (hamiltonBasisVector 2) (hamiltonBasisVector 0) +
        v 2 • (even.ι (hamiltonThreeForm (K := K))).bilin
          (hamiltonBasisVector 0) (hamiltonBasisVector 1)
  map_add' v w := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, smul_add]
    abel

omit [Invertible (2 : K)] in
private theorem map_hamiltonVectorEven (v : Fin 3 → K) :
    evenHamiltonEquivWeightedSumSquaresOne (hamiltonVectorEven v) =
      (pureHamiltonEquivWeightedSumSquaresOne v : ℍ[K]) := by
  simp only [hamiltonVectorEven, LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul]
  have h12 : evenHamiltonEquivWeightedSumSquaresOne
      ((even.ι (hamiltonThreeForm (K := K))).bilin
        (hamiltonBasisVector (K := K) 1) (hamiltonBasisVector (K := K) 2)) =
      (⟨0, 0, 1, 0⟩ : ℍ[K]) := by
    rw [evenHamiltonEquivWeightedSumSquaresOne_ι]
    ext <;> simp [hamiltonBasisVector, Pi.basisFun_apply, QuaternionAlgebra.mk_mul_mk]
  have h20 : evenHamiltonEquivWeightedSumSquaresOne
      ((even.ι (hamiltonThreeForm (K := K))).bilin
        (hamiltonBasisVector (K := K) 2) (hamiltonBasisVector (K := K) 0)) =
      (⟨0, -1, 0, 0⟩ : ℍ[K]) := by
    rw [evenHamiltonEquivWeightedSumSquaresOne_ι]
    ext <;> simp [hamiltonBasisVector, Pi.basisFun_apply, QuaternionAlgebra.mk_mul_mk]
  have h01 : evenHamiltonEquivWeightedSumSquaresOne
      ((even.ι (hamiltonThreeForm (K := K))).bilin
        (hamiltonBasisVector (K := K) 0) (hamiltonBasisVector (K := K) 1)) =
      (⟨0, 0, 0, -1⟩ : ℍ[K]) := by
    rw [evenHamiltonEquivWeightedSumSquaresOne_ι]
    ext <;> simp [hamiltonBasisVector, Pi.basisFun_apply, QuaternionAlgebra.mk_mul_mk]
  simp only [h12, h20, h01]
  apply QuaternionAlgebra.ext <;> simp

omit [Invertible (2 : K)] in
private theorem hamiltonBasisVector_isOrtho {i j : Fin 3} (hij : i ≠ j) :
    (hamiltonThreeForm (K := K)).IsOrtho
      (hamiltonBasisVector i) (hamiltonBasisVector j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [hamiltonBasisVector, QuadraticMap.isOrtho_def, hamiltonThreeForm,
      weightedSumSquares_apply, Fin.sum_univ_three, Pi.basisFun_apply]

omit [Invertible (2 : K)] in
private theorem ι_hamiltonBasisVector_sq (i : Fin 3) :
    ι (hamiltonThreeForm (K := K)) (hamiltonBasisVector i) *
        ι (hamiltonThreeForm (K := K)) (hamiltonBasisVector i) = 1 := by
  rw [ι_sq_scalar]
  fin_cases i <;>
    simp [hamiltonThreeForm, weightedSumSquares_apply, Fin.sum_univ_three,
      hamiltonBasisVector, Pi.basisFun_apply]

omit [Invertible (2 : K)] in
private theorem hamiltonVectorEven_basisVector (i : Fin 3) :
    hamiltonVectorEven (K := K) (hamiltonBasisVector i) =
      ![(even.ι (hamiltonThreeForm (K := K))).bilin
          (hamiltonBasisVector 1) (hamiltonBasisVector 2),
        (even.ι (hamiltonThreeForm (K := K))).bilin
          (hamiltonBasisVector 2) (hamiltonBasisVector 0),
        (even.ι (hamiltonThreeForm (K := K))).bilin
          (hamiltonBasisVector 0) (hamiltonBasisVector 1)] i := by
  fin_cases i <;> apply Subtype.ext <;>
    simp [hamiltonVectorEven, even.ι, hamiltonBasisVector, Pi.basisFun_apply]

omit [Invertible (2 : K)] in
private theorem hamiltonVolume_eq :
    hamiltonVolume (K := K) =
      ι (hamiltonThreeForm (K := K)) (hamiltonBasisVector 0) *
        (ι (hamiltonThreeForm (K := K)) (hamiltonBasisVector 1) *
          ι (hamiltonThreeForm (K := K)) (hamiltonBasisVector 2)) := by
  simp [hamiltonVolume, hamiltonBasisList]

omit [Invertible (2 : K)] in
private theorem coe_hamiltonVectorEven_basisVector (i : Fin 3) :
    (hamiltonVectorEven (K := K) (hamiltonBasisVector i) :
        CliffordAlgebra (hamiltonThreeForm (K := K))) =
      ι (hamiltonThreeForm (K := K)) (hamiltonBasisVector i) * hamiltonVolume := by
  have h10 := ι_mul_ι_comm_of_isOrtho
    (hamiltonBasisVector_isOrtho (K := K) (i := 0) (j := 1) (by decide)).symm
  have h20 := ι_mul_ι_comm_of_isOrtho
    (hamiltonBasisVector_isOrtho (K := K) (i := 0) (j := 2) (by decide)).symm
  have h21 := ι_mul_ι_comm_of_isOrtho
    (hamiltonBasisVector_isOrtho (K := K) (i := 1) (j := 2) (by decide)).symm
  rw [hamiltonVectorEven_basisVector, hamiltonVolume_eq]
  -- The three coordinate cases expose the even-subalgebra coercion before Clifford calculation.
  fin_cases i
  · change ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2) =
      ι _ (hamiltonBasisVector 0) *
        (ι _ (hamiltonBasisVector 0) *
          (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2)))
    rw [← mul_assoc, ι_hamiltonBasisVector_sq, one_mul]
  · change ι _ (hamiltonBasisVector 2) * ι _ (hamiltonBasisVector 0) =
      ι _ (hamiltonBasisVector 1) *
        (ι _ (hamiltonBasisVector 0) *
          (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2)))
    calc
      ι _ (hamiltonBasisVector 2) * ι _ (hamiltonBasisVector 0) =
          -(ι _ (hamiltonBasisVector 0) * ι _ (hamiltonBasisVector 2)) := h20
      _ = -((ι _ (hamiltonBasisVector 0) * ι _ (hamiltonBasisVector 1)) *
          (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2))) := by
        congr 1
        -- Insert the square of the middle basis vector so the adjacent factors cancel.
        rw [show ι _ (hamiltonBasisVector 0) * ι _ (hamiltonBasisVector 2) =
            ι _ (hamiltonBasisVector 0) * (1 * ι _ (hamiltonBasisVector 2)) by rw [one_mul],
          ← ι_hamiltonBasisVector_sq (K := K) 1]
        noncomm_ring
      _ = (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 0)) *
          (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2)) := by
        rw [h10, neg_mul]
      _ = ι _ (hamiltonBasisVector 1) *
          (ι _ (hamiltonBasisVector 0) *
            (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2))) := by
        noncomm_ring
  · change ι _ (hamiltonBasisVector 0) * ι _ (hamiltonBasisVector 1) =
      ι _ (hamiltonBasisVector 2) *
        (ι _ (hamiltonBasisVector 0) *
          (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2)))
    symm
    calc
      ι _ (hamiltonBasisVector 2) *
          (ι _ (hamiltonBasisVector 0) *
            (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2))) =
          (ι _ (hamiltonBasisVector 2) * ι _ (hamiltonBasisVector 0)) *
            (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2)) := by
        noncomm_ring
      _ = -(ι _ (hamiltonBasisVector 0) * ι _ (hamiltonBasisVector 2)) *
          (ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2)) := by rw [h20]
      _ = -(ι _ (hamiltonBasisVector 0) *
          ((ι _ (hamiltonBasisVector 2) * ι _ (hamiltonBasisVector 1)) *
            ι _ (hamiltonBasisVector 2))) := by noncomm_ring
      _ = -(ι _ (hamiltonBasisVector 0) *
          (-(ι _ (hamiltonBasisVector 1) * ι _ (hamiltonBasisVector 2)) *
            ι _ (hamiltonBasisVector 2))) := by rw [h21]
      _ = ι _ (hamiltonBasisVector 0) *
          (ι _ (hamiltonBasisVector 1) *
            (ι _ (hamiltonBasisVector 2) * ι _ (hamiltonBasisVector 2))) := by
        noncomm_ring
      _ = ι _ (hamiltonBasisVector 0) * ι _ (hamiltonBasisVector 1) := by
        rw [ι_hamiltonBasisVector_sq, mul_one]

omit [Invertible (2 : K)] in
private theorem coe_hamiltonVectorEven (v : Fin 3 → K) :
    (hamiltonVectorEven (K := K) v : CliffordAlgebra (hamiltonThreeForm (K := K))) =
      ι (hamiltonThreeForm (K := K)) v * hamiltonVolume (K := K) := by
  suffices h :
      (even (hamiltonThreeForm (K := K))).toSubmodule.subtype.comp hamiltonVectorEven =
        (LinearMap.mulRight K (hamiltonVolume (K := K))).comp
          (ι (hamiltonThreeForm (K := K))) by
    exact LinearMap.congr_fun h v
  apply (Pi.basisFun K (Fin 3)).ext
  intro i
  change (hamiltonVectorEven (K := K) (hamiltonBasisVector i) :
      CliffordAlgebra (hamiltonThreeForm (K := K))) =
    ι (hamiltonThreeForm (K := K)) (hamiltonBasisVector i) * hamiltonVolume (K := K)
  exact coe_hamiltonVectorEven_basisVector (K := K) i

private theorem hamiltonVectorEven_spin_action
    (s : spinGroup (hamiltonThreeForm (K := K))) (v : Fin 3 → K) :
    hamiltonVectorEven (s • v) =
      evenUnitaryGroupEvenPart _ (spinGroupToEvenUnitary _ s) * hamiltonVectorEven v *
        reverseEven _ (evenUnitaryGroupEvenPart _ (spinGroupToEvenUnitary _ s)) := by
  apply Subtype.ext
  rw [coe_hamiltonVectorEven, spinGroup_smul_apply, ι_spinVectorAction_apply]
  simp only [Subalgebra.coe_mul, coe_hamiltonVectorEven]
  rw [coe_evenUnitaryGroupEvenPart, coe_reverseEven_apply, coe_evenUnitaryGroupEvenPart,
    coe_spinGroupToEvenUnitary_apply]
  -- Read the subgroup equality in the ambient Clifford algebra before moving the central volume.
  change (s : CliffordAlgebra _) * ι _ v * star (s : CliffordAlgebra _) * hamiltonVolume =
    (s : CliffordAlgebra _) * (ι _ v * hamiltonVolume) * reverse (s : CliffordAlgebra _)
  have hrev : reverse (s : CliffordAlgebra (hamiltonThreeForm (K := K))) =
      star (s : CliffordAlgebra (hamiltonThreeForm (K := K))) :=
    reverse_eq_star_of_mem_even
      ⟨(s : CliffordAlgebra (hamiltonThreeForm (K := K))), spinGroup.mem_even s.2⟩
  rw [hrev]
  have hcomm : hamiltonVolume (K := K) * star (s : CliffordAlgebra _) =
      star (s : CliffordAlgebra _) * hamiltonVolume :=
    (Subalgebra.mem_center_iff.mp (hamiltonVolume_mem_center (K := K)) _).symm
  -- Reassociate to place the central volume next to the reversed Spin element.
  rw [show (s : CliffordAlgebra _) * ι _ v * star (s : CliffordAlgebra _) * hamiltonVolume =
      (s : CliffordAlgebra _) *
        (ι _ v * (star (s : CliffordAlgebra _) * hamiltonVolume)) by noncomm_ring, ← hcomm]
  noncomm_ring

/-- Under the canonical Hamilton and pure-quaternion coordinates, the Spin action on the sum of
three squares is conjugation by the corresponding norm-one quaternion. -/
theorem spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne_action
    (s : spinGroup (weightedSumSquares K ![(1 : K), 1, 1])) (v : Fin 3 → K) :
    (pureHamiltonEquivWeightedSumSquaresOne (s • v) : ℍ[K]) =
      (spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne s : ℍ[K]) *
        (pureHamiltonEquivWeightedSumSquaresOne v : ℍ[K]) *
          star (spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne s : ℍ[K]) := by
  rw [← map_hamiltonVectorEven, hamiltonVectorEven_spin_action, map_mul, map_mul,
    map_hamiltonVectorEven, evenHamiltonEquivWeightedSumSquaresOne_reverseEven,
    spinGroupEquivHamiltonUnitaryWeightedSumSquaresOne,
    coe_spinGroupEquivQuaternionUnitary_apply]

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
