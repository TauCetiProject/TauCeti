/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Exceptional.Six.ExteriorSquare
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Data.Fintype.EquivFin

/-!
# Hyperbolic coordinates for the six-dimensional wedge form

The volume pairing on `⋀²(K⁴)` is split over every nontrivial commutative ring. Its three
hyperbolic pairs are `(e₀₁, e₂₃)`, `(-e₀₂, e₁₃)` and `(e₀₃, e₁₂)`. These coordinates identify
the wedge form with the un-halved polar form of `splitEvenForm K 3`. When two is invertible,
half its diagonal is therefore isometric to the standard quadratic space of three hyperbolic
planes. This connects the exterior-square action with the split Clifford-algebra model.

The construction uses Mathlib's exterior-power basis and the determinant formula for the
volume pairing, rather than choosing an unspecified isometry of six-dimensional spaces.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 20.
-/

public section

namespace TauCeti

open Module

universe u

private def wedgePairIndices : Fin 3 ⊕ Fin 3 → Fin 2 → Fin 4 :=
  Sum.elim ![![0, 1], ![0, 2], ![0, 3]] ![![2, 3], ![1, 3], ![1, 2]]

private def wedgePairEmbedding (i : Fin 3 ⊕ Fin 3) : Fin 2 ↪o Fin 4 :=
  OrderEmbedding.ofStrictMono (wedgePairIndices i) (by
    rcases i with i | i <;> fin_cases i <;>
      intro a b hab <;> fin_cases a <;> fin_cases b <;>
      norm_num [wedgePairIndices] at *)

private noncomputable def wedgePairIndex : (Fin 3 ⊕ Fin 3) ≃ Set.powersetCard (Fin 4) 2 :=
  Equiv.ofBijective (fun i ↦ Set.powersetCard.ofFinEmbEquiv (wedgePairEmbedding i)) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · apply Set.powersetCard.ofFinEmbEquiv.injective.comp
      intro i j h
      have hinj : Function.Injective wedgePairIndices := by decide
      exact hinj (congrArg (fun e : Fin 2 ↪o Fin 4 ↦ e.toFun) h)
    · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Set.powersetCard.card]
      norm_num [Nat.choose])

private def wedgePairSign (K : Type u) [CommRing K] (i : Fin 3 ⊕ Fin 3) : Kˣ :=
  if i = Sum.inl 1 then -1 else 1

variable (K : Type u) [CommRing K] [Nontrivial K]

/-- The ordered hyperbolic basis `(e₀₁, -e₀₂, e₀₃; e₂₃, e₁₃, e₁₂)` of `⋀²(K⁴)`.
The two halves are indexed by `Fin 3 ⊕ Fin 3`. -/
noncomputable def spinSixWedgeBasis : Basis (Fin 3 ⊕ Fin 3) K (⋀[K]^2 (Fin 4 → K)) :=
  (((Pi.basisFun K (Fin 4)).exteriorPower 2).reindex wedgePairIndex.symm).unitsSMul
    (wedgePairSign K)

omit [Nontrivial K] in
private theorem spinSixWedgeBasis_apply (i : Fin 3 ⊕ Fin 3) :
    spinSixWedgeBasis K i = (wedgePairSign K i : K) •
      exteriorPower.ιMulti K 2 (fun j ↦ Pi.single (wedgePairIndices i j) 1) := by
  simp [spinSixWedgeBasis, Basis.unitsSMul_apply, exteriorPower.ιMulti_family,
    wedgePairIndex, wedgePairEmbedding, Function.comp_def, Pi.basisFun_apply, Units.smul_def]

omit [Nontrivial K] in
/-- The first three basis vectors are `e₀₁`, `-e₀₂`, and `e₀₃`. -/
@[simp]
theorem spinSixWedgeBasis_inl (i : Fin 3) :
    spinSixWedgeBasis K (Sum.inl i) = (-1 : K) ^ (i : ℕ) •
      exteriorPower.ιMulti K 2 ![Pi.single 0 1, Pi.single i.succ 1] := by
  rw [spinSixWedgeBasis_apply]
  have hindices : (fun j ↦ Pi.single (wedgePairIndices (Sum.inl i) j) (1 : K)) =
      ![Pi.single 0 1, Pi.single i.succ 1] := by
    fin_cases i <;> ext j <;> fin_cases j <;> rfl
  rw [hindices]
  congr 1
  fin_cases i <;> norm_num [wedgePairSign]

omit [Nontrivial K] in
/-- The last three basis vectors are `e₂₃`, `e₁₃`, and `e₁₂`. -/
@[simp]
theorem spinSixWedgeBasis_inr (i : Fin 3) :
    spinSixWedgeBasis K (Sum.inr i) = exteriorPower.ιMulti K 2
      (fun j ↦ Pi.single ((![![2, 3], ![1, 3], ![1, 2]] : Fin 3 → Fin 2 → Fin 4) i j) 1) := by
  simp [spinSixWedgeBasis_apply, wedgePairSign, wedgePairIndices]

private noncomputable def splitSixBasis : Basis (Fin 3 ⊕ Fin 3) K (SplitEvenSpace K 3) :=
  (Pi.basisFun K (Fin 3)).dualBasis.prod (Pi.basisFun K (Fin 3))

private theorem spinSixWedgeForm_basis (i j : Fin 3 ⊕ Fin 3) :
    spinSixWedgeForm K (spinSixWedgeBasis K i) (spinSixWedgeBasis K j) =
      Matrix.fromBlocks (0 : Matrix (Fin 3) (Fin 3) K) 1 1 0 i j := by
  -- Compute the full Gram matrix once from the determinant formula for pure wedges.
  simp only [spinSixWedgeBasis_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    spinSixWedgeForm_ιMulti]
  rw [Matrix.det_succ_row_zero]
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [wedgePairSign, wedgePairIndices, Matrix.det_fin_three,
      Matrix.submatrix_apply, Fin.succAbove, Fin.append, Fin.addCases, Pi.single_apply]

/-- The first half of the hyperbolic wedge basis is totally isotropic for the wedge pairing. -/
@[simp↓]
theorem spinSixWedgeForm_basis_inl_inl (i j : Fin 3) :
    spinSixWedgeForm K (spinSixWedgeBasis K (Sum.inl i))
      (spinSixWedgeBasis K (Sum.inl j)) = 0 := by
  simpa using spinSixWedgeForm_basis K (Sum.inl i) (Sum.inl j)

/-- The second half of the hyperbolic wedge basis is totally isotropic for the wedge pairing. -/
@[simp↓]
theorem spinSixWedgeForm_basis_inr_inr (i j : Fin 3) :
    spinSixWedgeForm K (spinSixWedgeBasis K (Sum.inr i))
      (spinSixWedgeBasis K (Sum.inr j)) = 0 := by
  simpa using spinSixWedgeForm_basis K (Sum.inr i) (Sum.inr j)

/-- The two halves of the hyperbolic wedge basis are dual for the wedge pairing. -/
@[simp↓]
theorem spinSixWedgeForm_basis_inl_inr (i j : Fin 3) :
    spinSixWedgeForm K (spinSixWedgeBasis K (Sum.inl i))
      (spinSixWedgeBasis K (Sum.inr j)) = if i = j then 1 else 0 := by
  simpa [Matrix.one_apply] using spinSixWedgeForm_basis K (Sum.inl i) (Sum.inr j)

/-- The reverse mixed pairing is the same Kronecker delta. -/
@[simp↓]
theorem spinSixWedgeForm_basis_inr_inl (i j : Fin 3) :
    spinSixWedgeForm K (spinSixWedgeBasis K (Sum.inr i))
      (spinSixWedgeBasis K (Sum.inl j)) = if i = j then 1 else 0 := by
  simpa [Matrix.one_apply] using spinSixWedgeForm_basis K (Sum.inr i) (Sum.inl j)

private theorem spinSixWedgeBasis_pairing (i j : Fin 3 ⊕ Fin 3) :
    spinSixWedgeForm K (spinSixWedgeBasis K i) (spinSixWedgeBasis K j) =
      (splitEvenForm K 3).polarBilin (splitSixBasis K i) (splitSixBasis K j) := by
  rcases i with i | i <;> rcases j with j | j <;>
    simp [splitSixBasis, Basis.prod_apply, polar_splitEvenForm,
      QuadraticMap.polarBilin_apply_apply, Pi.basisFun_apply, Pi.single_apply, eq_comm]

/-- Hyperbolic coordinates identify the wedge pairing with the un-halved polar form of three
hyperbolic planes. This comparison does not require two to be invertible. -/
noncomputable def spinSixWedgeIsometryEquivPolarSplit :
    (spinSixWedgeForm K).IsometryEquiv (splitEvenForm K 3).polarBilin :=
  (spinSixWedgeBasis K).isometryEquivOfToMatrixEq (splitSixBasis K)
    (by ext i j; simpa only [LinearMap.BilinForm.toMatrix_apply] using
      spinSixWedgeBasis_pairing K i j)

/-- The first half of the wedge basis maps to the standard dual-coordinate axis. -/
@[simp↓]
theorem spinSixWedgeIsometryEquivPolarSplit_apply_inl (i : Fin 3) :
    spinSixWedgeIsometryEquivPolarSplit K (spinSixWedgeBasis K (Sum.inl i)) =
      ((Pi.basisFun K (Fin 3)).coord i, 0) := by
  simp only [spinSixWedgeIsometryEquivPolarSplit,
    Basis.isometryEquivOfToMatrixEq_apply_basis]
  simp [splitSixBasis, Basis.prod_apply]

/-- The second half of the wedge basis maps to the standard coordinate axis. -/
@[simp↓]
theorem spinSixWedgeIsometryEquivPolarSplit_apply_inr (i : Fin 3) :
    spinSixWedgeIsometryEquivPolarSplit K (spinSixWedgeBasis K (Sum.inr i)) =
      (0, Pi.single i 1) := by
  simp only [spinSixWedgeIsometryEquivPolarSplit,
    Basis.isometryEquivOfToMatrixEq_apply_basis]
  simp [splitSixBasis, Basis.prod_apply, Pi.basisFun_apply]

/-- The inverse hyperbolic coordinates recover the first half of the wedge basis. -/
@[simp]
theorem spinSixWedgeIsometryEquivPolarSplit_symm_apply_inl (i : Fin 3) :
    (spinSixWedgeIsometryEquivPolarSplit K).symm ((Pi.basisFun K (Fin 3)).coord i, 0) =
      spinSixWedgeBasis K (Sum.inl i) := by
  apply (spinSixWedgeIsometryEquivPolarSplit K).injective
  simp only [← LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv,
    ← LinearMap.BilinForm.IsometryEquiv.coe_symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  exact (spinSixWedgeIsometryEquivPolarSplit_apply_inl K i).symm

/-- The inverse hyperbolic coordinates recover the second half of the wedge basis. -/
@[simp]
theorem spinSixWedgeIsometryEquivPolarSplit_symm_apply_inr (i : Fin 3) :
    (spinSixWedgeIsometryEquivPolarSplit K).symm (0, Pi.single i 1) =
      spinSixWedgeBasis K (Sum.inr i) := by
  apply (spinSixWedgeIsometryEquivPolarSplit K).injective
  simp only [← LinearMap.BilinForm.IsometryEquiv.coe_toLinearEquiv,
    ← LinearMap.BilinForm.IsometryEquiv.coe_symm_toLinearEquiv, LinearEquiv.apply_symm_apply]
  exact (spinSixWedgeIsometryEquivPolarSplit_apply_inr K i).symm

variable [Invertible (2 : K)]

/-- The quadratic form whose un-halved polar form is the volume pairing on `⋀²(K⁴)`.
It is half the diagonal of the wedge pairing; the factor `⅟2` makes its un-halved polar form
equal to `spinSixWedgeForm` (see `polarBilin_spinSixWedgeQuadraticForm`). -/
noncomputable def spinSixWedgeQuadraticForm : QuadraticForm K (⋀[K]^2 (Fin 4 → K)) :=
  ⅟(2 : K) • (spinSixWedgeForm K).toQuadraticMap

/-- The quadratic wedge form is half the diagonal of the wedge pairing. -/
@[simp]
theorem spinSixWedgeQuadraticForm_apply (x : ⋀[K]^2 (Fin 4 → K)) :
    spinSixWedgeQuadraticForm K x = ⅟(2 : K) * spinSixWedgeForm K x x := by
  simp [spinSixWedgeQuadraticForm, LinearMap.BilinMap.toQuadraticMap_apply]

/-- The un-halved polar form of the normalized wedge quadratic form is the wedge pairing. -/
@[simp]
theorem polarBilin_spinSixWedgeQuadraticForm :
    (spinSixWedgeQuadraticForm K).polarBilin = spinSixWedgeForm K := by
  apply LinearMap.ext₂
  intro x y
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    spinSixWedgeQuadraticForm_apply, map_add, LinearMap.add_apply]
  rw [(spinSixWedgeForm_isSymm K).eq y x]
  calc
    _ = (⅟(2 : K) * 2) * spinSixWedgeForm K x y := by ring
    _ = spinSixWedgeForm K x y := by simp

/-- The normalized wedge quadratic form is isometric to three standard hyperbolic planes. -/
noncomputable def spinSixWedgeQuadraticIsometryEquivSplit :
    (spinSixWedgeQuadraticForm K).IsometryEquiv (splitEvenForm K 3) where
  __ := (spinSixWedgeIsometryEquivPolarSplit K).toLinearEquiv
  map_app' x := by
    rw [spinSixWedgeQuadraticForm_apply,
      ← (spinSixWedgeIsometryEquivPolarSplit K).map_app x x]
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
    simp [← mul_assoc]

/-- The quadratic isometry uses exactly the already specified bilinear coordinates. -/
@[simp]
theorem spinSixWedgeQuadraticIsometryEquivSplit_toLinearEquiv :
    (spinSixWedgeQuadraticIsometryEquivSplit K).toLinearEquiv =
      (spinSixWedgeIsometryEquivPolarSplit K).toLinearEquiv := (rfl)

/-- Evaluation of the quadratic comparison is evaluation of the bilinear comparison. -/
@[simp]
theorem spinSixWedgeQuadraticIsometryEquivSplit_apply (x : ⋀[K]^2 (Fin 4 → K)) :
    spinSixWedgeQuadraticIsometryEquivSplit K x = spinSixWedgeIsometryEquivPolarSplit K x := (rfl)

/-- The inverse quadratic comparison uses the inverse bilinear coordinates. -/
@[simp]
theorem spinSixWedgeQuadraticIsometryEquivSplit_symm_apply (x : SplitEvenSpace K 3) :
    (spinSixWedgeQuadraticIsometryEquivSplit K).symm x =
      (spinSixWedgeIsometryEquivPolarSplit K).symm x := (rfl)

end TauCeti
