/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Points
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Differential
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Tangent.Basic
public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic

/-!
# Two-entry coroot cocharacters of the special linear group

For distinct indices `i ≠ j` in `Fin n`, the two-coordinate diagonal matrices
`Matrix.SpecialLinearGroup.diag2nUnit hij u = diag(…, u, …, u⁻¹, …)` have determinant one over
every commutative ring `R`. This file promotes `u ↦ diag2nUnit hij u` to a cocharacter of `SLₙ`,
given contravariantly on coordinate Hopf algebras by

```text
diag2nCocharacter R hij : O(SLₙ) →ₐc[R] R[T; T⁻¹].
```

The construction factors the general-linear weight cocharacter
`TauCeti.GeneralLinear.weightCocharacter (Pi.single i 1 - Pi.single j 1)` through the
determinant-one quotient `O(GLₙ) ⟶ O(SLₙ)`, using the vanishing of the weight sum. Over every
commutative base ring `R` and coefficient `R`-algebra `B`, its differential sends a tangent vector
`d` of `𝔾ₘ` to `(MultiplicativeGroup.tangentLinearEquiv d) • (Eᵢᵢ - Eⱼⱼ)` in `sl(n, B)`, and its
coordinate morphism is surjective (so the represented cocharacter `𝔾ₘ → SLₙ` is a closed
immersion).

For `n = 2` and `(i, j) = (0, 1)`, this is the fundamental coroot cocharacter `t ↦ diag(t, t⁻¹)`
of `SL₂`: its differential sends the canonical generator of `Lie(𝔾ₘ)` to the Cartan element
`H = E₀₀ - E₁₁` of `sl(2)`, and its value at `-1` is `-I ∈ SL₂`.

## Main declarations

* `TauCeti.SpecialLinear.diag2nWeight`: the integer weight `Pi.single i 1 - Pi.single j 1`.
* `TauCeti.SpecialLinear.diag2nCoordinateMap` and `TauCeti.SpecialLinear.diag2nCocharacter`:
  the coordinate morphism `O(SLₙ) →ₐc[R] R[T; T⁻¹]` of `t ↦ diag2nUnit hij t`.
* `TauCeti.SpecialLinear.diag2nCocharacter_comp_coordinateMap`: compatibility with the ambient
  general-linear weight cocharacter.
* `TauCeti.SpecialLinear.diag2nCocharacter_surjective`: surjectivity of the coordinate morphism over
  every commutative ring.
* `TauCeti.SpecialLinear.pointsMulEquiv_mapDomain_diag2nCocharacter` and
  `TauCeti.SpecialLinear.pointsMulEquiv_pointsHom_diag2nCocharacter`: on `A`-points, the cocharacter
  sends `u : Aˣ` to `Matrix.SpecialLinearGroup.diag2nUnit hij u`.
* `TauCeti.SpecialLinear.pointsMulEquiv_pointsHom_diag2nCocharacter_neg_one`: in `SL₂`, evaluating
  the standard coroot cocharacter at `-1` gives `-1`.
* `TauCeti.SpecialLinear.tangentMatrix_derivationComp_diag2nCocharacter`: its differential sends a
  tangent vector `d` to `LieAlgebra.SpecialLinear.singleSubSingle i j` scaled by the tangent
  parameter of `d`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 21.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §§16.2 and 26.3.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u v

section Weights

variable {n : ℕ}

/-- The integer weight vector `eᵢ - eⱼ` placing `1` at `i`, `-1` at `j`, and `0` elsewhere
when `i ≠ j`. -/
def diag2nWeight (i j : Fin n) : Fin n → ℤ :=
  Pi.single i 1 - Pi.single j 1

@[simp]
theorem diag2nWeight_apply (i j k : Fin n) :
    diag2nWeight i j k = Pi.single (M := fun _ ↦ ℤ) i 1 k - Pi.single (M := fun _ ↦ ℤ) j 1 k :=
  (rfl)

theorem diag2nWeight_self_left {i j : Fin n} (hij : i ≠ j) :
    diag2nWeight i j i = 1 := by
  simp [hij]

theorem diag2nWeight_self_right {i j : Fin n} (hij : i ≠ j) :
    diag2nWeight i j j = -1 := by
  simp [hij.symm]

theorem diag2nWeight_of_ne {i j k : Fin n} (hki : k ≠ i) (hkj : k ≠ j) :
    diag2nWeight i j k = 0 := by
  simp [hki, hkj]

/-- The entries of `diag2nWeight i j` sum to zero. -/
theorem sum_diag2nWeight_eq_zero (i j : Fin n) :
    ∑ k, diag2nWeight i j k = 0 := by
  simp [diag2nWeight]

end Weights

section Cocharacter

variable (R : Type u) [CommRing R] {n : ℕ} {i j : Fin n}

private theorem weightCocharacter_determinantGroupLike_diag2nWeight :
    GeneralLinear.weightCocharacter (R := R) (diag2nWeight i j)
        (GeneralLinear.determinantGroupLike R n : GeneralLinear.coordinateHopfAlgebra R n) = 1 := by
  let p : WithConv (LaurentPolynomial R →ₐ[R] LaurentPolynomial R) :=
    toConv (AlgHom.id R (LaurentPolynomial R))
  have hdet := GeneralLinear.point_apply_determinantGroupLike (R := R) (n := n)
    (BialgHom.mapDomain (GeneralLinear.weightCocharacter (R := R) (diag2nWeight i j)) p)
  have hp : (BialgHom.mapDomain (GeneralLinear.weightCocharacter (R := R) (diag2nWeight i j))
      p).ofConv = (GeneralLinear.weightCocharacter (R := R) (diag2nWeight i j)).toAlgHom := by
    ext x
    simp [p, BialgHom.mapDomain_apply]
  rw [hp, BialgHom.coe_toAlgHom] at hdet
  rw [hdet, ← GeneralLinear.pointsMulEquiv_apply, GeneralLinear.mapDomain_weightCocharacter,
    GeneralLinear.pointsMulEquiv_weightCocharacterPoints]
  rw [← Matrix.GeneralLinearGroup.val_det_apply, det_diagGL]
  have hprod : ∏ k : Fin n,
      GeneralLinear.weightDiagonalUnits (diag2nWeight i j)
        (MultiplicativeGroup.pointsMulEquiv p) k =
      (MultiplicativeGroup.pointsMulEquiv p) ^ (∑ k : Fin n, diag2nWeight i j k) := by
    simp [GeneralLinear.weightDiagonalUnits_apply, Finset.prod_zpow_eq_zpow_sum]
  rw [congrArg Units.val hprod, sum_diag2nWeight_eq_zero, zpow_zero, Units.val_one]

/-- **The categorical coordinate morphism of the two-entry coroot cocharacter of `SLₙ`.**
It factors `GeneralLinear.weightCocharacter (diag2nWeight i j)` through the determinant-one
quotient `O(GLₙ) ⟶ O(SLₙ)`. -/
noncomputable def diag2nCoordinateMap (hij : i ≠ j) :
    coordinateHopfAlgebra R n ⟶ _root_.CommHopfAlgCat.of R (LaurentPolynomial R) :=
  let _ := hij
  CommHopfAlgCat.liftQuotient (definingHopfIdeal R n)
    (_root_.CommHopfAlgCat.ofHom (GeneralLinear.weightCocharacter (R := R) (diag2nWeight i j)))
    ((definingHopfIdeal_toIdeal_le_ker_iff R n _).2
      (weightCocharacter_determinantGroupLike_diag2nWeight R))

/-- **The two-entry coroot cocharacter `O(SLₙ) →ₐc[R] R[T; T⁻¹]`** attached to `i ≠ j`,
representing `u ↦ Matrix.SpecialLinearGroup.diag2nUnit hij u`. -/
noncomputable def diag2nCocharacter (hij : i ≠ j) :
    coordinateHopfAlgebra R n →ₐc[R] LaurentPolynomial R :=
  (diag2nCoordinateMap R hij).hom

/-- `diag2nCocharacter` is the bialgebra morphism underlying `diag2nCoordinateMap`. -/
@[simp]
theorem hom_diag2nCoordinateMap (hij : i ≠ j) :
    (diag2nCoordinateMap R hij).hom = diag2nCocharacter R hij :=
  (rfl)

/-- Composing the quotient map `O(GLₙ) ⟶ O(SLₙ)` with `diag2nCoordinateMap` recovers the ambient
general-linear weight cocharacter. -/
@[simp]
theorem coordinateMap_comp_diag2nCoordinateMap (hij : i ≠ j) :
    coordinateMap R n ≫ diag2nCoordinateMap R hij =
      _root_.CommHopfAlgCat.ofHom (GeneralLinear.weightCocharacter (R := R) (diag2nWeight i j)) :=
  CommHopfAlgCat.mkQuotient_comp_liftQuotient _ _ _

/-- Composing `diag2nCocharacter` with the coordinate map `O(GLₙ) →ₐc[R] O(SLₙ)` recovers
`GeneralLinear.weightCocharacter (diag2nWeight i j)`. -/
theorem diag2nCocharacter_comp_coordinateMap (hij : i ≠ j) :
    (diag2nCocharacter R hij).comp (coordinateMap R n).hom =
      GeneralLinear.weightCocharacter (R := R) (diag2nWeight i j) := by
  simpa only [_root_.CommHopfAlgCat.hom_comp, hom_diag2nCoordinateMap,
    _root_.CommHopfAlgCat.hom_ofHom] using
    congrArg _root_.CommHopfAlgCat.Hom.hom (coordinateMap_comp_diag2nCoordinateMap R hij)

/-- Evaluation of `diag2nCocharacter` on the image of a generic matrix entry `X_{ab}`. -/
theorem diag2nCocharacter_apply_coordinateMap_X (hij : i ≠ j) (a b : Fin n) :
    diag2nCocharacter R hij
        ((coordinateMap R n).hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
          (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (a, b))))) =
      if a = b then LaurentPolynomial.T (diag2nWeight i j a) else 0 := by
  rw [← BialgHom.comp_apply, diag2nCocharacter_comp_coordinateMap,
    GeneralLinear.weightCocharacter_apply_X]

/-- **The coordinate morphism of `diag2nCocharacter` is surjective** over every commutative ring:
contravariantly, the coroot cocharacter `𝔾ₘ → SLₙ` is a closed immersion. -/
theorem diag2nCocharacter_surjective (hij : i ≠ j) :
    Function.Surjective (diag2nCocharacter R hij) := by
  change Function.Surjective (diag2nCocharacter R hij).toAlgHom
  rw [← AlgHom.range_eq_top, eq_top_iff]
  suffices ∀ p : LaurentPolynomial R, p ∈ (diag2nCocharacter R hij).toAlgHom.range from
    fun p _ ↦ this p
  have hT1 : LaurentPolynomial.T 1 ∈ (diag2nCocharacter R hij).toAlgHom.range := by
    refine ⟨(coordinateMap R n).hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
      (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (i, i)))), ?_⟩
    simpa [hij] using diag2nCocharacter_apply_coordinateMap_X R hij i i
  have hTm1 : LaurentPolynomial.T (-1) ∈ (diag2nCocharacter R hij).toAlgHom.range := by
    refine ⟨(coordinateMap R n).hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv R n
      (GeneralLinear.coordinateRingMap R n (MvPolynomial.X (j, j)))), ?_⟩
    simpa [hij.symm] using diag2nCocharacter_apply_coordinateMap_X R hij j j
  have hpow (a : ℤ) (m : ℕ) :
      (LaurentPolynomial.T a : LaurentPolynomial R) ^ m = LaurentPolynomial.T (m * a) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ih, ← LaurentPolynomial.T_add]
      push_cast
      ring_nf
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => exact Subalgebra.add_mem _ hp hq
  | C_mul_T k r =>
    have hTk : LaurentPolynomial.T k ∈ (diag2nCocharacter R hij).toAlgHom.range := by
      rcases Int.eq_nat_or_neg k with ⟨m, rfl | rfl⟩
      · have hm : (LaurentPolynomial.T 1 : LaurentPolynomial R) ^ m = LaurentPolynomial.T m := by
          rw [hpow, mul_one]
        exact hm ▸ Subalgebra.pow_mem _ hT1 m
      · have hm : (LaurentPolynomial.T (-1) : LaurentPolynomial R) ^ m =
            LaurentPolynomial.T (-(m : ℤ)) := by
          rw [hpow, mul_neg, mul_one]
        exact hm ▸ Subalgebra.pow_mem _ hTm1 m
    have hCr : LaurentPolynomial.C r ∈ (diag2nCocharacter R hij).toAlgHom.range := by
      rw [LaurentPolynomial.C_eq_algebraMap]
      exact Subalgebra.algebraMap_mem _ r
    exact Subalgebra.mul_mem _ hCr hTk

end Cocharacter

section Points

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable {n : ℕ} {i j : Fin n}

/-- **On `A`-points, `diag2nCocharacter` sends a `𝔾ₘ`-point to `diag2nUnit hij`.** -/
theorem pointsMulEquiv_mapDomain_diag2nCocharacter (hij : i ≠ j)
    (p : WithConv (LaurentPolynomial R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) n (BialgHom.mapDomain (diag2nCocharacter R hij) p) =
      Matrix.SpecialLinearGroup.diag2nUnit hij (MultiplicativeGroup.pointsMulEquiv p) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [← pointsMulEquiv_toGL R n, Matrix.SpecialLinearGroup.toGL_diag2nUnit]
  have hquot : CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra R n)
      (definingHopfIdeal R n) (CommAlgCat.of R A)
      (BialgHom.mapDomain (diag2nCocharacter R hij) p) =
      BialgHom.mapDomain (GeneralLinear.weightCocharacter (R := R) (diag2nWeight i j)) p := by
    apply WithConv.ofConv_injective
    ext x
    rw [CommHopfAlgCat.quotientPointsHom_apply]
    simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply,
      ← diag2nCocharacter_comp_coordinateMap R hij, BialgHom.comp_toAlgHom]
  rw [hquot, GeneralLinear.mapDomain_weightCocharacter,
    GeneralLinear.pointsMulEquiv_weightCocharacterPoints]
  congr 1
  funext r
  rw [GeneralLinear.weightDiagonalUnits_apply]
  by_cases hri : r = i
  · subst hri
    simp [hij]
  · by_cases hrj : r = j
    · subst hrj
      simp [hri]
    · simp [hri, hrj]

/-- **On unit parameters `u : Aˣ`, `Cocharacter.pointsHom` of `diag2nCocharacter` produces
`Matrix.SpecialLinearGroup.diag2nUnit hij u`.** -/
@[simp]
theorem pointsMulEquiv_pointsHom_diag2nCocharacter (hij : i ≠ j) (u : Aˣ) :
    pointsMulEquiv (R := R) (A := A) n (Cocharacter.pointsHom A (diag2nCocharacter R hij) u) =
      Matrix.SpecialLinearGroup.diag2nUnit hij u := by
  rw [Cocharacter.pointsHom_apply, pointsMulEquiv_mapDomain_diag2nCocharacter]
  congr 1
  ext
  simp [MultiplicativeGroup.pointsMulEquiv_apply]

/-- The coroot cocharacter is injective on unit-valued points over every commutative `R`-algebra. -/
theorem pointsHom_diag2nCocharacter_injective (hij : i ≠ j) :
    Function.Injective (Cocharacter.pointsHom A (diag2nCocharacter R hij)) := by
  intro u v huv
  have hmat := congrArg (pointsMulEquiv (R := R) (A := A) n) huv
  rw [pointsMulEquiv_pointsHom_diag2nCocharacter,
    pointsMulEquiv_pointsHom_diag2nCocharacter] at hmat
  have hii := congrArg (fun M : Matrix.SpecialLinearGroup (Fin n) A ↦
    (M : Matrix (Fin n) (Fin n) A) i i) hmat
  simp only [Matrix.SpecialLinearGroup.diag2nUnit_coe, Matrix.diagonal_apply_eq, ↓reduceIte] at hii
  exact Units.ext hii

/-- In `SL₂`, evaluating the standard coroot cocharacter `t ↦ diag(t, t⁻¹)` at `-1` gives `-I`. -/
@[simp]
theorem pointsMulEquiv_pointsHom_diag2nCocharacter_neg_one :
    pointsMulEquiv (R := R) (A := A) 2
        (Cocharacter.pointsHom A (diag2nCocharacter R (zero_ne_one : (0 : Fin 2) ≠ 1)) (-1)) =
      -1 := by
  rw [pointsMulEquiv_pointsHom_diag2nCocharacter]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.SpecialLinearGroup.diag2nUnit_coe]

end Points

section Differential

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
variable {n : ℕ} {i j : Fin n}

/-- **The differential of `diag2nCocharacter` in `sl(n, B)`**: a tangent vector `d` of `𝔾ₘ` maps to
`LieAlgebra.SpecialLinear.singleSubSingle i j` evaluated at its tangent parameter. -/
@[simp]
theorem tangentMatrix_derivationComp_diag2nCocharacter (hij : i ≠ j)
    (d : Derivation R (LaurentPolynomial R)
      (Bialgebra.CounitAlgebra R (LaurentPolynomial R) B)) :
    tangentMatrix n (derivationComp (B := B) (diag2nCocharacter R hij) d) =
      LieAlgebra.SpecialLinear.singleSubSingle i j (MultiplicativeGroup.tangentLinearEquiv d) := by
  apply Subtype.ext
  rw [tangentMatrix_apply_coe, HopfIdeal.quotientLieHom_apply, ← LinearMap.comp_apply,
    ← derivationComp_comp]
  have hcomp : (diag2nCocharacter R hij).comp
      (Bialgebra.Quotient.mkBialgHom (R := R) (definingHopfIdeal R n).toIdeal) =
      GeneralLinear.weightCocharacter (R := R) (diag2nWeight i j) :=
    diag2nCocharacter_comp_coordinateMap R hij
  rw [hcomp, GeneralLinear.tangentMatrix_derivationComp_weightCocharacter]
  ext a b
  rw [LieAlgebra.SpecialLinear.val_singleSubSingle, Matrix.sub_apply,
    Matrix.single_apply, Matrix.single_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i
    · subst hai
      simp only [↓reduceIte, diag2nWeight_self_left hij, one_zsmul, hij.symm, and_self, sub_zero]
    · by_cases haj : a = j
      · subst haj
        simp only [↓reduceIte, diag2nWeight_self_right hij, neg_one_zsmul, hij, and_self, zero_sub]
      · simp only [↓reduceIte, diag2nWeight_of_ne hai haj, zero_zsmul, Ne.symm hai, Ne.symm haj,
          and_self, sub_zero]
  · have hia : ¬(i = a ∧ i = b) := fun ⟨h1, h2⟩ ↦ hab (h1.symm.trans h2)
    have hja : ¬(j = a ∧ j = b) := fun ⟨h1, h2⟩ ↦ hab (h1.symm.trans h2)
    simp only [hab, hia, hja, ↓reduceIte, sub_zero]

/-- Under `tangentLieEquivSl`, the canonical unit tangent vector of `𝔾ₘ` maps along
`diag2nCocharacter` to the coroot element `Eᵢᵢ - Eⱼⱼ` of `sl(n, B)`. -/
@[simp]
theorem derivationComp_diag2nCocharacter_unit (hij : i ≠ j) :
    derivationComp (B := B) (diag2nCocharacter R hij)
        ((MultiplicativeGroup.tangentLinearEquiv (R := R) (B := B)).symm 1) =
      (tangentLieEquivSl (R := R) (B := B) n).symm
        (LieAlgebra.SpecialLinear.singleSubSingle i j 1) := by
  apply (tangentLieEquivSl (R := R) (B := B) n).injective
  simpa only [LieEquiv.coe_toLieHom, tangentLieEquivSl_apply (R := R) (B := B),
    tangentMatrix_derivationComp_diag2nCocharacter (R := R) (B := B),
    LinearEquiv.apply_symm_apply] using
    ((tangentLieEquivSl (R := R) (B := B) n).apply_symm_apply
      (LieAlgebra.SpecialLinear.singleSubSingle i j 1)).symm

end Differential

end TauCeti.SpecialLinear
