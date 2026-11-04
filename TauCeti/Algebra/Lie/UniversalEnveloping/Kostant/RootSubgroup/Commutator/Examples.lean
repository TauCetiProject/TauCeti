/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import TauCeti.Algebra.Lie.G2.ShortRoot.Basic
public import TauCeti.Algebra.Lie.Matrix.IntegralCast
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.CoordinateLattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.G2.Relations
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.CubeZeroMatrix

/-!
# Explicit matrix checks for Steinberg's Chevalley commutator relations

This file instantiates the Kostant root-subgroup commutator relations on three explicit integral
matrix representations over an arbitrary commutative ring `R`, verifying the exponents and signs in
Steinberg's convention `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹` across singly, doubly, and triply laced root
strings:

1. **Type `A₂` on `R³`** (`a2RootMatrix`): `⁅x_α(u), x_β(v)⁆ = x_{α+β}(u * v)`, falsified upon
   negating the exponent whenever `(2 : R) ≠ 0`.
2. **Type `C₂ = Sp₄` on `R⁴`** (`c2RootMatrix`): `⁅x_α(u), x_β(v)⁆ = x_{α+β}(-(u * v)) *
   x_{α+2β}(-(u * v ^ 2))`, with `(0, 2)` entry `-1` at `u = v = 1`, distinguishing Steinberg's
   `-1` sign on `c_{1,2}` from `+1` whenever `(2 : R) ≠ 0`.
3. **Type `G₂` on `R⁷`** (`g2PosRootMatrix`): verifies `⁅x_α(u), x_β(v)⁆`, `⁅x_β(u), x_α(v)⁆`, and
   `⁅x_α(u), x_{α+β}(v)⁆` on the seven-dimensional short-root module, and checks that negating
   `c_{3,2}` or `c_{2,3}` falsifies the relation whenever `(4 : R) ≠ 0` or `(2 : R) ≠ 0`.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.integralMatrixRootSubgroup`: the Kostant root-subgroup
  homomorphism `Multiplicative R →* Matrix.GeneralLinearGroup n R` attached to a cube-zero family of
  integral matrices with integral divided squares on `coordinateLattice n`.
* `TauCeti.UniversalEnvelopingAlgebra.a2RootMatrix`, `c2RootMatrix`, and `g2PosRootMatrix`: the
  positive root-string matrix families in types `A₂`, `C₂`, and `G₂`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_a2RootSubgroup`,
  `commutatorElement_c2RootSubgroup`, `commutatorElement_g2PosRootSubgroup_short_long`,
  `commutatorElement_g2PosRootSubgroup_long_short`, and
  `commutatorElement_g2PosRootSubgroup_short_short` (with sign-falsification checks).

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15, pp. 22--25.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plates I, III, and IX.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§19.3 and 25--27.
-/

public section

open scoped Matrix commutatorElement
open TauCeti.AdditiveGroup (gaPointsMulEquiv)
open Multiplicative (ofAdd toAdd)
open _root_.UniversalEnvelopingAlgebra (ι)

namespace TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra
attribute [local instance] TauCeti.moduleNNRat

/-! ## Kostant root subgroups of cube-zero integral matrix families -/

section IntegralMatrixFamily

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem representation_matrix_ι (X : Matrix n n ℚ) :
    representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ X) = Matrix.toLinAlgEquiv' X :=
  LinearMap.ext fun v => by
    rw [representation_ι_apply, Matrix.lie_apply, Matrix.toLinAlgEquiv'_apply]

/-- An integral matrix that cubes to zero acts with vanishing cube on `n → ℚ`. -/
theorem pow_three_representation_matrix_eq_zero {X : Matrix n n ℤ} (hcube : X ^ 3 = 0) :
    representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ (TauCeti.matrixIntCastLieHom ℚ X)) ^ 3 = 0 := by
  rw [representation_matrix_ι, TauCeti.matrixIntCastLieHom_eq_map]
  have hmap : X.map (Int.cast : ℤ → ℚ) = (RingHom.mapMatrix (Int.castRingHom ℚ)) X := by
    ext a b; simp
  rw [hmap, ← map_pow, ← map_pow, hcube]; simp

/-- An integral matrix that cubes to zero acts nilpotently on `n → ℚ`. -/
theorem isNilpotent_representation_matrix {X : Matrix n n ℤ} (hcube : X ^ 3 = 0) :
    IsNilpotent
      (representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ (TauCeti.matrixIntCastLieHom ℚ X))) :=
  ⟨3, pow_three_representation_matrix_eq_zero hcube⟩

private theorem dividedPower_two_representation_matrix_apply {X D : Matrix n n ℤ}
    (hsq : X * X = 2 • D) (v : n → ℚ) :
    Associative.dividedPower 2
      (representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ (TauCeti.matrixIntCastLieHom ℚ X))) v =
      D.map (Int.castRingHom ℚ) *ᵥ v := by
  have hmapX : TauCeti.matrixIntCastLieHom ℚ X = (RingHom.mapMatrix (Int.castRingHom ℚ)) X := by
    ext a b; simp
  have hsq' : representation ℚ (Matrix n n ℚ) (n → ℚ)
      (ι ℚ (TauCeti.matrixIntCastLieHom ℚ X)) ^ 2 =
      (2 : ℕ) • Matrix.toLinAlgEquiv' (D.map (Int.castRingHom ℚ)) := by
    rw [representation_matrix_ι, hmapX, ← map_pow, ← map_pow, pow_two, hsq, map_nsmul,
      map_nsmul, RingHom.mapMatrix_apply]
  rw [Associative.dividedPower_def, LinearMap.smul_apply, hsq', LinearMap.smul_apply,
    Matrix.toLinAlgEquiv'_apply, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  norm_num [Nat.factorial]

/-- The standard coordinate lattice is preserved by the Kostant `ℤ`-form of any family of cube-zero
integral matrices whose squares are even integral matrices. -/
theorem kostantForm_integralMatrix_mem_coordinateLattice {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    (u : _root_.UniversalEnvelopingAlgebra ℚ (Matrix n n ℚ))
    (hu : u ∈ kostantForm (fun i => TauCeti.matrixIntCastLieHom ℚ (E i)) Empty.elim)
    (v : n → ℚ) (hv : v ∈ (TauCeti.coordinateLattice n).toAddSubgroup) :
    representation ℚ (Matrix n n ℚ) (n → ℚ) u v ∈
      (TauCeti.coordinateLattice n).toAddSubgroup := by
  refine kostantForm_apply_mem_coordinateLattice_of_pow_eq_zero
    (fun i => TauCeti.matrixIntCastLieHom ℚ (E i)) Empty.elim
    (representation ℚ (Matrix n n ℚ) (n → ℚ))
    (wt := fun _ => Empty.elim) 3 (fun i => pow_three_representation_matrix_eq_zero (hcube i))
    (fun i m hm w hw => ?_)
    (fun a => (isCartanWeightVector_iff Empty.elim _).mpr Empty.rec) hu hv
  have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm' with rfl | rfl | rfl
  · simpa using hw
  · rw [Associative.dividedPower_one, representation_ι_apply, Matrix.lie_apply]
    exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (E i) hw
  · rw [dividedPower_two_representation_matrix_apply (hsq i)]
    have hD : (D i).map (Int.castRingHom ℚ) = TauCeti.matrixIntCastLieHom ℚ (D i) := by
      ext a b; simp
    rw [hD]; exact Matrix.intCastLieHom_mulVec_mem_coordinateLattice (D i) hw

/-- **The Kostant root subgroup of a cube-zero integral matrix family** in the standard coordinate
basis over `R`. -/
noncomputable def integralMatrixRootSubgroup {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    (R : Type*) [CommRing R] (i : I) :
    Multiplicative R →* _root_.Matrix.GeneralLinearGroup n R :=
  (kostantRootSubgroupMatrix (fun k => TauCeti.matrixIntCastLieHom ℚ (E k)) Empty.elim
    (representation ℚ (Matrix n n ℚ) (n → ℚ)) (TauCeti.coordinateLattice n).toAddSubgroup
    (kostantForm_integralMatrix_mem_coordinateLattice E D hsq hcube) i
    (isNilpotent_representation_matrix (hcube i))
    (TauCeti.coordinateLatticeBasis n)).comp (gaPointsMulEquiv (R := ℤ) (A := R)).symm.toMonoidHom

/-- The matrix of `integralMatrixRootSubgroup` at `u` is `1 + u • Eᵢ + u² • Dᵢ`. -/
@[simp]
theorem coe_integralMatrixRootSubgroup {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    (R : Type*) [CommRing R] (i : I) (u : Multiplicative R) :
    ((integralMatrixRootSubgroup E D hsq hcube R i u : _root_.Matrix.GeneralLinearGroup n R) :
        Matrix n n R) =
      1 + toAdd u • (E i).map (Int.cast : ℤ → R) +
        toAdd u ^ 2 • (D i).map (Int.cast : ℤ → R) := by
  have hact₁ : ∀ s,
      representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ (TauCeti.matrixIntCastLieHom ℚ (E i)))
        ((TauCeti.coordinateLatticeBasis n s : TauCeti.coordinateLattice n) : n → ℚ) =
        ∑ r, E i r s •
          ((TauCeti.coordinateLatticeBasis n r : TauCeti.coordinateLattice n) : n → ℚ) := by
    intro s; rw [representation_ι_apply, Matrix.lie_apply]
    have hE : TauCeti.matrixIntCastLieHom ℚ (E i) = (E i).map (Int.castRingHom ℚ) := by
      ext a b; simp
    rw [hE]; exact Matrix.intCast_mulVec_coordinateLatticeBasis_eq_sum (E i) s
  have hact₂ : ∀ s,
      Associative.dividedPower 2
        (representation ℚ (Matrix n n ℚ) (n → ℚ) (ι ℚ (TauCeti.matrixIntCastLieHom ℚ (E i))))
        ((TauCeti.coordinateLatticeBasis n s : TauCeti.coordinateLattice n) : n → ℚ) =
        ∑ r, D i r s •
          ((TauCeti.coordinateLatticeBasis n r : TauCeti.coordinateLattice n) : n → ℚ) := by
    intro s; rw [dividedPower_two_representation_matrix_apply (hsq i)]
    exact Matrix.intCast_mulVec_coordinateLatticeBasis_eq_sum (D i) s
  simpa only [integralMatrixRootSubgroup, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] using
    kostantRootSubgroupMatrix_eq_one_add_smul_add_smul
      (fun k => TauCeti.matrixIntCastLieHom ℚ (E k)) Empty.elim
      (representation ℚ (Matrix n n ℚ) (n → ℚ)) (TauCeti.coordinateLattice n).toAddSubgroup
      (kostantForm_integralMatrix_mem_coordinateLattice E D hsq hcube) i
      (isNilpotent_representation_matrix (hcube i))
      (TauCeti.coordinateLatticeBasis n) (E i) (D i)
      (TauCeti.nilpotencyClass_le_of_pow_eq_zero
        (pow_three_representation_matrix_eq_zero (hcube i)))
      hact₁ hact₂ ((gaPointsMulEquiv (R := ℤ) (A := R)).symm u)

/-- When the divided-square matrix `D i` vanishes, `integralMatrixRootSubgroup` is `1 + u • Eᵢ`. -/
theorem coe_integralMatrixRootSubgroup_of_eq_zero {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    (R : Type*) [CommRing R] {i : I} (hD : D i = 0) (u : Multiplicative R) :
    ((integralMatrixRootSubgroup E D hsq hcube R i u : _root_.Matrix.GeneralLinearGroup n R) :
        Matrix n n R) =
      1 + toAdd u • (E i).map (Int.cast : ℤ → R) := by
  rw [coe_integralMatrixRootSubgroup, hD, Matrix.map_zero _ Int.cast_zero, smul_zero, add_zero]

/-- An off-diagonal entry `±1` where the divided square vanishes makes the root-subgroup
parametrization injective over every commutative ring. -/
theorem integralMatrixRootSubgroup_eq_iff_of_entry_unit {I : Type*}
    (E D : I → Matrix n n ℤ) (hsq : ∀ i, E i * E i = 2 • D i) (hcube : ∀ i, E i ^ 3 = 0)
    {R : Type*} [CommRing R] {i : I} {r s : n} (hrs : r ≠ s)
    (hE : E i r s = 1 ∨ E i r s = -1) (hD : D i r s = 0) (u v : R) :
    integralMatrixRootSubgroup E D hsq hcube R i (ofAdd u) =
      integralMatrixRootSubgroup E D hsq hcube R i (ofAdd v) ↔ u = v := by
  refine ⟨fun h => ?_, fun h => congrArg _ (congrArg ofAdd h)⟩
  have hentry := congrArg (fun g : _root_.Matrix.GeneralLinearGroup n R => (g : Matrix n n R) r s) h
  simp only [coe_integralMatrixRootSubgroup, toAdd_ofAdd, Matrix.add_apply, Matrix.one_apply_ne hrs,
    Matrix.smul_apply, Matrix.map_apply, hD, Int.cast_zero, smul_eq_mul, mul_zero, zero_add,
    add_zero] at hentry
  rcases hE with h1 | hm1
  · simpa [h1] using hentry
  · exact neg_inj.mp (by simpa [hm1] using hentry)

private theorem intLie {I : Type*} (E : I → Matrix n n ℤ) (i j k : I) (c : ℤ)
    (h : ⁅E i, E j⁆ = c • E k) :
    ⁅TauCeti.matrixIntCastLieHom ℚ (E i), TauCeti.matrixIntCastLieHom ℚ (E j)⁆ =
      c • TauCeti.matrixIntCastLieHom ℚ (E k) := by
  rw [← (TauCeti.matrixIntCastLieHom ℚ).map_lie, h, map_zsmul]

private theorem intZsmulLie {I : Type*} (E : I → Matrix n n ℤ) (i j k : I) (a b : ℤ)
    (h : a • ⁅E i, E j⁆ = b • E k) :
    a • ⁅TauCeti.matrixIntCastLieHom ℚ (E i), TauCeti.matrixIntCastLieHom ℚ (E j)⁆ =
      b • TauCeti.matrixIntCastLieHom ℚ (E k) := by
  rw [← (TauCeti.matrixIntCastLieHom ℚ).map_lie, ← map_zsmul, h, map_zsmul]

private theorem intLieLie {I : Type*} (E : I → Matrix n n ℤ) (i j k : I) (c : ℤ)
    (h : ⁅E i, ⁅E i, E j⁆⁆ = c • E k) :
    ⁅TauCeti.matrixIntCastLieHom ℚ (E i),
        ⁅TauCeti.matrixIntCastLieHom ℚ (E i), TauCeti.matrixIntCastLieHom ℚ (E j)⁆⁆ =
      c • TauCeti.matrixIntCastLieHom ℚ (E k) := by
  rw [← (TauCeti.matrixIntCastLieHom ℚ).map_lie, ← (TauCeti.matrixIntCastLieHom ℚ).map_lie, h,
    map_zsmul]

private theorem intLieZero {I : Type*} (E : I → Matrix n n ℤ) (i j : I) (h : ⁅E i, E j⁆ = 0) :
    ⁅TauCeti.matrixIntCastLieHom ℚ (E i), TauCeti.matrixIntCastLieHom ℚ (E j)⁆ = 0 := by
  rw [← (TauCeti.matrixIntCastLieHom ℚ).map_lie, h, map_zero]

end IntegralMatrixFamily

/-! ## Check 1: Type `A₂` on `R³` -/

section TypeA2

/-- The three positive root matrices `E₀₁`, `E₁₂`, `E₀₂` of `𝔰𝔩₃` in the standard basis. -/
def a2RootMatrix : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![Matrix.single 0 1 1, Matrix.single 1 2 1, Matrix.single 0 2 1]

/-- Each positive root matrix of `A₂` squares to zero. -/
theorem a2RootMatrix_mul_self (i : Fin 3) :
    a2RootMatrix i * a2RootMatrix i = (2 : ℕ) • (0 : Matrix (Fin 3) (Fin 3) ℤ) := by
  revert i; decide

/-- Each positive root matrix of `A₂` cubes to zero. -/
theorem a2RootMatrix_pow_three (i : Fin 3) : a2RootMatrix i ^ 3 = 0 := by
  revert i; decide

/-- The Kostant root subgroups `x_α`, `x_β`, `x_{α+β}` of `A₂` in `GL₃(R)`. -/
noncomputable abbrev a2RootSubgroup (R : Type*) [CommRing R] (i : Fin 3) :
    Multiplicative R →* _root_.Matrix.GeneralLinearGroup (Fin 3) R :=
  integralMatrixRootSubgroup a2RootMatrix 0 a2RootMatrix_mul_self a2RootMatrix_pow_three R i

private theorem a2Nil (i : Fin 3) : IsNilpotent (representation ℚ (Matrix (Fin 3) (Fin 3) ℚ)
    (Fin 3 → ℚ) (ι ℚ (TauCeti.matrixIntCastLieHom ℚ (a2RootMatrix i)))) :=
  isNilpotent_representation_matrix (a2RootMatrix_pow_three i)

/-- **Type-`A₂` Chevalley commutator check.** With `e_α = E₀₁`, `e_β = E₁₂`, and
`e_{α+β} = E₀₂` (`N_{α,β} = 1`), Steinberg's commutator is `⁅x_α(u), x_β(v)⁆ = x_{α+β}(u * v)`. -/
theorem commutatorElement_a2RootSubgroup {R : Type*} [CommRing R] (u v : R) :
    ⁅a2RootSubgroup R 0 (ofAdd u), a2RootSubgroup R 1 (ofAdd v)⁆ =
      a2RootSubgroup R 2 (ofAdd (u * v)) := by
  simpa only [a2RootSubgroup, integralMatrixRootSubgroup, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, toAdd_ofAdd, Int.cast_one, one_mul] using
    commutatorElement_kostantRootSubgroupMatrix_of_lie_eq'
      (fun k => TauCeti.matrixIntCastLieHom ℚ (a2RootMatrix k)) Empty.elim
      (representation ℚ (Matrix (Fin 3) (Fin 3) ℚ) (Fin 3 → ℚ))
      (TauCeti.coordinateLattice (Fin 3)).toAddSubgroup
      (kostantForm_integralMatrix_mem_coordinateLattice a2RootMatrix 0
        a2RootMatrix_mul_self a2RootMatrix_pow_three)
      (TauCeti.coordinateLatticeBasis (Fin 3))
      (intLie a2RootMatrix 0 1 2 1 (by decide +kernel))
      (intLieZero a2RootMatrix 0 2 (by decide +kernel))
      (intLieZero a2RootMatrix 1 2 (by decide +kernel))
      (a2Nil 0) (a2Nil 1) (a2Nil 2)
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd u))
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd v))

/-- Flipping `c_{1,1} = N_{α,β}` to `-N_{α,β}` in `A₂` falsifies the commutator formula whenever
`(2 : R) ≠ 0`. -/
theorem commutatorElement_a2RootSubgroup_one_ne_neg {R : Type*} [CommRing R] :
    ⁅a2RootSubgroup R 0 (ofAdd (1 : R)), a2RootSubgroup R 1 (ofAdd (1 : R))⁆ ≠
      a2RootSubgroup R 2 (ofAdd (-1 : R)) ↔ (2 : R) ≠ 0 := by
  rw [commutatorElement_a2RootSubgroup, mul_one, ne_eq,
    integralMatrixRootSubgroup_eq_iff_of_entry_unit a2RootMatrix 0
      a2RootMatrix_mul_self a2RootMatrix_pow_three (r := 0) (s := 2) (by decide)
      (Or.inl (by decide)) rfl]
  exact not_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

end TypeA2

/-! ## Check 2: Type `C₂ = Sp₄` on `R⁴` -/

section TypeC2

/-- The four positive root matrices of `C₂ = Sp₄` along the root string from long `α` (`E₁₃`) and
short `β` (`E₀₁ - E₃₂`): `e_{α+β} = E₀₃ + E₁₂` and `e_{α+2β} = E₀₂`. -/
def c2RootMatrix : Fin 4 → Matrix (Fin 4) (Fin 4) ℤ :=
  ![Matrix.single 1 3 1, Matrix.single 0 1 1 - Matrix.single 3 2 1,
    Matrix.single 0 3 1 + Matrix.single 1 2 1, Matrix.single 0 2 1]

/-- Each positive root matrix of `C₂` in the four-dimensional symplectic basis squares to zero. -/
theorem c2RootMatrix_mul_self (i : Fin 4) :
    c2RootMatrix i * c2RootMatrix i = (2 : ℕ) • (0 : Matrix (Fin 4) (Fin 4) ℤ) := by
  revert i; decide

/-- Each positive root matrix of `C₂` in the four-dimensional symplectic basis cubes to zero. -/
theorem c2RootMatrix_pow_three (i : Fin 4) : c2RootMatrix i ^ 3 = 0 := by
  revert i; decide

/-- The Kostant root subgroups `x_α`, `x_β`, `x_{α+β}`, `x_{α+2β}` of `C₂` in `GL₄(R)`. -/
noncomputable abbrev c2RootSubgroup (R : Type*) [CommRing R] (i : Fin 4) :
    Multiplicative R →* _root_.Matrix.GeneralLinearGroup (Fin 4) R :=
  integralMatrixRootSubgroup c2RootMatrix 0 c2RootMatrix_mul_self c2RootMatrix_pow_three R i

private theorem c2Nil (i : Fin 4) : IsNilpotent (representation ℚ (Matrix (Fin 4) (Fin 4) ℚ)
    (Fin 4 → ℚ) (ι ℚ (TauCeti.matrixIntCastLieHom ℚ (c2RootMatrix i)))) :=
  isNilpotent_representation_matrix (c2RootMatrix_pow_three i)

/-- **Type-`C₂` Chevalley commutator check.** With `e_α = E₁₃` (long), `e_β = E₀₁ - E₃₂` (short),
`⁅e_β, e_α⁆ = e_{α+β}`, and `⁅e_β, e_{α+β}⁆ = 2 e_{α+2β}` (`M_{β,α,2} = 1`), Steinberg's commutator
is `⁅x_α(u), x_β(v)⁆ = x_{α+β}(-(u * v)) * x_{α+2β}(-(u * v ^ 2))`. -/
theorem commutatorElement_c2RootSubgroup {R : Type*} [CommRing R] (u v : R) :
    ⁅c2RootSubgroup R 0 (ofAdd u), c2RootSubgroup R 1 (ofAdd v)⁆ =
      c2RootSubgroup R 2 (ofAdd (-(u * v))) * c2RootSubgroup R 3 (ofAdd (-(u * v ^ 2))) := by
  simpa only [c2RootSubgroup, integralMatrixRootSubgroup, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, toAdd_ofAdd, Int.cast_neg, Int.cast_one,
    neg_one_mul] using
    commutatorElement_kostantRootSubgroupMatrix_of_lie_lie_rev_eq'
      (fun k => TauCeti.matrixIntCastLieHom ℚ (c2RootMatrix k)) Empty.elim
      (representation ℚ (Matrix (Fin 4) (Fin 4) ℚ) (Fin 4 → ℚ))
      (TauCeti.coordinateLattice (Fin 4)).toAddSubgroup
      (kostantForm_integralMatrix_mem_coordinateLattice c2RootMatrix 0
        c2RootMatrix_mul_self c2RootMatrix_pow_three)
      (TauCeti.coordinateLatticeBasis (Fin 4))
      (intLie c2RootMatrix 0 1 2 (-1) (by decide +kernel))
      (intLieLie c2RootMatrix 1 0 3 (2 * (1 : ℤ)) (by decide +kernel))
      (intLieZero c2RootMatrix 1 3 (by decide +kernel))
      (intLieZero c2RootMatrix 0 2 (by decide +kernel))
      (c2Nil 0) (c2Nil 1) (c2Nil 2) (c2Nil 3)
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd u))
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd v))

/-- At `u = v = 1`, the `(0, 2)` entry (`(1, 3)` in `1`-indexed coordinates) of `⁅x_α(1), x_β(1)⁆`
in `Sp₄(R)` is `-1`. -/
theorem commutatorElement_c2RootSubgroup_one_apply_zero_two {R : Type*} [CommRing R] :
    ((⁅c2RootSubgroup R 0 (ofAdd (1 : R)), c2RootSubgroup R 1 (ofAdd (1 : R))⁆ :
        _root_.Matrix.GeneralLinearGroup (Fin 4) R) : Matrix (Fin 4) (Fin 4) R) 0 2 = -1 := by
  rw [commutatorElement_c2RootSubgroup, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_four]
  simp only [c2RootSubgroup, coe_integralMatrixRootSubgroup, toAdd_ofAdd]; simp [c2RootMatrix]

/-- Replacing Steinberg's constant `-1` sign on `c_{1,2} = -M_{β,α,2}` by `(-1) ^ 2 = +1` falsifies
the `C₂` commutator formula whenever `(2 : R) ≠ 0`. -/
theorem commutatorElement_c2RootSubgroup_one_ne_pos {R : Type*} [CommRing R] :
    ⁅c2RootSubgroup R 0 (ofAdd (1 : R)), c2RootSubgroup R 1 (ofAdd (1 : R))⁆ ≠
      c2RootSubgroup R 2 (ofAdd (-1 : R)) * c2RootSubgroup R 3 (ofAdd (1 : R)) ↔ (2 : R) ≠ 0 := by
  rw [commutatorElement_c2RootSubgroup, mul_one, one_pow, mul_one, ne_eq, mul_right_inj,
    integralMatrixRootSubgroup_eq_iff_of_entry_unit c2RootMatrix 0
      c2RootMatrix_mul_self c2RootMatrix_pow_three (r := 0) (s := 2) (by decide)
      (Or.inl (by decide)) rfl]
  exact not_congr ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩

end TypeC2

/-! ## Check 3: Type `G₂` in its seven-dimensional representation -/

section TypeG2

/-- The six positive root matrices of `G₂` on the seven-dimensional short-root module, ordered as
`α` (short), `β` (long), `α + β` (`⁅e_α, e_β⁆`), `2α + β` (`(ad e_α)² e_β / 2`),
`3α + β` (`(ad e_α)³ e_β / 6`), and `3α + 2β` (`(ad ⁅e_α, e_β⁆)² e_α / 6`). -/
def g2PosRootMatrix : Fin 6 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![TauCeti.G2ShortRoot.raisingMatrix 0, TauCeti.G2ShortRoot.raisingMatrix 1,
    Matrix.single 0 2 1 - 2 • Matrix.single 1 3 1 + Matrix.single 3 5 1 - Matrix.single 4 6 1,
    -(2 • Matrix.single 0 3 1) + Matrix.single 1 4 1 + Matrix.single 2 5 1 - Matrix.single 3 6 1,
    Matrix.single 0 4 1 - Matrix.single 2 6 1, -Matrix.single 0 5 1 - Matrix.single 1 6 1]

/-- The integral divided-square matrices `e_γ² / 2` for the six positive roots of `G₂`: single unit
matrices for the three short roots `α`, `α + β`, `2α + β`, and `0` for the three long roots. -/
def g2PosDividedSquareMatrix : Fin 6 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![Matrix.single 2 4 1, 0, -Matrix.single 1 5 1, Matrix.single 0 6 1, 0, 0]

/-- Each positive root matrix of `G₂` on the seven-dimensional module squares to twice its
integral divided-square matrix. -/
theorem g2PosRootMatrix_mul_self (i : Fin 6) :
    g2PosRootMatrix i * g2PosRootMatrix i = 2 • g2PosDividedSquareMatrix i := by
  revert i; decide

/-- Each positive root matrix of `G₂` on the seven-dimensional module cubes to zero. -/
theorem g2PosRootMatrix_pow_three (i : Fin 6) : g2PosRootMatrix i ^ 3 = 0 := by
  revert i; decide

/-- The Kostant root subgroups `x_γ` for all six positive roots of `G₂` in `GL₇(R)`. -/
noncomputable abbrev g2PosRootSubgroup (R : Type*) [CommRing R] (i : Fin 6) :
    Multiplicative R →* _root_.Matrix.GeneralLinearGroup (Fin 7) R :=
  integralMatrixRootSubgroup g2PosRootMatrix g2PosDividedSquareMatrix
    g2PosRootMatrix_mul_self g2PosRootMatrix_pow_three R i

private noncomputable abbrev g2E (k : Fin 6) := TauCeti.matrixIntCastLieHom ℚ (g2PosRootMatrix k)

private abbrev g2Mem := kostantForm_integralMatrix_mem_coordinateLattice g2PosRootMatrix
  g2PosDividedSquareMatrix g2PosRootMatrix_mul_self g2PosRootMatrix_pow_three

private theorem g2Nil (i : Fin 6) : IsNilpotent (representation ℚ (Matrix (Fin 7) (Fin 7) ℚ)
    (Fin 7 → ℚ) (ι ℚ (g2E i))) :=
  isNilpotent_representation_matrix (g2PosRootMatrix_pow_three i)

private abbrev g2ZLie := intZsmulLie g2PosRootMatrix
private abbrev g2Zero := intLieZero g2PosRootMatrix

/-- **Type-`G₂` Chevalley commutator check (`α` short, `β` long).** On the seven-dimensional module,
`⁅x_α(u), x_β(v)⁆ = x_{α+β}(uv) x_{2α+β}(u²v) x_{3α+β}(u³v) x_{3α+2β}(2 u³v²)`, confirming
`c_{3,2} = (2/3) M_{α+β,α,2}` (`= 2` in the normalized root vector `e_{3α+2β}`). -/
theorem commutatorElement_g2PosRootSubgroup_short_long {R : Type*} [CommRing R] (u v : R) :
    ⁅g2PosRootSubgroup R 0 (ofAdd u), g2PosRootSubgroup R 1 (ofAdd v)⁆ =
      g2PosRootSubgroup R 2 (ofAdd (u * v)) * g2PosRootSubgroup R 3 (ofAdd (u ^ 2 * v)) *
        g2PosRootSubgroup R 4 (ofAdd (u ^ 3 * v)) *
        g2PosRootSubgroup R 5 (ofAdd (2 * (u ^ 3 * v ^ 2))) := by
  simpa only [g2PosRootSubgroup, integralMatrixRootSubgroup, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, toAdd_ofAdd, Int.cast_one, one_mul,
    mul_one] using
    commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul' g2E Empty.elim
      (representation ℚ (Matrix (Fin 7) (Fin 7) ℚ) (Fin 7 → ℚ))
      (TauCeti.coordinateLattice (Fin 7)).toAddSubgroup g2Mem (TauCeti.coordinateLatticeBasis _)
      (intLie g2PosRootMatrix 0 1 2 1 (by decide +kernel))
      (g2ZLie 0 2 3 1 (2 * (1 : ℤ)) (by decide +kernel))
      (g2ZLie 0 3 4 1 (3 * (1 : ℤ)) (by decide +kernel))
      (g2ZLie 3 2 5 ((1 : ℤ) * 1) (3 * (1 : ℤ)) (by decide +kernel))
      (g2Zero 0 4 (by decide +kernel)) (g2Zero 0 5 (by decide +kernel))
      (g2Zero 1 2 (by decide +kernel)) (g2Zero 3 4 (by decide +kernel))
      (g2Zero 2 5 (by decide +kernel)) (g2Zero 3 5 (by decide +kernel))
      (g2Zero 4 5 (by decide +kernel)) (g2Nil 0) (g2Nil 1) (g2Nil 2) (g2Nil 3) (g2Nil 4) (g2Nil 5)
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd u))
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd v))

/-- **Type-`G₂` Chevalley commutator check (`β` long, `α` short).** Exchanging the roles of `e_α`
and `e_β` gives `⁅x_β(u), x_α(v)⁆ = x_{α+β}(-uv) x_{2α+β}(-uv²) x_{3α+β}(-uv³) x_{3α+2β}(u²v³)`,
confirming `c_{2,3} = (1/3) M_{α+β,β,2}`. -/
theorem commutatorElement_g2PosRootSubgroup_long_short {R : Type*} [CommRing R] (u v : R) :
    ⁅g2PosRootSubgroup R 1 (ofAdd u), g2PosRootSubgroup R 0 (ofAdd v)⁆ =
      g2PosRootSubgroup R 2 (ofAdd (-(u * v))) * g2PosRootSubgroup R 3 (ofAdd (-(u * v ^ 2))) *
        g2PosRootSubgroup R 4 (ofAdd (-(u * v ^ 3))) *
        g2PosRootSubgroup R 5 (ofAdd (u ^ 2 * v ^ 3)) := by
  simpa only [g2PosRootSubgroup, integralMatrixRootSubgroup, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, toAdd_ofAdd, Int.cast_neg, Int.cast_one,
    neg_one_mul, one_mul] using
    commutatorElement_kostantRootSubgroupMatrix_of_lie_eq_three_nsmul_rev' g2E Empty.elim
      (representation ℚ (Matrix (Fin 7) (Fin 7) ℚ) (Fin 7 → ℚ))
      (TauCeti.coordinateLattice (Fin 7)).toAddSubgroup g2Mem (TauCeti.coordinateLatticeBasis _)
      (intLie g2PosRootMatrix 1 0 2 (-1) (by decide +kernel))
      (g2ZLie 2 0 3 (-1) (2 * (1 : ℤ)) (by decide +kernel))
      (g2ZLie 0 3 4 1 (3 * (1 : ℤ)) (by decide +kernel))
      (g2ZLie 2 3 5 ((1 : ℤ) * (-1)) (3 * (1 : ℤ)) (by decide +kernel))
      (g2Zero 0 4 (by decide +kernel)) (g2Zero 0 5 (by decide +kernel))
      (g2Zero 1 2 (by decide +kernel)) (g2Zero 3 4 (by decide +kernel))
      (g2Zero 2 5 (by decide +kernel)) (g2Zero 3 5 (by decide +kernel))
      (g2Zero 4 5 (by decide +kernel)) (g2Nil 1) (g2Nil 0) (g2Nil 2) (g2Nil 3) (g2Nil 4) (g2Nil 5)
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd u))
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd v))

/-- **Type-`G₂` Chevalley commutator check for two short roots (`α` and `α + β`).** On the
seven-dimensional module,
`⁅x_α(u), x_{α+β}(v)⁆ = x_{2α+β}(2uv) x_{3α+β}(3u²v) x_{3α+2β}(-3uv²)`. -/
theorem commutatorElement_g2PosRootSubgroup_short_short {R : Type*} [CommRing R] (u v : R) :
    ⁅g2PosRootSubgroup R 0 (ofAdd u), g2PosRootSubgroup R 2 (ofAdd v)⁆ =
      g2PosRootSubgroup R 3 (ofAdd (2 * u * v)) *
        g2PosRootSubgroup R 4 (ofAdd (3 * u ^ 2 * v)) *
        g2PosRootSubgroup R 5 (ofAdd (-(3 * u * v ^ 2))) := by
  simpa only [g2PosRootSubgroup, integralMatrixRootSubgroup, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, toAdd_ofAdd, Int.cast_neg, Int.cast_one,
    one_mul, neg_one_mul] using
    commutatorElement_kostantRootSubgroupMatrix_of_g2_short_pair' g2E Empty.elim
      (representation ℚ (Matrix (Fin 7) (Fin 7) ℚ) (Fin 7 → ℚ))
      (TauCeti.coordinateLattice (Fin 7)).toAddSubgroup g2Mem (TauCeti.coordinateLatticeBasis _)
      (intLie g2PosRootMatrix 0 2 3 (2 * (1 : ℤ)) (by decide +kernel))
      (g2ZLie 0 3 4 1 (3 * (1 : ℤ)) (by decide +kernel))
      (g2ZLie 3 2 5 1 (3 * (1 : ℤ)) (by decide +kernel))
      (g2Zero 0 4 (by decide +kernel)) (g2Zero 0 5 (by decide +kernel))
      (g2Zero 2 5 (by decide +kernel)) (g2Zero 3 4 (by decide +kernel))
      (g2Zero 3 5 (by decide +kernel)) (g2Zero 4 5 (by decide +kernel))
      (g2Nil 0) (g2Nil 2) (g2Nil 3) (g2Nil 4) (g2Nil 5)
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd u))
      ((gaPointsMulEquiv (R := ℤ) (A := R)).symm (ofAdd v))

/-- Negating the `c_{3,2}` coefficient (`2 ↦ -2`) in `⁅x_α(1), x_β(1)⁆` falsifies the `G₂`
short-long commutator formula whenever `(4 : R) ≠ 0`. -/
theorem commutatorElement_g2PosRootSubgroup_short_long_one_ne_neg {R : Type*} [CommRing R] :
    ⁅g2PosRootSubgroup R 0 (ofAdd (1 : R)), g2PosRootSubgroup R 1 (ofAdd (1 : R))⁆ ≠
      g2PosRootSubgroup R 2 (ofAdd (1 : R)) * g2PosRootSubgroup R 3 (ofAdd (1 : R)) *
        g2PosRootSubgroup R 4 (ofAdd (1 : R)) *
        g2PosRootSubgroup R 5 (ofAdd (-2 : R)) ↔ (4 : R) ≠ 0 := by
  rw [commutatorElement_g2PosRootSubgroup_short_long]
  simp only [one_pow, mul_one]
  rw [ne_eq, mul_right_inj,
    integralMatrixRootSubgroup_eq_iff_of_entry_unit g2PosRootMatrix g2PosDividedSquareMatrix
      g2PosRootMatrix_mul_self g2PosRootMatrix_pow_three (r := 0) (s := 5) (by decide)
      (Or.inr (by decide)) rfl]
  exact not_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

/-- Negating the `c_{2,3}` coefficient (`1 ↦ -1`) in `⁅x_β(1), x_α(1)⁆` falsifies the `G₂`
long-short commutator formula whenever `(2 : R) ≠ 0`. -/
theorem commutatorElement_g2PosRootSubgroup_long_short_one_ne_neg {R : Type*} [CommRing R] :
    ⁅g2PosRootSubgroup R 1 (ofAdd (1 : R)), g2PosRootSubgroup R 0 (ofAdd (1 : R))⁆ ≠
      g2PosRootSubgroup R 2 (ofAdd (-1 : R)) * g2PosRootSubgroup R 3 (ofAdd (-1 : R)) *
        g2PosRootSubgroup R 4 (ofAdd (-1 : R)) *
        g2PosRootSubgroup R 5 (ofAdd (-1 : R)) ↔ (2 : R) ≠ 0 := by
  rw [commutatorElement_g2PosRootSubgroup_long_short]
  simp only [one_pow, mul_one]
  rw [ne_eq, mul_right_inj,
    integralMatrixRootSubgroup_eq_iff_of_entry_unit g2PosRootMatrix g2PosDividedSquareMatrix
      g2PosRootMatrix_mul_self g2PosRootMatrix_pow_three (r := 0) (s := 5) (by decide)
      (Or.inr (by decide)) rfl]
  exact not_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩

end TypeG2

end TauCeti.UniversalEnvelopingAlgebra
