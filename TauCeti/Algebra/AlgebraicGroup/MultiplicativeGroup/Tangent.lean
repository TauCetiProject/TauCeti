/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Basic
import TauCeti.Algebra.Polynomial.Laurent.Basic

/-!
# The tangent Lie algebra of the multiplicative group

The tangent module at the identity of the multiplicative group is free of rank one. A tangent
derivation of the Laurent polynomial Hopf algebra `R[T;T⁻¹]` is determined by its value on `T`,
and every value in a coefficient ring `B` occurs. The resulting equivalence is `B`-linear,
even when `B` is noncommutative. For commutative `B`, the tangent Lie bracket vanishes.

## Main declarations

* `TauCeti.MultiplicativeGroup.derivation_T_zsmul`: tangent derivations evaluate every
  Laurent monomial by its exponent times their value on `T`.
* `TauCeti.MultiplicativeGroup.tangentLinearEquiv`: the tangent space of `𝔾ₘ` is linearly
  equivalent to `B`.
* `TauCeti.MultiplicativeGroup.tangent_bracket_eq_zero`: the tangent Lie bracket of `𝔾ₘ`
  vanishes.

## References

The construction follows the formal pattern of
`TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent`.
Laurent evaluation at a unit and the dual-number derivation dictionary construct the inverse
equivalence. Laurent-polynomial induction and the counit formula for `T` come from Mathlib's
`Mathlib.Algebra.Polynomial.Laurent` and `Mathlib.RingTheory.Bialgebra.MonoidAlgebra`.
-/

public section

open scoped LaurentPolynomial

namespace TauCeti

namespace MultiplicativeGroup

open TauCeti.Bialgebra TrivSqZeroExt

universe u w

noncomputable section

variable {R : Type u} [CommSemiring R]
variable {B : Type w}

local notation "H" => R[T;T⁻¹]
local notation "C" => CounitAlgebra R H B

section Semiring

variable [Semiring B] [Algebra R B]

private lemma derivation_T_add (d : Derivation R H C) (m n : ℤ) :
    d (LaurentPolynomial.T (m + n)) =
      d (LaurentPolynomial.T m) + d (LaurentPolynomial.T n) := by
  rw [LaurentPolynomial.T_add, Derivation.leibniz]
  apply (CounitAlgebra.algEquivSelf R H B).injective
  simp only [map_add, CounitAlgebra.algEquivSelf_smul, LaurentPolynomial.counit_T,
    map_one, one_mul, add_comm]

private def monomialValues (d : Derivation R H C) : ℤ →+ C where
  toFun n := d (LaurentPolynomial.T n)
  map_zero' := by simp
  map_add' := derivation_T_add d

private lemma monomialValues_apply (d : Derivation R H C) (n : ℤ) :
    monomialValues d n = d (LaurentPolynomial.T n) :=
  rfl

/-- Two tangent derivations of the Laurent polynomial algebra are equal if they agree on `T`. -/
@[ext]
theorem derivation_ext {d e : Derivation R H C}
    (h : d (LaurentPolynomial.T 1) = e (LaurentPolynomial.T 1)) : d = e := by
  have hT (n : ℤ) : d (LaurentPolynomial.T n) = e (LaurentPolynomial.T n) :=
    DFunLike.congr_fun
      (AddMonoidHom.ext_int (f := monomialValues d) (g := monomialValues e) h) n
  apply Derivation.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | C_mul_T n a =>
      rw [Derivation.leibniz, Derivation.leibniz, hT]
      rw [LaurentPolynomial.C_eq_algebraMap, Derivation.map_algebraMap,
        Derivation.map_algebraMap]

private noncomputable def tangentCoordinate : Derivation R H C →ₗ[B] B where
  toFun d := CounitAlgebra.algEquivSelf R H B (d (LaurentPolynomial.T 1))
  map_add' _d _e := (CounitAlgebra.algEquivSelf R H B).map_add _ _
  map_smul' b d := algEquivSelf_derivation_smul_apply b d _

private lemma tangentCoordinate_apply (d : Derivation R H C) :
    tangentCoordinate d =
      CounitAlgebra.algEquivSelf R H B (d (LaurentPolynomial.T 1)) :=
  rfl

end Semiring

section Ring

variable [Ring B] [Algebra R B]

/-- A tangent derivation takes `Tⁿ` to the integer multiple `n • d(T)` of its value on `T`. -/
theorem derivation_T_zsmul (d : Derivation R H C) (n : ℤ) :
    d (LaurentPolynomial.T n) = n • d (LaurentPolynomial.T 1) := by
  simpa only [zsmul_one, Int.cast_id, monomialValues_apply] using
    map_zsmul (monomialValues d) n (1 : ℤ)

private noncomputable def infinitesimalUnit (c : C) : (DualNumber C)ˣ :=
  have h : IsUnit (inl 1 + inr c : DualNumber C) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simp
  h.unit

private lemma infinitesimalUnit_map_fst (c : C) :
    Units.map (fstHom R C C : DualNumber C →* C) (infinitesimalUnit c) = 1 := by
  ext
  simp [infinitesimalUnit]

private theorem tangentCoordinate_surjective :
    Function.Surjective (tangentCoordinate (R := R) (B := B)) := by
  intro b
  let c : C := (CounitAlgebra.algEquivSelf R H B).symm b
  let q : H →ₐ[R] DualNumber C := laurentEval (infinitesimalUnit c)
  have hq : (fstHom R C C).comp q = IsScalarTower.toAlgHom R H C := by
    simp only [q, comp_laurentEval, infinitesimalUnit_map_fst]
    apply (laurentEval_unique 1 _ ?_).symm
    simp only [IsScalarTower.toAlgHom_apply, CounitAlgebra.algebraMap_apply,
      LaurentPolynomial.counit_T, ← CounitAlgebra.algebraMap_base R H B, map_one,
      Units.val_one]
  let d : Derivation R H C :=
    (derivationToTrivSqZeroExtEquivLift R H C).symm ⟨q, hq⟩
  refine ⟨d, ?_⟩
  rw [tangentCoordinate_apply]
  dsimp only [d]
  rw [derivationToTrivSqZeroExtEquivLift_symm_apply]
  simp only [q, laurentEval_T_one, infinitesimalUnit, IsUnit.unit_spec, snd_add, snd_inl,
    snd_inr, zero_add, c, AlgEquiv.apply_symm_apply]

/-- **The tangent module at the identity of `𝔾ₘ` is free of rank one.** The equivalence sends
a counit-valued derivation to its value on the Laurent generator `T`. -/
noncomputable def tangentLinearEquiv : Derivation R H C ≃ₗ[B] B :=
  LinearEquiv.ofBijective tangentCoordinate
    ⟨fun _ _ h => derivation_ext ((CounitAlgebra.algEquivSelf R H B).injective h),
      tangentCoordinate_surjective⟩

/-- The tangent equivalence evaluates a derivation on the Laurent generator `T`. -/
@[simp]
theorem tangentLinearEquiv_apply (d : Derivation R H C) :
    tangentLinearEquiv d =
      CounitAlgebra.algEquivSelf R H B (d (LaurentPolynomial.T 1)) := by
  rfl

/-- The derivation corresponding to `b : B` takes the Laurent monomial `Tⁿ` to `n • b`.
Values are transported to `B` through `CounitAlgebra.algEquivSelf`; in particular, the values
on `T` and `T⁻¹` are `b` and `-b`. -/
-- Evaluate before simplification removes the coefficient equivalence or changes `T 0`.
@[simp↓]
theorem tangentLinearEquiv_symm_apply_T (b : B) (n : ℤ) :
    CounitAlgebra.algEquivSelf R H B
      ((tangentLinearEquiv (R := R) (B := B)).symm b (LaurentPolynomial.T n)) = n • b := by
  have h : CounitAlgebra.algEquivSelf R H B
      ((tangentLinearEquiv (R := R) (B := B)).symm b (LaurentPolynomial.T 1)) = b := by
    simpa only [tangentLinearEquiv_apply] using
      (tangentLinearEquiv (R := R) (B := B)).apply_symm_apply b
  rw [derivation_T_zsmul, map_zsmul, h]

end Ring

section Lie

variable [CommRing B] [Algebra R B]

/-- **The tangent Lie algebra of `𝔾ₘ` is abelian.** -/
@[simp]
theorem tangent_bracket_eq_zero (d e : Derivation R H C) : ⁅d, e⁆ = 0 :=
  trivial_lie_zero _ _ d e

end Lie

end

end MultiplicativeGroup

end TauCeti
