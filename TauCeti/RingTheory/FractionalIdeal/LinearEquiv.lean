/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations
public import TauCeti.RingTheory.Ideal.Quotient.Semilocal
import TauCeti.RingTheory.FractionalIdeal.CoprimeRepresentative
import TauCeti.RingTheory.Ideal.LinearEquiv

/-!
# Linear isomorphisms between fractional ideals and the product identity

Scaling by a nonzero element of the fraction field is an `R`-linear isomorphism, so fractional
ideals in the same ideal class are isomorphic `R`-modules. Over a Dedekind domain the direct sum
of two fractional ideals depends only on their product: this is Steinitz's product identity

```text
I ⊕ J ≅ R ⊕ IJ.
```

Applied repeatedly to a decomposition `M ≅ I₁ ⊕ ⋯ ⊕ Iₙ` of a lattice into rank-one pieces, it
gives `M ≅ Rⁿ⁻¹ ⊕ I₁ ⋯ Iₙ`; it is the relation `[I] + [J] = [R] + [IJ]` behind the identification
of the rank-zero part of the projective `K₀` of a Dedekind domain with its ideal class group.

The proof is by coprime representatives. For integral ideals `I` and `J` with `i + j = 1`,
`i ∈ I`, `j ∈ J`, the map `I × J → R`, `(x, y) ↦ x + y` is onto with kernel the antidiagonal
copy of `I ⊓ J`, and `r ↦ (i r, j r)` splits it. This gives `Ideal.prodEquivProdInf`, a
submodule counterpart of the Chinese remainder isomorphism `Ideal.quotientInfEquivQuotientProd`.
For fractional ideals, `J` may be scaled to an integral ideal `J'`, and the invertible ideal `I`
to an integral ideal `I'` coprime to `J'`
(`FractionalIdeal.exists_coeIdeal_eq_spanSingleton_mul_and_sup_eq_top`), for which
`I' ⊓ J' = I' J'`.

## Main definitions

* `FractionalIdeal.spanSingletonMulEquiv`: multiplication by a left-regular element `a` is an
  isomorphism from `I` onto `(a) I`.
* `FractionalIdeal.coeIdealEquiv`: an integral ideal is isomorphic to its fractional ideal.

## Main results

* `FractionalIdeal.nonempty_prod_linearEquiv_prod_mul`: **the product identity**. For an invertible
  fractional ideal `I` and a nonzero fractional ideal `J` of a Noetherian domain of dimension at
  most one, for instance a Dedekind domain, `I × J ≃ R × IJ`.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Graduate Studies in
  Mathematics 145, AMS, 2013, Chapter I, §3, Propositions 3.4 and 3.5.
-/

public section

open scoped nonZeroDivisors

namespace FractionalIdeal

section Equiv

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P] [Algebra R P]

/-- Multiplication by a left-regular element `a` is an `R`-linear isomorphism from a fractional
ideal `I` onto `(a) I`. -/
noncomputable def spanSingletonMulEquiv [IsLocalization S P] {a : P} (ha : IsLeftRegular a)
    (I : FractionalIdeal S P) : I ≃ₗ[R] (spanSingleton S a * I : FractionalIdeal S P) :=
  (Submodule.equivMapOfInjective (LinearMap.mulLeft R a) ha (I : Submodule R P)).trans <|
    LinearEquiv.ofEq _ _ <| by
      rw [coeToSubmodule_mul, coeToSubmodule_spanSingleton, Submodule.span_singleton_mul]
      ext x
      simp [Submodule.mem_smul_pointwise_iff_exists, eq_comm]

@[simp]
theorem coe_spanSingletonMulEquiv_apply [IsLocalization S P] {a : P} (ha : IsLeftRegular a)
    (I : FractionalIdeal S P) (x : I) : (spanSingletonMulEquiv ha I x : P) = a * x :=
  (rfl)

variable [FaithfulSMul R P]

/-- An integral ideal `I` is `R`-linearly isomorphic to the fractional ideal it defines, by the
inverse of `algebraMap R P`. -/
noncomputable def coeIdealEquiv (I : Ideal R) : (I : FractionalIdeal S P) ≃ₗ[R] I :=
  (Submodule.equivMapOfInjective (Algebra.linearMap R P)
    (FaithfulSMul.algebraMap_injective R P) I).symm

theorem coe_coeIdealEquiv_symm_apply (I : Ideal R) (x : I) :
    ((coeIdealEquiv (S := S) (P := P) I).symm x : P) = algebraMap R P x :=
  (rfl)

theorem algebraMap_coeIdealEquiv_apply (I : Ideal R) (x : (I : FractionalIdeal S P)) :
    algebraMap R P (coeIdealEquiv I x) = x := by
  rw [← coe_coeIdealEquiv_symm_apply, LinearEquiv.symm_apply_apply]

end Equiv

variable {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **The product identity.** Let `R` be a Noetherian domain of dimension at most one, for
instance a Dedekind domain, with fraction field `K`. For an invertible fractional ideal `I` and a
nonzero fractional ideal `J`, there is an `R`-linear isomorphism `I × J ≃ R × IJ`. Over a Dedekind
domain every nonzero fractional ideal is invertible (`Ne.isUnit`). -/
theorem nonempty_prod_linearEquiv_prod_mul {I J : FractionalIdeal R⁰ K} (hI : IsUnit I)
    (hJ : J ≠ 0) : Nonempty ((I × J) ≃ₗ[R] R × (I * J : FractionalIdeal R⁰ K)) := by
  -- A fractional ideal with an integral multiple `c X = Y` is isomorphic to `Y`.
  have key {c : K} {X : FractionalIdeal R⁰ K} {Y : Ideal R} (hc : c ≠ 0)
      (h : spanSingleton R⁰ c * X = Y) : X ≃ₗ[R] Y :=
    spanSingletonMulEquiv (IsRegular.of_ne_zero hc).left X ≪≫ₗ
      LinearEquiv.ofEq _ _ (congrArg _ h) ≪≫ₗ coeIdealEquiv Y
  -- Replace `J` by the integral ideal `J' = d J`.
  obtain ⟨d, J', hd, hJJ'⟩ := J.exists_eq_spanSingleton_mul
  have hd' : algebraMap R K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd
  have hJb : spanSingleton R⁰ (algebraMap R K d) * J = J' := by
    rw [hJJ', ← mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, one_mul]
  have hJ' : J' ≠ ⊥ := by
    rintro rfl
    simp [hJJ'] at hJ
  -- Replace `I` by an integral ideal `I' = a I` coprime to `J'`, so that `I' ⊓ J' = I' J'`.
  obtain ⟨a, ha, I', hII', hcop⟩ := exists_coeIdeal_eq_spanSingleton_mul_and_sup_eq_top hI.unit
    (Ideal.finite_setOfPred_isMaximal_and_le_of_ne_bot hJ')
  rw [hI.unit_spec] at hII'
  replace hcop := Ideal.isCoprime_iff_sup_eq.mpr hcop
  obtain ⟨i, hi, j, hj, hij⟩ := hcop.exists
  have hIJ : spanSingleton R⁰ (a * algebraMap R K d) * (I * J) = ↑(I' * J') := by
    rw [coeIdeal_mul, hII', ← hJb, map_mul, mul_mul_mul_comm]
  have eIJ : ↥(I' ⊓ J') ≃ₗ[R] (I * J : FractionalIdeal R⁰ K) :=
    LinearEquiv.ofEq _ _ (Ideal.mul_eq_inf_of_isCoprime hcop).symm ≪≫ₗ
      (key (mul_ne_zero ha hd') hIJ).symm
  exact ⟨(key ha hII'.symm).prodCongr (key hd' hJb) ≪≫ₗ Ideal.prodEquivProdInf hi hj hij ≪≫ₗ
    (LinearEquiv.refl R R).prodCongr eIJ⟩

end FractionalIdeal
