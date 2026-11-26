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
ideals in the same ideal class are isomorphic `R`-modules. Conversely, every `R`-linear map between
`R`-submodules of the fraction field is a scaling. Over a Dedekind domain the direct sum
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
* `FractionalIdeal.linearEquivOne`: `R` is isomorphic to the unit fractional ideal `(1)`.

## Main results

* `LinearMap.exists_coe_apply_eq_mul`: every `R`-linear map between `R`-submodules of the fraction
  field `K` of `R` is multiplication by an element of `K`.
* `LinearMap.eq_spanSingleton_mul_of_surjective`: a surjective `R`-linear map `I → J` between
  fractional ideals that is multiplication by `f` shows `J = (f) I`.
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

variable (S P) in
/-- The identification `x ↦ x` of `R` with the unit fractional ideal `(1)`, the image of `R` in
`P`, as `R`-modules. -/
noncomputable def linearEquivOne : R ≃ₗ[R] (1 : FractionalIdeal S P) :=
  (LinearEquiv.ofInjective (Algebra.linearMap R P) (FaithfulSMul.algebraMap_injective R P)).trans
    (LinearEquiv.ofEq _ _ (by rw [coeToSubmodule_one, Submodule.one_eq_range]))

@[simp]
theorem coe_linearEquivOne_apply (x : R) : (linearEquivOne S P x : P) = algebraMap R P x := by
  rw [linearEquivOne, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact LinearEquiv.ofInjective_apply _ x

end Equiv

end FractionalIdeal

namespace LinearMap

/-- **A linear map between submodules of a fraction field is a multiplication.** If `K` is the
fraction field of a domain `R` and `I, J` are `R`-submodules of `K`, every `R`-linear map
`I → J` is `x ↦ f x` for some `f ∈ K`. -/
theorem exists_coe_apply_eq_mul {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {I J : Submodule R K} (φ : I →ₗ[R] J) :
    ∃ f : K, ∀ x : I, (φ x : K) = f * x := by
  have : IsDomain R := (IsFractionRing.injective R K).isDomain (algebraMap R K)
  by_cases hI : ∀ x : I, (x : K) = 0
  · refine ⟨0, fun x ↦ ?_⟩
    rw [show x = 0 from Subtype.ext (hI x), map_zero, Submodule.coe_zero, zero_mul]
  push Not at hI
  obtain ⟨x₀, hx₀⟩ := hI
  refine ⟨φ x₀ / x₀, fun x ↦ ?_⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj R⁰ ((x : K) / x₀)
  have hs : algebraMap R K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property
  have hrs' : (x : K) * algebraMap R K s = algebraMap R K r * x₀ := by
    rw [← hrs]
    field_simp
  have key : (s : R) • x = r • x₀ :=
    Subtype.ext (by simpa [Algebra.smul_def, mul_comm] using hrs')
  have hφ := congrArg (fun y : J ↦ (y : K)) (congrArg φ key)
  simp only [map_smul, Submodule.coe_smul, Algebra.smul_def] at hφ
  field_simp
  apply mul_left_cancel₀ hs
  linear_combination (x₀ : K) * hφ - (φ x₀ : K) * hrs'

/-- **A surjective scaling between fractional ideals identifies the target.** If a surjective
`R`-linear map `φ : I → J` between fractional ideals is `x ↦ f x`, then `J = (f) I`. -/
theorem eq_spanSingleton_mul_of_surjective {R : Type*} [CommRing R] {S : Submonoid R}
    {P : Type*} [CommRing P] [Algebra R P] [IsLocalization S P] {I J : FractionalIdeal S P}
    (φ : I →ₗ[R] J) (hφ : Function.Surjective φ) {f : P} (hf : ∀ x : I, (φ x : P) = f * x) :
    J = FractionalIdeal.spanSingleton S f * I := by
  refine FractionalIdeal.eq_spanSingleton_mul.mpr ⟨fun y hy ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hφ ⟨y, hy⟩
    exact ⟨x, x.property, by rw [← hf, hx]⟩
  · rw [← hf ⟨x, hx⟩]
    exact (φ ⟨x, hx⟩).property

end LinearMap

namespace FractionalIdeal

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
