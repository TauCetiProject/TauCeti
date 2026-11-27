/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Finite
public import TauCeti.NumberTheory.NumberField.Discriminant.Archimedean

/-!
# Modulus of a finite Weil idele

When the product of a finite idele, its conjugate and a diagonal field element is an
integral unit, the modulus of the idele is the product of the infinite absolute values
of that element. For the generator of the relative different in a cyclotomic CM extension,
this product is expressed in terms of the absolute root discriminant. It determines the
archimedean size of the scalar used to normalize the Weil vacuum.

The normalization is that of `New.Parameters.ideleAbs_alpha_eq_prod` in
`grh/src/New/Derivatives/Field/WeilData.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
at commit `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open NumberField IsDedekindDomain TauCeti.GlobalNumberFields
open IsDedekindDomain.FiniteAdeleRing

namespace NumberField.FiniteAdeleRing

variable {K : Type*} [Field K] [NumberField K]

/-- Over a totally complex field, the modulus of such an idele is the unweighted product of
the infinite absolute values of the diagonal element. -/
theorem norm_eq_prod_infinitePlace_of_mul_map_mem_integralUnits [IsTotallyComplex K]
    (σ : K ≃+* K) (a : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) (x : Kˣ)
    (h : a * Units.map (finiteAdeleEquiv K K σ).toMonoidHom a * unitEmbedding (𝓞 K) K x ∈
      integralUnits (𝓞 K) K) :
    ‖(a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ = ∏ v : InfinitePlace K, v (x : K) := by
  have ha : 0 ≤ ‖(a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ := by
    rw [← coe_ideleNorm_ofFiniteIdele]
    positivity
  have hp : 0 ≤ ∏ v : InfinitePlace K, v (x : K) :=
    Finset.prod_nonneg fun v _ ↦ v.val.nonneg _
  apply (pow_left_inj₀ ha hp two_ne_zero).mp
  rw [norm_sq_eq_abs_norm_of_mul_map_mem_integralUnits σ a x h, ← Finset.prod_pow]
  simpa only [IsTotallyComplex.mult_eq, Rat.cast_abs] using
    (InfinitePlace.prod_eq_abs_norm (x : K)).symm

/-- If an absolute different generator has local sizes `r` times those of `x` at infinity,
the modulus of the normalized finite idele is `(rootDiscr K / r)` to the power of the
number of infinite places. For a cyclotomic compositum with imaginary quadratic base,
`x` is the relative different generator and `r` is the square root of the base discriminant's
absolute value. -/
theorem norm_eq_rootDiscr_div_pow_of_mul_map_mem_integralUnits [IsTotallyComplex K]
    (σ : K ≃+* K) (a : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) (x : Kˣ)
    (h : a * Units.map (finiteAdeleEquiv K K σ).toMonoidHom a * unitEmbedding (𝓞 K) K x ∈
      integralUnits (𝓞 K) K) {δ : 𝓞 K} (hδ : differentIdeal ℤ (𝓞 K) = Ideal.span {δ})
    {r : ℝ} (hr : ∀ v : InfinitePlace K, v (δ : K) = v (x : K) * r) :
    ‖(a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ =
      (rootDiscr K / r) ^ Fintype.card (InfinitePlace K) := by
  rw [norm_eq_prod_infinitePlace_of_mul_map_mem_integralUnits σ a x h, div_pow,
    ← TauCeti.NumberField.prod_different_generator_eq_rootDiscr_pow hδ]
  have hδ₀ : δ ≠ 0 := by
    rintro rfl
    exact differentIdeal_ne_bot (by simpa using hδ)
  have hr₀ : r ≠ 0 := by
    intro he
    obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hv := hr v
    rw [he, mul_zero] at hv
    have hp : 0 < v (δ : K) := InfinitePlace.pos_iff.mpr
      (RingOfIntegers.coe_ne_zero_iff.mpr hδ₀)
    exact hp.ne' hv
  simp only [hr, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  exact (mul_div_cancel_right₀ _ (pow_ne_zero _ hr₀)).symm

end NumberField.FiniteAdeleRing
