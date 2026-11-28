/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.BoundedCoefficients
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.OfType
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Haar
import TauCeti.MeasureTheory.Constructions.Polish.Units
import TauCeti.NumberTheory.NumberField.Countable
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology
import TauCeti.RingTheory.FractionalIdeal.Norm

/-!
# The finite Tate integral

Let `K` be a number field, `𝔸_{K,f}ˣ` its finite ideles, `Ô^× ⊂ 𝔸_{K,f}ˣ` the everywhere-integral
units and `|x| = ∏_v |x_v|_v` the idele norm, read here as the Haar character
`MeasureTheory.distribHaarChar` of `x` on the finite adeles. For a character `ψ` of the finite
ideles and a set `S` of finite places, this file computes Tate's zeta integral of `ψ` at the finite
places against a function `f` that is determined at `S`: if `f` vanishes unless `x` is integral
outside `S` and a unit at `S`, `f(u) ψ(u) = 1_V(u)` on `Ô^×`, and `f` depends on integral ideles
only through their components at `S`, then for `Re s > 1` and every left-invariant measure `μ` that
is finite on compact sets,

`∫ f(x) ψ(x) |x| ^ s dμ(x) = L^S(s, ψ) · μ(Ô^× ∩ V)`,

where `L^S(s, ψ) = ∏_{v ∉ S} (1 - ψ(ϖ_v) N(v) ^ (-s))⁻¹` is the partial Euler product
`TauCeti.primeEulerProduct` of the values of `ψ` at uniformizers.

The computation is Tate's, at the finite places only. The fractional ideal of a finite idele
(`IsDedekindDomain.FiniteAdeleRing.toFractionalIdeal`) has kernel `Ô^×`, so the integrand is
supported on the integral ideles, the disjoint union over the nonzero integral ideals `𝔞` of the
cosets `ϖ ^ 𝔞 · Ô^×` (`IsDedekindDomain.FiniteAdeleRing.uniformizerPow`). On the coset of `𝔞` the
idele norm is `N(𝔞)⁻¹` (`IsDedekindDomain.FiniteAdeleRing.coe_distribHaarChar_eq_inv_absNorm`) and
the integrand is `ψ(ϖ ^ 𝔞) N(𝔞) ^ (-s)` times the translate of `1_V`, so by invariance of `μ` its
integral is `ψ(ϖ ^ 𝔞) N(𝔞) ^ (-s) μ(Ô^× ∩ V)`. The map `𝔞 ↦ ψ(ϖ ^ 𝔞)` on the ideals prime to `S`,
extended by zero, is completely multiplicative (`MonoidHom.heckeIdealCharacter`), so the sum of
these terms is the Euler product by `TauCeti.hasSum_primeEulerProduct`.

The Euler product converges when the Euler coefficients `ψ(ϖ_v)` (`MonoidHom.heckeCoeff`) have
modulus at most one. This holds for the characters of interest, the *Hecke characters of type `n`*
(`MonoidHom.IsHeckeOfType`), which are unitary (`MonoidHom.IsHeckeOfType.norm_heckeCoeff`).

## Main results

* `MonoidHom.hasSum_heckeIdealCharacter_div_absNorm_cpow`: the Dirichlet series of the ideal
  character is the partial Euler product `L^S(s, ψ)`.
* `TauCeti.integrable_mul_distribHaarChar_cpow` and
  `TauCeti.integral_mul_distribHaarChar_cpow_eq_primeEulerProduct_mul`: the finite Tate integral
  converges and equals `L^S(s, ψ) · μ(Ô^× ∩ V)`.

## Provenance

The finite Tate integral corresponds to results of grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic PBC), file `src/Lib/ClassField/HeckeL/ContinuationAtOne.lean`:
`New.IsHeckeOfType.integral_mul_finIdeleAbs_rpow_eq_eulerProd_mul` and
`New.IsHeckeOfType.tate_integral`, and the proof follows its method, an unfolding over the fibres of
the fractional-ideal map. Here the integral is stated for complex `s`,
every left-invariant measure finite on compact sets, every set `S` of places and a measurable `V`,
under a bound on the Euler coefficients alone.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter XV, §4.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField MeasureTheory
open scoped nonZeroDivisors Pointwise

/-! ### The Dirichlet series of the ideal character -/

namespace MonoidHom

section EulerProduct

variable {K : Type*} [Field K] [NumberField K] {ψ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ}
  {ϖ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ} {S : Set (HeightOneSpectrum (𝓞 K))}

/-- **The Dirichlet series of the ideal character is the partial Euler product.** If the Euler
coefficients outside `S` have modulus at most one, then for `Re s > 1` the series
`∑_𝔞 ψ(ϖ ^ 𝔞) N(𝔞) ^ (-s)` over the nonzero ideals prime to `S` sums to
`L^S(s, ψ) = ∏_{v ∉ S} (1 - ψ(ϖ_v) N(v) ^ (-s))⁻¹`. -/
theorem hasSum_heckeIdealCharacter_div_absNorm_cpow (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : (Ideal (𝓞 K))⁰ ↦
        ψ.heckeIdealCharacter ϖ S I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s)
      (TauCeti.primeEulerProduct (Sᶜ.indicator (ψ.heckeCoeff ϖ)) s) := by
  simpa only [heckeIdealCharacter_apply_asIdeal] using
    TauCeti.hasSum_primeEulerProduct _ (norm_heckeIdealCharacter_le_one hψ) hs

end EulerProduct

end MonoidHom

/-! ### The finite Tate integral -/

namespace TauCeti

section TateIntegral

variable {K : Type*} [Field K] [NumberField K] {μ : Measure (FiniteAdeleRing (𝓞 K) K)ˣ}
  {ψ : (FiniteAdeleRing (𝓞 K) K)ˣ →* ℂˣ} {ϖ : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ}
  {S : Set (HeightOneSpectrum (𝓞 K))} {V : Set (FiniteAdeleRing (𝓞 K) K)ˣ}
  {f : (FiniteAdeleRing (𝓞 K) K)ˣ → ℂ} {s : ℂ}

/-- A function vanishing unless `x` is a unit at `S` vanishes on the finite ideles whose fractional
ideal is a nonzero integral ideal divisible by a prime of `S`. -/
private theorem apply_eq_zero_of_not_isPrimeTo
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (I : (Ideal (𝓞 K))⁰) {x : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hx : toFractionalIdeal x = FractionalIdeal.mk0 K I) (hI : ¬ (I : Ideal (𝓞 K)).IsPrimeTo S) :
    f x = 0 := by
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  by_contra h
  obtain ⟨v, hv, hdvd⟩ : ∃ v ∈ S, v.asIdeal ∣ (I : Ideal (𝓞 K)) := by
    by_contra! h'
    exact hI (Ideal.isPrimeTo_iff.mpr ⟨hI0, h'⟩)
  have h0 : adicOrd x v = 0 := adicOrd_eq_zero_iff.mpr ((hf₀ x h).2 v hv)
  rw [← count_coe_toFractionalIdeal, hx, FractionalIdeal.coe_mk0,
    FractionalIdeal.count_coeIdeal_eq_zero_iff hI0] at h0
  exact h0 hdvd

/-- On the finite ideles whose fractional ideal is a nonzero integral ideal `I`, the Tate integrand
is the term of `I` in the Dirichlet series of the ideal character on the translate of `V` by
`ϖ ^ I`, and `0` off it. -/
private theorem tateIntegrand_eq_indicator
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1))
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hf₁ : ∀ u ∈ integralUnits (𝓞 K) K, f u * ψ u = V.indicator 1 u)
    (hf₂ : ∀ x : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K → ∀ u ∈ integralUnits (𝓞 K) K,
      (∀ v ∈ S, (x : FiniteAdeleRing (𝓞 K) K) v = (u : FiniteAdeleRing (𝓞 K) K) v) → f x = f u)
    (I : (Ideal (𝓞 K))⁰) {x : (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hx : toFractionalIdeal x = FractionalIdeal.mk0 K I) :
    f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s =
      (uniformizerPow ϖ (FractionalIdeal.mk0 K I) • V).indicator
        (fun _ ↦ ψ.heckeIdealCharacter ϖ S I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s) x := by
  classical
  set y := uniformizerPow ϖ (FractionalIdeal.mk0 K I)
  have hI0 : (I : Ideal (𝓞 K)) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  -- the idele norm of `x` is `N(I)⁻¹`
  have hnorm : ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s =
      ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s)⁻¹ := by
    rw [coe_distribHaarChar_eq_inv_absNorm, hx, FractionalIdeal.coe_mk0,
      FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Complex.ofReal_inv,
      Complex.ofReal_natCast, Complex.inv_cpow _ _ (by
        rw [Complex.natCast_arg]
        exact Real.pi_ne_zero.symm)]
  by_cases hI : (I : Ideal (𝓞 K)).IsPrimeTo S
  · -- `u = y⁻¹ x` is an everywhere-integral unit with the components of `x` at `S`
    have hu : y⁻¹ * x ∈ integralUnits (𝓞 K) K := by
      rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, map_mul, map_inv, hx,
        toFractionalIdeal_uniformizerPow hϖ, inv_mul_cancel]
    have hxint : (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K := by
      rw [← toFractionalIdeal_le_one_iff, hx, FractionalIdeal.coe_mk0]
      exact FractionalIdeal.coeIdeal_le_one
    have hS (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
        (x : FiniteAdeleRing (𝓞 K) K) v = ((y⁻¹ * x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K) v := by
      rw [← coe_unitsProj_apply, ← coe_unitsProj_apply, map_mul, map_inv,
        unitsProj_uniformizerPow, FractionalIdeal.coe_mk0,
        (FractionalIdeal.count_coeIdeal_eq_zero_iff hI0).mpr (hI.not_dvd hv), zpow_zero, inv_one,
        one_mul]
    have hfx : f x = f (y⁻¹ * x) := hf₂ x hxint _ hu hS
    have hψx : (ψ x : ℂ) = ψ y * ψ (y⁻¹ * x) := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
    have h1 := hf₁ _ hu
    rw [hnorm, hfx, hψx, Set.indicator_apply, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
      MonoidHom.heckeIdealCharacter_apply_of_isPrimeTo hI, div_eq_mul_inv]
    by_cases hV : y⁻¹ * x ∈ V
    · rw [Set.indicator_of_mem hV, Pi.one_apply] at h1
      rw [ite_eq_left hV]
      linear_combination (ψ y * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s)⁻¹ : ℂ) * h1
    · rw [Set.indicator_of_notMem hV] at h1
      rw [ite_eq_right hV]
      linear_combination (ψ y * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s)⁻¹ : ℂ) * h1
  · simp [apply_eq_zero_of_not_isPrimeTo hf₀ I hx hI,
      MonoidHom.heckeIdealCharacter_apply_of_not_isPrimeTo hI]

/-- A finite idele where a function vanishing off the ideles integral outside `S` and units at `S`
is nonzero has a nonzero integral ideal as its fractional ideal. -/
private theorem exists_toFractionalIdeal_eq_mk0
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    {x : (FiniteAdeleRing (𝓞 K) K)ˣ} (hx : f x ≠ 0) :
    ∃ I : (Ideal (𝓞 K))⁰, toFractionalIdeal x = FractionalIdeal.mk0 K I := by
  have hxint : (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K := by
    refine mem_integralAdeles.mpr fun v ↦ ?_
    by_cases hv : v ∈ S
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, (hf₀ x hx).2 v hv]
    · exact (hf₀ x hx).1 v hv
  refine ⟨toIntegralIdeal ⟨x, mem_integralFiniteIdeles.mpr hxint⟩, Units.ext ?_⟩
  rw [FractionalIdeal.coe_mk0, coe_toIntegralIdeal]

/-- The integral, over the finite ideles with fractional ideal `J`, of a constant `e` on the
translate of `V` by `ϖ ^ J` is `μ(Ô^× ∩ V) e`: the fibre is the coset `ϖ ^ J • Ô^×`. -/
private theorem setIntegral_preimage_toFractionalIdeal_indicator [μ.IsMulLeftInvariant]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1)) (hV : MeasurableSet V)
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (e : E) :
    ∫ x in toFractionalIdeal ⁻¹' {J}, (uniformizerPow ϖ J • V).indicator (fun _ ↦ e) x ∂μ =
      μ.real (integralUnits (𝓞 K) K ∩ V) • e := by
  rw [integral_indicator_const e (hV.const_smul _), measureReal_restrict_apply (hV.const_smul _),
    preimage_toFractionalIdeal_singleton hϖ, measureReal_def, measureReal_def,
    ← Set.smul_set_inter, measure_smul, Set.inter_comm]

/-- The finite Tate integral converges, and its value is the partial Euler product times
`μ(Ô^× ∩ V)`. -/
private theorem integrable_and_integral_eq [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1))
    (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1) (hV : MeasurableSet V)
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hf₁ : ∀ u ∈ integralUnits (𝓞 K) K, f u * ψ u = V.indicator 1 u)
    (hf₂ : ∀ x : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K → ∀ u ∈ integralUnits (𝓞 K) K,
      (∀ v ∈ S, (x : FiniteAdeleRing (𝓞 K) K) v = (u : FiniteAdeleRing (𝓞 K) K) v) → f x = f u)
    (hs : 1 < s.re) :
    Integrable (fun x ↦ f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s)
        μ ∧
      ∫ x, f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s ∂μ =
        primeEulerProduct (Sᶜ.indicator (ψ.heckeCoeff ϖ)) s *
          μ.real (integralUnits (𝓞 K) K ∩ V) := by
  set U := (integralUnits (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)ˣ)
  set F := fun x ↦ f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s
  -- the fibre `P I` of the fractional-ideal map over `I` is the coset `y I • Ô^×`, on which `F`
  -- is the constant `c I` on the translate of `V`
  let y (I : (Ideal (𝓞 K))⁰) := uniformizerPow ϖ (FractionalIdeal.mk0 K I)
  let P (I : (Ideal (𝓞 K))⁰) := toFractionalIdeal ⁻¹' {FractionalIdeal.mk0 K I}
  let c (I : (Ideal (𝓞 K))⁰) : ℂ :=
    ψ.heckeIdealCharacter ϖ S I / (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ s
  have hc := MonoidHom.hasSum_heckeIdealCharacter_div_absNorm_cpow hψ hs
  have hPm (I) : MeasurableSet (P I) :=
    ((isLocallyConstant_toFractionalIdeal (𝓞 K) K).isOpen_fiber _).measurableSet
  have hFP (I) : Set.EqOn F ((y I • V).indicator fun _ ↦ c I) (P I) := fun _ hx ↦
    tateIntegrand_eq_indicator hϖ hf₀ hf₁ hf₂ I hx
  have hμP (I) : μ (P I) < ⊤ := by
    simp only [P, preimage_toFractionalIdeal_singleton hϖ, measure_smul]
    exact (isCompact_integralUnits (𝓞 K) K).measure_lt_top
  have hint (I) : ∫ x in P I, F x ∂μ = c I * μ.real (U ∩ V) := by
    rw [setIntegral_congr_fun (hPm I) (hFP I),
      setIntegral_preimage_toFractionalIdeal_indicator hϖ hV, Complex.real_smul, mul_comm]
  have hint_norm (I) : ∫ x in P I, ‖F x‖ ∂μ = μ.real (U ∩ V) * ‖c I‖ := by
    rw [setIntegral_congr_fun (hPm I) fun x hx ↦ by
      rw [hFP I hx, norm_indicator_eq_indicator_norm],
      setIntegral_preimage_toFractionalIdeal_indicator hϖ hV, smul_eq_mul]
  have hFint (I) : IntegrableOn F (P I) μ :=
    ((integrableOn_const (hμP I).ne).indicator (hV.const_smul _)).congr_fun (hFP I).symm (hPm I)
  have hdisj : Pairwise (Function.onFun Disjoint P) := fun I J hIJ ↦
    Set.disjoint_left.mpr fun x hxI hxJ ↦ hIJ <| Subtype.ext <| FractionalIdeal.coeIdeal_injective
      (K := K) <| by
        simpa only [FractionalIdeal.coe_mk0] using congrArg Units.val (hxI.symm.trans hxJ)
  have hUnion : IntegrableOn F (⋃ I, P I) μ :=
    integrableOn_iUnion_of_summable_integral_norm hFint <| by
      simpa only [hint_norm] using (summable_norm_iff.mpr hc.summable).mul_left _
  -- `F` vanishes off the integral ideles, which are the union of the fibres
  have hzero : ∀ x ∉ ⋃ I, P I, F x = 0 := fun x hx ↦ by
    by_contra hF
    obtain ⟨I, hI⟩ := exists_toFractionalIdeal_eq_mk0 hf₀
      (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    exact hx (Set.mem_iUnion.mpr ⟨I, hI⟩)
  refine ⟨hUnion.integrable_of_forall_notMem_eq_zero hzero, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have h := hasSum_integral_iUnion hPm hdisj hUnion
  simp only [hint] at h
  exact h.unique (hc.mul_right _)

/-- **The finite Tate integral converges.** Let `ϖ` be uniformizers of the completions, `S` a set of
places such that the Euler coefficients `ψ(ι_v(ϖ_v))` of `ψ` have modulus at most one outside `S`,
`V` a measurable set of finite ideles, and `f` a function on the finite ideles that vanishes unless
`x` is integral outside `S` and a unit at `S`, satisfies `f(u) ψ(u) = 1_V(u)` on `Ô^×`, and takes
the same value at an integral idele and at an integral unit with the same components at `S` (as it
does when its value on integral ideles depends only on the components at `S`). Then for
`Re s > 1` and every left-invariant measure `μ` that is finite on compact sets,
`f(x) ψ(x) |x| ^ s` is integrable. -/
theorem integrable_mul_distribHaarChar_cpow [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1))
    (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1) (hV : MeasurableSet V)
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hf₁ : ∀ u ∈ integralUnits (𝓞 K) K, f u * ψ u = V.indicator 1 u)
    (hf₂ : ∀ x : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K → ∀ u ∈ integralUnits (𝓞 K) K,
      (∀ v ∈ S, (x : FiniteAdeleRing (𝓞 K) K) v = (u : FiniteAdeleRing (𝓞 K) K) v) → f x = f u)
    (hs : 1 < s.re) :
    Integrable
      (fun x ↦ f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s) μ :=
  (integrable_and_integral_eq hϖ hψ hV hf₀ hf₁ hf₂ hs).1

/-- **The finite Tate integral.** Under the hypotheses of
`TauCeti.integrable_mul_distribHaarChar_cpow`, for `Re s > 1`,

`∫ f(x) ψ(x) |x| ^ s dμ(x) = L^S(s, ψ) · μ(Ô^× ∩ V)`,

where `L^S(s, ψ) = ∏_{v ∉ S} (1 - ψ(ι_v(ϖ_v)) N(v) ^ (-s))⁻¹` and `|x|` is the idele norm. For a
Hecke character of type `n` the hypothesis on the Euler coefficients holds for every `S`
(`MonoidHom.IsHeckeOfType.norm_heckeCoeff`). For an open `V ∋ 1` and a Haar measure `μ`, the factor
`μ(Ô^× ∩ V)` is finite and nonzero, `Ô^× ∩ V` being a compact neighbourhood of `1` intersected with
an open one (`TauCeti.isCompact_integralUnits`, `TauCeti.isOpen_integralUnits`). -/
theorem integral_mul_distribHaarChar_cpow_eq_primeEulerProduct_mul [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ]
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = WithZero.exp (-1))
    (hψ : ∀ v ∉ S, ‖ψ.heckeCoeff ϖ v‖ ≤ 1) (hV : MeasurableSet V)
    (hf₀ : ∀ x, f x ≠ 0 →
      (∀ v ∉ S, (x : FiniteAdeleRing (𝓞 K) K) v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 K) K) v) = 1)
    (hf₁ : ∀ u ∈ integralUnits (𝓞 K) K, f u * ψ u = V.indicator 1 u)
    (hf₂ : ∀ x : (FiniteAdeleRing (𝓞 K) K)ˣ,
      (x : FiniteAdeleRing (𝓞 K) K) ∈ integralAdeles (𝓞 K) K → ∀ u ∈ integralUnits (𝓞 K) K,
      (∀ v ∈ S, (x : FiniteAdeleRing (𝓞 K) K) v = (u : FiniteAdeleRing (𝓞 K) K) v) → f x = f u)
    (hs : 1 < s.re) :
    ∫ x, f x * ψ x * ((distribHaarChar (FiniteAdeleRing (𝓞 K) K) x : ℝ) : ℂ) ^ s ∂μ =
      primeEulerProduct (Sᶜ.indicator (ψ.heckeCoeff ϖ)) s *
        μ.real (integralUnits (𝓞 K) K ∩ V) :=
  (integrable_and_integral_eq hϖ hψ hV hf₀ hf₁ hf₂ hs).2

end TateIntegral

end TauCeti
