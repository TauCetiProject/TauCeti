/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AddChar.Fourier
public import TauCeti.NumberTheory.LocalField.TateZeta.Nonarchimedean
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import TauCeti.MeasureTheory.Group.Correlation
import TauCeti.MeasureTheory.Measure.Haar.DistribChar
import TauCeti.NumberTheory.LocalField.HaarCharacter
import TauCeti.NumberTheory.LocalField.NormedField
import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.NumberTheory.LocalField.Units.Shell
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Tate's local functional equation over a nonarchimedean local field

Let `K` be a nonarchimedean local field (of either characteristic) with residue field of
cardinality `q` and normalized absolute value `|·|`, `μ` an additive Haar measure on `K`, `ν` a
Haar measure on `Kˣ`, `ψ` a continuous nontrivial additive character of `K` with values in the
unit circle, and `ω : Kˣ → ℂˣ` a quasi-character of exponent `r` (`‖ω(x)‖ = |x| ^ r`). The test
functions are the locally constant compactly supported `f : K → ℂ` (the Schwartz–Bruhat space
`S(K)`), and the Fourier transform is the one with Tate's positive kernel,

`𝓕f(y) = ∫ ψ(x y) f(x) dμ(x)`,

which is Mathlib's `VectorFourier.fourierIntegral ψ μ (-LinearMap.mul K K)`: Mathlib's transform
uses `ψ(-L x y)`, so the form `L = -(x y)` gives the positive kernel. For the form `x y` one gets
the negative kernel, `F⁺f(y) = F⁻f(-y)`. By `TauCeti.NumberTheory.LocalField.AddChar.Fourier`, `𝓕`
maps `S(K)` to itself. Write `z(s, ω; f) = ∫_{Kˣ} f(x) ω(x) |x| ^ s dν(x)`
(`TauCeti.TateZeta.localZetaIntegral`), which converges for `re s + r > 0`.

**Tate's local functional equation.** For `f, g ∈ S(K)` and `0 < re s + r < 1`,

`z(s, ω; f) z(1 - s, ω⁻¹; 𝓕g) = z(s, ω; g) z(1 - s, ω⁻¹; 𝓕f)`.

The proof is Tate's. Since `ω(u) |u| ^ s · ω⁻¹(u) |u| ^ (1 - s) = |u|`, the substitution
`v = u t` turns the left side into `∫_t (∫_u f(u) 𝓕g(u t) |u| dν(u)) ω⁻¹(t) |t| ^ (1 - s) dν(t)`
(`MeasureTheory.integral_mul_integral_eq_integral_integral_mul`). The measure `|u| dν(u)` is a
positive multiple of `μ` on `Kˣ`
(`TauCeti.TateZeta.exists_pos_forall_integral_eq_smul_integral_units`), so the inner integral is
a multiple of `∫ f(x) 𝓕g(x t) dμ(x) = ∫∫ f(x) g(y) ψ(x y t) dμ(x) dμ(y)`, which is symmetric
in `f` and `g`.

Evaluating at Tate's test vector `f₀ = 1_{U(K, c(ω))}`, the indicator of the unit subgroup on
which `ω` is trivial (`c(ω)` the conductor exponent), whose zeta integral is the constant
`ν(U(K, c(ω))) ≠ 0`, gives the **gamma factor** `γ(s, ω, ψ) = z(1 - s, ω⁻¹; 𝓕f₀) / z(s, ω; f₀)`
and the functional equation `z(1 - s, ω⁻¹; 𝓕f) = γ(s, ω, ψ) z(s, ω; f)` for all `f`. The factor
does not depend on `ν`, it is holomorphic on `re s + r < 1`, and it is the only constant with this
property. Rescaling `μ` by `c` rescales `𝓕`, hence `γ`, by `c`.

For unramified `ω`, `ψ` of conductor exponent `0` and `μ(𝒪[K]) = 1`, `1_𝒪` is its own transform,
so `γ(s, ω, ψ) = L(1 - s, ω⁻¹) / L(s, ω)` with `L(s, ω) = (1 - ω(ϖ) q ^ (-s))⁻¹`: the
`ε`-factor is `1`.

## Main definitions

* `TauCeti.TateZeta.gammaTestFunction ω`: Tate's test vector `1_{U(K, c(ω))}`.
* `TauCeti.TateZeta.gammaFactor ω μ ψ s`: the gamma factor `γ(s, ω, ψ)`.

## Main results

* `TauCeti.TateZeta.exists_pos_forall_integral_eq_smul_integral_units`: `μ = c |u| dν(u)` on
  `Kˣ` for some `c > 0`.
* `TauCeti.TateZeta.integral_mul_fourierIntegral_mul_comm`: `∫ f 𝓕g(· t) = ∫ g 𝓕f(· t)`.
* `TauCeti.TateZeta.localZetaIntegral_mul_localZetaIntegral_fourierIntegral_comm`: Tate's
  symmetric identity on the strip `0 < re s + r < 1`.
* `TauCeti.TateZeta.localZetaIntegral_functionalEquation`:
  `z(1 - s, ω⁻¹; 𝓕f) = γ(s, ω, ψ) z(s, ω; f)` on the strip, for every Haar measure `ν`.
* `TauCeti.TateZeta.eq_gammaFactor_of_forall`, `TauCeti.TateZeta.gammaFactor_eq`: uniqueness of
  `γ` and its independence of `ν`.
* `TauCeti.TateZeta.differentiableOn_gammaFactor`: `γ` is holomorphic on `re s + r < 1`.
* `TauCeti.TateZeta.fourierIntegral_indicator_integer`,
  `TauCeti.TateZeta.gammaFactor_of_unramified`: the unramified computation.

The meromorphic continuation of both sides is in
`TauCeti.NumberTheory.LocalField.TateZeta.Continuation`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §2.4, Lemma 2.4.2 and Theorem 2.4.1.
* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, §3, (3.23)–(3.26).
* The argument follows `localTate_existsUnique`, `localZeta_correlation`, `local_fourier_pair` and
  `local_integral_module` in `RiemannMasullo/Ch03_IdelicZeta/Sec3.lean` of the Riemann–Masullo
  formalization (https://github.com/mccorvie/riemann-masullo), which proves the equation at the
  completions of a number field for Bruhat's Schwartz–Bruhat space, with the kernel
  `conj ψ(x y)` and the measures of Tate's thesis. Here `K` is any nonarchimedean local field,
  the measures are arbitrary Haar measures and the kernel is `ψ(x y)`.
-/

public section
noncomputable section

open MeasureTheory Measure Complex ValuativeRel Set
open scoped NNReal ENNReal

namespace TauCeti.TateZeta

/-! ### The Fourier transform with Tate's kernel -/

section Fourier

variable {K : Type*} [Field K]

/-- The form `-(x y)`, for which Mathlib's `VectorFourier.fourierIntegral` has Tate's positive
kernel `ψ(x y)`. -/
theorem nondegenerate_neg_mul : (-LinearMap.mul K K : LinearMap.BilinForm K K).Nondegenerate :=
  ⟨fun x hx ↦ by simpa using hx 1, fun y hy ↦ by simpa using hy 1⟩

/-- With the form `-(x y)`, the Fourier transform has Tate's positive kernel:
`𝓕 f (y) = ∫ ψ(x y) f(x) dμ(x)`. -/
theorem fourierIntegral_neg_mul_apply [MeasurableSpace K] (ψ : AddChar K Circle) (μ : Measure K)
    (f : K → ℂ) (y : K) :
    VectorFourier.fourierIntegral ψ μ (-LinearMap.mul K K) f y =
      ∫ x, (ψ (x * y) : ℂ) * f x ∂μ := by
  simp [VectorFourier.fourierIntegral, Circle.smul_def]

/-- **Symmetry of the Fourier pairing.** For integrable `f`, `g` and every `t`,
`∫ f(x) 𝓕g(x t) dμ(x) = ∫ g(x) 𝓕f(x t) dμ(x)`: both are `∫∫ f(x) g(y) ψ(x y t)`. -/
theorem integral_mul_fourierIntegral_mul_comm [TopologicalSpace K] [IsTopologicalRing K]
    [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] {ψ : AddChar K Circle}
    (hψ : Continuous ψ) (μ : Measure K) [SFinite μ] {f g : K → ℂ} (hf : Integrable f μ)
    (hg : Integrable g μ) (t : K) :
    ∫ x, f x * VectorFourier.fourierIntegral ψ μ (-LinearMap.mul K K) g (x * t) ∂μ =
      ∫ x, g x * VectorFourier.fourierIntegral ψ μ (-LinearMap.mul K K) f (x * t) ∂μ := by
  simp_rw [fourierIntegral_neg_mul_apply, ← integral_const_mul]
  have hk : Continuous fun z : K × K ↦ (ψ (z.2 * (z.1 * t)) : ℂ) :=
    continuous_subtypeVal.comp
      (hψ.comp (continuous_snd.mul (continuous_fst.mul continuous_const)))
  have hm : AEStronglyMeasurable (fun z : K × K ↦ f z.1 * ((ψ (z.2 * (z.1 * t)) : ℂ) * g z.2))
      (μ.prod μ) := by
    have hf' : AEStronglyMeasurable (fun z : K × K ↦ f z.1) (μ.prod μ) := hf.1.comp_fst
    have hg' : AEStronglyMeasurable (fun z : K × K ↦ g z.2) (μ.prod μ) := hg.1.comp_snd
    exact hf'.mul (hk.aestronglyMeasurable.mul hg')
  have hint : Integrable (fun z : K × K ↦ f z.1 * ((ψ (z.2 * (z.1 * t)) : ℂ) * g z.2))
      (μ.prod μ) :=
    (hf.norm.mul_prod hg.norm).mono' hm (ae_of_all _ fun z ↦ by simp)
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun y ↦ integral_congr_ae (ae_of_all _ fun x ↦ ?_))
  simp only
  rw [show y * (x * t) = x * (y * t) by ring]
  ring

end Fourier

/-! ### Additive and multiplicative Haar measures -/

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

/-- The density `|x|⁻¹` of the multiplicative Haar measure with respect to additive Haar
measure, with value `∞` at `0`. -/
private def invAbsDensity (x : K) : ℝ≥0∞ := (ENNReal.ofReal (normalizedAbsoluteValue K x : ℝ))⁻¹

/-- The measure `|x|⁻¹ dμ(x)` on `Kˣ`. -/
private def unitsModulusMeasure (μ : Measure K) : Measure Kˣ :=
  (μ.withDensity invAbsDensity).comap Units.val

private theorem measurable_invAbsDensity : Measurable (invAbsDensity (K := K)) := by
  exact (ENNReal.measurable_ofReal.comp continuous_normalizedAbsoluteValue.measurable).inv

/-- Integrating `h(u) |u|` against `|x|⁻¹ dμ` on `Kˣ` gives the additive integral of `h`. -/
private theorem integral_unitsModulusMeasure (μ : Measure K) [μ.IsAddHaarMeasure] (h : K → ℂ) :
    ∫ u : Kˣ, h u * ((normalizedAbsoluteValue K (u : K) : ℝ) : ℂ) ∂unitsModulusMeasure μ =
      ∫ x, h x ∂μ := by
  have : NullSingletonClass μ := IsAddHaarMeasure.nullSingletonClass μ
  have he : MeasurableEmbedding (Units.val : Kˣ → K) := Units.measurableEmbedding_val₀
  have hv : range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
  rw [unitsModulusMeasure,
    ← he.integral_map (g := fun x ↦ h x * ((normalizedAbsoluteValue K x : ℝ) : ℂ)),
    he.map_comap, hv, restrict_withDensity (measurableSet_singleton 0).compl,
    restrict_compl_singleton, integral_withDensity_eq_integral_toReal_smul
      measurable_invAbsDensity ?_]
  · refine integral_congr_ae ?_
    filter_upwards [μ.ae_ne 0] with x hx
    have hx' : ((normalizedAbsoluteValue K x : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (normalizedAbsoluteValue K).ne_zero hx
    simp only [invAbsDensity, ENNReal.toReal_inv, ENNReal.toReal_ofReal (NNRat.cast_nonneg _),
      Complex.real_smul, Complex.ofReal_inv]
    field_simp
  · filter_upwards [μ.ae_ne 0] with x hx
    simpa [invAbsDensity] using (normalizedAbsoluteValue K).ne_zero hx


/-- Multiplication by `a ∈ Kˣ` preserves `|x|⁻¹ dμ`, since it scales `μ` by `|a|⁻¹`. -/
private theorem map_smul_withDensity_invAbsDensity (μ : Measure K) [μ.IsAddHaarMeasure]
    (a : Kˣ) : (μ.withDensity invAbsDensity).map (a • ·) = μ.withDensity invAbsDensity := by
  refine map_smul_withDensity μ a fun x ↦ ?_
  rw [distribHaarChar_eq_normalizedAbsoluteValue]
  have ha : (0 : ℝ) < normalizedAbsoluteValue K (a : K) := by
    exact_mod_cast (normalizedAbsoluteValue K).pos a.ne_zero
  have hca : ((normalizedAbsoluteValue K (a : K) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (normalizedAbsoluteValue K (a : K) : ℝ) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    norm_cast
  rw [invAbsDensity, invAbsDensity, Units.smul_def, smul_eq_mul, map_mul, NNRat.cast_mul, hca,
    ENNReal.ofReal_mul ha.le]
  rcases eq_or_ne x 0 with rfl | -
  · rw [map_zero, NNRat.cast_zero, ENNReal.ofReal_zero, mul_zero, ENNReal.inv_zero,
      ENNReal.mul_top (by simpa using ha)]
  rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 ha).ne') (Or.inl ENNReal.ofReal_ne_top),
    ENNReal.mul_inv_cancel_left (ENNReal.ofReal_pos.2 ha).ne' ENNReal.ofReal_ne_top]

private instance (μ : Measure K) [μ.IsAddHaarMeasure] :
    (unitsModulusMeasure μ).IsMulLeftInvariant := by
  have he := Units.measurableEmbedding_val₀ (G₀ := K)
  refine ⟨fun a ↦ ext fun s hs ↦ ?_⟩
  have hset : (a • · : K → K) ⁻¹' (Units.val '' s) = Units.val '' ((a * ·) ⁻¹' s) := by
    ext x
    constructor
    · rintro ⟨u, hu, hux⟩
      refine ⟨a⁻¹ * u, by simpa using hu, ?_⟩
      have hux' : (u : K) = a • x := hux
      change ((a⁻¹ : Kˣ) : K) * u = x
      rw [hux', Units.smul_def, smul_eq_mul, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_mul]
    · rintro ⟨v, hv, rfl⟩
      exact ⟨a * v, hv, by simp [Units.smul_def]⟩
  rw [map_apply (measurable_const_mul a) hs, unitsModulusMeasure, he.comap_apply,
    he.comap_apply, ← hset, ← map_apply (continuous_const_smul (a : Kˣ)).measurable
      (he.measurableSet_image' hs), map_smul_withDensity_invAbsDensity]

private instance (μ : Measure K) [μ.IsAddHaarMeasure] :
    IsFiniteMeasureOnCompacts (unitsModulusMeasure μ) := by
  have he := Units.measurableEmbedding_val₀ (G₀ := K)
  refine ⟨fun S hS ↦ ?_⟩
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hcont : Continuous fun u : Kˣ ↦ (normalizedAbsoluteValue K (u : K) : ℝ) :=
    continuous_normalizedAbsoluteValue.comp Units.continuous_val
  obtain ⟨u₀, -, hmin⟩ := hS.exists_isMinOn hne hcont.continuousOn
  have hδ : (0 : ℝ) < normalizedAbsoluteValue K (u₀ : K) := by
    exact_mod_cast (normalizedAbsoluteValue K).pos u₀.ne_zero
  have hSm : MeasurableSet (Units.val '' S) := he.measurableSet_image' hS.measurableSet
  rw [unitsModulusMeasure, he.comap_apply, withDensity_apply _ hSm]
  calc ∫⁻ x in Units.val '' S, invAbsDensity x ∂μ
      ≤ ∫⁻ _ in Units.val '' S, (ENNReal.ofReal (normalizedAbsoluteValue K (u₀ : K) : ℝ))⁻¹ ∂μ :=
        setLIntegral_mono measurable_const fun x ⟨u, hu, hux⟩ ↦ by
          rw [← hux]
          exact ENNReal.inv_le_inv.2 (ENNReal.ofReal_le_ofReal (hmin hu))
    _ = (ENNReal.ofReal (normalizedAbsoluteValue K (u₀ : K) : ℝ))⁻¹ * μ (Units.val '' S) :=
        setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (ENNReal.ofReal_pos.2 hδ))
        (hS.image Units.continuous_val).measure_lt_top

/-- **Additive and multiplicative Haar measures.** For an additive Haar measure `μ` on `K` and a
Haar measure `ν` on `Kˣ` there is a constant `c > 0` with `∫ h dμ = c ∫_{Kˣ} h(u) |u| dν(u)` for
every `h : K → ℂ`: the measure `|u| dν(u)` is a multiple of `μ` on `Kˣ`, and `{0}` is `μ`-null. -/
theorem exists_pos_forall_integral_eq_smul_integral_units (μ : Measure K) [μ.IsAddHaarMeasure]
    (ν : Measure Kˣ) [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ h : K → ℂ,
      ∫ x, h x ∂μ = c • ∫ u : Kˣ, h u * ((normalizedAbsoluteValue K (u : K) : ℝ) : ℂ) ∂ν := by
  have := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  have hρ := isMulLeftInvariant_eq_smul (unitsModulusMeasure μ) ν
  set c := haarScalarFactor (unitsModulusMeasure μ) ν
  have key (h : K → ℂ) : ∫ x, h x ∂μ =
      (c : ℝ) • ∫ u : Kˣ, h u * ((normalizedAbsoluteValue K (u : K) : ℝ) : ℂ) ∂ν := by
    rw [← integral_unitsModulusMeasure μ h, hρ, integral_smul_nnreal_measure, NNReal.smul_def]
  refine ⟨c, lt_of_le_of_ne c.coe_nonneg fun hc ↦ ?_, key⟩
  -- If `c = 0`, then `μ(𝒪[K]) = 0`, which is absurd.
  have hOc : IsCompact (𝒪[K] : Set K) := by
    simpa using (integerPositiveCompacts K).isCompact
  have hOm : MeasurableSet (𝒪[K] : Set K) := hOc.isClosed.measurableSet
  have h0 := key ((𝒪[K] : Set K).indicator fun _ ↦ 1)
  rw [← hc, zero_smul, integral_indicator_const _ hOm, Complex.real_smul,
    mul_one, Complex.ofReal_eq_zero] at h0
  have hpos : 0 < μ (𝒪[K] : Set K) := by
    simpa using (μ.measure_pos_of_nonempty_interior
      (integerPositiveCompacts K).interior_nonempty :)
  exact (ENNReal.toReal_pos hpos.ne' hOc.measure_lt_top.ne).ne' h0


/-! ### Tate's local functional equation -/

omit [MeasurableSpace K] [BorelSpace K] in
/-- The characteristic exponent of `ω⁻¹` is minus that of `ω`. -/
theorem characterExponent_inv (ω : Kˣ →ₜ* ℂˣ) :
    characterExponent K ω⁻¹ = -characterExponent K ω := by
  have h := characterExponent_mul ω ω⁻¹
  rw [mul_inv_cancel, characterExponent_one] at h
  linarith

/-- The local zeta integral `z(s, ω; f)` for `ν` and the normalized absolute value. -/
local notation "𝔷[" ν "]" => localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue _ x : ℝ))

/-- The Fourier transform `f ↦ ∫ ψ(x y) f(x) dμ(x)` with Tate's kernel. -/
local notation "𝓕[" ψ ", " μ "]" => VectorFourier.fourierIntegral ψ μ (-LinearMap.mul _ _)

section FunctionalEquation

variable (μ : Measure K) [μ.IsAddHaarMeasure] (ν : Measure Kˣ) [ν.IsHaarMeasure]
  {ψ : AddChar K Circle}

/-- The transform of a test function is again a test function. -/
theorem isLocallyConstant_hasCompactSupport_fourierIntegral (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) {g : K → ℂ} (hg : IsLocallyConstant g) (hgc : HasCompactSupport g) :
    IsLocallyConstant (𝓕[ψ, μ] g) ∧ HasCompactSupport (𝓕[ψ, μ] g) :=
  ⟨VectorFourier.isLocallyConstant_fourierIntegral_of_hasCompactSupport hψ μ _ hgc,
    VectorFourier.hasCompactSupport_fourierIntegral_of_isLocallyConstant hψ h1
      nondegenerate_neg_mul μ hg hgc⟩

/-- Tate's correlation: on the strip, `z(s, ω; f) z(1 - s, ω⁻¹; 𝓕g)` is the integral over `t` of
`c⁻¹ ∫ f(x) 𝓕g(x t) dμ(x)` against `ω⁻¹(t) |t| ^ (1 - s) dν(t)`, where `c` relates `μ` to
`|u| dν(u)`. -/
private theorem localZetaIntegral_mul_fourier_eq (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (ω : Kˣ →ₜ* ℂˣ) {c : ℝ} (hc : 0 < c) (hμν : ∀ h : K → ℂ,
      ∫ x, h x ∂μ = c • ∫ u : Kˣ, h u * ((normalizedAbsoluteValue K (u : K) : ℝ) : ℂ) ∂ν)
    {f g : K → ℂ} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f)
    (hg : IsLocallyConstant g) (hgc : HasCompactSupport g) {s : ℂ}
    (hs₀ : 0 < s.re + characterExponent K ω) (hs₁ : s.re + characterExponent K ω < 1) :
    𝔷[ν] ω f s * 𝔷[ν] ω⁻¹ (𝓕[ψ, μ] g) (1 - s) =
      ∫ t : Kˣ, ((c : ℂ)⁻¹ * ∫ x, f x * 𝓕[ψ, μ] g (x * t) ∂μ) *
        ((ω⁻¹ t : ℂ) * ((normalizedAbsoluteValue K (t : K) : ℝ) : ℂ) ^ (1 - s)) ∂ν := by
  have := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  obtain ⟨hgl, hgcc⟩ := isLocallyConstant_hasCompactSupport_fourierIntegral μ hψ h1 hg hgc
  have hA := localZetaIntegral_convergent ν ω hf.continuous hfc hs₀
  have hB := localZetaIntegral_convergent ν ω⁻¹ hgl.continuous hgcc (s := 1 - s) (by
    rw [characterExponent_inv, sub_re, one_re]; linarith)
  simp only [localZetaIntegral_def]
  rw [integral_mul_integral_eq_integral_integral_mul ν hA hB]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  simp only
  rw [hμν, Complex.real_smul, inv_mul_cancel_left₀ (by exact_mod_cast hc.ne'),
    ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
  have hu : (0 : ℝ) < normalizedAbsoluteValue K (u : K) := by
    exact_mod_cast (normalizedAbsoluteValue K).pos u.ne_zero
  have hu' : ((normalizedAbsoluteValue K (u : K) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hω : (ω u : ℂ) ≠ 0 := (ω u).ne_zero
  have hinv (v : Kˣ) : (ω⁻¹ v : ℂ) = (ω v : ℂ)⁻¹ := by
    rw [ContinuousMonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  simp only [Units.val_mul, map_mul, NNRat.cast_mul, Complex.ofReal_mul, hinv]
  rw [Complex.ofReal_mul_cpow hu.le]
  have hpow : ((normalizedAbsoluteValue K (u : K) : ℝ) : ℂ) ^ s *
      ((normalizedAbsoluteValue K (u : K) : ℝ) : ℂ) ^ (1 - s) =
      ((normalizedAbsoluteValue K (u : K) : ℝ) : ℂ) := by
    rw [← cpow_add _ _ hu', add_sub_cancel, cpow_one]
  have hωu : (ω u : ℂ) * (ω u : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hω
  set U := ((normalizedAbsoluteValue K (u : K) : ℝ) : ℂ)
  set A := f u * 𝓕[ψ, μ] g (u * t) * (ω t : ℂ)⁻¹ *
    ((normalizedAbsoluteValue K (t : K) : ℝ) : ℂ) ^ (1 - s)
  linear_combination A * hpow + A * (U ^ s * U ^ (1 - s)) * hωu

/-- **Tate's local functional equation, symmetric form.** For test functions `f`, `g` on `K` and
`s` in the strip `0 < re s + r < 1`, where `r` is the exponent of `ω`,
`z(s, ω; f) z(1 - s, ω⁻¹; 𝓕g) = z(s, ω; g) z(1 - s, ω⁻¹; 𝓕f)`, for every Haar measure `ν` on
`Kˣ`, every additive Haar measure `μ` and the Fourier transform `𝓕f(y) = ∫ ψ(x y) f(x) dμ(x)`. -/
theorem localZetaIntegral_mul_localZetaIntegral_fourierIntegral_comm (hψ : Continuous ψ)
    (h1 : ψ ≠ 1) (ω : Kˣ →ₜ* ℂˣ) {f g : K → ℂ} (hf : IsLocallyConstant f)
    (hfc : HasCompactSupport f) (hg : IsLocallyConstant g) (hgc : HasCompactSupport g) {s : ℂ}
    (hs₀ : 0 < s.re + characterExponent K ω) (hs₁ : s.re + characterExponent K ω < 1) :
    𝔷[ν] ω f s * 𝔷[ν] ω⁻¹ (𝓕[ψ, μ] g) (1 - s) = 𝔷[ν] ω g s * 𝔷[ν] ω⁻¹ (𝓕[ψ, μ] f) (1 - s) := by
  obtain ⟨c, hc, hμν⟩ := exists_pos_forall_integral_eq_smul_integral_units μ ν
  rw [localZetaIntegral_mul_fourier_eq μ ν hψ h1 ω hc hμν hf hfc hg hgc hs₀ hs₁,
    localZetaIntegral_mul_fourier_eq μ ν hψ h1 ω hc hμν hg hgc hf hfc hs₀ hs₁]
  simp_rw [integral_mul_fourierIntegral_mul_comm hψ μ
    (hf.continuous.integrable_of_hasCompactSupport hfc)
    (hg.continuous.integrable_of_hasCompactSupport hgc)]

end FunctionalEquation

/-! ### The gamma factor -/

variable (ω : Kˣ →ₜ* ℂˣ)

/-- **Tate's test vector** for a quasi-character `ω`: the indicator of the unit subgroup
`U(K, c(ω))`, on which `ω` is trivial, `c(ω)` being the conductor exponent. -/
def gammaTestFunction : K → ℂ :=
  (Units.val '' (unitFiltration K (ClassFieldTheory.characterConductorExp K ω) : Set Kˣ)).indicator
    1

omit [MeasurableSpace K] [BorelSpace K] in
/-- The image of a unit subgroup `U(K, n)` in `K` is open and closed. -/
theorem isClopen_image_val_unitFiltration (n : ℕ) :
    IsClopen (Units.val '' (unitFiltration K n : Set Kˣ)) := by
  refine ⟨((isCompact_unitFiltration n).image Units.continuous_val).isClosed, ?_⟩
  obtain ⟨V, hV, hVU⟩ := (Units.isEmbedding_val₀ (G₀ := K)).isInducing.isOpen_iff.1
    (isOpen_unitFiltration (K := K) n)
  have hv : range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    exact ⟨by rintro ⟨u, rfl⟩; exact u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
  rw [← hVU, image_preimage_eq_inter_range, hv]
  exact hV.inter isOpen_compl_singleton

omit [MeasurableSpace K] [BorelSpace K] in
theorem isLocallyConstant_gammaTestFunction : IsLocallyConstant (gammaTestFunction ω) := by
  rw [gammaTestFunction, ← LocallyConstant.coe_charFn ℂ (isClopen_image_val_unitFiltration _)]
  exact LocallyConstant.isLocallyConstant _

omit [MeasurableSpace K] [BorelSpace K] in
theorem hasCompactSupport_gammaTestFunction : HasCompactSupport (gammaTestFunction ω) :=
  HasCompactSupport.intro ((isCompact_unitFiltration _).image Units.continuous_val)
    fun _ hx ↦ indicator_of_notMem hx _

/-- The zeta integral of Tate's test vector is the volume of `U(K, c(ω))`, for every `s`. -/
theorem localZetaIntegral_gammaTestFunction (ν : Measure Kˣ) (s : ℂ) :
    𝔷[ν] ω (gammaTestFunction ω) s =
      ν.real (unitFiltration K (ClassFieldTheory.characterConductorExp K ω)) := by
  set U := unitFiltration K (ClassFieldTheory.characterConductorExp K ω)
  have hU : MeasurableSet (U : Set Kˣ) := (isOpen_unitFiltration _).measurableSet
  rw [localZetaIntegral_def, ← integral_indicator_one hU, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
  have hmem : (u : K) ∈ Units.val '' (U : Set Kˣ) ↔ u ∈ U := Units.val_injective.mem_set_image
  by_cases hu : u ∈ U
  · have hk : ω u = 1 := ClassFieldTheory.unitFiltration_characterConductorExp_le_ker K ω hu
    have h0 : u ∈ unitFiltration K 0 := unitFiltration_antitone (Nat.zero_le _) hu
    dsimp only [gammaTestFunction]
    rw [indicator_of_mem (hmem.2 hu), indicator_of_mem hu, hk,
      normalizedAbsoluteValue_of_mem_unitFiltration_zero h0]
    simp
  · dsimp only [gammaTestFunction]
    rw [indicator_of_notMem (mt hmem.1 hu), indicator_of_notMem hu]
    simp

omit [BorelSpace K] in
theorem measureReal_unitFiltration_pos (ν : Measure Kˣ) [ν.IsHaarMeasure] (n : ℕ) :
    0 < ν.real (unitFiltration K n) :=
  ENNReal.toReal_pos ((isOpen_unitFiltration n).measure_ne_zero ν ⟨1, one_mem _⟩)
    (isCompact_unitFiltration n).measure_lt_top.ne

/-- **The local gamma factor** `γ(s, ω, ψ)` for the Fourier transform with kernel `ψ(x y)` and
additive measure `μ`: the ratio `z(1 - s, ω⁻¹; 𝓕f₀) / z(s, ω; f₀)` at Tate's test vector `f₀`,
computed with the Haar measure `TauCeti.unitsHaar K` (it does not depend on this choice, see
`TauCeti.TateZeta.gammaFactor_eq`). -/
def gammaFactor (μ : Measure K) (ψ : AddChar K Circle) (s : ℂ) : ℂ :=
  𝔷[unitsHaar K] ω⁻¹ (𝓕[ψ, μ] (gammaTestFunction ω)) (1 - s) /
    (unitsHaar K).real (unitFiltration K (ClassFieldTheory.characterConductorExp K ω))

/-- The gamma factor may be computed with any Haar measure `ν` on `Kˣ`. -/
theorem gammaFactor_eq (μ : Measure K) (ψ : AddChar K Circle) (ν : Measure Kˣ)
    [ν.IsHaarMeasure] (s : ℂ) :
    gammaFactor ω μ ψ s = 𝔷[ν] ω⁻¹ (𝓕[ψ, μ] (gammaTestFunction ω)) (1 - s) /
      ν.real (unitFiltration K (ClassFieldTheory.characterConductorExp K ω)) := by
  have := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  have hρ := isMulLeftInvariant_eq_smul (unitsHaar K) ν
  set c := haarScalarFactor (unitsHaar K) ν
  have hc : (c : ℂ) ≠ 0 := by
    intro h
    have h' : c = 0 := by exact_mod_cast h
    exact NeZero.ne (unitsHaar K) (by rw [hρ, h', zero_smul])
  rw [gammaFactor, hρ, localZetaIntegral_def, localZetaIntegral_def, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply, NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul]
  exact mul_div_mul_left _ _ hc

variable (μ : Measure K) [μ.IsAddHaarMeasure] (ν : Measure Kˣ) [ν.IsHaarMeasure]
  {ψ : AddChar K Circle}

/-- **Tate's local functional equation.** For every locally constant compactly supported `f` on
`K` and `s` in the strip `0 < re s + r < 1`, where `r` is the exponent of `ω`,
`z(1 - s, ω⁻¹; 𝓕f) = γ(s, ω, ψ) z(s, ω; f)`, for every Haar measure `ν` on `Kˣ`. -/
theorem localZetaIntegral_functionalEquation (hψ : Continuous ψ) (h1 : ψ ≠ 1) {f : K → ℂ}
    (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) {s : ℂ}
    (hs₀ : 0 < s.re + characterExponent K ω) (hs₁ : s.re + characterExponent K ω < 1) :
    𝔷[ν] ω⁻¹ (𝓕[ψ, μ] f) (1 - s) = gammaFactor ω μ ψ s * 𝔷[ν] ω f s := by
  have h := localZetaIntegral_mul_localZetaIntegral_fourierIntegral_comm μ ν hψ h1 ω hf hfc
    (isLocallyConstant_gammaTestFunction ω) (hasCompactSupport_gammaTestFunction ω) hs₀ hs₁
  rw [localZetaIntegral_gammaTestFunction] at h
  have hm : ((ν.real (unitFiltration K (ClassFieldTheory.characterConductorExp K ω)) : ℝ) : ℂ) ≠
      0 := by exact_mod_cast (measureReal_unitFiltration_pos ν _).ne'
  rw [gammaFactor_eq ω μ ψ ν, div_mul_eq_mul_div, eq_div_iff hm]
  linear_combination -h

omit [μ.IsAddHaarMeasure] in
/-- **Uniqueness of the gamma factor.** A constant `γ` with `z(1 - s, ω⁻¹; 𝓕f) = γ z(s, ω; f)`
for all test functions `f` is `γ(s, ω, ψ)`. -/
theorem eq_gammaFactor_of_forall {s γ : ℂ} (hγ : ∀ f : K → ℂ, IsLocallyConstant f →
      HasCompactSupport f → 𝔷[ν] ω⁻¹ (𝓕[ψ, μ] f) (1 - s) = γ * 𝔷[ν] ω f s) :
    γ = gammaFactor ω μ ψ s := by
  have h := hγ _ (isLocallyConstant_gammaTestFunction ω) (hasCompactSupport_gammaTestFunction ω)
  have hm : ((ν.real (unitFiltration K (ClassFieldTheory.characterConductorExp K ω)) : ℝ) : ℂ) ≠
      0 := by exact_mod_cast (measureReal_unitFiltration_pos ν _).ne'
  rw [gammaFactor_eq ω μ ψ ν, h, localZetaIntegral_gammaTestFunction, mul_div_cancel_right₀ _ hm]

/-- **Holomorphy of the gamma factor.** `s ↦ γ(s, ω, ψ)` is holomorphic on the half-plane
`re s + r < 1`, where `r` is the exponent of `ω`; on the strip `0 < re s + r < 1` it is the
ratio of the two sides of Tate's functional equation. -/
theorem differentiableOn_gammaFactor (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    DifferentiableOn ℂ (gammaFactor ω μ ψ) {s | s.re + characterExponent K ω < 1} := by
  obtain ⟨hl, hc⟩ := isLocallyConstant_hasCompactSupport_fourierIntegral μ hψ h1
    (isLocallyConstant_gammaTestFunction ω) (hasCompactSupport_gammaTestFunction ω)
  have hd := differentiableOn_localZetaIntegral (unitsHaar K) ω⁻¹ hl.continuous hc
  refine (hd.comp (s := {s | s.re + characterExponent K ω < 1})
    ((differentiable_const 1).sub differentiable_id).differentiableOn fun s hs ↦ ?_).div_const _
  change s.re + characterExponent K ω < 1 at hs
  change 0 < (1 - s).re + characterExponent K ω⁻¹
  rw [sub_re, one_re, characterExponent_inv]
  linarith



/-! ### The unramified gamma factor -/

/-- For `ψ` of conductor exponent `0` and `μ(𝒪[K]) = 1`, the Fourier transform of `1_𝒪` is
`1_𝒪`: the annihilator of `𝒪[K]` for `ψ(x y)` is `𝒪[K]`. -/
theorem fourierIntegral_indicator_integer (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hψ0 : ψ.conductorExponent = 0) (hμ : μ 𝒪[K] = 1) :
    𝓕[ψ, μ] ((𝒪[K] : Set K).indicator (1 : K → ℂ)) = (𝒪[K] : Set K).indicator 1 := by
  have h0 := AddChar.setOf_eq_one_mem_nhds_zero hψ
  have hO : MeasurableSet ((𝒪[K]).toAddSubgroup : Set K) :=
    (Valuation.isClopen_integer (v := valuation K)).isClosed.measurableSet
  have hann : (((𝒪[K]).toAddSubgroup.characterAnnihilator ψ (-LinearMap.mul K K)) : Set K) =
      𝒪[K] := by
    ext y
    have key := AddChar.forall_mul_eq_one_iff_valuation_le h0 h1 0 y
    rw [hψ0, neg_zero, sub_zero, zpow_zero] at key
    rw [SetLike.mem_coe, AddSubgroup.mem_characterAnnihilator, SetLike.mem_coe,
      Valuation.mem_integer_iff, ← key]
    -- `𝒪[K]` is stable under negation, and `ψ (-(x y))` is `ψ ((-x) y)`.
    refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
    · have hx' : -x ∈ (𝒪[K]).toAddSubgroup := neg_mem (show x ∈ 𝒪[K] from
        (Valuation.mem_integer_iff _ _).2 hx)
      simpa using h _ hx'
    · have hx' : valuation K (-x) ≤ uniformizer K ^ (0 : ℤ) := by
        rw [Valuation.map_neg, zpow_zero]
        exact (Valuation.mem_integer_iff _ _).1 hx
      simpa using h _ hx'
  have h := VectorFourier.fourierIntegral_indicator_addSubgroup ψ μ (-LinearMap.mul K K) hO
    (1 : ℂ)
  rw [hann, measureReal_def] at h
  simp only [Pi.one_def]
  simpa [hμ] using h

omit [MeasurableSpace K] [BorelSpace K] in
/-- For `re s + r > 0`, where `r` is the exponent of `ω`, and a uniformizer `ϖ`,
`1 - ω(ϖ) q ^ (-s) ≠ 0`: the second term has norm `q ^ (-(re s + r)) < 1`. -/
theorem one_sub_mul_natCard_cpow_ne_zero {ω : Kˣ →ₜ* ℂˣ} {ϖ : Kˣ} (hϖ : IsUniformizer K ϖ)
    {s : ℂ} (hs : 0 < s.re + characterExponent K ω) :
    1 - (ω ϖ : ℂ) * (Nat.card 𝓀[K] : ℂ) ^ (-s) ≠ 0 := by
  have hq := one_lt_natCard_residueField (K := K) (R := ℝ)
  have hq₀ : (0 : ℝ) < Nat.card 𝓀[K] := zero_lt_one.trans hq
  intro h
  have hn : ‖(ω ϖ : ℂ) * (Nat.card 𝓀[K] : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, norm_coe_apply_eq_rpow_characterExponent, coe_normalizedAbsoluteValue_eq_zpow,
      (isUniformizer_def ϖ).1 hϖ, toAdd_ofAdd, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos hq₀, neg_re, ← Real.rpow_intCast, ← Real.rpow_mul hq₀.le,
      ← Real.rpow_add hq₀]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by push_cast; linarith)
  rw [← (sub_eq_zero.1 h), norm_one] at hn
  exact lt_irrefl _ hn

/-- **The unramified gamma factor.** If `ω` is unramified, `ψ` has conductor exponent `0` and
`μ(𝒪[K]) = 1`, then on the strip `0 < re s + r < 1`,
`γ(s, ω, ψ) = (1 - ω(ϖ) q ^ (-s)) (1 - ω(ϖ)⁻¹ q ^ (-(1 - s)))⁻¹ = L(1 - s, ω⁻¹) / L(s, ω)`, so
that the epsilon factor is `1`. This is the local equation for `1_𝒪`, which is its own Fourier
transform. -/
theorem gammaFactor_of_unramified (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (hψ0 : ψ.conductorExponent = 0) (hμ : μ 𝒪[K] = 1) (hω : unitFiltration K 0 ≤ ω.ker)
    {ϖ : Kˣ} (hϖ : IsUniformizer K ϖ) {s : ℂ} (hs₀ : 0 < s.re + characterExponent K ω)
    (hs₁ : s.re + characterExponent K ω < 1) :
    gammaFactor ω μ ψ s = (1 - ω ϖ * (Nat.card 𝓀[K] : ℂ) ^ (-s)) *
      (1 - (ω ϖ : ℂ)⁻¹ * (Nat.card 𝓀[K] : ℂ) ^ (-(1 - s)))⁻¹ := by
  have hinv (v : Kˣ) : (ω⁻¹ v : ℂ) = (ω v : ℂ)⁻¹ := by
    rw [ContinuousMonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  have hω' : unitFiltration K 0 ≤ (ω⁻¹).ker := fun u hu ↦ by
    have h : ω u = 1 := hω hu
    change ω⁻¹ u = 1
    rw [ContinuousMonoidHom.inv_apply, h, inv_one]
  have hX := one_sub_mul_natCard_cpow_ne_zero hϖ hs₀
  have hFE := localZetaIntegral_functionalEquation ω μ (unitsHaar K) hψ h1
    ((LocallyConstant.coe_charFn ℂ (Valuation.isClopen_integer (v := valuation K))) ▸
      LocallyConstant.isLocallyConstant _) (hasCompactSupport_indicator_integer K) hs₀ hs₁
  rw [fourierIntegral_indicator_integer μ hψ h1 hψ0 hμ,
    localZetaIntegral_unitsHaar_indicator_integer_of_unramified hω' hϖ (by
      rw [characterExponent_inv, sub_re, one_re]; linarith),
    localZetaIntegral_unitsHaar_indicator_integer_of_unramified hω hϖ hs₀, hinv] at hFE
  rw [hFE, mul_left_comm, mul_inv_cancel₀ hX, mul_one]

end TauCeti.TateZeta
