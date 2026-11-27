/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.Analysis.SpecialFunctions.Complex.ArchimedeanCharacter
public import TauCeti.MeasureTheory.Constructions.Polish.Units
public import TauCeti.MeasureTheory.Measure.Haar.ArchimedeanMultHaar
public import TauCeti.NumberTheory.LocalField.TateZeta.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.Distribution.SchwartzSpace.SingularWeight
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The local Tate zeta integral at the real and complex places

At an archimedean place the local field is `ℝ`, with normalized absolute value `|x|`, or `ℂ`, with
normalized absolute value `|z|_ℂ = z conj(z) = normSq z`. Following Tate and Kudla, the
multiplicative Haar measures are `dx / |x|` on `ℝˣ` and `2 dx dy / |z|_ℂ` on `ℂˣ`
(`TauCeti.realUnitsMultHaar`, `TauCeti.complexUnitsMultHaar`, the restrictions to the units of
`TauCeti.realMultHaar` and `TauCeti.complexMultHaar`). For a Schwartz function `f` and a
quasi-character `χ` of exponent `r`, that is `‖χ(x)‖ = |x| ^ r`, this file studies

`z(s, χ; f) = ∫ f(x) χ(x) |x| ^ s d^×x`

(`TauCeti.TateZeta.localZetaIntegral`).

* **Convergence and holomorphy.** The integrand has norm `‖f(x)‖ |x| ^ (re s + r)`, which is
  `‖f(x)‖ ‖x‖ ^ (re s + r - 1)` against Lebesgue measure on `ℝ` and twice
  `‖f(z)‖ ‖z‖ ^ (2 (re s + r) - 2)` on `ℂ`. Both are integrable for `re s + r > 0`
  (`SchwartzMap.integrable_norm_rpow_mul_norm_of_neg_finrank_lt`), so `z(s, χ; f)` converges
  absolutely on that half-plane and is holomorphic there; for a unitary `χ` this is `re s > 0`.
  For fixed `s` in the half-plane, `f ↦ z(s, χ; f)` is a continuous linear functional on the
  Schwartz space.
* **Gaussians.** `z(s, 1; e^(-π x²)) = Γ_ℝ(s)` and `z(s, 1; e^(-2π |z|_ℂ)) = π Γ_ℂ(s)` on
  `re s > 0`, with Deligne's `Γ_ℝ(s) = π^(-s/2) Γ(s/2)` and `Γ_ℂ(s) = 2 (2π)^(-s) Γ(s)`.
* **Standard functions.** In Kudla's normal forms `ω(x) = x^(-a)`, `a ∈ {0, 1}`, on `ℝˣ`, and
  `ω(z) = z^(-a) conj(z)^(-b)` on `ℂˣ`, the standard functions `x^a e^(-π x²)` and
  `π⁻¹ z^a conj(z)^b e^(-2π |z|_ℂ)` have zeta integral `Γ_ℝ(s)` and `Γ_ℂ(s)`, the archimedean
  local factors `L(s, ω)`. Test functions of the wrong angular weight have zeta integral `0`.

## Main definitions

* `TauCeti.realUnitsMultHaar`, `TauCeti.complexUnitsMultHaar`: `dx / |x|` on `ℝˣ` and
  `2 dx dy / |z|_ℂ` on `ℂˣ`; both are Haar measures.
* `TauCeti.TateZeta.realLocalZetaCLM`, `TauCeti.TateZeta.complexLocalZetaCLM`: for `s` in the
  half-plane of absolute convergence, `f ↦ z(s, χ; f)` as a continuous linear functional on
  `𝓢(ℝ, ℂ)` and `𝓢(ℂ, ℂ)`.

## Main results

* `TauCeti.differentiableOn_integral_mul_cpow`: `s ↦ ∫ F(x) a(x) ^ s dν` is holomorphic on every
  half-plane `α < re s` on which `‖F‖ a ^ σ` is integrable for all `σ > α`.
* `TauCeti.TateZeta.integrable_localZetaIntegrand_real`,
  `TauCeti.TateZeta.differentiableOn_localZetaIntegral_real`: absolute convergence and
  holomorphy at `ℝ` on `re s + r > 0`; `..._complex` likewise at `ℂ`.
* `TauCeti.TateZeta.localZetaIntegral_real_gaussian`: `z(s, 1; e^(-π x²)) = Γ_ℝ(s)`.
* `TauCeti.TateZeta.localZetaIntegral_complex_gaussian`: `z(s, 1; e^(-2π |z|_ℂ)) = π Γ_ℂ(s)`.
* `TauCeti.TateZeta.localZetaIntegral_realUnitsCharacter_standard`,
  `TauCeti.TateZeta.localZetaIntegral_complexUnitsCharacter_standard`: the standard functions in
  Kudla's normal forms have zeta integral `Γ_ℝ(s)` and `Γ_ℂ(s)`.
* `TauCeti.TateZeta.localZetaIntegral_complexUnitsCharacter_eq_zero_of_rotation`: a test function
  of angular weight `m` has zeta integral `0` against a character of angular weight `k ≠ -m`.

## Implementation notes

The complex place uses `|z|_ℂ = normSq z` as the absolute value in the zeta integral, as in the
roadmap and in Tau Ceti's `TauCeti.existsUnique_norm_coe_complexUnits_eq_rpow`; the parameters of
`TauCeti.complexUnitsCharacter s k`, `z ↦ |z| ^ s (z / |z|) ^ k`, use the usual modulus, so its
exponent for `|z|_ℂ` is `re s / 2`. The complex Gaussian integral is `π Γ_ℂ(s) = (2π)^(1-s) Γ(s)`
for the twice-Lebesgue additive measure (Kudla's normalization); the standard function carries
the factor `π⁻¹` so that its value is Deligne's `Γ_ℂ(s)`.

Every Haar measure on `ℝˣ` or `ℂˣ` is a positive multiple of the ones here, and
`TauCeti.TateZeta.localZetaIntegral_smul_measure` rescales the zeta integral accordingly.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich, eds., *Algebraic Number Theory*, §2.4–2.5.
* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, §3, (3.18)–(3.21).
* The convergence statement at the infinite places of a number field is
  `infiniteLocalIdelicZetaIntegral_integrable` and the Gaussian values are
  `infiniteLocalIdelicZFunction_standardGaussian` in `RiemannMasullo/Ch03_IdelicZeta/Sec3b.lean`
  and `RiemannMasullo/Ch03_IdelicZeta/Sec4.lean` of the Riemann–Masullo formalization
  (https://github.com/mccorvie/riemann-masullo). That development uses Bruhat's Schwartz–Bruhat
  space, the norm `‖z‖²` with angular weight `(z / ‖z‖) ^ k`, and the complex factor
  `(2π) ^ (-s) Γ(s) = Γ_ℂ(s) / 2`; this file uses Mathlib's Schwartz space and Deligne's
  `Γ_ℂ`.
-/

public section
noncomputable section

open MeasureTheory Measure Set Complex Filter Topology SchwartzMap
open scoped Real

namespace TauCeti

/-! ### Multiplicative Haar measures on the units of `ℝ` and `ℂ` -/

section UnitsComap

variable {K : Type*} [GroupWithZero K] [TopologicalSpace K] [ContinuousMul K] [PolishSpace K]
  [MeasurableSpace K] [BorelSpace K] {μ : Measure K}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [TopologicalSpace K] [ContinuousMul K] [PolishSpace K] [MeasurableSpace K] [BorelSpace K] in
private theorem range_units_val : range (Units.val : Kˣ → K) = {0}ᶜ := by
  ext y
  refine ⟨?_, fun hy ↦ ⟨Units.mk0 y hy, rfl⟩⟩
  rintro ⟨u, rfl⟩
  exact u.ne_zero

/-- Integrating a function of `x : K` over `Kˣ` against the pullback of a measure that does not
charge `0` is integrating it over `K`. -/
private theorem integral_comap_units_val [NullSingletonClass μ] (g : K → E) :
    ∫ x : Kˣ, g x ∂μ.comap Units.val = ∫ y, g y ∂μ := by
  rw [← Units.measurableEmbedding_val.integral_map, Units.measurableEmbedding_val.map_comap,
    range_units_val, restrict_compl_singleton]

omit [NormedSpace ℝ E] in
/-- Integrability over `Kˣ` of a function of `x : K` is integrability over `K`. -/
private theorem integrable_comap_units_val_iff [NullSingletonClass μ] {g : K → E} :
    Integrable (fun x : Kˣ ↦ g x) (μ.comap Units.val) ↔ Integrable g μ := by
  have h := Units.measurableEmbedding_val.integrable_map_iff (μ := μ.comap Units.val) (g := g)
  rw [Units.measurableEmbedding_val.map_comap, range_units_val, restrict_compl_singleton] at h
  exact h.symm

/-- The pullback to `Kˣ` of a measure invariant under multiplication by units is left invariant. -/
private theorem isMulLeftInvariant_comap_units_val
    (h : ∀ b : Kˣ, μ.map ((b : K) * ·) = μ) : (μ.comap Units.val).IsMulLeftInvariant where
  map_mul_left_eq_self b := by
    have he := Units.measurableEmbedding_val (M := K)
    ext S hS
    rw [map_apply (measurable_const_mul b) hS, he.comap_apply, he.comap_apply]
    have himage : Units.val '' ((b * ·) ⁻¹' S) = ((b : K) * ·) ⁻¹' (Units.val '' S) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨b * u, hu, rfl⟩
      · rintro ⟨v, hv, hvy⟩
        refine ⟨b⁻¹ * v, by simpa using hv, ?_⟩
        rw [Units.val_mul, hvy, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          one_mul]
    rw [himage, ← map_apply (measurable_const_mul _) (he.measurableSet_image.2 hS), h b]

end UnitsComap

/-- The multiplicative Haar measure `dx / |x|` of `ℝˣ`: the pullback of `TauCeti.realMultHaar`
along `ℝˣ → ℝ`. -/
def realUnitsMultHaar : Measure ℝˣ :=
  realMultHaar.comap Units.val

/-- The multiplicative Haar measure `2 dx dy / |z|_ℂ` of `ℂˣ`: the pullback of
`TauCeti.complexMultHaar` along `ℂˣ → ℂ`. -/
def complexUnitsMultHaar : Measure ℂˣ :=
  complexMultHaar.comap Units.val

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrating a function of `x : ℝ` against `dx / |x|` over `ℝˣ` is integrating it against
`TauCeti.realMultHaar` over `ℝ`. -/
theorem integral_realUnitsMultHaar (g : ℝ → E) :
    ∫ x : ℝˣ, g x ∂realUnitsMultHaar = ∫ y, g y ∂realMultHaar :=
  integral_comap_units_val g

omit [NormedSpace ℝ E] in
/-- A function of `x : ℝ` is integrable against `dx / |x|` over `ℝˣ` exactly when it is
integrable against `TauCeti.realMultHaar` over `ℝ`. -/
theorem integrable_realUnitsMultHaar_iff {g : ℝ → E} :
    Integrable (fun x : ℝˣ ↦ g x) realUnitsMultHaar ↔ Integrable g realMultHaar :=
  integrable_comap_units_val_iff

/-- Integrating a function of `z : ℂ` against `2 dx dy / |z|_ℂ` over `ℂˣ` is integrating it
against `TauCeti.complexMultHaar` over `ℂ`. -/
theorem integral_complexUnitsMultHaar (g : ℂ → E) :
    ∫ z : ℂˣ, g z ∂complexUnitsMultHaar = ∫ w, g w ∂complexMultHaar :=
  integral_comap_units_val g

omit [NormedSpace ℝ E] in
/-- A function of `z : ℂ` is integrable against `2 dx dy / |z|_ℂ` over `ℂˣ` exactly when it is
integrable against `TauCeti.complexMultHaar` over `ℂ`. -/
theorem integrable_complexUnitsMultHaar_iff {g : ℂ → E} :
    Integrable (fun z : ℂˣ ↦ g z) complexUnitsMultHaar ↔ Integrable g complexMultHaar :=
  integrable_comap_units_val_iff

end

instance : realUnitsMultHaar.IsMulLeftInvariant :=
  isMulLeftInvariant_comap_units_val fun b ↦ map_realMultHaar_mul_left b.ne_zero

instance : complexUnitsMultHaar.IsMulLeftInvariant :=
  isMulLeftInvariant_comap_units_val fun b ↦ map_complexMultHaar_mul_left b.ne_zero

/-- A density that is continuous and positive away from `0`, pulled back to the units: the
resulting measure is finite on compact sets and positive on nonempty open sets. -/
private theorem isFiniteMeasureOnCompacts_isOpenPosMeasure_comap_units_val
    {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] (ν : Measure K)
    [ν.IsAddHaarMeasure] {ρ : K → ℝ} (hρ : ContinuousOn ρ {0}ᶜ) (hρm : Measurable ρ)
    (hρpos : ∀ x ≠ 0, 0 < ρ x) :
    IsFiniteMeasureOnCompacts ((ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)).comap Units.val) ∧
      ((ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)).comap Units.val).IsOpenPosMeasure := by
  have he := Units.measurableEmbedding_val (M := K)
  have hval : IsOpenEmbedding (Units.val : Kˣ → K) := Units.isOpenEmbedding_val
  have hsub (S : Set Kˣ) : Units.val '' S ⊆ {0}ᶜ := by
    rintro _ ⟨u, -, rfl⟩
    exact u.ne_zero
  refine ⟨⟨fun C hC ↦ ?_⟩, ⟨fun U hU hne ↦ ?_⟩⟩
  · rw [he.comap_apply, withDensity_apply _ (he.measurableSet_image.2 ?_)]
    · have hC' := hC.image Units.continuous_val
      obtain ⟨M, hM⟩ := hC'.bddAbove_image (hρ.mono (hsub C))
      calc ∫⁻ x in Units.val '' C, ENNReal.ofReal (ρ x) ∂ν
          ≤ ∫⁻ _ in Units.val '' C, ENNReal.ofReal M ∂ν :=
            setLIntegral_mono measurable_const fun x hx ↦
              ENNReal.ofReal_le_ofReal (hM (mem_image_of_mem ρ hx))
        _ < ⊤ := by
            rw [setLIntegral_const]
            exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC'.measure_lt_top
    · exact hC.isClosed.measurableSet
  · rw [he.comap_apply, Ne, withDensity_apply_eq_zero' (f := fun x ↦ ENNReal.ofReal (ρ x))
      (ENNReal.measurable_ofReal.comp hρm).aemeasurable]
    have hset : {x | ENNReal.ofReal (ρ x) ≠ 0} ∩ Units.val '' U = Units.val '' U := by
      refine inter_eq_right.2 fun x hx ↦ ?_
      simpa using hρpos x (hsub U hx)
    rw [hset]
    exact (hval.isOpenMap U hU).measure_ne_zero ν (hne.image _)

instance : realUnitsMultHaar.IsHaarMeasure := by
  have h := isFiniteMeasureOnCompacts_isOpenPosMeasure_comap_units_val volume
    (ρ := fun x : ℝ ↦ |x|⁻¹) (continuous_abs.continuousOn.inv₀ fun x hx ↦ abs_ne_zero.2 hx)
    continuous_abs.measurable.inv fun x hx ↦ inv_pos.2 (abs_pos.2 hx)
  have hm : realUnitsMultHaar = (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal |x|⁻¹).comap
      Units.val := by rw [realUnitsMultHaar, realMultHaar_def]
  have : IsFiniteMeasureOnCompacts realUnitsMultHaar := hm ▸ h.1
  have : realUnitsMultHaar.IsOpenPosMeasure := hm ▸ h.2
  exact {}

instance : complexUnitsMultHaar.IsHaarMeasure := by
  have h := isFiniteMeasureOnCompacts_isOpenPosMeasure_comap_units_val volume
    (ρ := fun z : ℂ ↦ 2 * (‖z‖ ^ 2)⁻¹)
    (continuousOn_const.mul ((continuous_norm.pow 2).continuousOn.inv₀ fun z hz ↦
      pow_ne_zero 2 (norm_ne_zero_iff.2 hz)))
    (measurable_const.mul (measurable_norm.pow_const 2).inv)
    fun z hz ↦ mul_pos two_pos (inv_pos.2 (pow_pos (norm_pos_iff.2 hz) 2))
  have hm : complexUnitsMultHaar = (volume.withDensity fun z : ℂ ↦
      ENNReal.ofReal (2 * (‖z‖ ^ 2)⁻¹)).comap Units.val := by
    rw [complexUnitsMultHaar, complexMultHaar_def]
  have : IsFiniteMeasureOnCompacts complexUnitsMultHaar := hm ▸ h.1
  have : complexUnitsMultHaar.IsOpenPosMeasure := hm ▸ h.2
  exact {}

/-! ### Radial integrals -/

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A radial integral against `dx / |x|` is twice the corresponding integral against `dt / t`. -/
theorem integral_realMultHaar_comp_abs (G : ℝ → E) :
    ∫ y, G |y| ∂realMultHaar = (2 : ℝ) • ∫ t, G t ∂multHaar := by
  have h := integral_fun_norm_addHaar (volume : Measure ℝ) (fun r ↦ r⁻¹ • G r)
  simp only [Real.norm_eq_abs, Module.finrank_self, one_smul, pow_zero, tsub_self] at h
  rw [integral_realMultHaar, h, integral_multHaar_eq_setIntegral]
  norm_num

/-- A radial integral against `2 dx dy / |z|_ℂ` is `4π` times the corresponding integral against
`dt / t`. -/
theorem integral_complexMultHaar_comp_norm (G : ℝ → E) :
    ∫ z, G ‖z‖ ∂complexMultHaar = (4 * π) • ∫ t, G t ∂multHaar := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r ↦ (2 * (r ^ 2)⁻¹) • G r)
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    rw [Measure.real, Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul,
      ENNReal.coe_toReal, NNReal.coe_real_pi]
  have hint : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • (2 * (y ^ 2)⁻¹) • G y =
      (2 : ℝ) • ∫ y in Ioi (0 : ℝ), y⁻¹ • G y := by
    rw [← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    simp only [smul_smul]
    congr 1
    field_simp
    ring
  rw [integral_complexMultHaar, h, integral_multHaar_eq_setIntegral, Complex.finrank_real_complex,
    hball, hint, smul_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  push_cast
  ring

/-- `∫ t ^ w e^(-b t²) dt / t = Γ(w / 2) b ^ (-w / 2) / 2` for `b > 0` and `re w > 0`. -/
theorem integral_multHaar_cpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {w : ℂ} (hw : 0 < w.re) :
    ∫ t, (t : ℂ) ^ w * (Real.exp (-(b * t ^ 2)) : ℂ) ∂multHaar =
      (1 / 2 : ℂ) * ((b : ℂ) ^ (-(w / 2)) * Gamma (w / 2)) := by
  have hw2 : 0 < (w / 2).re := by rw [div_ofNat_re]; exact half_pos hw
  set h : ℝ → ℂ := fun u ↦ (u : ℂ) ^ (w / 2) * (Real.exp (-(b * u)) : ℂ)
  have hmap := map_multHaar_rpow (γ := 2) two_ne_zero
  have hh : AEStronglyMeasurable h (multHaar.map (· ^ (2 : ℝ))) :=
    ((Complex.measurable_ofReal.pow_const _).mul
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const_mul b).neg))).aestronglyMeasurable
  have key := integral_map (μ := multHaar) (measurable_id'.pow_const (2 : ℝ)).aemeasurable hh
  rw [hmap, integral_smul_measure, integral_multHaar_cpow_mul_exp_neg_mul hb.le hw2] at key
  rw [← integral_congr_ae (ae_pos_multHaar.mono fun t (ht : 0 < t) ↦ ?_)]
  · rw [← key]
    norm_num
  · simp only [h, Real.rpow_two]
    rw [ofReal_pow, ofReal_pow_cpow ht.le, Nat.cast_ofNat, mul_div_cancel₀ _ two_ne_zero]

end Radial

/-! ### Holomorphy of power-weighted integrals -/

/-- **Holomorphy on a half-plane of absolute convergence.** Let `a` be a positive measurable
function and `F` an almost everywhere strongly measurable function on a measure space, such that
`‖F‖ a ^ σ` is integrable for every `σ > α`. Then `s ↦ ∫ F(x) a(x) ^ s dν` is holomorphic on the
half-plane `α < re s`. -/
theorem differentiableOn_integral_mul_cpow {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {F : X → ℂ} {a : X → ℝ} (ha : ∀ x, 0 < a x) (hF : AEStronglyMeasurable F ν)
    (ham : Measurable a) {α : ℝ}
    (hint : ∀ σ : ℝ, α < σ → Integrable (fun x ↦ ‖F x‖ * a x ^ σ) ν) :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∫ x, F x * (a x : ℂ) ^ s ∂ν) {s | α < s.re} := by
  have hU : IsOpen {s : ℂ | α < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (analyticOnNhd_integral_of_dominated (F := fun s x ↦ F x * (a x : ℂ) ^ s) hU
    (fun s _ ↦ hF.mul ((Complex.measurable_ofReal.comp ham).pow_const s).aestronglyMeasurable) ?_
    (ae_of_all _ fun x s _ ↦ ?_)).differentiableOn
  · intro s (hs : α < s.re)
    obtain ⟨δ, hδ, hδα⟩ : ∃ δ : ℝ, 0 < δ ∧ α < s.re - δ :=
      ⟨(s.re - α) / 2, by linarith, by linarith⟩
    refine ⟨{w | s.re - δ < w.re ∧ w.re < s.re + δ},
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds
        ⟨show s.re - δ < s.re by linarith, show s.re < s.re + δ by linarith⟩,
      fun x ↦ ‖F x‖ * a x ^ (s.re - δ) + ‖F x‖ * a x ^ (s.re + δ),
      (hint _ hδα).add (hint _ (by linarith)), ae_of_all _ fun x w hw ↦ ?_⟩
    dsimp only
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (ha x), ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rcases le_total (a x) 1 with h1 | h1
    · exact (Real.rpow_le_rpow_of_exponent_ge (ha x) h1 hw.1.le).trans
        (le_add_of_nonneg_right (Real.rpow_pos_of_pos (ha x) _).le)
    · exact (Real.rpow_le_rpow_of_exponent_le h1 hw.2.le).trans
        (le_add_of_nonneg_left (Real.rpow_pos_of_pos (ha x) _).le)
  · exact ((differentiableAt_id.const_cpow
      (Or.inl (ofReal_ne_zero.2 (ha x).ne'))).const_mul (F x)).differentiableWithinAt

namespace TateZeta

/-! ### The real place -/

section Real

variable (f : 𝓢(ℝ, ℂ))

/-- For `σ > 0`, `‖f(y)‖ |y| ^ σ` is integrable against `dx / |x|`, since against Lebesgue measure
it is `‖f(y)‖ |y| ^ (σ - 1)` with `σ - 1 > -1`. -/
private theorem integrable_realMultHaar_norm_mul_rpow {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun y : ℝ ↦ ‖f y‖ * |y| ^ σ) realMultHaar := by
  rw [integrable_realMultHaar_iff]
  refine (f.integrable_norm_rpow_mul_norm_of_neg_finrank_lt volume (t := σ - 1)
    (by simp; linarith)).congr ((Measure.ae_ne volume 0).mono fun y hy ↦ ?_)
  simp only [Real.norm_eq_abs, smul_eq_mul]
  rw [Real.rpow_sub_one (abs_pos.2 hy).ne']
  field_simp

/-- `∫ ‖f(y)‖ |y| ^ σ dy / |y| = ∫ ‖y‖ ^ (σ - 1) ‖f(y)‖ dy`. -/
private theorem integral_realMultHaar_norm_mul_rpow (σ : ℝ) :
    ∫ y : ℝ, ‖f y‖ * |y| ^ σ ∂realMultHaar = ∫ y : ℝ, ‖y‖ ^ (σ - 1) * ‖f y‖ := by
  rw [integral_realMultHaar]
  refine integral_congr_ae ((Measure.ae_ne volume 0).mono fun y hy ↦ ?_)
  simp only [Real.norm_eq_abs, smul_eq_mul]
  rw [Real.rpow_sub_one (abs_pos.2 hy).ne']
  field_simp

/-- The norm of the zeta integrand at `ℝ`, for a quasi-character of exponent `r`. -/
private theorem norm_zetaIntegrand_real {χ : ℝˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r) (s : ℂ) (x : ℝˣ) :
    ‖f x * (χ x : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s‖ = ‖f x‖ * |(x : ℝ)| ^ (s.re + r) := by
  have hx : 0 < |(x : ℝ)| := abs_pos.2 x.ne_zero
  rw [norm_mul, norm_mul, hχ, norm_cpow_eq_rpow_re_of_pos hx, mul_assoc,
    ← Real.rpow_add hx, add_comm r]

private theorem measurable_zetaIntegrand_real (χ : ℝˣ →ₜ* ℂˣ) (s : ℂ) :
    Measurable fun x : ℝˣ ↦ f x * (χ x : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s :=
  ((f.continuous.comp Units.continuous_val).measurable.mul
    (Units.continuous_val.comp χ.continuous).measurable).mul
    ((Complex.continuous_ofReal.comp (continuous_abs.comp
      Units.continuous_val)).measurable.pow_const s)

/-- **Absolute convergence at `ℝ`.** For a Schwartz function `f` and a quasi-character `χ` of
`ℝˣ` of exponent `r`, the zeta integrand `f(x) χ(x) |x| ^ s` is integrable against `dx / |x|`
for `re s + r > 0`. -/
theorem integrable_localZetaIntegrand_real {χ : ℝˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    Integrable (fun x : ℝˣ ↦ f x * (χ x : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s) realUnitsMultHaar :=
  (integrable_realUnitsMultHaar_iff.2 (integrable_realMultHaar_norm_mul_rpow f hs)).mono'
    (measurable_zetaIntegrand_real f χ s).aestronglyMeasurable
    (ae_of_all _ fun x ↦ (norm_zetaIntegrand_real f hχ s x).le)

/-- **Holomorphy at `ℝ`.** For a Schwartz function `f` and a quasi-character `χ` of `ℝˣ` of
exponent `r`, `s ↦ z(s, χ; f)` is holomorphic on `re s + r > 0`. -/
theorem differentiableOn_localZetaIntegral_real {χ : ℝˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r) :
    DifferentiableOn ℂ (localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) χ f)
      {s | 0 < s.re + r} := by
  have h := differentiableOn_integral_mul_cpow realUnitsMultHaar (F := fun x ↦ f x * (χ x : ℂ))
    (a := fun x ↦ |(x : ℝ)|) (α := -r) (fun x ↦ abs_pos.2 x.ne_zero)
    ((f.continuous.comp Units.continuous_val).mul
      (Units.continuous_val.comp χ.continuous)).aestronglyMeasurable
    (continuous_abs.comp Units.continuous_val).measurable fun σ hσ ↦ ?_
  · rw [show localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) χ f =
        fun s ↦ ∫ x : ℝˣ, f x * (χ x : ℂ) * ((|(x : ℝ)| : ℝ) : ℂ) ^ s ∂realUnitsMultHaar from
      funext fun s ↦ localZetaIntegral_def _ _ _ _ _]
    exact h.mono fun s (hs : 0 < s.re + r) ↦ show -r < s.re by linarith
  · refine (integrable_realUnitsMultHaar_iff.2
      (integrable_realMultHaar_norm_mul_rpow f (σ := σ + r) (by linarith))).congr
      (ae_of_all _ fun x ↦ ?_)
    have hx : 0 < |(x : ℝ)| := abs_pos.2 x.ne_zero
    simp only [norm_mul, hχ, mul_assoc, ← Real.rpow_add hx, add_comm r]

/-- **Continuity on the Schwartz space at `ℝ`.** For a quasi-character `χ` of `ℝˣ` of exponent
`r` and `re s + r > 0`, the local zeta integral `f ↦ z(s, χ; f)` is a continuous linear functional
on `𝓢(ℝ, ℂ)`. -/
def realLocalZetaCLM (χ : ℝˣ →ₜ* ℂˣ) {r : ℝ} (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r)
    {s : ℂ} (hs : 0 < s.re + r) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  mkCLMtoNormedSpace (fun f ↦ localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) χ f s)
    (fun f g ↦ localZetaIntegral_add realUnitsMultHaar _ χ
        (integrable_localZetaIntegrand_real f hχ hs) (integrable_localZetaIntegrand_real g hχ hs))
    (fun c f ↦ localZetaIntegral_const_mul realUnitsMultHaar _ χ c f s)
    (by
      obtain ⟨S, C, hC, hbound⟩ := exists_integral_norm_rpow_mul_norm_le (E := ℝ) (F := ℂ) volume ℂ
        (t := s.re + r - 1) (by simp; linarith)
      refine ⟨S, C, hC, fun f ↦ ?_⟩
      rw [localZetaIntegral_def]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_ (hbound f))
      simp_rw [norm_zetaIntegrand_real f hχ s]
      rw [integral_realUnitsMultHaar (fun y ↦ ‖f y‖ * |y| ^ (s.re + r)),
        integral_realMultHaar_norm_mul_rpow])

@[simp]
theorem realLocalZetaCLM_apply (χ : ℝˣ →ₜ* ℂˣ) {r : ℝ}
    (hχ : ∀ x : ℝˣ, ‖(χ x : ℂ)‖ = |(x : ℝ)| ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    realLocalZetaCLM χ hχ hs f = localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) χ f s :=
  (rfl)

/-- **The real Gaussian.** `z(s, 1; e^(-π x²)) = Γ_ℝ(s) = π^(-s/2) Γ(s/2)` on `re s > 0`. -/
theorem localZetaIntegral_real_gaussian {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) 1
      (fun x ↦ (Real.exp (-(π * x ^ 2)) : ℂ)) s = Gammaℝ s := by
  rw [localZetaIntegral_def]
  simp only [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, mul_one]
  rw [integral_realUnitsMultHaar (fun y ↦ (Real.exp (-(π * y ^ 2)) : ℂ) * ((|y| : ℝ) : ℂ) ^ s)]
  have h := integral_realMultHaar_comp_abs (fun t ↦ (Real.exp (-(π * t ^ 2)) : ℂ) * (t : ℂ) ^ s)
  simp only [sq_abs] at h
  rw [h]
  simp_rw [mul_comm (Real.exp _ : ℂ)]
  rw [integral_multHaar_cpow_mul_exp_neg_mul_sq Real.pi_pos hs, Gammaℝ_def]
  norm_num
  ring_nf

/-- **The real standard functions.** In Kudla's normal form `ω(x) = x ^ (-a)`, `a ∈ {0, 1}`
(`TauCeti.realUnitsCharacter (-a) a`), the standard function `x ^ a e^(-π x²)` has zeta integral
`L(s, ω) = Γ_ℝ(s)` on `re s > 0`. -/
theorem localZetaIntegral_realUnitsCharacter_standard (ε : ZMod 2) {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral realUnitsMultHaar (fun x ↦ |x|) (realUnitsCharacter (-(ε.val : ℂ)) ε)
      (fun x ↦ (x : ℂ) ^ ε.val * (Real.exp (-(π * x ^ 2)) : ℂ)) s = Gammaℝ s := by
  rw [← localZetaIntegral_real_gaussian hs, localZetaIntegral_def, localZetaIntegral_def]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  have h := coe_realUnitsCharacter_sub_val_apply 0 ε x
  rw [zero_sub, cpow_zero, mul_one] at h
  simp only [h, ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, mul_one]
  have hx : ((x : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 x.ne_zero
  rw [zpow_neg, zpow_natCast]
  field_simp

end Real

/-! ### The complex place -/

section Complex

variable (f : 𝓢(ℂ, ℂ))

/-- `normSq z ^ σ = ‖z‖ ^ (2 σ)`. -/
private theorem normSq_rpow (z : ℂ) (σ : ℝ) : normSq z ^ σ = ‖z‖ ^ (2 * σ) := by
  rw [normSq_eq_norm_sq, Real.rpow_mul (norm_nonneg z), Real.rpow_two]

/-- For `σ > 0`, `‖f(z)‖ |z|_ℂ ^ σ` is integrable against `2 dx dy / |z|_ℂ`, since against
Lebesgue measure it is twice `‖f(z)‖ ‖z‖ ^ (2 σ - 2)` with `2 σ - 2 > -2`. -/
private theorem integrable_complexMultHaar_norm_mul_rpow {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun z : ℂ ↦ ‖f z‖ * normSq z ^ σ) complexMultHaar := by
  rw [integrable_complexMultHaar_iff]
  refine ((f.integrable_norm_rpow_mul_norm_of_neg_finrank_lt volume (t := 2 * σ - 2)
    (by simp; linarith)).const_mul 2).congr ((Measure.ae_ne volume 0).mono fun z hz ↦ ?_)
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  simp only [smul_eq_mul, normSq_rpow]
  rw [Real.rpow_sub hz', Real.rpow_two]
  field_simp

/-- `∫ ‖f(z)‖ |z|_ℂ ^ σ (2 dx dy / |z|_ℂ) = 2 ∫ ‖z‖ ^ (2 σ - 2) ‖f(z)‖ dx dy`. -/
private theorem integral_complexMultHaar_norm_mul_rpow (σ : ℝ) :
    ∫ z : ℂ, ‖f z‖ * normSq z ^ σ ∂complexMultHaar =
      2 * ∫ z : ℂ, ‖z‖ ^ (2 * σ - 2) * ‖f z‖ := by
  rw [integral_complexMultHaar, ← integral_const_mul]
  refine integral_congr_ae ((Measure.ae_ne volume 0).mono fun z hz ↦ ?_)
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  simp only [smul_eq_mul, normSq_rpow]
  rw [Real.rpow_sub hz', Real.rpow_two]
  field_simp

/-- The norm of the zeta integrand at `ℂ`, for a quasi-character of exponent `r`. -/
private theorem norm_zetaIntegrand_complex {χ : ℂˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) (s : ℂ) (z : ℂˣ) :
    ‖f z * (χ z : ℂ) * ((normSq (z : ℂ) : ℝ) : ℂ) ^ s‖ =
      ‖f z‖ * normSq (z : ℂ) ^ (s.re + r) := by
  have hz : 0 < normSq (z : ℂ) := normSq_pos.2 z.ne_zero
  rw [norm_mul, norm_mul, hχ, norm_cpow_eq_rpow_re_of_pos hz, mul_assoc,
    ← Real.rpow_add hz, add_comm r]

private theorem measurable_zetaIntegrand_complex (χ : ℂˣ →ₜ* ℂˣ) (s : ℂ) :
    Measurable fun z : ℂˣ ↦ f z * (χ z : ℂ) * ((normSq (z : ℂ) : ℝ) : ℂ) ^ s :=
  ((f.continuous.comp Units.continuous_val).measurable.mul
    (Units.continuous_val.comp χ.continuous).measurable).mul
    ((Complex.continuous_ofReal.comp (continuous_normSq.comp
      Units.continuous_val)).measurable.pow_const s)

/-- **Absolute convergence at `ℂ`.** For a Schwartz function `f` and a quasi-character `χ` of
`ℂˣ` of exponent `r` for `|z|_ℂ = normSq z`, the zeta integrand `f(z) χ(z) |z|_ℂ ^ s` is
integrable against `2 dx dy / |z|_ℂ` for `re s + r > 0`. -/
theorem integrable_localZetaIntegrand_complex {χ : ℂˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    Integrable (fun z : ℂˣ ↦ f z * (χ z : ℂ) * ((normSq (z : ℂ) : ℝ) : ℂ) ^ s)
      complexUnitsMultHaar :=
  (integrable_complexUnitsMultHaar_iff.2 (integrable_complexMultHaar_norm_mul_rpow f hs)).mono'
    (measurable_zetaIntegrand_complex f χ s).aestronglyMeasurable
    (ae_of_all _ fun z ↦ (norm_zetaIntegrand_complex f hχ s z).le)

/-- **Holomorphy at `ℂ`.** For a Schwartz function `f` and a quasi-character `χ` of `ℂˣ` of
exponent `r` for `|z|_ℂ = normSq z`, `s ↦ z(s, χ; f)` is holomorphic on `re s + r > 0`. -/
theorem differentiableOn_localZetaIntegral_complex {χ : ℂˣ →ₜ* ℂˣ} {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) :
    DifferentiableOn ℂ (localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) χ f)
      {s | 0 < s.re + r} := by
  have h := differentiableOn_integral_mul_cpow complexUnitsMultHaar
    (F := fun z ↦ f z * (χ z : ℂ)) (a := fun z ↦ normSq (z : ℂ)) (α := -r)
    (fun z ↦ normSq_pos.2 z.ne_zero)
    ((f.continuous.comp Units.continuous_val).mul
      (Units.continuous_val.comp χ.continuous)).aestronglyMeasurable
    (continuous_normSq.comp Units.continuous_val).measurable fun σ hσ ↦ ?_
  · rw [show localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) χ f =
        fun s ↦ ∫ z : ℂˣ, f z * (χ z : ℂ) * ((normSq (z : ℂ) : ℝ) : ℂ) ^ s
          ∂complexUnitsMultHaar from funext fun s ↦ localZetaIntegral_def _ _ _ _ _]
    exact h.mono fun s (hs : 0 < s.re + r) ↦ show -r < s.re by linarith
  · refine (integrable_complexUnitsMultHaar_iff.2
      (integrable_complexMultHaar_norm_mul_rpow f (σ := σ + r) (by linarith))).congr
      (ae_of_all _ fun z ↦ ?_)
    have hz : 0 < normSq (z : ℂ) := normSq_pos.2 z.ne_zero
    simp only [norm_mul, hχ, mul_assoc, ← Real.rpow_add hz, add_comm r]

/-- **Continuity on the Schwartz space at `ℂ`.** For a quasi-character `χ` of `ℂˣ` of exponent
`r` for `|z|_ℂ` and `re s + r > 0`, the local zeta integral `f ↦ z(s, χ; f)` is a continuous
linear functional on `𝓢(ℂ, ℂ)`. -/
def complexLocalZetaCLM (χ : ℂˣ →ₜ* ℂˣ) {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    𝓢(ℂ, ℂ) →L[ℂ] ℂ :=
  mkCLMtoNormedSpace (fun f ↦ localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) χ f s)
    (fun f g ↦ localZetaIntegral_add complexUnitsMultHaar _ χ
        (integrable_localZetaIntegrand_complex f hχ hs)
        (integrable_localZetaIntegrand_complex g hχ hs))
    (fun c f ↦ localZetaIntegral_const_mul complexUnitsMultHaar _ χ c f s)
    (by
      obtain ⟨S, C, hC, hbound⟩ := exists_integral_norm_rpow_mul_norm_le (E := ℂ) (F := ℂ) volume ℂ
        (t := 2 * (s.re + r) - 2) (by simp; linarith)
      refine ⟨S, 2 * C, by positivity, fun f ↦ ?_⟩
      rw [localZetaIntegral_def]
      refine (norm_integral_le_integral_norm _).trans (le_of_eq_of_le ?_
        ((mul_le_mul_of_nonneg_left (hbound f) zero_le_two).trans_eq (mul_assoc _ _ _).symm))
      simp_rw [norm_zetaIntegrand_complex f hχ s]
      rw [integral_complexUnitsMultHaar (fun w ↦ ‖f w‖ * normSq w ^ (s.re + r)),
        integral_complexMultHaar_norm_mul_rpow])

@[simp]
theorem complexLocalZetaCLM_apply (χ : ℂˣ →ₜ* ℂˣ) {r : ℝ}
    (hχ : ∀ z : ℂˣ, ‖(χ z : ℂ)‖ = normSq (z : ℂ) ^ r) {s : ℂ} (hs : 0 < s.re + r) :
    complexLocalZetaCLM χ hχ hs f =
      localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) χ f s :=
  (rfl)

/-- **The complex Gaussian.** For the twice-Lebesgue additive measure,
`z(s, 1; e^(-2π |z|_ℂ)) = (2π) ^ (1 - s) Γ(s) = π Γ_ℂ(s)` on `re s > 0`. -/
theorem localZetaIntegral_complex_gaussian {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) 1
      (fun z ↦ (Real.exp (-(2 * π * normSq z)) : ℂ)) s = π * Gammaℂ s := by
  rw [localZetaIntegral_def]
  simp only [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, mul_one]
  rw [integral_complexUnitsMultHaar
    (fun w ↦ (Real.exp (-(2 * π * normSq w)) : ℂ) * ((normSq w : ℝ) : ℂ) ^ s)]
  have h := integral_complexMultHaar_comp_norm
    (fun t ↦ (Real.exp (-(2 * π * t ^ 2)) : ℂ) * (t : ℂ) ^ (2 * s))
  rw [← integral_congr_ae (ae_of_all _ fun w ↦ ?_)] at h
  · rw [h]
    simp_rw [mul_comm (Real.exp _ : ℂ)]
    rw [integral_multHaar_cpow_mul_exp_neg_mul_sq (by positivity) (by simpa using hs), Gammaℂ_def]
    rw [mul_div_cancel_left₀ _ two_ne_zero, ofReal_mul, ofReal_ofNat]
    simp only [real_smul, ofReal_mul, ofReal_ofNat]
    ring
  · rw [normSq_eq_norm_sq, ofReal_pow, ofReal_pow_cpow (norm_nonneg w)]
    push_cast
    ring_nf

/-- **The complex standard functions.** In Kudla's normal form `ω(z) = z ^ (-a) conj(z) ^ (-b)`
(`TauCeti.complexUnitsCharacter (-(a + b)) (b - a)`), the standard function
`π⁻¹ z ^ a conj(z) ^ b e^(-2π |z|_ℂ)` has zeta integral `L(s, ω) = Γ_ℂ(s)` on `re s > 0`. -/
theorem localZetaIntegral_complexUnitsCharacter_standard (a b : ℕ) {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z)
      (complexUnitsCharacter (-(a + b : ℂ)) (b - a))
      (fun z ↦ (π : ℂ)⁻¹ * (z ^ a * (starRingEnd ℂ z) ^ b) *
        (Real.exp (-(2 * π * normSq z)) : ℂ)) s = Gammaℂ s := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [← mul_div_cancel_left₀ (Gammaℂ s) hπ, ← localZetaIntegral_complex_gaussian hs,
    div_eq_inv_mul, ← localZetaIntegral_const_mul, localZetaIntegral_def, localZetaIntegral_def]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  have h := coe_complexUnitsCharacter_two_mul_sub_apply a b 0 z
  rw [mul_zero, zero_sub, cpow_zero, mul_one] at h
  simp only [h, ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, mul_one]
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hz' : (starRingEnd ℂ) (z : ℂ) ≠ 0 := (map_ne_zero _).2 hz
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]
  field_simp

/-- **Vanishing by angular weight.** If the test function has angular weight `m`, that is
`f(e^(iθ) z) = e^(i m θ) f(z)`, and the character `TauCeti.complexUnitsCharacter u k` has angular
weight `k` with `m + k ≠ 0`, then `z(s, χ; f) = 0` for every `s`. -/
theorem localZetaIntegral_complexUnitsCharacter_eq_zero_of_rotation {f : ℂ → ℂ} {m k : ℤ}
    (hmk : m + k ≠ 0) (hf : ∀ (θ : ℝ) (z : ℂ), f (exp (θ * I) * z) = exp (θ * I) ^ m * f z)
    (u s : ℂ) :
    localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) (complexUnitsCharacter u k) f s =
      0 := by
  set θ : ℝ := π / (m + k)
  have hmkC : (m : ℂ) + k ≠ 0 := by exact_mod_cast hmk
  set ζ : ℂˣ := Units.mk0 (exp (θ * I)) (exp_ne_zero _)
  have hζ0 : (ζ : ℂ) ≠ 0 := ζ.ne_zero
  have hζ : ‖(ζ : ℂ)‖ = 1 := norm_exp_ofReal_mul_I θ
  have hθ : ((m + k : ℤ) : ℂ) * (θ : ℂ) = π := by
    simp only [θ]
    push_cast
    field_simp
  have hpow : (ζ : ℂ) ^ (m + k) = -1 := by
    rw [Units.val_mk0, ← exp_intCast_mul, ← mul_assoc, hθ, exp_pi_mul_I]
  have hfζ : (fun z ↦ f (ζ * z)) = fun z ↦ (ζ : ℂ) ^ m * f z := funext fun z ↦ hf θ z
  have hnormSq : normSq (ζ : ℂ) = 1 := by rw [normSq_eq_norm_sq, hζ, one_pow]
  have h := localZetaIntegral_comp_mul_left complexUnitsMultHaar (fun z ↦ normSq z)
    (complexUnitsCharacter u k) (fun z ↦ normSq_pos.2 z.ne_zero)
    (fun z w ↦ by simp only [Units.val_mul, map_mul]) f ζ s
  set Z := localZetaIntegral complexUnitsMultHaar (fun z ↦ normSq z) (complexUnitsCharacter u k) f s
  simp only [coe_complexUnitsCharacter_apply, hζ, hnormSq, ofReal_one, one_cpow, div_one,
    one_mul, mul_one] at h
  rw [hfζ, localZetaIntegral_const_mul] at h
  -- `ζ ^ m Z = ζ ^ (-k) Z` with `ζ ^ (m + k) = -1`, so `Z = 0`.
  have h3 : (ζ : ℂ) ^ (m + k) * Z = Z := by
    rw [zpow_add₀ hζ0, mul_comm ((ζ : ℂ) ^ m), mul_assoc, h, ← mul_assoc,
      mul_inv_cancel₀ (zpow_ne_zero _ hζ0), one_mul]
  rw [hpow] at h3
  linear_combination (-1 / 2 : ℂ) * h3

end Complex

end TateZeta

end TauCeti
