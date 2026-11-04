/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Kronecker's theorem for linear flows on tori

For a finite index type `ι`, a line `t ↦ θ + t ν` in the torus `(ℝ / pℤ)^ι` is an orbit of a
linear flow. Its velocity `ν` is *nonresonant* if no nonzero integer vector `k` satisfies
`∑ i, k i * ν i = 0`. Kronecker's theorem (`TauCeti.AddCircle.denseRange_coe_add_mul_iff`)
states that the line is dense exactly when `ν` is nonresonant. For a resonance `k`, the character
`x ↦ exp (2πi ⟪k, x⟫ / p)` is constant along the line but not on the torus, so the line is not
dense.

Density of a nonresonant line follows from Weyl's equidistribution theorem for linear flows
(`TauCeti.UnitAddTorus.tendsto_inv_smul_intervalIntegral`): on the unit torus, the time averages
`T⁻¹ ∫₀ᵀ f (θ + t ν) dt` of a continuous function `f` tend to its integral `∫ f`. For a monomial
`mFourier n` this is a direct computation: along the line it is a constant multiple of
`t ↦ exp (2πi ⟪n, ν⟫ t)` (`TauCeti.UnitAddTorus.mFourier_coe_add_mul`), and its integral
vanishes for `n ≠ 0` (`TauCeti.UnitAddTorus.integral_mFourier`). It extends to every continuous
function because the trigonometric polynomials are uniformly dense. A continuous bump function
supported in an open set missed by the line has positive integral but vanishing time averages, so
no such open set exists.

These statements decide when an orbit of a completely integrable system, which is a line on an
invariant torus in action–angle coordinates, fills that torus densely.

## Main results

* `TauCeti.UnitAddTorus.integral_mFourier`: `∫ mFourier n` is `1` for `n = 0` and `0` otherwise.
* `TauCeti.UnitAddTorus.tendsto_inv_smul_intervalIntegral`: Weyl's theorem, time averages along a
  nonresonant line tend to the space average.
* `TauCeti.AddCircle.denseRange_coe_add_mul_iff`: Kronecker's theorem, a line in `(ℝ / pℤ)^ι` is
  dense exactly when its velocity is nonresonant.

## References

* H. Weyl, *Über die Gleichverteilung von Zahlen mod. Eins*, Mathematische Annalen 77 (1916),
  313–352.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Graduate Texts in
  Mathematics 60, Springer, 1989, Section 51 (time and space averages on the torus).
-/

public section

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped Real

noncomputable section

/-- The measure on `ℝ / ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

namespace TauCeti

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The integral of the monomial `mFourier n` over the unit torus is `1` for `n = 0` and `0`
otherwise. -/
@[simp]
theorem integral_mFourier (n : d → ℤ) : ∫ x, mFourier n x = if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp orthonormal_mFourier) 0 n
  simp only [ContinuousMap.inner_toLp, mFourier_zero, ContinuousMap.one_apply, map_one,
    mul_one, eq_comm (a := (0 : d → ℤ))] at h
  rw [volume_eq_pi_haarAddCircle, ← h]
  -- Mathlib states `orthonormal_mFourier` for its file-local normalization
  -- `volume = haarAddCircle` on `UnitAddCircle`, whose product measure is the measure above.
  rfl

/-- Along the line `t ↦ θ + t ν` of the unit torus, the monomial `mFourier n` is the product of its
value at `θ` with the exponential `exp (2πi ⟪n, ν⟫ t)`. -/
theorem mFourier_coe_add_mul (n : d → ℤ) (θ ν : d → ℝ) (t : ℝ) :
    mFourier n (fun i ↦ ((θ i + ν i * t : ℝ) : UnitAddCircle)) =
      Complex.exp (2 * π * Complex.I * ∑ i, (n i : ℂ) * θ i) *
        Complex.exp (2 * π * Complex.I * (∑ i, (n i : ℝ) * ν i : ℝ) * t) := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [← Complex.exp_sum, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- The time average of `mFourier n` along a line whose velocity `ν` satisfies `⟪n, ν⟫ ≠ 0` tends
to `0`. -/
private theorem tendsto_average_mFourier_of_ne_zero (n : d → ℤ) (θ ν : d → ℝ)
    (hn : ∑ i, (n i : ℝ) * ν i ≠ 0) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, mFourier n (fun i ↦ ((θ i + ν i * t : ℝ) :
      UnitAddCircle))) atTop (𝓝 0) := by
  simp_rw [mFourier_coe_add_mul, intervalIntegral.integral_const_mul]
  generalize ∑ i, (n i : ℝ) * ν i = c at hn ⊢
  generalize Complex.exp (2 * π * Complex.I * ∑ i, (n i : ℂ) * θ i) = A
  have ha : 2 * π * Complex.I * c ≠ 0 := by simp [Real.pi_ne_zero, hn]
  have hnorm (x : ℝ) : ‖Complex.exp (2 * π * Complex.I * c * x)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  refine squeeze_zero_norm' ?_ (zero_mul (‖A‖ * (2 / ‖2 * π * Complex.I * c‖)) ▸
    tendsto_inv_atTop_zero.mul_const _)
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [integral_exp_mul_complex ha, norm_smul, norm_mul, norm_div,
    Real.norm_of_nonneg (inv_nonneg.2 hT.le)]
  gcongr
  calc ‖Complex.exp (2 * π * Complex.I * c * T) - Complex.exp (2 * π * Complex.I * c * (0 : ℝ))‖
      ≤ ‖Complex.exp (2 * π * Complex.I * c * T)‖ +
        ‖Complex.exp (2 * π * Complex.I * c * (0 : ℝ))‖ := norm_sub_le _ _
    _ = 2 := by rw [hnorm, hnorm]; norm_num

/-- Weyl's theorem for the trigonometric polynomials, the span of the monomials `mFourier n`. -/
private theorem tendsto_inv_smul_intervalIntegral_of_mem_span {ν : d → ℝ}
    (hν : ∀ k : d → ℤ, ∑ i, (k i : ℝ) * ν i = 0 → k = 0) (θ : d → ℝ) {g : C(UnitAddTorus d, ℂ)}
    (hg : g ∈ Submodule.span ℂ (range (mFourier (d := d)))) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, g (fun i ↦ ((θ i + ν i * t : ℝ) : UnitAddCircle)))
      atTop (𝓝 (∫ x, g x)) := by
  have hint (g : C(UnitAddTorus d, ℂ)) (T : ℝ) : IntervalIntegrable
      (fun t ↦ g (fun i ↦ ((θ i + ν i * t : ℝ) : UnitAddCircle))) volume 0 T :=
    (g.continuous.comp (by fun_prop)).intervalIntegrable _ _
  have hgi (g : C(UnitAddTorus d, ℂ)) : Integrable g :=
    g.continuous.integrable_of_hasCompactSupport (.of_compactSpace _)
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨n, rfl⟩ := hg
    rw [integral_mFourier]
    split_ifs with hn
    · subst hn
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with T hT
      simp [mFourier_zero, hT.ne']
    · exact tendsto_average_mFourier_of_ne_zero n θ ν fun h ↦ hn (hν n h)
  | zero => simp
  | add g h _ _ hg hh =>
    simp only [ContinuousMap.add_apply, intervalIntegral.integral_add (hint g _) (hint h _),
      integral_add (hgi g) (hgi h), smul_add]
    exact hg.add hh
  | smul c g _ hg =>
    simp only [ContinuousMap.smul_apply, intervalIntegral.integral_smul, integral_smul]
    exact (hg.const_smul c).congr fun T ↦ smul_comm c T⁻¹ _

/-- **Weyl's equidistribution theorem for linear flows.** If the velocity `ν` is nonresonant, that
is `⟪k, ν⟫ ≠ 0` for every nonzero `k ∈ ℤ^d`, then along every line `t ↦ θ + t ν` of the unit
torus the time averages `T⁻¹ ∫₀ᵀ f (θ + t ν) dt` of a continuous function `f` tend to its space
average `∫ f`. -/
theorem tendsto_inv_smul_intervalIntegral {ν : d → ℝ}
    (hν : ∀ k : d → ℤ, ∑ i, (k i : ℝ) * ν i = 0 → k = 0) (θ : d → ℝ) (f : C(UnitAddTorus d, ℂ)) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, f (fun i ↦ ((θ i + ν i * t : ℝ) : UnitAddCircle)))
      atTop (𝓝 (∫ x, f x)) := by
  set γ : ℝ → UnitAddTorus d := fun t i ↦ ((θ i + ν i * t : ℝ) : UnitAddCircle)
  have hint (g : C(UnitAddTorus d, ℂ)) (T : ℝ) :
      IntervalIntegrable (fun t ↦ g (γ t)) volume 0 T :=
    (g.continuous.comp (by fun_prop)).intervalIntegrable _ _
  have hgi (g : C(UnitAddTorus d, ℂ)) : Integrable g :=
    g.continuous.integrable_of_hasCompactSupport (.of_compactSpace _)
  -- Time and space averages are bounded by the sup norm.
  have havg (g : C(UnitAddTorus d, ℂ)) {T : ℝ} (hT : 0 < T) :
      ‖T⁻¹ • ∫ t in 0..T, g (γ t)‖ ≤ ‖g‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hT.le)]
    refine (mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_of_norm_le_const
      fun t _ ↦ g.norm_coe_le_norm (γ t)) (inv_nonneg.2 hT.le)).trans_eq ?_
    rw [sub_zero, abs_of_pos hT]
    field_simp
  have hmean (g : C(UnitAddTorus d, ℂ)) : ‖∫ x, g x‖ ≤ ‖g‖ := by
    simpa using norm_integral_le_of_norm_le_const (μ := volume)
      (Eventually.of_forall g.norm_coe_le_norm)
  -- Approximate `f` by a trigonometric polynomial `g` to within `ε / 3`.
  have hf : f ∈ closure (Submodule.span ℂ (range (mFourier (d := d))) :
      Set C(UnitAddTorus d, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_mFourier_closure_eq_top]
    trivial
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf (ε / 3) (by positivity)
  obtain ⟨T₀, hT₀⟩ := Metric.tendsto_atTop.mp
    (tendsto_inv_smul_intervalIntegral_of_mem_span hν θ hg) (ε / 3) (by positivity)
  refine ⟨max T₀ 1, fun T hT ↦ ?_⟩
  have hTpos : 0 < T := one_pos.trans_le (le_of_max_le_right hT)
  have h1 := havg (f - g) hTpos
  have h2 := hmean (f - g)
  have h3 := hT₀ T (le_of_max_le_left hT)
  rw [dist_eq_norm] at hfg h3 ⊢
  have e1 : (T⁻¹ • ∫ t in 0..T, (f - g) (γ t)) =
      (T⁻¹ • ∫ t in 0..T, f (γ t)) - T⁻¹ • ∫ t in 0..T, g (γ t) := by
    simp only [ContinuousMap.sub_apply, intervalIntegral.integral_sub (hint f T) (hint g T),
      smul_sub]
  have e2 : ∫ x, (f - g) x = (∫ x, f x) - ∫ x, g x := by
    simp only [ContinuousMap.sub_apply, integral_sub (hgi f) (hgi g)]
  calc ‖(T⁻¹ • ∫ t in 0..T, f (γ t)) - ∫ x, f x‖
      = ‖(T⁻¹ • ∫ t in 0..T, (f - g) (γ t)) + ((T⁻¹ • ∫ t in 0..T, g (γ t)) - ∫ x, g x) -
          ∫ x, (f - g) x‖ := by
        rw [e1, e2]
        congr 1
        abel
    _ ≤ ‖T⁻¹ • ∫ t in 0..T, (f - g) (γ t)‖ + ‖(T⁻¹ • ∫ t in 0..T, g (γ t)) - ∫ x, g x‖ +
          ‖∫ x, (f - g) x‖ := norm_sub_le_of_le (norm_add_le _ _) le_rfl
    _ < ε := by linarith

/-- Kronecker's theorem on the unit torus; `AddCircle.denseRange_coe_add_mul_iff` states it for
every period. -/
private theorem denseRange_coe_add_mul_iff (θ ν : d → ℝ) :
    DenseRange (fun t : ℝ ↦ fun i ↦ ((θ i + ν i * t : ℝ) : UnitAddCircle)) ↔
      ∀ k : d → ℤ, ∑ i, (k i : ℝ) * ν i = 0 → k = 0 := by
  set γ : ℝ → UnitAddTorus d := fun t i ↦ ((θ i + ν i * t : ℝ) : UnitAddCircle)
  constructor
  · -- A resonance `⟪k, ν⟫ = 0` makes the nonconstant character `mFourier k` constant along `γ`.
    intro hd k hk
    by_contra hk0
    set C := Complex.exp (2 * π * Complex.I * ∑ i, (k i : ℂ) * θ i)
    have hC : (mFourier k : UnitAddTorus d → ℂ) = fun _ ↦ C := by
      refine hd.equalizer (mFourier k).continuous continuous_const (funext fun t ↦ ?_)
      rw [Function.comp_apply, mFourier_coe_add_mul, hk]
      simp [C]
    have h := integral_mFourier k
    rw [hC] at h
    simp [hk0, C, Complex.exp_ne_zero] at h
  · -- Otherwise a bump function supported off the closure of `γ` contradicts Weyl's theorem.
    intro hν
    by_contra hd
    rw [DenseRange, dense_iff_closure_eq, ← ne_eq, ne_univ_iff_exists_notMem] at hd
    obtain ⟨x₀, hx₀⟩ := hd
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl x₀ hx₀
    let b : C(UnitAddTorus d, ℝ) := ⟨fun x ↦ max 0 (r - dist x x₀), by fun_prop⟩
    let f : C(UnitAddTorus d, ℂ) := ⟨fun x ↦ (b x : ℂ), by fun_prop⟩
    have hzero (t : ℝ) : f (γ t) = 0 := by
      have ht : γ t ∉ Metric.ball x₀ r := fun h ↦ hball h (subset_closure (mem_range_self t))
      rw [Metric.mem_ball, not_lt] at ht
      simp [f, b, ht]
    have hlim : Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, f (γ t)) atTop (𝓝 (∫ x, f x)) :=
      tendsto_inv_smul_intervalIntegral hν θ f
    simp only [hzero, intervalIntegral.integral_zero, smul_zero] at hlim
    have hpos : 0 < ∫ x, b x :=
      b.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
        (.of_compactSpace _) (fun x ↦ le_max_left _ _) (x := x₀) (by simpa [b] using hr)
    have h0 : ∫ x, f x = ((∫ x, b x : ℝ) : ℂ) := integral_ofReal
    rw [← tendsto_nhds_unique tendsto_const_nhds hlim] at h0
    exact hpos.ne' (by exact_mod_cast h0.symm)

end UnitAddTorus

namespace AddCircle

/-- **Kronecker's theorem for linear flows on tori.** A line `t ↦ θ + t ν` in the torus
`(ℝ / pℤ)^ι` is dense exactly when its velocity `ν` is nonresonant: `∑ i, k i * ν i ≠ 0` for every
nonzero integer vector `k`. -/
theorem denseRange_coe_add_mul_iff {ι : Type*} [Fintype ι] {p : ℝ} (hp : p ≠ 0) (θ ν : ι → ℝ) :
    DenseRange (fun t : ℝ ↦ fun i ↦ ((θ i + ν i * t : ℝ) : AddCircle p)) ↔
      ∀ k : ι → ℤ, ∑ i, (k i : ℝ) * ν i = 0 → k = 0 := by
  let H : UnitAddTorus ι ≃ₜ (ι → AddCircle p) :=
    Homeomorph.piCongrRight fun _ ↦ AddCircle.homeomorphAddCircle 1 p one_ne_zero hp
  have hH : (fun t : ℝ ↦ fun i ↦ ((θ i + ν i * t : ℝ) : AddCircle p)) =
      H ∘ fun t i ↦ ((θ i / p + ν i / p * t : ℝ) : UnitAddCircle) := by
    funext t i
    simp only [Function.comp_apply, H, Homeomorph.piCongrRight_apply,
      AddCircle.homeomorphAddCircle_apply_mk]
    congr 1
    field_simp
  rw [DenseRange, hH, range_comp, H.isDenseEmbedding.dense_image, ← DenseRange,
    UnitAddTorus.denseRange_coe_add_mul_iff]
  refine forall_congr' fun k ↦ ?_
  have hsum : ∑ i, (k i : ℝ) * (ν i / p) = (∑ i, (k i : ℝ) * ν i) / p := by
    rw [Finset.sum_div]
    simp only [mul_div_assoc]
  rw [hsum, div_eq_zero_iff, or_iff_left hp]

end AddCircle

end TauCeti
