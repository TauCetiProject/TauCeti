/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Caccioppoli.Truncation
public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.SpecificLimits.FastGeometric
public import TauCeti.Analysis.Sobolev.FiniteMeasure
import TauCeti.MeasureTheory.Function.LocalBoundsOnBalls
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Local boundedness of weak subsolutions (De Giorgi)

Let `a` be measurable and uniformly elliptic on `Ω ⊆ ℝⁿ` with constants `0 < λ ≤ Λ`, and let
`u ∈ H¹(Ω)` be a weak subsolution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` in `Ω`,

meaning `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. This file proves De Giorgi's local
boundedness theorem: on every ball `B(x₀, R) ⊆ Ω` and above every level `k`,

`u ≤ k + D R^{-n/2} ‖(u - k)⁺‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`,

with `D` depending on `λ`, `Λ`, the dimension `n ≥ 1` and the normalization of the additive
Haar measure used for the `L²` norm. No regularity of the coefficients beyond measurability
is used. This is the first half of the De Giorgi–Nash–Moser theorem; Hölder continuity is the
second.

The `_of_local_subsolution` and `_of_local_solution` forms allow an ambient Sobolev function
while requiring the coefficient hypotheses and the weak equation only on the selected ball,
with no assumptions on the coefficients or equation outside that ball.

The energy recursion `setIntegral_sq_mul_max_sub_sq_le_of_caccioppoli` is useful when a Sobolev
inequality `‖v‖_q ≤ S ‖∇v‖₂` is available on `W^{1,2}_0(B(x₀, R))` for some `q > 2`. It controls
higher truncation levels on smaller balls and yields the local bound below. The bound can be used
as the boundedness input for interior oscillation and Hölder regularity estimates.

## De Giorgi's classes

The equation enters De Giorgi's iteration only through the Caccioppoli inequality for the
truncations `w = (u - l)⁺` above the level `k`,

`∫ ψ² ‖∇w‖² ≤ A ∫ ‖∇ψ‖² w² + B ∫ ψ² w²` for every smooth cutoff `ψ`,

so the iteration is carried out for every `u` with this property (`TauCeti.PDE.CaccioppoliAbove`),
with constants `A, B ≥ 0`. Weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` have it at every level with
`A = (2Λ/λ)²` and `B = 0`. The zeroth-order term `B ∫ ψ² w²` is what a drift contributes, and it
costs a factor `(1 + A + B R²)ⁿ` in the bound on `B(x₀, R/2)`.

A mass coefficient `c` without a sign contributes, at the level `l` above `k = 0`, a further
linear term `E (l - k) ∫ ψ² w`, since `|c u| w ≤ |c| (w² + l w)` where `u > l ≥ 0`
(`TauCeti.PDE.CaccioppoliAboveLinear`). Between the levels `k + K - K/2ʲ` and
`k + K - K/2^{j+1}` of the iteration it is at most `2^{j+1} E` times the truncation at the lower
level, so it costs a factor `(1 + A + (B + E) R²)ⁿ`, like a zeroth-order term.

The Sobolev inequality enters as a hypothesis in the general form, so the theorem applies to any
exponent `q > 2` for which it is available, with a constant `D S^{1/α}`, `α = 1 - 2/q`. For the
scale-invariant bound it is applied on the ball `B(x₀, R)` itself, where the Sobolev inequality
for sets of finite measure,
`TauCeti.W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball`, holds for some `q > 2`
in every dimension, with `S` a multiple of `R ^ (1 - n (1/2 - 1/q))`. Then `S^{1/α} R^{-1/α}` is a
multiple of `R^{-n/2}`. In dimension `n ≥ 3` the Gagliardo–Nirenberg–Sobolev inequality would
serve as well, but in dimensions `1` and `2` there is no critical exponent and the dependence of
`S` on the ball is essential.

## Lower exponents

The `L²` norm on the right can be replaced by any `Lᵖ` norm with `0 < p ≤ 2`, at the cost of
the scaling exponent `-n/2` becoming `-n/p`:

`u ≤ k + D R^{-n/p} ‖(u - k)⁺‖_{Lᵖ(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`.

Writing `F(r)` for the essential supremum of `(u - k)⁺` on `B(x₀, r)`, the `L²` bound on
concentric balls `r < ρ` and the interpolation `‖w‖²_{L²} ≤ F(ρ)^{2-p} ‖w‖ᵖ_{Lᵖ}` give
`F(r) ≤ F(ρ)/2 + C (ρ - r)^{-n/p} ‖(u - k)⁺‖_{Lᵖ}`, and the absorption lemma
`TauCeti.exists_le_mul_mul_rpow_add_of_le_mul_add` removes the term `F(ρ)/2`
(`TauCeti.exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball`). Small `p` is
what Moser's proof of the Harnack inequality needs, where the supremum bound for subsolutions is
matched with an infimum bound for supersolutions through a small positive power.

## Main declarations

* `TauCeti.PDE.setIntegral_sq_mul_max_sub_sq_le_of_caccioppoli`: De Giorgi's energy recursion
  between two truncation levels, for a function satisfying the Caccioppoli inequality.
* `TauCeti.PDE.CaccioppoliAbove`: De Giorgi's class above a level, the truncations satisfying the
  Caccioppoli inequality.
* `TauCeti.PDE.CaccioppoliAboveLinear`: De Giorgi's class with the linear term of a mass
  coefficient without a sign.
* `exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoliAboveLinear`:
  the scale-invariant local bound for functions in De Giorgi's classes with a linear term, in
  every dimension `n ≥ 1`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoli`: the
  scale-invariant local bound for functions in De Giorgi's classes, in every dimension `n ≥ 1`.
* `TauCeti.PDE.ae_abs_value_le_mul_sqrt_setIntegral_of_ae_value_le`: one-sided bounds for `u`
  and `-u` give a two-sided bound.
* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_max_sub_sq_le`: the energy recursion for
  weak subsolutions.
* `TauCeti.PDE.UniformlyEllipticOn.caccioppoliAbove`: weak subsolutions belong to De Giorgi's
  class above every level.
* `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral_of_forall_eLpNorm_le`:
  local boundedness of weak subsolutions on a ball, under a Sobolev inequality with exponent
  `q > 2` and constant `S` on that ball, with a constant homogeneous in `S`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral`: the scale-invariant bound
  `u ≤ k + D R^{-n/2} ‖(u - k)⁺‖_{L²(B(x₀, R))}` in every dimension `n ≥ 1`.
* `TauCeti.PDE.exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral`: the two-sided bound
  `|u| ≤ D R^{-n/2} ‖u‖_{L²(B(x₀, R))}` for weak solutions.
* `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_eLpNorm_le`: local
  boundedness of weak subsolutions with the `Lᵖ` norm of `(u - k)⁺`, `0 < p ≤ 2`, on the right,
  under a Sobolev inequality on every ball inside `Ω`.
* `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow`: the bound
  `u ≤ k + D R^{-n/p} ‖(u - k)⁺‖_{Lᵖ(B(x₀, R))}` in every dimension `n ≥ 1`.

## References

* E. De Giorgi, *Sulla differenziabilità e l'analiticità delle estremali degli integrali
  multipli regolari*, Mem. Accad. Sci. Torino (1957).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 4.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 8.
-/

public section

noncomputable section

open Filter MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff ENNReal Gradient InnerProductSpace NNReal Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)}

/-! ### De Giorgi's classes and iteration in `L²` -/

section L2

variable [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}

private theorem value_restrictL_ae_ball_half_and_setIntegral_comp_eq
    (u : W1p mu Omega 2) {x₀ : EuclideanSpace ℝ ι} {R : ℝ}
    (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) (f : ℝ → ℝ) :
    let U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
    (W1p.value (W1p.restrictL (U := U) hball u) =ᵐ[mu.restrict (Metric.ball x₀ (R / 2))]
      W1p.value u) ∧
      ∫ x in Metric.ball x₀ R, f (W1p.value (W1p.restrictL (U := U) hball u) x) ∂mu =
        ∫ x in Metric.ball x₀ R, f (W1p.value u x) ∂mu := by
  let U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
  have hw : W1p.value (W1p.restrictL (U := U) hball u) =ᵐ[mu.restrict (Metric.ball x₀ R)]
      W1p.value u :=
    W1p.value_restrictL_ae (U := U) hball u
  have hhalf : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ R := fun x hx =>
    Metric.mem_ball.2 (by linarith [Metric.mem_ball.1 hx, @dist_nonneg _ _ x x₀])
  exact ⟨ae_restrict_of_ae_restrict_of_subset hhalf hw,
    integral_congr_ae (hw.mono fun _ hx => congrArg f hx)⟩

/-- The truncation `(u - l)⁺`, as an element of `W^{1,2}(Ω)`, has pointwise square at most
`((u - k)⁺)²` almost everywhere on `Ω` when `k ≤ l`. -/
private theorem value_posPartAboveOfMemLp_sq_le_ae {u : W1p mu Omega 2} {k l : ℝ} (hkl : k ≤ l)
    (hwl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega)) :
    ∀ᵐ x ∂mu.restrict Omega,
      W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hwl) x ^ 2 ≤
        max (W1p.value u x - k) 0 ^ 2 := by
  filter_upwards [W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hwl] with x hx
  rw [hx]
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max (sub_le_sub_left hkl _) le_rfl) 2

/-- The cutoff step of De Giorgi's energy recursion. If `w = (u - l)⁺` satisfies the Caccioppoli
inequality with `I = ∫_{Ω ∩ supp ψ} ((u - k)⁺)²`, then `z = ψ w ∈ W^{1,2}_0(Ω)` has
`‖∇z‖² ≤ 2 ((1 + A) G² + B) I`, `z² = ψ² ((u - l)⁺)²` almost everywhere, and `z = 0` off
`supp ψ ∩ {u > l}`. -/
private theorem exists_mem_w1p0Submodule_norm_gradient_sq_le_of_caccioppoli
    {u : W1p mu Omega 2} {k l : ℝ} (hkl : k < l)
    (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {G : ℝ}
    (hG : ∀ x, ‖∇ ψ x‖ ≤ G) {A B : ℝ} (hA : 0 ≤ A)
    (hcacc :
      let w := W1p.posPartAboveOfMemLp (by norm_num) l u
        (W1p.memLp_posPartAbove_of_le u hkl.le hwLp)
      ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
        A * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu +
          B * ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
            max (W1p.value u x - k) 0 ^ 2 ∂mu) :
    ∃ z ∈ w1p0Submodule mu Omega 2,
      ‖W1p.gradient z‖ ^ 2 ≤ 2 * ((1 + A) * G ^ 2 + B) *
        (∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
          max (W1p.value u x - k) 0 ^ 2 ∂mu) ∧
      (∀ᵐ x ∂mu.restrict Omega,
        W1p.value z x ^ 2 = ψ x ^ 2 * max (W1p.value u x - l) 0 ^ 2) ∧
      ∀ᵐ x ∂mu.restrict Omega,
        x ∉ tsupport ψ ∩ {x | l < W1p.value u x} → W1p.value z x = 0 := by
  set T := tsupport ψ
  set I := ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ T, max (W1p.value u x - k) 0 ^ 2 ∂mu
  -- The truncation at the higher level is dominated by the one at the lower level.
  have hwl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega) :=
    W1p.memLp_posPartAbove_of_le u hkl.le hwLp
  set w := W1p.posPartAboveOfMemLp (by norm_num) l u hwl
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  set z := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  have hzw : ∀ᵐ x ∂mu.restrict Omega, W1p.value z x = ψ x * max (W1p.value u x - l) 0 := by
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hwl] with x hzx hwx
    rw [hzx, hwx, smul_eq_mul]
  set J := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
  -- The truncation in `hcacc` carries its own proof of `2 ≠ ∞`; by proof irrelevance it is `w`.
  replace hcacc : ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤ A * J + B * I := hcacc
  -- `∇ψ` vanishes off the support of `ψ`, where `(u - l)⁺ ≤ (u - k)⁺`.
  have hJ : J ≤ G ^ 2 * I := by
    have hbound := W1p.setIntegral_norm_gradient_sq_mul_value_sq_le w hψ hG (S := T)
      (by simp [T]) hwLp.integrable_sq (value_posPartAboveOfMemLp_sq_le_ae hkl.le hwl)
    simpa only [J, I] using hbound
  refine ⟨z, W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by norm_num) hψ hM hψM'
    hgradM' hcpt hts w, ?_, hzw.mono fun x hx => by rw [hx]; ring, ?_⟩
  -- The gradient `ψ ∇w + w ∇ψ` of `z = ψ w`, bounded through the Caccioppoli inequality.
  · have hleib := W1p.norm_gradient_contDiffSMul_sq_le hψ hM hψM' hgradM' w
    have hAJ := mul_le_mul_of_nonneg_left hJ (by linarith : (0 : ℝ) ≤ 1 + A)
    nlinarith
  -- `z` vanishes off `supp ψ ∩ {u > l}`.
  · filter_upwards [hzw] with x hzx hxA
    rw [hzx]
    by_cases hxT : x ∈ T
    · have hxl : W1p.value u x ≤ l := le_of_not_gt fun hlt => hxA ⟨hxT, hlt⟩
      rw [max_eq_right (by linarith), mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hxT, zero_mul]


/-- **De Giorgi's energy recursion.** Suppose that `W^{1,2}_0(Ω)` satisfies a Sobolev inequality
`‖v‖_q ≤ S ‖∇v‖₂` for some exponent `q ≥ 2`. Let `u ∈ H¹(Ω)`, take levels `k < l` with
`(u - k)⁺ ∈ L²(Ω)`, and a smooth `ψ` compactly supported in `Ω` with `‖∇ψ‖ ≤ G`. Write
`w = (u - l)⁺` and `I = ∫_{Ω ∩ supp ψ} ((u - k)⁺)²`, and suppose that `w` satisfies the
Caccioppoli inequality

`∫_Ω ψ² ‖∇w‖² ≤ A ∫_Ω ‖∇ψ‖² w² + B I`

with `A ≥ 0`. Then

`∫_Ω ψ² w² ≤ 2 ((1 + A) G² + B) S² · I · (I / (l - k)²)^{1 - 2/q}`.

The truncation at the higher level is controlled by a power `1 + (1 - 2/q) > 1` of the
truncation at the lower level: this superlinear gain is what drives De Giorgi's iteration. For
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` the Caccioppoli inequality holds with `A = (2Λ/λ)²` and `B = 0`
(`TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_max_sub_sq_le`). For equations with a
drift it carries a zeroth-order term `B ∫_Ω ψ² w²`, which is at most `B I` when `|ψ| ≤ 1`. -/
theorem setIntegral_sq_mul_max_sub_sq_le_of_caccioppoli {q : ℝ≥0∞} (hq : 2 ≤ q) {S : ℝ≥0}
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u : W1p mu Omega 2} {k l : ℝ} (hkl : k < l)
    (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {G : ℝ}
    (hG : ∀ x, ‖∇ ψ x‖ ≤ G) {A B : ℝ} (hA : 0 ≤ A)
    (hcacc :
      let w := W1p.posPartAboveOfMemLp (by norm_num) l u
        (W1p.memLp_posPartAbove_of_le u hkl.le hwLp)
      ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
        A * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu +
          B * ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
            max (W1p.value u x - k) 0 ^ 2 ∂mu) :
    ∫ x in Omega, ψ x ^ 2 * max (W1p.value u x - l) 0 ^ 2 ∂mu ≤
      2 * ((1 + A) * G ^ 2 + B) * S ^ 2 *
        (∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
          max (W1p.value u x - k) 0 ^ 2 ∂mu) *
        ((∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
          max (W1p.value u x - k) 0 ^ 2 ∂mu) / (l - k) ^ 2) ^ (1 - 2 / q.toReal) := by
  set T := tsupport ψ
  set I := ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ T, max (W1p.value u x - k) 0 ^ 2 ∂mu
  have hTfin : mu T ≠ (∞ : ℝ≥0∞) := hcpt.measure_lt_top.ne
  obtain ⟨z, hz, hgradz, hz2, hvA⟩ :=
    exists_mem_w1p0Submodule_norm_gradient_sq_le_of_caccioppoli hkl hwLp hψ hcpt hts hG hA hcacc
  -- `z` vanishes off `A' = supp ψ ∩ {u > l}`, whose measure Chebyshev's inequality controls.
  set A' := T ∩ {x | l < W1p.value u x}
  have hAfin : mu ((Omega : Set (EuclideanSpace ℝ ι)) ∩ A') ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hTfin (measure_mono (inter_subset_right.trans inter_subset_left))
  have hsob := W1p.integral_value_sq_le_of_eLpNorm_le hq (hS z hz) hAfin hvA
  -- Chebyshev: on `{u > l}`, the lower truncation `(u - k)⁺` is at least `l - k`.
  have hcheb : mu.real ((Omega : Set (EuclideanSpace ℝ ι)) ∩ A') ≤ I / (l - k) ^ 2 := by
    rw [← inter_assoc]
    exact MeasureTheory.measureReal_inter_lt_le_setIntegral_max_sub_sq_div hkl
      (IntegrableOn.mono_set hwLp.integrable_sq inter_subset_left)
  rw [integral_congr_ae (hz2.mono fun x hx => hx.symm)]
  refine hsob.trans ?_
  have hγ := one_sub_two_div_toReal_nonneg hq
  calc (S : ℝ) ^ 2 * ‖W1p.gradient z‖ ^ 2 *
        mu.real ((Omega : Set (EuclideanSpace ℝ ι)) ∩ A') ^ (1 - 2 / q.toReal)
      ≤ S ^ 2 * (2 * ((1 + A) * G ^ 2 + B) * I) *
          (I / (l - k) ^ 2) ^ (1 - 2 / q.toReal) := by
        have hX : 0 ≤ 2 * ((1 + A) * G ^ 2 + B) * I := (sq_nonneg _).trans hgradz
        gcongr
    _ = _ := by ring

/-- **De Giorgi's class above a level.** `CaccioppoliAbove u k A B` states that the truncations
`w = (u - l)⁺` of `u ∈ H¹(Ω)` at every level `l ≥ k` with `w ∈ L²(Ω)` satisfy the Caccioppoli
inequality

`∫_Ω ψ² ‖∇w‖² ≤ A ∫_Ω ‖∇ψ‖² w² + B ∫_Ω ψ² w²`

for every smooth `ψ` compactly supported in `Ω`. This is the only way the equation enters
De Giorgi's iteration. -/
def CaccioppoliAbove (u : W1p mu Omega 2) (k A B : ℝ) : Prop :=
  ∀ l, k ≤ l → ∀ (hl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ}, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in Omega, ψ x ^ 2 *
          ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x‖ ^ 2 ∂mu ≤
        A * ∫ x in Omega,
            ‖∇ ψ x‖ ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu +
          B * ∫ x in Omega,
            ψ x ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu

/-- Membership in De Giorgi's class above `k`: the Caccioppoli inequality for the truncations
`(u - l)⁺` at every level `l ≥ k` with `(u - l)⁺ ∈ L²(Ω)`, against every admissible cutoff. -/
theorem CaccioppoliAbove.intro {u : W1p mu Omega 2} {k A B : ℝ}
    (h : ∀ l, k ≤ l → ∀ (hl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
      {ψ : EuclideanSpace ℝ ι → ℝ}, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∫ x in Omega, ψ x ^ 2 *
            ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x‖ ^ 2 ∂mu ≤
          A * ∫ x in Omega,
              ‖∇ ψ x‖ ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu +
            B * ∫ x in Omega,
              ψ x ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu) :
    CaccioppoliAbove u k A B :=
  h

/-- For `u` in De Giorgi's class above `k`, the truncation `w = (u - l)⁺` at a level `l ≥ k`
with `w ∈ L²(Ω)` satisfies `∫_Ω ψ² ‖∇w‖² ≤ A ∫_Ω ‖∇ψ‖² w² + B ∫_Ω ψ² w²` for every smooth `ψ`
compactly supported in `Ω`. -/
theorem CaccioppoliAbove.setIntegral_sq_mul_norm_gradient_sq_le {u : W1p mu Omega 2}
    {k A B : ℝ} (h : CaccioppoliAbove u k A B) {l : ℝ} (hkl : k ≤ l)
    (hl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 *
        ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x‖ ^ 2 ∂mu ≤
      A * ∫ x in Omega,
          ‖∇ ψ x‖ ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu +
        B * ∫ x in Omega,
          ψ x ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu :=
  h l hkl hl hψ hcpt hts

/-- De Giorgi's class shrinks as the level rises and grows with the constants `A` and `B`. -/
theorem CaccioppoliAbove.mono {u : W1p mu Omega 2} {k k' A A' B B' : ℝ}
    (h : CaccioppoliAbove u k A B) (hk : k ≤ k') (hA : A ≤ A') (hB : B ≤ B') :
    CaccioppoliAbove u k' A' B' :=
  .intro fun l hkl hl _ hψ hcpt hts =>
    (h.setIntegral_sq_mul_norm_gradient_sq_le (hk.trans hkl) hl hψ hcpt hts).trans <|
      add_le_add (mul_le_mul_of_nonneg_right hA (integral_nonneg fun _ => by positivity))
        (mul_le_mul_of_nonneg_right hB (integral_nonneg fun _ => by positivity))

/-- **De Giorgi's class above a level, with a linear term.** `CaccioppoliAboveLinear u k A B E`
states that the truncations `w = (u - l)⁺` of `u ∈ H¹(Ω)` at every level `l ≥ k` with
`w ∈ L²(Ω)` satisfy the Caccioppoli inequality

`∫_Ω ψ² ‖∇w‖² ≤ A ∫_Ω ‖∇ψ‖² w² + B ∫_Ω ψ² w² + E (l - k) ∫_Ω ψ² w`

for every smooth `ψ` compactly supported in `Ω`. The last term is what a mass coefficient `c`
without a sign contributes at the level `l` above `k = 0`: on `{u > l}` the product `|c u| w` is at
most `|c| (w² + l w)`. For `E = 0` this is `TauCeti.PDE.CaccioppoliAbove`
(`TauCeti.PDE.CaccioppoliAbove.caccioppoliAboveLinear`). -/
def CaccioppoliAboveLinear (u : W1p mu Omega 2) (k A B E : ℝ) : Prop :=
  ∀ l, k ≤ l → ∀ (hl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ}, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∫ x in Omega, ψ x ^ 2 *
          ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x‖ ^ 2 ∂mu ≤
        A * ∫ x in Omega,
            ‖∇ ψ x‖ ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu +
          B * ∫ x in Omega,
            ψ x ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu +
          E * (l - k) * ∫ x in Omega,
            ψ x ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ∂mu

/-- Membership in De Giorgi's class with a linear term above `k`: the Caccioppoli inequality for
the truncations `(u - l)⁺` at every level `l ≥ k` with `(u - l)⁺ ∈ L²(Ω)`, against every
admissible cutoff. -/
theorem CaccioppoliAboveLinear.intro {u : W1p mu Omega 2} {k A B E : ℝ}
    (h : ∀ l, k ≤ l → ∀ (hl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
      {ψ : EuclideanSpace ℝ ι → ℝ}, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∫ x in Omega, ψ x ^ 2 *
            ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x‖ ^ 2 ∂mu ≤
          A * ∫ x in Omega,
              ‖∇ ψ x‖ ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu +
            B * ∫ x in Omega,
              ψ x ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu +
            E * (l - k) * ∫ x in Omega,
              ψ x ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ∂mu) :
    CaccioppoliAboveLinear u k A B E :=
  h

/-- For `u` in De Giorgi's class with a linear term above `k`, the truncation `w = (u - l)⁺` at a
level `l ≥ k` with `w ∈ L²(Ω)` satisfies
`∫_Ω ψ² ‖∇w‖² ≤ A ∫_Ω ‖∇ψ‖² w² + B ∫_Ω ψ² w² + E (l - k) ∫_Ω ψ² w` for every smooth `ψ`
compactly supported in `Ω`. -/
theorem CaccioppoliAboveLinear.setIntegral_sq_mul_norm_gradient_sq_le {u : W1p mu Omega 2}
    {k A B E : ℝ} (h : CaccioppoliAboveLinear u k A B E) {l : ℝ} (hkl : k ≤ l)
    (hl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 *
        ‖W1p.gradient (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x‖ ^ 2 ∂mu ≤
      A * ∫ x in Omega,
          ‖∇ ψ x‖ ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu +
        B * ∫ x in Omega,
          ψ x ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ^ 2 ∂mu +
        E * (l - k) * ∫ x in Omega,
          ψ x ^ 2 * W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hl) x ∂mu :=
  h l hkl hl hψ hcpt hts

/-- De Giorgi's class with a linear term grows with the constants `A`, `B` and `E`. Unlike
`TauCeti.PDE.CaccioppoliAbove.mono`, the level `k` stays fixed, since raising it would change the
linear term `E (l - k)`. -/
theorem CaccioppoliAboveLinear.mono {u : W1p mu Omega 2} {k A A' B B' E E' : ℝ}
    (h : CaccioppoliAboveLinear u k A B E) (hA : A ≤ A') (hB : B ≤ B') (hE : E ≤ E') :
    CaccioppoliAboveLinear u k A' B' E' :=
  .intro fun l hkl hl _ hψ hcpt hts =>
    (h.setIntegral_sq_mul_norm_gradient_sq_le hkl hl hψ hcpt hts).trans <|
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hA (integral_nonneg fun _ => by positivity))
        (mul_le_mul_of_nonneg_right hB (integral_nonneg fun _ => by positivity)))
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hE (sub_nonneg.2 hkl))
          (integral_nonneg_of_ae
            ((W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hl).mono fun x hx => by
              simp only [Pi.zero_apply]; rw [hx]; positivity)))

/-- De Giorgi's class is the case `E = 0` of the class with a linear term. -/
theorem CaccioppoliAbove.caccioppoliAboveLinear {u : W1p mu Omega 2} {k A B : ℝ}
    (h : CaccioppoliAbove u k A B) : CaccioppoliAboveLinear u k A B 0 :=
  .intro fun l hkl hl _ hψ hcpt hts => by
    rw [zero_mul, zero_mul, add_zero]
    exact h.setIntegral_sq_mul_norm_gradient_sq_le hkl hl hψ hcpt hts

/-- The radii `r₀ = R/2 + R/2^{j+1}`, `r₁ = R/2 + R/2^{j+2}` and `ρ = (r₀ + r₁)/2` of one step of
De Giorgi's iteration on balls are ordered `0 < r₁ < ρ < r₀ ≤ R`, with gap `ρ - r₁ = R/2^{j+3}`. -/
private theorem sub_eq_div_two_pow_and_pos_and_lt_and_lt_and_le {R r₀ r₁ ρ : ℝ} (hR : 0 < R) {j : ℕ}
    (h₀ : r₀ = R / 2 + R / 2 ^ (j + 1))
    (h₁ : r₁ = R / 2 + R / 2 ^ (j + 2)) (hρ : ρ = (r₀ + r₁) / 2) :
    ρ - r₁ = R / 2 ^ (j + 3) ∧ 0 < r₁ ∧ r₁ < ρ ∧ ρ < r₀ ∧ r₀ ≤ R := by
  have hρr₁ : ρ - r₁ = R / 2 ^ (j + 3) := by
    simp only [hρ, h₀, h₁, pow_succ]
    field_simp
    ring
  have h3 : 0 < R / 2 ^ (j + 3) := by positivity
  refine ⟨hρr₁, by rw [h₁]; positivity, by linarith, ?_, ?_⟩
  · have : ρ = r₀ - R / 2 ^ (j + 3) := by
      simp only [hρ, h₀, h₁, pow_succ]
      field_simp
      ring
    linarith
  · have : R / 2 ^ (j + 1) ≤ R / 2 := div_le_div_of_nonneg_left hR.le two_pos
      (le_self_pow₀ one_le_two (Nat.succ_ne_zero j))
    rw [h₀]
    linarith

/-- The levels `k = k₀ + (K - K/2^j)` and `l = k₀ + (K - K/2^{j+1})` of one step of De Giorgi's
iteration satisfy `k₀ ≤ k < l`, with gap `l - k = K/2^{j+1}`. -/
private theorem sub_eq_div_two_pow_and_le_and_lt {k₀ K k l : ℝ} (hK : 0 < K) {j : ℕ}
    (hk : k = k₀ + (K - K / 2 ^ j))
    (hl : l = k₀ + (K - K / 2 ^ (j + 1))) : l - k = K / 2 ^ (j + 1) ∧ k₀ ≤ k ∧ k < l := by
  have hlk : l - k = K / 2 ^ (j + 1) := by
    simp only [hl, hk, pow_succ]
    field_simp
    ring
  refine ⟨hlk, ?_, by rw [← sub_pos, hlk]; positivity⟩
  have : K / 2 ^ j ≤ K := div_le_self hK.le (one_le_pow₀ one_le_two)
  rw [hk]
  linarith

/-- The cutoff, zeroth-order and linear coefficients of one step of De Giorgi's iteration are at
most a multiple of `4ʲ R⁻²`, since the cutoff has gradient at most `c / (R / 2^{j+3})` and
`2^{j+1} ≤ 2 · 4ʲ`. -/
private theorem one_add_mul_div_div_two_pow_sq_add_le {A B E c R : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hR : 0 < R) (j : ℕ) :
    (1 + A) * (c / (R / 2 ^ (j + 3))) ^ 2 + (B + E * 2 ^ (j + 1)) ≤
      (64 * c ^ 2 * (1 + A) + (B + 2 * E) * R ^ 2) * 4 ^ j * (R ^ 2)⁻¹ := by
  have h64 : ((2 : ℝ) ^ (j + 3)) ^ 2 = 64 * 4 ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
    ring
  have hcR : (c / (R / 2 ^ (j + 3))) ^ 2 = 64 * c ^ 2 * 4 ^ j * (R ^ 2)⁻¹ := by
    rw [div_div_eq_mul_div, div_pow, mul_pow, h64]
    field_simp
  have hBR : (B + 2 * E) * 4 ^ j = (B + 2 * E) * R ^ 2 * 4 ^ j * (R ^ 2)⁻¹ := by field_simp
  have h4 : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  have h2 : (2 : ℝ) ^ j ≤ 4 ^ j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hBE : B + E * 2 ^ (j + 1) ≤ (B + 2 * E) * 4 ^ j := by
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left h4 hB, mul_le_mul_of_nonneg_left h2 hE]
  rw [hcR]
  linarith

/-- The algebra closing one step of De Giorgi's iteration: with `Y` in place of the integral over
the larger ball,
`2 (M 4ʲ R⁻²) S² Y (Y / (K / 2^{j+1})²)^α = (2 M S² 4^α R⁻² (K²)^{-α}) (4 · 4^α)ʲ Y^{1+α}`. -/
private theorem mul_mul_div_div_two_pow_sq_rpow_eq {M S R Y K α : ℝ} {j : ℕ} (hY : 0 ≤ Y)
    (hK : 0 < K)
    (hα : 0 ≤ α) :
    2 * (M * 4 ^ j * (R ^ 2)⁻¹) * S ^ 2 * Y * (Y / (K / 2 ^ (j + 1)) ^ 2) ^ α =
      (2 * M * S ^ 2 * 4 ^ α * (R ^ 2)⁻¹ * (K ^ 2) ^ (-α)) * (4 * 4 ^ α) ^ j * Y ^ (1 + α) := by
  have h4 : (4 : ℝ) ^ (j + 1) = (2 ^ (j + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have hdiv : Y / (K / 2 ^ (j + 1)) ^ 2 = Y * (4 ^ (j + 1) * (K ^ 2)⁻¹) := by
    rw [h4]
    field_simp
  have hpow : (Y * (4 ^ (j + 1) * (K ^ 2)⁻¹)) ^ α =
      Y ^ α * (4 ^ α * (4 ^ α) ^ j) * (K ^ 2) ^ (-α) := by
    rw [Real.mul_rpow hY (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_pow_comm (by norm_num), Real.inv_rpow (by positivity),
      ← Real.rpow_neg (by positivity), pow_succ]
    ring
  have hYpow : Y * Y ^ α = Y ^ (1 + α) := by
    rw [Real.rpow_one_add' hY (by linarith)]
  rw [hdiv, hpow, ← hYpow, mul_pow]
  ring

/-- For `0 ≤ ψ ≤ 1` and `k ≤ l`, `∫_Ω ψ² ((u - l)⁺)² ≤ ∫_{Ω ∩ supp ψ} ((u - k)⁺)²`: the
zeroth-order term of the Caccioppoli inequality at the level `l`. -/
private theorem setIntegral_sq_mul_posPart_sq_le {u : W1p mu Omega 2} {k l : ℝ} (hkl : k ≤ l)
    (hwk : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    (hwl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ01 : range ψ ⊆ Icc 0 1) :
    ∫ x in Omega, ψ x ^ 2 *
      W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hwl) x ^ 2 ∂mu ≤
      ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
        max (W1p.value u x - k) 0 ^ 2 ∂mu :=
  W1p.setIntegral_sq_mul_value_sq_le _ (fun x => by
    obtain ⟨h0, h1⟩ := hψ01 (mem_range_self x)
    exact pow_le_one₀ h0 h1) subset_rfl
    hwk.integrable_sq (value_posPartAboveOfMemLp_sq_le_ae hkl hwl)

/-- For continuous `0 ≤ ψ ≤ 1`, `k ≤ l` and `l - k₀ ≤ N (l - k)`,
`E (l - k₀) ∫_Ω ψ² (u - l)⁺ ≤ E N ∫_{Ω ∩ supp ψ} ((u - k)⁺)²`: the linear term of the
Caccioppoli inequality above `k₀` at the level `l`, since `(l - k) (u - l)⁺ ≤ ((u - k)⁺)²`
pointwise. -/
private theorem mul_mul_setIntegral_sq_mul_posPart_le {u : W1p mu Omega 2} {k₀ k l E N : ℝ}
    (hE : 0 ≤ E) (hN : 0 ≤ N) (hkl : k ≤ l) (hlk₀ : l - k₀ ≤ N * (l - k))
    (hwk : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    (hwl : MemLp (fun x => max (W1p.value u x - l) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : Continuous ψ) (hψ01 : range ψ ⊆ Icc 0 1) :
    E * (l - k₀) * ∫ x in Omega, ψ x ^ 2 *
      W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hwl) x ∂mu ≤
      E * N * ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
        max (W1p.value u x - k) 0 ^ 2 ∂mu := by
  set J := ∫ x in Omega, ψ x ^ 2 *
    W1p.value (W1p.posPartAboveOfMemLp (by norm_num) l u hwl) x ∂mu
  have hJ : 0 ≤ J := integral_nonneg_of_ae (by
    filter_upwards [W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hwl] with x hx
    rw [hx]
    exact mul_nonneg (sq_nonneg _) (le_max_right _ _))
  -- The base case `E = N = 1`: `(l - k) J ≤ ∫_{Ω ∩ supp ψ} ((u - k)⁺)²`.
  suffices hbase : (l - k) * J ≤ ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
      max (W1p.value u x - k) 0 ^ 2 ∂mu by
    calc E * (l - k₀) * J ≤ E * (N * (l - k)) * J := by gcongr
      _ = E * N * ((l - k) * J) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase (mul_nonneg hE hN)
  refine le_trans ?_ (setIntegral_sq_mul_posPart_sq_le le_rfl hwk hwk hψ01)
  rw [← integral_const_mul]
  have hψ2M : ∀ᵐ x ∂mu.restrict Omega, ‖ψ x ^ 2‖ ≤ 1 := .of_forall fun x => by
    obtain ⟨h0, h1⟩ := hψ01 (mem_range_self x)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_one₀ h0 h1
  refine integral_mono_of_nonneg ?_ ((Lp.memLp _).integrable_sq.bdd_mul
    (hψ.pow 2).aestronglyMeasurable hψ2M) ?_
  · filter_upwards [W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hwl] with x hx
    rw [hx]
    exact mul_nonneg (sub_nonneg.2 hkl) (mul_nonneg (sq_nonneg _) (le_max_right _ _))
  · filter_upwards [W1p.value_posPartAboveOfMemLp_ae (by norm_num) l u hwl,
      W1p.value_posPartAboveOfMemLp_ae (by norm_num) k u hwk] with x hxl hxk
    rw [hxl, hxk]
    -- `(l - k) (t - l)⁺ ≤ ((t - k)⁺)²`, since `t - k = (t - l) + (l - k)` above `l`.
    have hpt : (l - k) * max (W1p.value u x - l) 0 ≤ max (W1p.value u x - k) 0 ^ 2 := by
      rcases le_or_gt (W1p.value u x) l with hxu | hxu
      · rw [max_eq_right (by linarith), mul_zero]
        positivity
      · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
        nlinarith
    calc (l - k) * (ψ x ^ 2 * max (W1p.value u x - l) 0)
        = ψ x ^ 2 * ((l - k) * max (W1p.value u x - l) 0) := by ring
      _ ≤ ψ x ^ 2 * max (W1p.value u x - k) 0 ^ 2 :=
        mul_le_mul_of_nonneg_left hpt (sq_nonneg _)

/-- One step of De Giorgi's iteration on balls. Suppose that the truncations `(u - l)⁺` at every
level `l ≥ k₀` satisfy the Caccioppoli inequality with a linear term, with constants
`A, B, E ≥ 0`, against every cutoff (`TauCeti.PDE.CaccioppoliAboveLinear`).
Along the radii `rⱼ = R/2 + R/2^{j+1}`, shrinking from `R` to `R/2`, and the levels
`kⱼ = k₀ + (K - K/2^j)`, rising from `k₀` to `k₀ + K`, the quantities
`Yⱼ = ∫_{B(x₀, rⱼ)} ((u - kⱼ)⁺)²` satisfy `Yⱼ₊₁ ≤ C bʲ Yⱼ^{1 + α}` with `α = 1 - 2/q`,
`b = 4 · 4^α` and `C` proportional to `R⁻² (K²)^{-α}`. The cutoff between `B(x₀, rⱼ₊₁)` and
`B(x₀, rⱼ)` is supplied by `hc`, with gradient at most `c` over the gap. The linear term costs at
most `2^{j+1} E` times the integral at the lower level, because the level gap is `K/2^{j+1}`. -/
private theorem setIntegral_ball_max_sub_sq_succ_le {q : ℝ≥0∞} (hq : 2 ≤ q) {S : ℝ≥0}
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u : W1p mu Omega 2} {k₀ : ℝ}
    (hwLp : MemLp (fun x => max (W1p.value u x - k₀) 0) 2 (mu.restrict Omega))
    {A B E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hcacc : CaccioppoliAboveLinear u k₀ A B E)
    {c : ℝ} (hc : ∀ (x₀ : EuclideanSpace ℝ ι) {r R : ℝ}, 0 < r → r < R →
      ∃ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        EqOn ψ 1 (Metric.closedBall x₀ r) ∧ tsupport ψ ⊆ Metric.closedBall x₀ R ∧
          ∀ x, ‖∇ ψ x‖ ≤ c / (R - r))
    {x₀ : EuclideanSpace ℝ ι} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {K : ℝ} (hK : 0 < K)
    {α : ℝ} (hα : α = 1 - 2 / q.toReal) (j : ℕ) :
    ∫ x in Metric.ball x₀ (R / 2 + R / 2 ^ (j + 2)),
        max (W1p.value u x - (k₀ + (K - K / 2 ^ (j + 1)))) 0 ^ 2 ∂mu ≤
      (2 * (64 * c ^ 2 * (1 + A) + (B + 2 * E) * R ^ 2) * S ^ 2 * 4 ^ α * (R ^ 2)⁻¹ *
          (K ^ 2) ^ (-α)) * (4 * 4 ^ α) ^ j *
        (∫ x in Metric.ball x₀ (R / 2 + R / 2 ^ (j + 1)),
          max (W1p.value u x - (k₀ + (K - K / 2 ^ j))) 0 ^ 2 ∂mu) ^ (1 + α) := by
  have hα0 : 0 ≤ α := hα ▸ one_sub_two_div_toReal_nonneg hq
  set r₀ := R / 2 + R / 2 ^ (j + 1)
  set r₁ := R / 2 + R / 2 ^ (j + 2)
  set ρ := (r₀ + r₁) / 2
  set k := k₀ + (K - K / 2 ^ j)
  set l := k₀ + (K - K / 2 ^ (j + 1))
  obtain ⟨hρr₁, hr₁, hr₁ρ, hρr₀, hr₀R⟩ :=
    sub_eq_div_two_pow_and_pos_and_lt_and_lt_and_le hR (j := j) rfl rfl rfl
  obtain ⟨hlk, hk0, hkl⟩ := sub_eq_div_two_pow_and_le_and_lt hK (j := j) rfl rfl
  obtain ⟨ψ, hψ, hψ01, hψ1, hψts, hψG⟩ := hc x₀ hr₁ hr₁ρ
  have hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    hψts.trans ((Metric.closedBall_subset_ball hρr₀).trans
      ((Metric.ball_subset_ball hr₀R).trans hball))
  have hcpt : HasCompactSupport ψ :=
    (isCompact_closedBall x₀ ρ).of_isClosed_subset (isClosed_tsupport ψ) hψts
  have hwk := W1p.memLp_posPartAbove_of_le u hk0 hwLp
  have hwl := W1p.memLp_posPartAbove_of_le u hkl.le hwk
  set I := ∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
    max (W1p.value u x - k) 0 ^ 2 ∂mu
  -- The linear term is at most `2^{j+1} E I`, since `l - k₀ ≤ K = 2^{j+1} (l - k)`.
  have hlk₀ : l - k₀ ≤ 2 ^ (j + 1) * (l - k) := by
    rw [hlk, mul_div_cancel₀ _ (by positivity)]
    have : 0 ≤ K / 2 ^ (j + 1) := by positivity
    linarith
  have hstep := setIntegral_sq_mul_max_sub_sq_le_of_caccioppoli hq hS hkl hwk hψ hcpt hts hψG hA
    (B := B + E * 2 ^ (j + 1))
    ((hcacc.setIntegral_sq_mul_norm_gradient_sq_le (hk0.trans hkl.le) hwl hψ hcpt hts).trans <| by
      have hBZ := mul_le_mul_of_nonneg_left
        (setIntegral_sq_mul_posPart_sq_le hkl.le hwk hwl hψ01) hB
      linear_combination hBZ + mul_mul_setIntegral_sq_mul_posPart_le hE (by positivity) hkl.le
        hlk₀ hwk hwl hψ.continuous hψ01)
  -- Integrability of the truncations on `Ω`, and nonnegativity.
  have hint : ∀ m : ℝ, k₀ ≤ m →
      IntegrableOn (fun x => max (W1p.value u x - m) 0 ^ 2) (Omega : Set _) mu :=
    fun m hm => (W1p.memLp_posPartAbove_of_le u hm hwLp).integrable_sq
  have hnn : ∀ m : ℝ, ∀ x, 0 ≤ max (W1p.value u x - m) 0 ^ 2 := fun _ _ => by positivity
  set Y := ∫ x in Metric.ball x₀ r₀, max (W1p.value u x - k) 0 ^ 2 ∂mu
  have hY : 0 ≤ Y := integral_nonneg (hnn k)
  -- The left-hand side is below the cutoff integral, since `ψ = 1` on the smaller ball.
  have hlhs : ∫ x in Metric.ball x₀ r₁, max (W1p.value u x - l) 0 ^ 2 ∂mu ≤
      ∫ x in Omega, ψ x ^ 2 * max (W1p.value u x - l) 0 ^ 2 ∂mu :=
    MeasureTheory.setIntegral_le_setIntegral_sq_mul_of_ae_sq_eq_one (hint l (hk0.trans hkl.le))
      (ae_of_all _ fun x => hnn l x) (hψ.continuous.pow 2).aestronglyMeasurable
      (ae_of_all _ fun x => abs_le.2 ⟨by linarith [(hψ01 (mem_range_self x)).1],
        (hψ01 (mem_range_self x)).2⟩)
      (ae_restrict_of_forall_mem measurableSet_ball fun x hx => by
        simp [hψ1 (Metric.ball_subset_closedBall hx)])
      ((Metric.ball_subset_ball (hr₁ρ.trans hρr₀).le).trans
        ((Metric.ball_subset_ball hr₀R).trans hball))
  -- The integral over `Ω ∩ supp ψ` is below `Y`.
  have hI : I ≤ Y :=
    setIntegral_mono_set ((hint k hk0).mono_set
      ((Metric.ball_subset_ball hr₀R).trans hball))
      (Eventually.of_forall fun x => hnn k x)
      (inter_subset_right.trans (hψts.trans (Metric.closedBall_subset_ball hρr₀))).eventuallySubset
  -- The cutoff, zeroth-order and linear terms are all at most a multiple of `4ʲ R⁻²`.
  have hG := one_add_mul_div_div_two_pow_sq_add_le (A := A) (c := c) hB hE hR j
  refine hlhs.trans (hstep.trans ?_)
  rw [hρr₁, hlk]
  refine le_trans ?_ (mul_mul_div_div_two_pow_sq_rpow_eq hY hK hα0).le
  rw [← hα]
  gcongr

/-- **De Giorgi's threshold.** Suppose that the truncations of `u` at every level `l ≥ k₀`
satisfy the Caccioppoli inequality with a linear term, with constants `A, B, E ≥ 0`, and let `M`
dominate the constant `2 (64 c² (1 + A) + (B + 2E) R²) S²` of the recursion of
`setIntegral_ball_max_sub_sq_succ_le`. If `∫_{B(x₀, R)} ((u - k₀)⁺)²` lies below the threshold of
the fast geometric convergence lemma for that recursion with `M` in place of its constant, at
height `K > 0` above `k₀`, then `u ≤ k₀ + K` almost everywhere on `B(x₀, R/2)`. -/
private theorem ae_value_le_of_setIntegral_le {q : ℝ≥0∞} (hq : 2 ≤ q) {S : ℝ≥0}
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u : W1p mu Omega 2} {k₀ : ℝ}
    (hwLp : MemLp (fun x => max (W1p.value u x - k₀) 0) 2 (mu.restrict Omega))
    {A B E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hcacc : CaccioppoliAboveLinear u k₀ A B E)
    {c : ℝ} (hc : ∀ (x₀ : EuclideanSpace ℝ ι) {r R : ℝ}, 0 < r → r < R →
      ∃ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        EqOn ψ 1 (Metric.closedBall x₀ r) ∧ tsupport ψ ⊆ Metric.closedBall x₀ R ∧
          ∀ x, ‖∇ ψ x‖ ≤ c / (R - r))
    {x₀ : EuclideanSpace ℝ ι} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {K : ℝ} (hK : 0 < K)
    {α : ℝ} (hα : α = 1 - 2 / q.toReal) (hα0 : 0 < α) {M : ℝ}
    (hM : 2 * (64 * c ^ 2 * (1 + A) + (B + 2 * E) * R ^ 2) * S ^ 2 ≤ M)
    (hY0 : ∫ x in Metric.ball x₀ R, max (W1p.value u x - k₀) 0 ^ 2 ∂mu ≤
      (M * 4 ^ α * (R ^ 2)⁻¹ * (K ^ 2) ^ (-α)) ^ (-α⁻¹) * (4 * 4 ^ α) ^ (-(α ^ 2)⁻¹)) :
    ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)), W1p.value u x ≤ k₀ + K := by
  set Y : ℕ → ℝ := fun j => ∫ x in Metric.ball x₀ (R / 2 + R / 2 ^ (j + 1)),
    max (W1p.value u x - (k₀ + (K - K / 2 ^ j))) 0 ^ 2 ∂mu
  have hlev : ∀ j : ℕ, k₀ ≤ k₀ + (K - K / 2 ^ j) := fun j => by
    have : K / 2 ^ j ≤ K := div_le_self hK.le (one_le_pow₀ one_le_two)
    linarith
  have hnn : ∀ m : ℝ, ∀ x, 0 ≤ max (W1p.value u x - m) 0 ^ 2 := fun _ _ => by positivity
  have hint : ∀ m : ℝ, k₀ ≤ m →
      IntegrableOn (fun x => max (W1p.value u x - m) 0 ^ 2) (Omega : Set _) mu :=
    fun m hm => (W1p.memLp_posPartAbove_of_le u hm hwLp).integrable_sq
  have hb : (1 : ℝ) < 4 * 4 ^ α := by
    have := Real.one_le_rpow (x := (4 : ℝ)) (z := α) (by norm_num) hα0.le
    linarith
  have hY0' : Y 0 = ∫ x in Metric.ball x₀ R, max (W1p.value u x - k₀) 0 ^ 2 ∂mu := by
    simp only [Y, zero_add, pow_one, pow_zero, div_one, sub_self, add_zero, add_halves]
  -- The recursion of `setIntegral_ball_max_sub_sq_succ_le`, with its constant enlarged to `M`.
  have hrec : ∀ j, Y (j + 1) ≤
      (M * 4 ^ α * (R ^ 2)⁻¹ * (K ^ 2) ^ (-α)) * (4 * 4 ^ α) ^ j * Y j ^ (1 + α) := fun j => by
    refine (setIntegral_ball_max_sub_sq_succ_le hq hS hwLp hA hB hE hcacc hc hR hball hK hα
      j).trans ?_
    gcongr
  have hlim := tendsto_atTop_zero_of_le_mul_pow_mul_rpow (Y := Y)
    (fun j => integral_nonneg (hnn _)) hb hα0 (hY0'.trans_le hY0) hrec
  -- The truncation at level `k₀ + K` on the half ball is below every term of the sequence.
  have hhalf : Metric.ball x₀ (R / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) :=
    (Metric.ball_subset_ball (by linarith)).trans hball
  have hZ : ∀ j,
      ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - (k₀ + K)) 0 ^ 2 ∂mu ≤ Y j := by
    intro j
    have hsub : Metric.ball x₀ (R / 2) ⊆ Metric.ball x₀ (R / 2 + R / 2 ^ (j + 1)) :=
      Metric.ball_subset_ball (le_add_of_nonneg_right (by positivity))
    have hr : R / 2 + R / 2 ^ (j + 1) ≤ R := by
      have : R / 2 ^ (j + 1) ≤ R / 2 := div_le_div_of_nonneg_left hR.le two_pos
        (le_self_pow₀ one_le_two (Nat.succ_ne_zero j))
      linarith
    calc ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - (k₀ + K)) 0 ^ 2 ∂mu
        ≤ ∫ x in Metric.ball x₀ (R / 2),
            max (W1p.value u x - (k₀ + (K - K / 2 ^ j))) 0 ^ 2 ∂mu :=
          setIntegral_mono ((hint _ (by linarith)).mono_set hhalf)
            ((hint _ (hlev j)).mono_set hhalf) fun x => pow_le_pow_left₀ (le_max_right _ _)
              (max_le_max (by have := div_nonneg hK.le (pow_nonneg zero_le_two j); linarith)
                le_rfl) 2
      _ ≤ Y j := setIntegral_mono_set ((hint _ (hlev j)).mono_set
            ((Metric.ball_subset_ball hr).trans hball))
          (Eventually.of_forall (hnn _)) hsub.eventuallySubset
  have hZ0 : ∫ x in Metric.ball x₀ (R / 2), max (W1p.value u x - (k₀ + K)) 0 ^ 2 ∂mu = 0 :=
    le_antisymm (ge_of_tendsto' hlim hZ) (integral_nonneg (hnn _))
  exact MeasureTheory.ae_le_of_setIntegral_max_sub_sq_eq_zero
    ((hint _ (by linarith)).mono_set hhalf) hZ0

/-- Enlarging the recursion constant `2 (64 C² (1 + A) + B R²) S²` to `2 (64 C²) (1 + A + B R²) S²`
is harmless when `C ≥ 1`. -/
private theorem mul_add_mul_sq_le_mul_add_mul_sq_of_one_le {C A B R S : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B)
    :
    2 * (64 * C ^ 2 * (1 + A) + B * R ^ 2) * S ^ 2 ≤
      2 * (64 * C ^ 2) * (1 + A + B * R ^ 2) * S ^ 2 := by
  have hc64 : 0 ≤ 64 * C ^ 2 - 1 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg S) (mul_nonneg hc64 (mul_nonneg hB (sq_nonneg R)))]

/-- The level gap `K = √(F^{1/α} b^{1/α²}) M^{1/(2α)} S^{1/α} R^{-1/α} √Y₀` makes `Y₀` exactly the
threshold `(E₁ R⁻² (K²)^{-α})^{-1/α} b^{-1/α²}` of fast geometric convergence, `E₁ = F M S²`. -/
private theorem eq_mul_inv_mul_sq_rpow_neg_rpow_mul_rpow {α F b M S R Y₀ K E₁ : ℝ} (hα0 : 0 < α)
    (hF : 0 < F) (hb0 : 0 < b)
    (hM : 0 < M) (hS0 : 0 < S) (hR : 0 < R) (hY₀ : 0 ≤ Y₀) (hE₁ : E₁ = F * M * S ^ 2)
    (hK : K = √(F ^ α⁻¹ * b ^ (α ^ 2)⁻¹) * M ^ (2 * α)⁻¹ * S ^ α⁻¹ * R ^ (-α⁻¹) * √Y₀)
    (hK0 : 0 < K) :
    Y₀ = (E₁ * (R ^ 2)⁻¹ * (K ^ 2) ^ (-α)) ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹) := by
  have hE₁0 : 0 < E₁ := hE₁ ▸ by positivity
  have hαmul : -α * -α⁻¹ = 1 := by field_simp
  have hKpow : ((K ^ 2) ^ (-α)) ^ (-α⁻¹) = K ^ 2 := by
    rw [← Real.rpow_mul (by positivity), hαmul, Real.rpow_one]
  have hRpow : ((R ^ 2)⁻¹) ^ (-α⁻¹) = (R ^ α⁻¹) ^ 2 := by
    rw [Real.inv_rpow (by positivity), Real.rpow_neg (x := R ^ 2) (by positivity),
      inv_inv, ← Real.rpow_pow_comm hR.le]
  have hfactor : (E₁ * (R ^ 2)⁻¹ * (K ^ 2) ^ (-α)) ^ (-α⁻¹) =
      E₁ ^ (-α⁻¹) * (R ^ α⁻¹) ^ 2 * K ^ 2 := by
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hE₁0.le (by positivity), hKpow, hRpow]
  -- `E₁ ^ α⁻¹ = F ^ α⁻¹ (M ^ (2α)⁻¹)² (S ^ α⁻¹)²`, so
  -- `K² = E₁ ^ α⁻¹ b ^ (α²)⁻¹ (R ^ (-α⁻¹))² Y₀`.
  have hMpow : M ^ α⁻¹ = (M ^ (2 * α)⁻¹) ^ 2 := by
    rw [← Real.rpow_mul_natCast hM.le]
    congr 1
    field_simp
    norm_num
  have hE₁pow : E₁ ^ α⁻¹ = F ^ α⁻¹ * (M ^ (2 * α)⁻¹) ^ 2 * (S ^ α⁻¹) ^ 2 := by
    rw [hE₁, Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow hF.le hM.le,
      Real.rpow_pow_comm hS0.le, hMpow]
  have hKsq : K ^ 2 = E₁ ^ α⁻¹ * b ^ (α ^ 2)⁻¹ * (R ^ (-α⁻¹)) ^ 2 * Y₀ := by
    rw [hK]
    simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ F ^ α⁻¹ * b ^ (α ^ 2)⁻¹),
      Real.sq_sqrt hY₀, hE₁pow]
    ring
  rw [hfactor, hKsq, Real.rpow_neg hE₁0.le, Real.rpow_neg hb0.le,
    Real.rpow_neg hR.le]
  field_simp

/-- **Local boundedness from the Caccioppoli and Sobolev inequalities.** Suppose that the
truncations of `u` at every level `l ≥ k` satisfy the Caccioppoli inequality with a linear term,
with constants `A, B, E ≥ 0`, that `(u - k)⁺ ∈ L²(Ω)`, and that `W^{1,2}_0(Ω)` satisfies a Sobolev
inequality with exponent `q > 2` and constant `S`. Then on every ball `B(x₀, R) ⊆ Ω`, `u` is at
most `k + D (1 + A + (B + 2E) R²)^{1/(2α)} S^{1/α} R^{-1/α} ‖(u - k)⁺‖_{L²(B(x₀, R))}`,
`α = 1 - 2/q`, almost everywhere on `B(x₀, R/2)`, with `D` independent of `S`, `A`, `B`, `E` and
`R`: this homogeneity in `S` is what makes the bound scale-invariant when `S` is the Sobolev
constant of the ball `B(x₀, R)` itself. -/
private theorem exists_ae_value_le_add_mul_rpow_mul_rpow_mul_rpow_mul_sqrt_setIntegral_of_memLp
    {q : ℝ≥0∞} (hq : 2 < q) :
    ∃ D : ℝ, 0 < D ∧ ∀ {S : ℝ≥0} {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2}
      {k A B E : ℝ} {x₀ : EuclideanSpace ℝ ι} {R : ℝ}, 0 < S → 0 ≤ A → 0 ≤ B → 0 ≤ E →
      (∀ v ∈ w1p0Submodule mu Omega 2,
        eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ) →
      CaccioppoliAboveLinear u k A B E →
      MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * (1 + A + (B + 2 * E) * R ^ 2) ^ (2 * (1 - 2 / q.toReal))⁻¹ *
          (S : ℝ) ^ (1 - 2 / q.toReal)⁻¹ * R ^ (-(1 - 2 / q.toReal)⁻¹) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨c, hc0, hc⟩ := exists_forall_contDiff_cutoff_closedBall (E := EuclideanSpace ℝ ι)
  set α : ℝ := 1 - 2 / q.toReal with hα
  have hα0 : 0 < α := by
    rcases eq_or_ne q (∞ : ℝ≥0∞) with rfl | hqt
    · simp [α]
    · have h2q : 2 < q.toReal := by
        simpa using (ENNReal.toReal_lt_toReal (by norm_num) hqt).2 hq
      rw [hα, sub_pos, div_lt_one (by linarith)]
      exact h2q
  -- Enlarge the cutoff constant to `c + 1 ≥ 1`.
  have hc'0 : 1 ≤ c + 1 := by linarith
  have hc' : ∀ (x₀ : EuclideanSpace ℝ ι) {r R : ℝ}, 0 < r → r < R →
      ∃ ψ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ ψ ∧ range ψ ⊆ Icc 0 1 ∧
        EqOn ψ 1 (Metric.closedBall x₀ r) ∧ tsupport ψ ⊆ Metric.closedBall x₀ R ∧
          ∀ x, ‖∇ ψ x‖ ≤ (c + 1) / (R - r) := fun x₀ r R hr hrR => by
    obtain ⟨ψ, h1, h2, h3, h4, h5, -⟩ := hc x₀ hr.le hrR
    exact ⟨ψ, h1, h2, h3, h4, fun x =>
      (h5 x).trans (div_le_div_of_nonneg_right (by linarith) (sub_pos.2 hrR).le)⟩
  set F : ℝ := 2 * (64 * (c + 1) ^ 2) * 4 ^ α
  have hF : 0 < F := by positivity
  set b : ℝ := 4 * 4 ^ α
  refine ⟨√(F ^ α⁻¹ * b ^ (α ^ 2)⁻¹), Real.sqrt_pos.2 (by positivity), ?_⟩
  intro S Omega u k A B E x₀ R hS0 hA hB hE hS hcacc hwLp hR hball
  have hS0' : (0 : ℝ) < S := hS0
  set M : ℝ := 1 + A + (B + 2 * E) * R ^ 2
  have hM : 0 < M := by positivity
  -- The enlarged recursion constant `N`, and `N 4^α = F M S²`.
  set N : ℝ := 2 * (64 * (c + 1) ^ 2) * M * (S : ℝ) ^ 2
  have hN : 2 * (64 * (c + 1) ^ 2 * (1 + A) + (B + 2 * E) * R ^ 2) * (S : ℝ) ^ 2 ≤ N :=
    mul_add_mul_sq_le_mul_add_mul_sq_of_one_le hc'0 (by positivity)
  set N₁ : ℝ := N * 4 ^ α
  have hN₁ : N₁ = F * M * (S : ℝ) ^ 2 := by
    simp only [N₁, N, F]
    ring
  set Y₀ := ∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu
  have hY₀ : 0 ≤ Y₀ := integral_nonneg fun x => by positivity
  rcases hY₀.eq_or_lt with hzero | hpos
  · -- Zero energy: `(u - k)⁺` vanishes almost everywhere on the ball.
    refine (ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball (half_le_self hR.le))
      (MeasureTheory.ae_le_of_setIntegral_max_sub_sq_eq_zero
        (IntegrableOn.mono_set hwLp.integrable_sq hball) hzero.symm)).mono fun x hx => ?_
    rw [← hzero, Real.sqrt_zero, mul_zero, add_zero]
    exact hx
  · set K := √(F ^ α⁻¹ * b ^ (α ^ 2)⁻¹) * M ^ (2 * α)⁻¹ * (S : ℝ) ^ α⁻¹ * R ^ (-α⁻¹) * √Y₀
    have hK : 0 < K := by positivity
    refine ae_value_le_of_setIntegral_le hq.le hS hwLp hA hB hE hcacc hc' hR hball hK hα hα0 hN
      (le_of_eq ?_)
    -- `K` was chosen to make `Y₀` exactly the threshold. The `change` only folds the recursion
    -- constant back into the abbreviations `N₁` and `b`, which `set` does not do for new goals.
    change Y₀ = (N₁ * (R ^ 2)⁻¹ * (K ^ 2) ^ (-α)) ^ (-α⁻¹) * b ^ (-(α ^ 2)⁻¹)
    exact eq_mul_inv_mul_sq_rpow_neg_rpow_mul_rpow hα0 hF (by positivity) hM hS0' hR hY₀ hN₁ rfl hK

/-- For `δ = 1/(4n)` and `S = K R ^ (1 - n δ)`,
`D₀ M ^ (1/(4δ)) S ^ (1/(2δ)) R ^ (-1/(2δ)) = D₀ K ^ (1/(2δ)) Mⁿ R ^ (-n/2)`. -/
private theorem mul_rpow_mul_rpow_mul_rpow_neg_eq_mul_rpow_mul_pow_mul_rpow {n : ℕ}
    (hn : (0 : ℝ) < n) {δ : ℝ}
    (hδ : δ = (4 * (n : ℝ))⁻¹) {K R S : ℝ} {D₀ M : ℝ} (hK : 0 < K) (hR : 0 < R)
    (hS : S = K * R ^ (1 - n * δ)) :
    D₀ * M ^ (2 * (2 * δ))⁻¹ * S ^ (2 * δ)⁻¹ * R ^ (-(2 * δ)⁻¹) =
      D₀ * K ^ (2 * δ)⁻¹ * M ^ n * R ^ (-(n : ℝ) / 2) := by
  have hexp : (1 - n * δ) * (2 * δ)⁻¹ + -(2 * δ)⁻¹ = -(n : ℝ) / 2 := by
    subst hδ
    field_simp
    ring
  have hn' : (2 * (2 * δ))⁻¹ = (n : ℝ) := by
    subst hδ
    field_simp
    ring
  rw [hS, hn', Real.rpow_natCast, Real.mul_rpow hK.le (by positivity), ← Real.rpow_mul hR.le]
  calc _ = D₀ * K ^ (2 * δ)⁻¹ * M ^ n *
        (R ^ ((1 - n * δ) * (2 * δ)⁻¹) * R ^ (-(2 * δ)⁻¹)) := by ring
    _ = _ := by rw [← Real.rpow_add hR, hexp]

/-- The scale-invariant local bound of
`exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoliAboveLinear` when `Ω`
is the ball `B(x₀, R)` itself, with the constant `1 + A + (B + 2E) R²` of the iteration. -/
private theorem exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_eq_ball
    [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2} {k A B E : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ}, (Omega : Set (EuclideanSpace ℝ ι)) = Metric.ball x₀ R →
      0 ≤ A → 0 ≤ B → 0 ≤ E → 0 < R →
      CaccioppoliAboveLinear u k A B E →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * (1 + A + (B + 2 * E) * R ^ 2) ^ Fintype.card ι *
          R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  set n : ℕ := Fintype.card ι
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hn0 : (0 : ℝ) < n := by linarith
  -- The exponents: `δ = 1/(4n)` and `1/q = 1/2 - δ`, so that `2 < q` and `δ < 1/n`.
  set δ : ℝ := (4 * n)⁻¹
  have hδ0 : 0 < δ := by positivity
  have hδn : δ < (n : ℝ)⁻¹ := (inv_lt_inv₀ (by positivity) hn0).2 (by linarith)
  have hδ2 : δ < 2⁻¹ := (inv_lt_inv₀ (by positivity) two_pos).2 (by linarith)
  set q : ℝ≥0 := Real.toNNReal (2⁻¹ - δ)⁻¹
  have hq : (q : ℝ) = (2⁻¹ - δ)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 (by linarith))
  have hq2 : (2 : ℝ≥0∞) < q := by
    have : (2 : ℝ) < q := by
      rw [hq, lt_inv_comm₀ two_pos (by linarith)]
      linarith
    exact_mod_cast this
  have hα : 1 - 2 / ((q : ℝ≥0∞)).toReal = 2 * δ := by
    rw [ENNReal.coe_toReal, hq, div_inv_eq_mul]
    ring
  obtain ⟨D₀, hD₀, hmain⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_rpow_mul_rpow_mul_sqrt_setIntegral_of_memLp (mu := mu)
      hq2
  -- The constant of the Sobolev inequality on balls, `S = K R ^ (1 - n δ)`.
  obtain ⟨K, hK, hsobK⟩ :=
    W1p.exists_forall_eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball (mu := mu)
      hq2.le (δ := δ) (by rw [ENNReal.toReal_ofNat, hq, inv_inv]; ring)
      (by rwa [finrank_euclideanSpace])
  simp only [finrank_euclideanSpace] at hsobK
  refine ⟨D₀ * K ^ (2 * δ)⁻¹, by positivity, ?_⟩
  intro Omega u k A B E x₀ R hΩ hA hB hE hR hcacc
  have : IsFiniteMeasure (mu.restrict Omega) := by
    rw [hΩ]
    exact isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  set S : ℝ≥0 := ⟨K * R ^ (1 - n * δ), by positivity⟩
  have hS : (S : ℝ) = K * R ^ (1 - n * δ) := NNReal.coe_mk _ _
  have hsob : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ :=
    fun v hv => by
      rw [← ENNReal.ofReal_coe_nnreal (p := S), hS]
      exact hsobK hΩ v hv
  have hbound := hmain (k := k) (NNReal.coe_pos.1 (by rw [hS]; positivity)) hA hB hE hsob hcacc
    ((Lp.memLp _).sub (memLp_const k)).pos_part hR hΩ.symm.subset
  rw [hα] at hbound
  rwa [mul_rpow_mul_rpow_mul_rpow_neg_eq_mul_rpow_mul_pow_mul_rpow hn0 rfl hK hR hS] at hbound

/-- **Local boundedness from the Caccioppoli inequality with a linear term (De Giorgi).** In
every dimension `n ≥ 1` there is `D > 0`, depending on the dimension and the normalization of the
additive Haar measure `mu`, such that the following holds. Let `u ∈ H¹(Ω)`, let `B(x₀, R) ⊆ Ω`
and `k` be a level, and suppose that the restriction of `u` to the ball satisfies the
Caccioppoli inequality with a linear term at every level `l ≥ k`: with `w = (u - l)⁺`, every
smooth `ψ` compactly supported in `B(x₀, R)` satisfies

`∫ ψ² ‖∇w‖² ≤ A ∫ ‖∇ψ‖² w² + B ∫ ψ² w² + E (l - k) ∫ ψ² w`

over `B(x₀, R)`, with `A, B, E ≥ 0`. Then

`u ≤ k + D (1 + A + (B + E) R²)ⁿ R^{-n/2} (∫_{B(x₀, R)} ((u - k)⁺)²)^{1/2}` almost everywhere
on `B(x₀, R/2)`.

Functions satisfying such Caccioppoli inequalities form the classes
`TauCeti.PDE.CaccioppoliAboveLinear`. Weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u ≤ 0`
with `c` of either sign belong to such a class above the level `0`, with `E` proportional to the
bound on `|c|`. In De Giorgi's iteration the levels `l` lie between `k` and `k + K` and are
`K/2^{j+1}` apart at the `j`-th step, so the linear term costs at most `2^{j+1} E` times the
truncation at the lower level, comparable to the factor `4ʲ` the cutoffs cost.

The Sobolev inequality that drives De Giorgi's iteration is the one on `W^{1,2}_0(B(x₀, R))`,
`TauCeti.W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball`, at an exponent `q > 2`
with `1/2 - 1/q < 1/n`, which exists in every dimension. Its constant is a multiple of
`R ^ (1 - n (1/2 - 1/q))`, and this power of `R` is exactly what turns the bound into the
scale-invariant one above. -/
theorem exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoliAboveLinear
    [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2} {k A B E : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ}
      (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))),
      let U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
      let uU : W1p mu U 2 := W1p.restrictL hball u
      0 ≤ A → 0 ≤ B → 0 ≤ E → 0 < R →
      CaccioppoliAboveLinear uU k A B E →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * (1 + A + (B + E) * R ^ 2) ^ Fintype.card ι *
          R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨D, hD, hmain⟩ :=
    exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_eq_ball (mu := mu)
  refine ⟨2 ^ Fintype.card ι * D, by positivity, ?_⟩
  intro Omega u k A B E x₀ R hball U uU hA hB hE hR hcacc
  obtain ⟨hw, hint⟩ := value_restrictL_ae_ball_half_and_setIntegral_comp_eq u hball
    fun t => max (t - k) 0 ^ 2
  -- `1 + A + (B + 2E) R² ≤ 2 (1 + A + (B + E) R²)`.
  have hfac : D * (1 + A + (B + 2 * E) * R ^ 2) ^ Fintype.card ι ≤
      2 ^ Fintype.card ι * D * (1 + A + (B + E) * R ^ 2) ^ Fintype.card ι := by
    rw [mul_comm (2 ^ _) D, mul_assoc, ← mul_pow]
    gcongr
    nlinarith [mul_nonneg hB (sq_nonneg R)]
  filter_upwards [hmain (u := uU) (k := k) rfl hA hB hE hR hcacc, hw] with x hx hwx
  rw [← hwx, ← hint]
  refine hx.trans ?_
  gcongr k + ?_ * _ * _

/-- **Local boundedness from the Caccioppoli inequality (De Giorgi).** In every dimension
`n ≥ 1` there is `D > 0`, depending on the dimension and the normalization of the additive Haar
measure `mu`, such that the following holds. Let `u ∈ H¹(Ω)`, let `B(x₀, R) ⊆ Ω` and `k` be a
level, and suppose that the restriction of `u` to the ball satisfies the Caccioppoli inequality
at every level `l ≥ k`: with `w = (u - l)⁺`, every smooth `ψ` compactly supported in `B(x₀, R)`
satisfies

`∫ ψ² ‖∇w‖² ≤ A ∫ ‖∇ψ‖² w² + B ∫ ψ² w²`

over `B(x₀, R)`, with `A, B ≥ 0`. Then

`u ≤ k + D (1 + A + B R²)ⁿ R^{-n/2} (∫_{B(x₀, R)} ((u - k)⁺)²)^{1/2}` almost everywhere on
`B(x₀, R/2)`.

Functions satisfying such Caccioppoli inequalities form De Giorgi's classes
(`TauCeti.PDE.CaccioppoliAbove`). Weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` belong to them at every
level with `B = 0`, which gives the scale-invariant bound
`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral`. A drift contributes the
zeroth-order term `B ∫ ψ² w²`, which is why the bound depends on `B R²`. This is the case `E = 0`
of `exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoliAboveLinear`. -/
theorem exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoli
    [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2} {k A B : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ}
      (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))),
      let U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
      let uU : W1p mu U 2 := W1p.restrictL hball u
      0 ≤ A → 0 ≤ B → 0 < R →
      CaccioppoliAbove uU k A B →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * (1 + A + B * R ^ 2) ^ Fintype.card ι *
          R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨D, hD, hmain⟩ :=
    exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoliAboveLinear
      (mu := mu)
  refine ⟨D, hD, fun hball hA hB hR hcacc => ?_⟩
  simpa only [add_zero] using hmain hball hA hB le_rfl hR hcacc.caccioppoliAboveLinear

/-- **From one-sided to two-sided local bounds.** If `u ∈ H¹(Ω)` and `-u` both satisfy the
one-sided local bound above the level `0` on `B(x₀, R) ⊆ Ω` with the same constant `K ≥ 0`, that
is `±u ≤ K ‖(±u)⁺‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`, then

`|u| ≤ K ‖u‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`.

This is how local boundedness of weak subsolutions gives local boundedness of weak solutions of
linear equations, for which `u` and `-u` are both subsolutions. -/
theorem ae_abs_value_le_mul_sqrt_setIntegral_of_ae_value_le
    {u : W1p mu Omega 2} {x₀ : EuclideanSpace ℝ ι} {R K : ℝ} (hK : 0 ≤ K)
    (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)))
    (hpos : ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)), W1p.value u x ≤
      K * √(∫ x in Metric.ball x₀ R, max (W1p.value u x) 0 ^ 2 ∂mu))
    (hneg : ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)), W1p.value (-u) x ≤
      K * √(∫ x in Metric.ball x₀ R, max (W1p.value (-u) x) 0 ^ 2 ∂mu)) :
    ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
      |W1p.value u x| ≤ K * √(∫ x in Metric.ball x₀ R, W1p.value u x ^ 2 ∂mu) := by
  -- The square of the positive part of a square-integrable function is dominated by its square.
  have hsq : ∀ w : W1p mu Omega 2,
      ∫ x in Metric.ball x₀ R, max (W1p.value w x) 0 ^ 2 ∂mu ≤
        ∫ x in Metric.ball x₀ R, W1p.value w x ^ 2 ∂mu := fun w => by
    refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
      ((Lp.memLp (W1p.value w)).mono_measure (Measure.restrict_mono hball le_rfl)).integrable_sq
      (ae_of_all _ fun x => ?_)
    calc max (W1p.value w x) 0 ^ 2 ≤ |W1p.value w x| ^ 2 :=
          pow_le_pow_left₀ (le_max_right _ _) (max_le (le_abs_self _) (abs_nonneg _)) 2
      _ = W1p.value w x ^ 2 := sq_abs _
  -- `-u` has the same `L²` norm on the ball.
  have hneg_ae := W1p.value_neg_ae u
  have hint : ∫ x in Metric.ball x₀ R, W1p.value (-u) x ^ 2 ∂mu =
      ∫ x in Metric.ball x₀ R, W1p.value u x ^ 2 ∂mu := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hball hneg_ae] with x hx
    rw [hx, Pi.neg_apply, neg_sq]
  have hhalf : Metric.ball x₀ (R / 2) ⊆ (Omega : Set (EuclideanSpace ℝ ι)) := fun x hx =>
    hball (Metric.mem_ball.2 (by linarith [Metric.mem_ball.1 hx, @dist_nonneg _ _ x x₀]))
  filter_upwards [hpos, hneg, ae_restrict_of_ae_restrict_of_subset hhalf hneg_ae]
    with x hx hx' hxn
  rw [hxn, Pi.neg_apply] at hx'
  have h₁ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hsq u)) hK
  have h₂ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hint ▸ hsq (-u))) hK
  rw [abs_le]
  constructor <;> linarith

/-! ### Local boundedness of weak subsolutions and solutions in `L²` -/

variable [DecidableEq ι] {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

/-- **De Giorgi's energy recursion for weak subsolutions.** Let `a` be measurable and uniformly
elliptic on `Ω` with constants `0 < λ ≤ Λ`, and suppose that `W^{1,2}_0(Ω)` satisfies a Sobolev
inequality `‖v‖_q ≤ S ‖∇v‖₂` for some exponent `q ≥ 2`. Let `u ∈ H¹(Ω)` be a weak subsolution of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`. Take levels
`k < l` with `(u - k)⁺ ∈ L²(Ω)`, and a smooth `ψ` compactly supported in `Ω` with
`‖∇ψ‖ ≤ G`. Then, writing `I = ∫_{Ω ∩ supp ψ} ((u - k)⁺)²`,

`∫_Ω ψ² ((u - l)⁺)² ≤ 2 (1 + (2Λ/λ)²) S² G² · I · (I / (l - k)²)^{1 - 2/q}`.

This is `TauCeti.PDE.setIntegral_sq_mul_max_sub_sq_le_of_caccioppoli` with the Caccioppoli
inequality for truncations of subsolutions. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_max_sub_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {q : ℝ≥0∞} (hq : 2 ≤ q) {S : ℝ≥0}
    (hS : ∀ v ∈ w1p0Submodule mu Omega 2,
      eLpNorm (W1p.value v) q (mu.restrict Omega) ≤ S * ‖W1p.gradient v‖ₑ)
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0)
    {k l : ℝ} (hkl : k < l)
    (hwLp : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict Omega))
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) {G : ℝ}
    (hG : ∀ x, ‖∇ ψ x‖ ≤ G) :
    ∫ x in Omega, ψ x ^ 2 * max (W1p.value u x - l) 0 ^ 2 ∂mu ≤
      2 * (1 + (2 * Lam / lam) ^ 2) * S ^ 2 * G ^ 2 *
        (∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
          max (W1p.value u x - k) 0 ^ 2 ∂mu) *
        ((∫ x in (Omega : Set (EuclideanSpace ℝ ι)) ∩ tsupport ψ,
          max (W1p.value u x - k) 0 ^ 2 ∂mu) / (l - k) ^ 2) ^ (1 - 2 / q.toReal) := by
  have hcacc := h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_nonpos ha hu
    (W1p.memLp_posPartAbove_of_le u hkl.le hwLp) hψ hcpt hts
  refine (setIntegral_sq_mul_max_sub_sq_le_of_caccioppoli hq hS hkl hwLp hψ hcpt hts hG
    (sq_nonneg (2 * Lam / lam)) (B := 0) ?_).trans_eq (by ring)
  simpa only [zero_mul, add_zero] using hcacc

/-- Weak subsolutions of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0` belong to De Giorgi's class above every level, with
`A = (2Λ/λ)²` and `B = 0`. -/
theorem UniformlyEllipticOn.caccioppoliAbove
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2,
      (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
        energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) (k : ℝ) :
    CaccioppoliAbove u k ((2 * Lam / lam) ^ 2) 0 := by
  refine .intro fun l _ hl ψ hψ hcpt hts => ?_
  rw [zero_mul, add_zero]
  exact h.setIntegral_sq_mul_norm_gradient_posPartAbove_sq_le_of_nonpos ha hu hl hψ hcpt hts

/-- **Local boundedness of weak subsolutions under a Sobolev inequality (De Giorgi).** Fix
ellipticity constants `λ, Λ` and an exponent `q > 2`, and let `α = 1 - 2/q`. There is `D > 0`,
depending only on these (and the dimension), such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, and let `u ∈ H¹(Ω)` be a weak
subsolution of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, that is `a(u, v) ≤ 0` for every nonnegative `v ∈ H¹₀(Ω)`.
If `B(x₀, R) ⊆ Ω` and `‖v‖_q ≤ S ‖∇v‖₂` for every `v ∈ W^{1,2}_0(B(x₀, R))`, then for every
level `k`,

`u ≤ k + D S^{1/α} R^{-1/α} (∫_{B(x₀, R)} ((u - k)⁺)²)^{1/2}` almost everywhere on `B(x₀, R/2)`.

The Sobolev inequality is only needed on the ball itself, so `S` may depend on the ball, and `D`
does not depend on `S`. This is what makes the bound scale-invariant: on `B(x₀, R)` the Sobolev
inequality for sets of finite measure holds with `S` a multiple of `R ^ (1 - n (1/2 - 1/q))`,
and `S^{1/α} R^{-1/α}` is then a multiple of `R^{-n/2}`; in every dimension that bound is
`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral`.

No regularity of the coefficients beyond measurability, and no boundary condition on `u`, is
assumed. Restricting `u` to the ball, which has finite measure, makes `(u - k)⁺` square
integrable. -/
theorem exists_ae_value_le_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral_of_forall_eLpNorm_le
    {q : ℝ≥0∞} (hq : 2 < q) :
    ∃ D : ℝ, 0 < D ∧ ∀ {S : ℝ≥0} {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ}, 0 < S →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ v ∈ w1p0Submodule mu ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩ 2,
        eLpNorm (W1p.value v) q (mu.restrict (Metric.ball x₀ R)) ≤ S * ‖W1p.gradient v‖ₑ) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * (S : ℝ) ^ (1 - 2 / q.toReal)⁻¹ * R ^ (-(1 - 2 / q.toReal)⁻¹) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨D, hD, hmain⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_rpow_mul_rpow_mul_sqrt_setIntegral_of_memLp (mu := mu) hq
  refine ⟨D * (1 + (2 * Lam / lam) ^ 2) ^ (2 * (1 - 2 / q.toReal))⁻¹, by positivity,
    fun {S Omega a u k x₀ R} hS0 h ha hu hR hball hS => ?_⟩
  set U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
  have hU : U ≤ Omega := hball
  have : IsFiniteMeasure (mu.restrict U) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  obtain ⟨hw, hint⟩ := value_restrictL_ae_ball_half_and_setIntegral_comp_eq u hball
    fun t => max (t - k) 0 ^ 2
  have hbound := hmain hS0 (sq_nonneg (2 * Lam / lam)) le_rfl le_rfl hS
    ((h.mono_set hball).caccioppoliAbove (ha.mono_measure (Measure.restrict_mono hball le_rfl))
      (energyFormH1_restrictL_nonpos hU hu) k).caccioppoliAboveLinear
    ((Lp.memLp _).sub (memLp_const k)).pos_part hR subset_rfl
  filter_upwards [hbound, hw] with x hx hwx
  rw [mul_zero, add_zero, zero_mul, add_zero] at hx
  rwa [← hwx, ← hint]

/-- **Local boundedness of weak subsolutions (De Giorgi).** In every dimension `n ≥ 1` there is
`D > 0`, depending on `λ`, `Λ`, the dimension and the normalization of the additive Haar measure
`mu`, such that for every measurable, uniformly elliptic `a` on `Ω` with constants `λ, Λ`, every
weak subsolution `u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, every level `k` and every ball
`B(x₀, R) ⊆ Ω`,

`u ≤ k + D R^{-n/2} (∫_{B(x₀, R)} ((u - k)⁺)²)^{1/2}` almost everywhere on `B(x₀, R/2)`.

This is `TauCeti.PDE.exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoli`
with the Caccioppoli inequality for truncations of subsolutions, which holds at every level with
`A = (2Λ/λ)²` and `B = 0`. -/
theorem exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ 2 ∂mu) := by
  obtain ⟨D, hD, hmain⟩ :=
    exists_ae_value_le_add_mul_pow_mul_rpow_mul_sqrt_setIntegral_of_caccioppoli (mu := mu)
  refine ⟨D * (1 + (2 * Lam / lam) ^ 2) ^ Fintype.card ι, by positivity,
    fun {Omega a u k x₀ R} h ha hu hR hball => ?_⟩
  have hU : (⟨Metric.ball x₀ R, Metric.isOpen_ball⟩ : Opens (EuclideanSpace ℝ ι)) ≤ Omega :=
    hball
  have hbound := hmain (k := k) hball (sq_nonneg (2 * Lam / lam)) le_rfl hR
    ((h.mono_set hball).caccioppoliAbove (ha.mono_measure (Measure.restrict_mono hball le_rfl))
      (energyFormH1_restrictL_nonpos hU hu) k)
  rwa [zero_mul, add_zero] at hbound

/-- **Local boundedness of weak solutions (De Giorgi).** In every dimension `n ≥ 1` there is
`D > 0`, depending on `λ`, `Λ`, the dimension and the normalization of the additive Haar measure
`mu`, such that for every measurable, uniformly elliptic `a` on `Ω` with constants `λ, Λ`, every
weak solution `u ∈ H¹(Ω)` of `-∂ᵢ(aⁱʲ ∂ⱼu) = 0`, that is `a(u, v) = 0` for every `v ∈ H¹₀(Ω)`,
and every ball `B(x₀, R) ⊆ Ω`,

`|u| ≤ D R^{-n/2} ‖u‖_{L²(B(x₀, R))}` almost everywhere on `B(x₀, R/2)`.

This is the two-sided form of `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral`,
obtained by applying it at the level `0` to the weak subsolutions `u` and `-u`. -/
theorem exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) = 0) →
      0 < R → Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        |W1p.value u x| ≤ D * R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, W1p.value u x ^ 2 ∂mu) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam) (Lam := Lam)
  refine ⟨D, hD, fun {Omega a u x₀ R} h ha hu hR hball => ?_⟩
  -- `-u` is a weak solution too.
  have hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 (-u) (v : W1p mu Omega 2) = 0 := fun v => by
    rw [energyFormH1_neg_left, hu v, neg_zero]
  exact ae_abs_value_le_mul_sqrt_setIntegral_of_ae_value_le (by positivity) hball
    (by simpa only [zero_add, sub_zero] using
      hbound (k := 0) h ha (fun v _ => (hu v).le) hR hball)
    (by simpa only [zero_add, sub_zero] using
      hbound (k := 0) h ha (fun v _ => (hu' v).le) hR hball)

end L2

/-! ### Local boundedness in terms of `Lᵖ` norms -/

section SubsolutionLp

variable [mu.IsAddHaarMeasure]

/-- **Transfer of local `L²` bounds above a level to `Lᵖ` bounds.** Fix `e`, `D ≥ 0` and
`0 < p ≤ 2`. There is `C > 0` such that for every `u ∈ H¹(Ω)`, every level `k` and every ball
`B(x₀, R) ⊆ Ω`, if `u ≤ k + D sᵉ ‖(u - k)⁺‖_{L²(B(y, s))}` almost everywhere on `B(y, s/2)` for
every ball `B(y, s) ⊆ B(x₀, R)`, then

`u ≤ k + C R^{2e/p} (∫_{B(x₀, R)} ((u - k)⁺)ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`.

This is `TauCeti.exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball` applied to
`(u - k)⁺`. -/
theorem exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_ball (e : ℝ)
    (D : ℝ) (hD : 0 ≤ D) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      (∀ y s, 0 < s → Metric.ball y s ⊆ Metric.ball x₀ R →
        ∀ᵐ x ∂mu.restrict (Metric.ball y (s / 2)),
          W1p.value u x ≤ k + D * s ^ e *
            √(∫ x in Metric.ball y s, max (W1p.value u x - k) 0 ^ 2 ∂mu)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + C * R ^ (2 * e / p) *
          (∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨C, hC, hmain⟩ :=
    exists_ae_le_mul_rpow_mul_setIntegral_rpow_of_forall_ball (mu := mu) e D hp hp2
  refine ⟨C, hC, fun {Omega u k x₀ R} hball hu => ?_⟩
  have : IsFiniteMeasure (mu.restrict (Metric.ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hw2 : MemLp (fun x => max (W1p.value u x - k) 0) 2 (mu.restrict (Metric.ball x₀ R)) :=
    (((Lp.memLp (W1p.value u)).mono_measure (Measure.restrict_mono hball le_rfl)).sub
      (memLp_const k)).pos_part
  filter_upwards [hmain (fun x => le_max_right _ _) hw2 fun y s hs hsub =>
    (hu y s hs hsub).mono fun x hx =>
      max_le (by linarith) (by positivity)] with x hx
  linarith [le_max_left (W1p.value u x - k) 0]

variable [DecidableEq ι] {lam Lam : ℝ}

/-- **Local boundedness of weak subsolutions in `Lᵖ` under a Sobolev inequality (De Giorgi).**
Fix ellipticity constants `λ, Λ`, an exponent `q > 2`, a constant `S` and `0 < p ≤ 2`. There is
`D > 0`, depending only on these (and the dimension), such that the following holds. Let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, suppose that `‖v‖_q ≤ S ‖∇v‖₂`
for every `v ∈ W^{1,2}_0(B)` and every ball `B ⊆ Ω`, and let `u ∈ H¹(Ω)` be a weak subsolution
of `-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`. Then for every level `k` and every ball `B(x₀, R) ⊆ Ω`,

`u ≤ k + D R^{-2/(α p)} (∫_{B(x₀, R)} ((u - k)⁺)ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`,

where `α = 1 - 2/q`. It follows from
`TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral_of_forall_eLpNorm_le`
on every ball inside `Ω`, which is why the Sobolev inequality is assumed on all of them. -/
theorem exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_eLpNorm_le {q : ℝ≥0∞}
    (hq : 2 < q) (S : ℝ≥0) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ y s, Metric.ball y s ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
        ∀ v ∈ w1p0Submodule mu ⟨Metric.ball y s, Metric.isOpen_ball⟩ 2,
          eLpNorm (W1p.value v) q (mu.restrict (Metric.ball y s)) ≤ S * ‖W1p.gradient v‖ₑ) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(2 * (1 - 2 / q.toReal)⁻¹ / p)) *
          (∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_rpow_mul_sqrt_setIntegral_of_forall_eLpNorm_le (mu := mu)
      (lam := lam) (Lam := Lam) hq
  -- Enlarge `S` to the positive constant `S + 1`.
  obtain ⟨C, hC, hmain⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_ball (mu := mu)
      (-(1 - 2 / q.toReal)⁻¹) (D * ((S + 1 : ℝ≥0) : ℝ) ^ (1 - 2 / q.toReal)⁻¹)
      (by positivity) hp hp2
  refine ⟨C, hC, fun {Omega a u k x₀ R} h ha hS hu hball => ?_⟩
  have := hmain (u := u) (k := k) hball fun y s hs hsub =>
    hbound (S := S + 1) (by positivity) h ha hu hs (hsub.trans hball) fun v hv =>
      (hS y s (hsub.trans hball) v hv).trans (by gcongr; exact le_self_add)
  rwa [mul_neg, neg_div] at this

/-- **Local boundedness of weak subsolutions in `Lᵖ` (De Giorgi).** Let `0 < p ≤ 2`. In every
dimension `n ≥ 1` there is `D > 0`, depending on `λ`, `Λ`, `p`, the dimension and the
normalization of the additive Haar measure `mu`, such that for every measurable, uniformly
elliptic `a` on `Ω` with constants `λ, Λ`, every weak subsolution `u ∈ H¹(Ω)` of
`-∂ᵢ(aⁱʲ ∂ⱼu) ≤ 0`, every level `k` and every ball `B(x₀, R) ⊆ Ω`,

`u ≤ k + D R^{-n/p} (∫_{B(x₀, R)} ((u - k)⁺)ᵖ)^{1/p}` almost everywhere on `B(x₀, R/2)`.

At `p = 2` this is `TauCeti.PDE.exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral`; small
`p` is the form in which local boundedness enters Moser's Harnack inequality. -/
theorem exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow [Nonempty ι] {p : ℝ} (hp : 0 < p)
    (hp2 : p ≤ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      (∀ v : W1p0 mu Omega 2,
        (∀ᵐ x ∂mu.restrict Omega, 0 ≤ W1p.value (v : W1p mu Omega 2) x) →
          energyFormH1 a 0 0 u (v : W1p mu Omega 2) ≤ 0) →
      Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι)) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(Fintype.card ι : ℝ) / p) *
          (∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam) (Lam := Lam)
  obtain ⟨C, hC, hmain⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_forall_ball (mu := mu)
      (-(Fintype.card ι : ℝ) / 2) D hD.le hp hp2
  refine ⟨C, hC, fun {Omega a u k x₀ R} h ha hu hball => ?_⟩
  have := hmain (u := u) (k := k) hball fun y s hs hsub => hbound h ha hu hs (hsub.trans hball)
  rwa [show 2 * (-(Fintype.card ι : ℝ) / 2) / p = -(Fintype.card ι : ℝ) / p by ring] at this

/-- **Local boundedness with hypotheses only on the ball.** For every `0 < p ≤ 2` and every
positive dimension,
the coefficients need be elliptic and measurable only on `B(x₀, R)`, and the restriction of
`u` to that ball need be a weak subsolution only there. The bound applies to the original
ambient-domain representative of `u`; its constant is independent of the radius. -/
theorem exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow_of_local_subsolution
    [Nonempty ι] {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2} {k : ℝ}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ}
      (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))),
      let U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
      let uU : W1p mu U 2 := W1p.restrictL hball u
      UniformlyEllipticOn (Metric.ball x₀ R) a lam Lam →
      AEStronglyMeasurable a (mu.restrict (Metric.ball x₀ R)) →
      (∀ v : W1p0 mu U 2,
        (∀ᵐ x ∂mu.restrict U, 0 ≤ W1p.value (v : W1p mu U 2) x) →
          energyFormH1 a 0 0 uU (v : W1p mu U 2) ≤ 0) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        W1p.value u x ≤ k + D * R ^ (-(Fintype.card ι : ℝ) / p) *
          (∫ x in Metric.ball x₀ R, max (W1p.value u x - k) 0 ^ p ∂mu) ^ p⁻¹ := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_value_le_add_mul_rpow_mul_setIntegral_rpow (mu := mu)
      (lam := lam) (Lam := Lam) hp hp2
  refine ⟨D, hD, ?_⟩
  intro Omega a u k x₀ R hball U uU h ha hu
  obtain ⟨hw, hint⟩ := value_restrictL_ae_ball_half_and_setIntegral_comp_eq u hball
    fun t => max (t - k) 0 ^ p
  filter_upwards [hbound (u := uU) (k := k) h ha hu Subset.rfl, hw] with x hx hwx
  rwa [← hwx, ← hint]

/-- **The two-sided local bound with hypotheses only on the ball.** A weak solution after
restriction to `B(x₀, R)` satisfies the scale-invariant absolute-value estimate on its half
ball, without ellipticity, measurability or the equation being required outside the ball. -/
theorem exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral_of_local_solution
    [Nonempty ι] :
    ∃ D : ℝ, 0 < D ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {u : W1p mu Omega 2}
      {x₀ : EuclideanSpace ℝ ι} {R : ℝ}
      (hball : Metric.ball x₀ R ⊆ (Omega : Set (EuclideanSpace ℝ ι))),
      let U : Opens (EuclideanSpace ℝ ι) := ⟨Metric.ball x₀ R, Metric.isOpen_ball⟩
      let uU : W1p mu U 2 := W1p.restrictL hball u
      UniformlyEllipticOn (Metric.ball x₀ R) a lam Lam →
      AEStronglyMeasurable a (mu.restrict (Metric.ball x₀ R)) →
      (∀ v : W1p0 mu U 2, energyFormH1 a 0 0 uU (v : W1p mu U 2) = 0) →
      ∀ᵐ x ∂mu.restrict (Metric.ball x₀ (R / 2)),
        |W1p.value u x| ≤ D * R ^ (-(Fintype.card ι : ℝ) / 2) *
          √(∫ x in Metric.ball x₀ R, W1p.value u x ^ 2 ∂mu) := by
  obtain ⟨D, hD, hbound⟩ :=
    exists_ae_abs_value_le_mul_rpow_mul_sqrt_setIntegral (mu := mu) (lam := lam) (Lam := Lam)
  refine ⟨D, hD, ?_⟩
  intro Omega a u x₀ R hball U uU h ha hu
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.2 (by linarith : R / 2 ≤ 0)]
  obtain ⟨hw, hint⟩ := value_restrictL_ae_ball_half_and_setIntegral_comp_eq u hball (· ^ 2)
  filter_upwards [hbound (u := uU) h ha hu hR Subset.rfl, hw] with x hx hwx
  rwa [← hwx, ← hint]

end SubsolutionLp

end PDE

end TauCeti
