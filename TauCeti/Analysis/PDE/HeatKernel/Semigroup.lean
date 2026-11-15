/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity
public import TauCeti.Analysis.Semigroups.Basic
public import TauCeti.MeasureTheory.Function.Lp.Convolution
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The heat semigroup on `Lᵖ`

On a finite-dimensional real inner product space `E` of dimension `n`, convolution with the heat
kernel `K_t(x) = (4πt)^(-n/2) exp(-‖x‖² / (4t))` defines, for `1 ≤ p < ∞`, the **heat
semigroup** `e^{tΔ}` on `Lᵖ(E; F)` with values in a real Banach space `F`:

`e^{tΔ} f = K_t ⋆ f = ∫ y, K_t(y) • f(· - y) dy` for `t > 0`, and `e^{0Δ} f = f`.

This file proves that it is a **strongly continuous contraction semigroup**:

* each `e^{tΔ}` is a contraction of `Lᵖ`, by Young's inequality, because `K_t ≥ 0` has mass one;
* `e^{(s+t)Δ} = e^{sΔ} e^{tΔ}`, from the Chapman–Kolmogorov identity `K_s ⋆ K_t = K_{s+t}` and
  associativity of convolution on `Lᵖ`;
* `e^{tΔ} f → f` in `Lᵖ` as `t → 0⁺`: the heat kernel is an approximate identity, applied to the
  continuous bounded `Lᵖ`-valued orbit `y ↦ f(· + y)` of translations.

It also proves that the semigroup is **positivity preserving** on real `Lᵖ`, since `K_t > 0`, and
**mass preserving** on `L¹`, `∫ e^{tΔ} f = ∫ f`, since `K_t` has mass one; so on nonnegative
functions it preserves the `L¹` norm.

For `t > 0` the class `e^{tΔ} f` is represented almost everywhere by the classical convolution
`K_t ⋆ f`; for essentially bounded `f`, `TauCeti.hasDerivAt_heatKernel_convolution` shows that
this convolution is smooth and solves the heat equation pointwise. The generator of the
semigroup, the Laplacian on `Lᵖ` with its natural domain, is not identified in this file.

The restriction `p < ∞` is essential: on `L^∞` the operators are still contractions, but the
semigroup is not strongly continuous at `0`.

## Main declarations

* `TauCeti.tendsto_convolutionLp_heatKernel`: `K_t ⋆ f → f` in `Lᵖ` as `t → 0⁺`.
* `TauCeti.heatSemigroup`: the heat semigroup on `Lᵖ`, as a `ContractionSemigroup`.
* `TauCeti.heatSemigroup_apply`, `TauCeti.heatSemigroup_apply_apply`: for `t ≠ 0`, the operator
  at time `t` is convolution with `K_t`.
* `TauCeti.heatSemigroup_zero`: the operator at time `0` is the identity.
* `TauCeti.heatSemigroup_ae_eq_convolution`: for `t ≠ 0`, `e^{tΔ} f` is represented almost
  everywhere by the classical convolution `K_t ⋆ f`.
* `TauCeti.heatSemigroup_nonneg`, `TauCeti.heatSemigroup_mono`: the semigroup preserves
  positivity and order.
* `TauCeti.integral_heatSemigroup`: the semigroup preserves the integral on `L¹`.
* `TauCeti.norm_heatSemigroup_of_nonneg`: it preserves the `L¹` norm of nonnegative functions.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.3.1.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup).
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Semigroups Topology
open scoped Convolution ENNReal NNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The heat kernel is an approximate identity on `Lᵖ`.** For `1 ≤ p < ∞` and `f ∈ Lᵖ`,
`K_t ⋆ f → f` in `Lᵖ` as `t → 0⁺`. -/
theorem tendsto_convolutionLp_heatKernel [CompleteSpace F] (hp : p ≠ ∞)
    (f : Lp F p (volume : Measure E)) :
    Tendsto (fun t : ℝ ↦ convolutionLp hp (heatKernel t) volume f) (𝓝[>] 0) (𝓝 f) := by
  -- Apply the pointwise approximate-identity theorem to the orbit of translations of `f`, a
  -- continuous `Lᵖ`-valued function of constant norm `‖f‖`, at the point `0`.
  set g : E → Lp F p (volume : Measure E) := fun y ↦ volume.translateLp p y f
  have hg : Continuous g := Measure.continuous_translateLp hp f
  have h := tendsto_heatKernel_convolution hg.aestronglyMeasurable
    (ae_of_all _ fun y ↦ (LinearIsometryEquiv.norm_map (volume.translateLp p y) f).le)
    (x₀ := 0) hg.continuousAt
  simp only [g, Measure.translateLp_zero] at h
  refine (h.comp (tendsto_id.prodMk tendsto_const_nhds)).congr'
    (eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) ↦ ?_)
  simp only [Function.comp_apply, id_eq, convolution_lsmul, zero_sub,
    convolutionLp_apply hp (integrable_heatKernel ht)]

/-- **The heat semigroup** `e^{tΔ}` on `Lᵖ(E; F)` for `1 ≤ p < ∞`: the identity at time `0`, and
convolution with the heat kernel `K_t` at time `t > 0` (`TauCeti.heatSemigroup_apply`). It is a
strongly continuous contraction semigroup. -/
def heatSemigroup [CompleteSpace F] (hp : p ≠ ∞) :
    ContractionSemigroup (Lp F p (volume : Measure E)) where
  toFun t := if t = 0 then .id ℝ _ else convolutionLp hp (heatKernel (t : ℝ)) volume
  map_zero' := ite_eq_left rfl
  map_add' s t := by
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    have hs' : 0 < (s : ℝ) := by positivity
    have ht' : 0 < (t : ℝ) := by positivity
    rw [ite_eq_right (add_pos (pos_iff_ne_zero.2 hs) (pos_iff_ne_zero.2 ht)).ne',
      ite_eq_right hs, ite_eq_right ht, NNReal.coe_add, ← heatKernel_convolution_heatKernel hs' ht',
      convolutionLp_convolution hp (integrable_heatKernel hs') (integrable_heatKernel ht')]
  continuousAt_zero' f := by
    rw [ContinuousAt, ite_eq_left rfl, ContinuousLinearMap.id_apply,
      ← nhdsNE_sup_pure]
    refine Tendsto.sup ?_ (tendsto_pure_left.2 fun s hs ↦ by simpa using mem_of_mem_nhds hs)
    -- Away from `t = 0` the operator is convolution with `K_t`, and `(t : ℝ) → 0⁺`.
    have hcoe : Tendsto ((↑) : ℝ≥0 → ℝ) (𝓝[≠] 0) (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨NNReal.continuous_coe.continuousWithinAt.tendsto.mono_right
        (by rw [NNReal.coe_zero]),
        eventually_nhdsWithin_of_forall fun t (ht : t ≠ 0) ↦ Set.mem_Ioi.2 (by positivity)⟩
    refine ((tendsto_convolutionLp_heatKernel hp f).comp hcoe).congr'
      (eventually_nhdsWithin_of_forall fun t (ht : t ≠ 0) ↦ ?_)
    dsimp only [Function.comp_apply]
    rw [ite_eq_right ht]
  contracting t := by
    split_ifs with ht
    · exact ContinuousLinearMap.norm_id_le
    · refine (norm_convolutionLp_le hp _).trans_eq ?_
      have ht' : 0 < (t : ℝ) := by positivity
      simp_rw [Real.norm_of_nonneg (heatKernel_pos ht' _).le, integral_heatKernel ht']

variable [CompleteSpace F]

/-- At time `0` the heat semigroup is the identity. -/
@[simp]
theorem heatSemigroup_zero (hp : p ≠ ∞) :
    heatSemigroup (E := E) (F := F) hp 0 = .id ℝ _ :=
  ite_eq_left rfl

/-- At a positive time `t` the heat semigroup is convolution with the heat kernel `K_t`. -/
theorem heatSemigroup_apply (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0) :
    heatSemigroup (E := E) (F := F) hp t = convolutionLp hp (heatKernel t) volume :=
  ite_eq_right ht

/-- At a positive time `t` the heat semigroup sends `f` to the `Lᵖ`-valued integral
`∫ y, K_t(y) • f(· - y) dy`. -/
theorem heatSemigroup_apply_apply (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0)
    (f : Lp F p (volume : Measure E)) :
    heatSemigroup hp t f = ∫ y, heatKernel t y • volume.translateLp p (-y) f := by
  rw [heatSemigroup_apply hp ht,
    convolutionLp_apply hp (integrable_heatKernel (by positivity))]

/-- At a positive time `t`, the heat semigroup applied to the class of `f ∈ Lᵖ` is represented
almost everywhere by the classical heat convolution `(K_t ⋆ f)(x) = ∫ y, K_t(y) • f(x - y) dy`. -/
theorem heatSemigroup_ae_eq_convolution (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0) {f : E → F}
    (hf : MemLp f p volume) : heatSemigroup hp t (hf.toLp f) =ᵐ[volume] heatKernel t ⋆ f := by
  rw [heatSemigroup_apply hp ht]
  exact convolutionLp_ae_eq_convolution hp
    (integrable_heatKernel (by positivity)) hf

/-- At a positive time `t`, the heat semigroup applied to `f : Lp` is represented almost
everywhere by convolution of the heat kernel with the chosen representative of `f`. -/
theorem heatSemigroup_ae_eq_convolution_coeFn (hp : p ≠ ∞) {t : ℝ≥0} (ht : t ≠ 0)
    (f : Lp F p (volume : Measure E)) :
    heatSemigroup hp t f =ᵐ[volume] heatKernel t ⋆ (f : E → F) := by
  simpa only [Lp.toLp_coeFn] using heatSemigroup_ae_eq_convolution hp ht (Lp.memLp f)

/-- **The heat semigroup preserves positivity.** If `f ∈ Lᵖ` is nonnegative almost everywhere,
so is `e^{tΔ} f`. -/
theorem heatSemigroup_nonneg (hp : p ≠ ∞) (t : ℝ≥0) {f : Lp ℝ p (volume : Measure E)}
    (hf : 0 ≤ f) : 0 ≤ heatSemigroup hp t f := by
  rcases eq_or_ne t 0 with rfl | ht
  · simpa using hf
  rw [heatSemigroup_apply hp ht]
  exact convolutionLp_nonneg hp (ae_of_all _ fun x ↦ (heatKernel_pos (by positivity) x).le) hf

/-- **The heat semigroup is monotone**: `f ≤ g` almost everywhere implies
`e^{tΔ} f ≤ e^{tΔ} g` almost everywhere. -/
theorem heatSemigroup_mono (hp : p ≠ ∞) (t : ℝ≥0) :
    Monotone (heatSemigroup (E := E) (F := ℝ) hp t) := fun f g hfg ↦ by
  simpa using heatSemigroup_nonneg hp t (sub_nonneg.2 hfg)

/-- **The heat semigroup preserves mass on `L¹`**: `∫ e^{tΔ} f = ∫ f` for `f ∈ L¹`. -/
@[simp]
theorem integral_heatSemigroup (t : ℝ≥0) (f : Lp F 1 (volume : Measure E)) :
    ∫ x, heatSemigroup ENNReal.one_ne_top t f x = ∫ x, f x := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have ht' : 0 < (t : ℝ) := by positivity
  rw [heatSemigroup_apply ENNReal.one_ne_top ht, integral_convolutionLp,
    integral_heatKernel ht', one_smul]

/-- On nonnegative functions the heat semigroup preserves the `L¹` norm: for `0 ≤ f ∈ L¹`,
`‖e^{tΔ} f‖₁ = ‖f‖₁`. -/
theorem norm_heatSemigroup_of_nonneg (t : ℝ≥0) {f : Lp ℝ 1 (volume : Measure E)} (hf : 0 ≤ f) :
    ‖heatSemigroup ENNReal.one_ne_top t f‖ = ‖f‖ := by
  rw [L1.norm_eq_integral_of_nonneg (heatSemigroup_nonneg ENNReal.one_ne_top t hf),
    L1.norm_eq_integral_of_nonneg hf, integral_heatSemigroup]

end TauCeti
