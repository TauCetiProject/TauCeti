/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Zero
public import Mathlib.Topology.Algebra.Module.LinearPMap

import TauCeti.Analysis.InnerProductSpace.Laplacian.DriftMaximumPrinciple

/-!
# The weak gradient as a closed unbounded operator on `Lᵖ`

This file realizes the weak gradient as a partially defined operator

`∇ : Lᵖ(Ω) →ₗ.[ℝ] Lᵖ(Ω; E)`

whose domain is the value range of the first-order Sobolev space `W^{1,p}(Ω)` and whose graph is
the set of value-gradient pairs `(u, ∇u)` of its elements. This is the operator-theoretic form of
the Sobolev space: `W^{1,p}(Ω)` is the domain of the weak gradient with its graph norm. For
`Ω = (0, 1) ⊆ ℝ` and `p = 2` it is the derivative `D f = f'` on `L²(0, 1)` with domain `H¹(0, 1)`
and no boundary condition.

The three basic properties of this operator are proved here.

* It is closed, for every `1 ≤ p ≤ ∞`: if `uₙ → u` and `∇uₙ → g` in `Lᵖ`, then `u ∈ W^{1,p}(Ω)`
  with `∇u = g`. The graph is the range of the value-gradient map from the complete space
  `W^{1,p}(Ω)`, which is bounded below since the Sobolev norm is at most the sum of the two
  component norms.
* At `p = 2` it is densely defined, since its domain contains the test functions.
* On a bounded nonempty domain in a nonzero space it is unbounded: for a unit vector `w` the
  exponential `x ↦ exp (c ⟪w, x⟫)` lies in the domain and its gradient has `Lᵖ` norm exactly
  `|c|` times its own.

## Main declarations

* `TauCeti.weakGradientPMap`: the weak gradient as a partially defined linear operator.
* `TauCeti.mem_graph_weakGradientPMap_iff`, `TauCeti.mem_domain_weakGradientPMap_iff`,
  `TauCeti.weakGradientPMap_apply` and `TauCeti.weakGradientPMap_apply_value`: its graph, its
  domain and its values.
* `TauCeti.isClosed_weakGradientPMap`: the weak gradient is a closed operator.
* `TauCeti.dense_domain_weakGradientPMap`: it is densely defined on `L²(Ω)`.
* `TauCeti.W1p.exists_value_gradient_ae_eq_exp_inner`: exponentials of linear functions are
  Sobolev functions on bounded domains, with their classical gradients.
* `TauCeti.norm_weakGradientPMap_exp_inner`: the `Lᵖ` norm identity for those exponentials.
* `TauCeti.not_exists_norm_weakGradientPMap_le`: the weak gradient is not bounded on `Lᵖ(Ω)`.

## References

H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.2 and
§9.1, for the space `H¹(0, 1)` as the domain of the weak derivative; T. Kato, *Perturbation
Theory for Linear Operators*, §III.5, for closed operators.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace Gradient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)]

/-! ### The weak gradient operator -/

/-- The value-gradient map `u ↦ (u, ∇u)` from `W^{1,p}(Ω)` to `Lᵖ(Ω) × Lᵖ(Ω; E)`. Its range is
the graph of the weak gradient. -/
private def valueGradientL :
    W1p mu Omega p →L[ℝ] Lp ℝ p (mu.restrict Omega) × Lp E p (mu.restrict Omega) :=
  W1p.valueL.prod W1p.gradientL

omit [FiniteDimensional ℝ E] in
private theorem valueGradientL_apply (u : W1p mu Omega p) :
    valueGradientL u = (W1p.value u, W1p.gradient u) := by
  rw [valueGradientL, ContinuousLinearMap.prod_apply, W1p.valueL_apply, W1p.gradientL_apply]

/-- The range of the value-gradient map is the graph of a linear operator: a Sobolev function
with zero value is zero. -/
private theorem snd_eq_zero_of_mem_range_valueGradientL
    (x : Lp ℝ p (mu.restrict Omega) × Lp E p (mu.restrict Omega))
    (hx : x ∈ LinearMap.range
      (valueGradientL (mu := mu) (Omega := Omega) (p := p) : W1p mu Omega p →ₗ[ℝ] _))
    (hx0 : x.1 = 0) : x.2 = 0 := by
  obtain ⟨u, rfl⟩ := hx
  rw [ContinuousLinearMap.coe_coe, valueGradientL_apply] at hx0 ⊢
  have hu : u = 0 := W1p.ext_value <| by
    rw [← W1p.valueL_apply (0 : W1p mu Omega p), map_zero]
    exact hx0
  rw [hu, ← W1p.gradientL_apply, map_zero]

variable (mu Omega p) in
/-- **The weak gradient as an unbounded operator** `Lᵖ(Ω) →ₗ.[ℝ] Lᵖ(Ω; E)`. Its domain consists of
the `Lᵖ` classes of the elements of `W^{1,p}(Ω)`, and it sends such a class to its weak
gradient. -/
def weakGradientPMap : Lp ℝ p (mu.restrict Omega) →ₗ.[ℝ] Lp E p (mu.restrict Omega) :=
  (LinearMap.range
    (valueGradientL (mu := mu) (Omega := Omega) (p := p) : W1p mu Omega p →ₗ[ℝ] _)).toLinearPMap

private theorem graph_weakGradientPMap :
    (weakGradientPMap mu Omega p).graph =
      LinearMap.range
        (valueGradientL (mu := mu) (Omega := Omega) (p := p) : W1p mu Omega p →ₗ[ℝ] _) :=
  Submodule.toLinearPMap_graph_eq _ snd_eq_zero_of_mem_range_valueGradientL

/-- The graph of the weak gradient consists of the value-gradient pairs of the elements of
`W^{1,p}(Ω)`. -/
theorem mem_graph_weakGradientPMap_iff
    {x : Lp ℝ p (mu.restrict Omega) × Lp E p (mu.restrict Omega)} :
    x ∈ (weakGradientPMap mu Omega p).graph ↔
      ∃ u : W1p mu Omega p, W1p.value u = x.1 ∧ W1p.gradient u = x.2 := by
  rw [graph_weakGradientPMap, LinearMap.mem_range]
  simp only [ContinuousLinearMap.coe_coe, valueGradientL_apply, Prod.ext_iff]

/-- The domain of the weak gradient is the value range of `W^{1,p}(Ω)`. -/
theorem mem_domain_weakGradientPMap_iff {f : Lp ℝ p (mu.restrict Omega)} :
    f ∈ (weakGradientPMap mu Omega p).domain ↔ ∃ u : W1p mu Omega p, W1p.value u = f := by
  rw [LinearPMap.mem_domain_iff]
  simp only [mem_graph_weakGradientPMap_iff]
  exact ⟨fun ⟨_, u, hu, _⟩ => ⟨u, hu⟩, fun ⟨u, hu⟩ => ⟨_, u, hu, rfl⟩⟩

/-- The value of a Sobolev function lies in the domain of the weak gradient. -/
@[simp]
theorem value_mem_domain_weakGradientPMap (u : W1p mu Omega p) :
    W1p.value u ∈ (weakGradientPMap mu Omega p).domain :=
  mem_domain_weakGradientPMap_iff.2 ⟨u, rfl⟩

/-- The weak gradient operator sends a domain element represented by a Sobolev function `u` to
the weak gradient of `u`. -/
theorem weakGradientPMap_apply {f : (weakGradientPMap mu Omega p).domain} {u : W1p mu Omega p}
    (h : W1p.value u = f) : weakGradientPMap mu Omega p f = W1p.gradient u := by
  obtain ⟨v, hv, hgrad⟩ :=
    mem_graph_weakGradientPMap_iff.1 (LinearPMap.mem_graph (weakGradientPMap mu Omega p) f)
  rw [← W1p.ext_value (hv.trans h.symm)]
  exact hgrad.symm

/-- The weak gradient operator sends the value of a Sobolev function to its weak gradient. -/
@[simp]
theorem weakGradientPMap_apply_value (u : W1p mu Omega p) :
    weakGradientPMap mu Omega p ⟨W1p.value u, value_mem_domain_weakGradientPMap u⟩ =
      W1p.gradient u :=
  weakGradientPMap_apply rfl

/-- **The weak gradient is a closed operator.** If `uₙ → u` in `Lᵖ(Ω)` with `uₙ ∈ W^{1,p}(Ω)` and
`∇uₙ → g` in `Lᵖ(Ω; E)`, then `u ∈ W^{1,p}(Ω)` and `∇u = g`. -/
theorem isClosed_weakGradientPMap : (weakGradientPMap mu Omega p).IsClosed := by
  let T := valueGradientL (mu := mu) (Omega := Omega) (p := p)
  have hbound : ∀ u : W1p mu Omega p, ‖u‖ ≤ (2 : NNReal) * ‖T u‖ := fun u => by
    rw [valueGradientL_apply]
    have hvalue := norm_fst_le (W1p.value u, W1p.gradient u)
    have hgradient := norm_snd_le (W1p.value u, W1p.gradient u)
    have := W1p.norm_le_norm_value_add_norm_gradient u
    push_cast
    linarith
  rw [LinearPMap.IsClosed, graph_weakGradientPMap, LinearMap.coe_range]
  exact (T.antilipschitz_of_bound hbound).isClosed_range T.uniformContinuous

/-- **The weak gradient is densely defined on `L²(Ω)`**: its domain contains the test
functions, which are dense. -/
theorem dense_domain_weakGradientPMap :
    Dense ((weakGradientPMap mu Omega 2).domain : Set (Lp ℝ 2 (mu.restrict Omega))) := by
  refine (W1p0.denseRange_valueL_two (mu := mu) (Omega := Omega)).mono ?_
  rintro _ ⟨u, rfl⟩
  rw [W1p0.valueL_apply]
  exact value_mem_domain_weakGradientPMap _

/-! ### Exponentials and unboundedness -/

/-- **Exponentials of linear functions are Sobolev functions on a bounded domain.** For `w : E` and
`c : ℝ`, the function `x ↦ exp (c ⟪w, x⟫)` is represented by an element of `W^{1,p}(Ω)` whose
weak gradient is its classical gradient `x ↦ (c exp (c ⟪w, x⟫)) • w`. -/
theorem W1p.exists_value_gradient_ae_eq_exp_inner (hΩ : Bornology.IsBounded (Omega : Set E))
    (w : E) (c : ℝ) :
    ∃ u : W1p mu Omega p,
      W1p.value u =ᵐ[mu.restrict Omega] (fun x => Real.exp (c * ⟪w, x⟫_ℝ)) ∧
      W1p.gradient u =ᵐ[mu.restrict Omega] fun x => (c * Real.exp (c * ⟪w, x⟫_ℝ)) • w := by
  have hcd : ContDiff ℝ 1 fun x : E => Real.exp (c * ⟪w, x⟫_ℝ) :=
    (contDiff_exp_inner c w).of_le (by exact_mod_cast le_top)
  simpa only [funext (gradient_exp_inner c w)] using
    W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := mu) (p := p) isOpen_univ
      hcd.contDiffOn hΩ.isCompact_closure subset_closure (subset_univ _)

/-- **The weak gradient scales the exponentials of linear functions.** On a bounded domain, if
`u ∈ W^{1,p}(Ω)` represents `x ↦ exp (c ⟪w, x⟫)` for a unit vector `w`, then the weak gradient
of `u` has `Lᵖ` norm `|c|` times that of `u`. -/
theorem norm_weakGradientPMap_exp_inner (hΩ : Bornology.IsBounded (Omega : Set E)) {w : E}
    (hw : ‖w‖ = 1) {c : ℝ} {u : W1p mu Omega p}
    (hu : W1p.value u =ᵐ[mu.restrict Omega] fun x => Real.exp (c * ⟪w, x⟫_ℝ)) :
    ‖weakGradientPMap mu Omega p ⟨W1p.value u, value_mem_domain_weakGradientPMap u⟩‖ =
      |c| * ‖W1p.value u‖ := by
  rw [weakGradientPMap_apply_value]
  obtain ⟨v, hv, hgv⟩ := W1p.exists_value_gradient_ae_eq_exp_inner (mu := mu) (p := p) hΩ w c
  rw [← W1p.ext_value (Lp.ext (hv.trans hu.symm))]
  have hpoint : ∀ᵐ x ∂mu.restrict Omega, ‖W1p.gradient v x‖ = |c| * ‖W1p.value v x‖ := by
    filter_upwards [hv, hgv] with x hx hgx
    rw [hx, hgx, norm_smul, hw, mul_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  refine le_antisymm (Lp.norm_le_mul_norm_of_ae_le_mul (hpoint.mono fun x hx => hx.le)) ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc' : 0 < |c| := abs_pos.2 hc
  have hle : ‖W1p.value v‖ ≤ |c|⁻¹ * ‖W1p.gradient v‖ :=
    Lp.norm_le_mul_norm_of_ae_le_mul <| hpoint.mono fun x hx => by
      rw [hx, ← mul_assoc, inv_mul_cancel₀ hc'.ne', one_mul]
  calc |c| * ‖W1p.value v‖ ≤ |c| * (|c|⁻¹ * ‖W1p.gradient v‖) := by gcongr
    _ = ‖W1p.gradient v‖ := by rw [← mul_assoc, mul_inv_cancel₀ hc'.ne', one_mul]

/-- **The weak gradient is unbounded.** On a bounded nonempty domain in a nonzero space, there is
no constant `C` with `‖∇f‖_p ≤ C ‖f‖_p` for every `f` in the domain of the weak gradient: the
exponential `x ↦ exp ((|C| + 1) ⟪w, x⟫)` along a unit vector `w` violates it. -/
theorem not_exists_norm_weakGradientPMap_le [Nontrivial E]
    (hΩ : Bornology.IsBounded (Omega : Set E)) (hne : (Omega : Set E).Nonempty) :
    ¬ ∃ C : ℝ, ∀ f : (weakGradientPMap mu Omega p).domain,
      ‖weakGradientPMap mu Omega p f‖ ≤ C * ‖(f : Lp ℝ p (mu.restrict Omega))‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨w, hw⟩ := exists_norm_eq E zero_le_one
  set c := |C| + 1
  obtain ⟨u, hu, -⟩ := W1p.exists_value_gradient_ae_eq_exp_inner (mu := mu) (p := p) hΩ w c
  have hnorm := norm_weakGradientPMap_exp_inner hΩ hw hu
  have hbound := hC ⟨W1p.value u, value_mem_domain_weakGradientPMap u⟩
  rw [hnorm] at hbound
  have hvalue : W1p.value u ≠ 0 := by
    intro hzero
    have : (ae (mu.restrict (Omega : Set E))).NeBot :=
      ae_restrict_neBot.2 (Omega.isOpen.measure_pos mu hne).ne'
    obtain ⟨x, hx, hx0⟩ := (hu.and (Lp.coeFn_zero ℝ p (mu.restrict Omega))).exists
    rw [hzero] at hx
    exact (Real.exp_pos _).ne' (hx.symm.trans hx0)
  have hpos : 0 < ‖W1p.value u‖ := norm_pos_iff.2 hvalue
  have habs : |c| = |C| + 1 := abs_of_pos (by positivity)
  rw [habs] at hbound
  nlinarith [le_abs_self C]

end TauCeti
