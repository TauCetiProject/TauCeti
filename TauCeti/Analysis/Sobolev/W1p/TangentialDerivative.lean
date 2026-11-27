/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.DifferenceQuotient
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
import TauCeti.Analysis.Sobolev.Wkp.StarConvex
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional
import TauCeti.MeasureTheory.Function.LpSeminorm.CompactExhaustion

/-!
# Tangential derivatives of Sobolev functions

Let `Ω` be an open set that every translation along a direction `τ` maps into itself, such as a
half-space `{x | c < ⟪x, ν⟫}` or a slab with `⟪τ, ν⟫ = 0`. Then the difference quotients
`t⁻¹ (u(· + t τ) - u)` of a Sobolev function `u` are again Sobolev functions on `Ω`, and those of a
function with zero boundary values have zero boundary values. This file shows that when `Ω` is
also convex they converge to the derivative `∂_τ u`, and deduces that the derivative of
`u ∈ W^{1,p}_0(Ω)` along `τ` has zero boundary values as soon as `u ∈ W^{2,p}(Ω)`. This is the step
that lets a regularity bootstrap for the Dirichlet problem on a half-space differentiate the
equation in the tangential directions: the derivative is again a solution with zero boundary
values.

* The difference quotients are bounded by the directional derivative on all of `Ω`:
  `‖t⁻¹ (u(· + t τ) - u)‖_{Lᵖ(Ω)} ≤ ‖⟪τ, ∇u⟫‖_{Lᵖ(Ω)}`
  (`TauCeti.W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le_of_mapsTo`), from the local estimate on
  compact sets.
* They converge to `⟪τ, ∇u⟫` in `Lᵖ(Ω)` for `1 ≤ p < ∞`
  (`TauCeti.W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_gradient`). For
  restrictions of test functions on the whole space this is the Taylor estimate
  `HasCompactSupport.tendsto_eLpNorm_inv_smul_comp_add_smul_sub_sub_fderiv`; these restrictions are
  dense in `W^{1,p}(Ω)` on a convex domain
  (`TauCeti.Wkp.denseRange_restrictL_ofTestFunctionₗ_top_of_convex`), and the uniform bound above
  passes the convergence to every `u`.
* If `u ∈ W^{1,p}_0(Ω)` and its first derivatives lie in `W^{1,p}(Ω)`, the difference quotients
  of `u` converge to `∂_τ u` in `W^{1,p}(Ω)`, coordinate by coordinate for the gradient. They lie
  in the closed subspace `W^{1,p}_0(Ω)`, and so does `∂_τ u`
  (`TauCeti.W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn`). In particular every tangential
  derivative of `u ∈ W^{2,p}(Ω)` with zero boundary values has zero boundary values
  (`TauCeti.Wkp.exists_hasWeakLineDerivOn_value_of_firstOrder_mem_w1p0Submodule`).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2 (difference quotients) and
  §6.3.2, proof of Theorem 5 (tangential derivatives of the solution at a flat boundary).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped Distributions ENNReal Gradient InnerProductSpace

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {τ : E}

/-- **Difference quotients on a translation-invariant domain.** If every translation along `τ` maps
`Ω` into itself, then for `u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`, and every step `t`

`‖t⁻¹ (u(· + t τ) - u)‖_{Lᵖ(Ω)} ≤ ‖⟪τ, ∇u⟫‖_{Lᵖ(Ω)}`.

No boundary condition on `u` and no regularity of `∂Ω` are needed. -/
theorem W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le_of_mapsTo (hp : p ≠ ∞)
    (hΩ : ∀ s : ℝ, MapsTo (· + s • τ) Omega Omega) (u : W1p mu Omega p) (t : ℝ) :
    eLpNorm (fun x ↦ t⁻¹ * (W1p.value u (x + t • τ) - W1p.value u x)) p (mu.restrict Omega)
      ≤ eLpNorm (fun x ↦ ⟪τ, W1p.gradient u x⟫_ℝ) p (mu.restrict Omega) := by
  refine MeasureTheory.eLpNorm_restrict_le_of_forall_isCompact Omega.isOpen hp
    ((Lp.aestronglyMeasurable _).congr (W1p.value_differenceQuotient_ae le_rfl τ t (hΩ t) u))
    fun K hKΩ hK =>
    W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le hp u τ t hK subset_rfl fun x hx s _ => ?_
  rw [smul_smul]
  exact hΩ (s * t) (hKΩ hx)

/-- The convergence of difference quotients for the restriction to `Ω` of a test function on the
whole space, from the Taylor estimate. -/
private theorem W1p.tendsto_eLpNorm_inv_mul_value_restrictL_ofTestFunctionₗ_sub
    (hΩ : ∀ s : ℝ, MapsTo (· + s • τ) Omega Omega) (ψ : 𝓓((⊤ : Opens E), ℝ)) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦
      t⁻¹ * (W1p.value (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p ψ))
          (x + t • τ) -
        W1p.value (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p ψ)) x) -
      ⟪τ, W1p.gradient (W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p ψ)) x⟫_ℝ)
      p (mu.restrict Omega)) (𝓝[≠] 0) (𝓝 0) := by
  set w := W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p ψ)
  have hsub : (Omega : Set E) ⊆ ((⊤ : Opens E) : Set E) := SetLike.coe_subset_coe.2 le_top
  -- On `Ω`, the value and the gradient of `w` are `ψ` and `∇ψ`.
  have hval : W1p.value w =ᵐ[mu.restrict Omega] ψ :=
    (W1p.value_restrictL_ae le_top _).trans
      (ae_restrict_of_ae_restrict_of_subset hsub (W1p.value_ofTestFunctionₗ_ae ψ))
  have hgrad : ∀ᵐ x ∂mu.restrict Omega, W1p.gradient w x = ∇ (ψ : E → ℝ) x :=
    W1p.gradient_restrictL_ofTestFunctionₗ_ae le_top ψ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ψ.hasCompactSupport.tendsto_eLpNorm_inv_smul_comp_add_smul_sub_sub_fderiv (p := p) (mu := mu)
      (ψ.contDiff.of_le (by simp)) τ) (fun _ ↦ bot_le) fun t ↦ ?_
  refine (eLpNorm_congr_ae ?_).trans_le (eLpNorm_mono_measure _ Measure.restrict_le_self)
  filter_upwards [hval, hval.comp_add_right_restrict_of_mapsTo (hΩ t), hgrad] with x h0 h1 h2
  simp only [h0, h1, h2, smul_eq_mul]
  rw [real_inner_comm, inner_gradient_left]

/-- **Difference quotients converge to the directional derivative.** Let `Ω` be convex and mapped
into itself by every translation along `τ`. For `u ∈ W^{1,p}(Ω)`, `1 ≤ p < ∞`, the difference
quotients `t⁻¹ (u(· + t τ) - u)` converge to `⟪τ, ∇u⟫` in `Lᵖ(Ω)` as `t → 0`. -/
theorem W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_gradient (hp : p ≠ ∞)
    (hΩc : Convex ℝ (Omega : Set E)) (hΩ : ∀ s : ℝ, MapsTo (· + s • τ) Omega Omega)
    (u : W1p mu Omega p) :
    Tendsto (fun t : ℝ ↦ eLpNorm (fun x ↦ t⁻¹ * (W1p.value u (x + t • τ) - W1p.value u x) -
      ⟪τ, W1p.gradient u x⟫_ℝ) p (mu.restrict Omega)) (𝓝[≠] 0) (𝓝 0) := by
  -- The error `F w t` of the difference quotient of `w` with step `t`.
  set F : W1p mu Omega p → ℝ → E → ℝ := fun w t x ↦
    t⁻¹ * (W1p.value w (x + t • τ) - W1p.value w x) - ⟪τ, W1p.gradient w x⟫_ℝ with hF
  -- It is bounded by `2 ‖τ‖ ‖w‖`, uniformly in the step, and additive in `w`.
  have hbound : ∀ w t, eLpNorm (F w t) p (mu.restrict Omega) ≤ 2 * (‖τ‖ₑ * ‖w‖ₑ) := fun w t ↦
    calc eLpNorm (F w t) p (mu.restrict Omega)
        ≤ eLpNorm (fun x ↦ t⁻¹ * (W1p.value w (x + t • τ) - W1p.value w x)) p
            (mu.restrict Omega) + eLpNorm (fun x ↦ ⟪τ, W1p.gradient w x⟫_ℝ) p
            (mu.restrict Omega) := eLpNorm_sub_le Fact.out
      _ ≤ ‖τ‖ₑ * ‖W1p.gradient w‖ₑ + ‖τ‖ₑ * ‖W1p.gradient w‖ₑ := add_le_add
          ((W1p.eLpNorm_inv_mul_value_comp_add_smul_sub_le_of_mapsTo hp hΩ w t).trans
            (W1p.eLpNorm_inner_gradient_le τ w)) (W1p.eLpNorm_inner_gradient_le τ w)
      _ ≤ 2 * (‖τ‖ₑ * ‖w‖ₑ) := by rw [← two_mul]; gcongr; exact W1p.enorm_gradient_le w
  have hadd : ∀ v w t, F v t =ᵐ[mu.restrict Omega] F (v - w) t + F w t := fun v w t ↦ by
    filter_upwards [W1p.value_sub_ae v w, (W1p.value_sub_ae v w).comp_add_right_restrict_of_mapsTo
      (hΩ t), Lp.coeFn_sub (W1p.gradient v) (W1p.gradient w)] with x h0 h1 h2
    simp only [hF, Pi.add_apply, W1p.gradient_sub, h0, h1, h2, Pi.sub_apply, inner_sub_right]
    ring
  -- Restrictions of test functions on the whole space are dense in `W^{1,p}(Ω)`.
  have hdense : DenseRange fun ψ : 𝓓((⊤ : Opens E), ℝ) ↦
      W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p ψ) := by
    have h := Wkp.denseRange_restrictL_ofTestFunctionₗ_top_of_convex (mu := mu) hp 1 hΩc
    simp only [Wkp.restrictL_one, Wkp.ofTestFunctionₗ_one] at h
    exact h
  -- An `ε / 2` argument: approximate `u` within `η` by such a restriction `w`.
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hlim : Tendsto (fun η : ℝ ↦ 2 * (‖τ‖ₑ * ENNReal.ofReal η)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun η : ℝ ↦ ENNReal.ofReal η) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul h (Or.inr eNorm_ne_top))
      (Or.inr ENNReal.ofNat_ne_top)
  obtain ⟨η, hηε, hη⟩ :=
    ((ENNReal.tendsto_nhds_zero.1 hlim (ε / 2) hε2).and self_mem_nhdsWithin).exists
  obtain ⟨ψ, hψ⟩ := hdense.exists_dist_lt u hη
  set w := W1p.restrictL (le_top : Omega ≤ ⊤) (W1p.ofTestFunctionₗ mu ⊤ p ψ)
  have huw : ‖u - w‖ₑ ≤ ENNReal.ofReal η := by
    rw [← ofReal_norm, ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal hψ.le
  filter_upwards [ENNReal.tendsto_nhds_zero.1
    (W1p.tendsto_eLpNorm_inv_mul_value_restrictL_ofTestFunctionₗ_sub (mu := mu) (p := p) hΩ ψ)
    (ε / 2) hε2] with t ht
  calc eLpNorm (F u t) p (mu.restrict Omega)
      = eLpNorm (F (u - w) t + F w t) p (mu.restrict Omega) := eLpNorm_congr_ae (hadd u w t)
    _ ≤ eLpNorm (F (u - w) t) p (mu.restrict Omega) + eLpNorm (F w t) p (mu.restrict Omega) :=
        eLpNorm_add_le Fact.out
    _ ≤ ε / 2 + ε / 2 := add_le_add ((hbound (u - w) t).trans
        ((by gcongr : 2 * (‖τ‖ₑ * ‖u - w‖ₑ) ≤ 2 * (‖τ‖ₑ * ENNReal.ofReal η)).trans hηε)) ht
    _ = ε := ENNReal.add_halves ε

/-- **Difference quotients converge in `W^{1,p}(Ω)`.** Let `Ω` be convex and mapped into itself by
every translation along `τ`, and let `1 ≤ p < ∞`. If the first weak derivatives `∂ⱼu` of
`u ∈ W^{1,p}(Ω)` along an orthonormal basis lie in `W^{1,p}(Ω)`, given as `D j`, and `d` is the
weak derivative of `u` along `τ`, then the difference quotients `t⁻¹ (u(· + t τ) - u)` converge to
`d` in `W^{1,p}(Ω)` as `t → 0`. -/
theorem W1p.tendsto_differenceQuotient {ι : Type*} [Fintype ι] (hp : p ≠ ∞)
    (hΩc : Convex ℝ (Omega : Set E)) (hΩ : ∀ s : ℝ, MapsTo (· + s • τ) Omega Omega)
    (b : OrthonormalBasis ι ℝ E) {u d : W1p mu Omega p} {D : ι → W1p mu Omega p}
    (hD : ∀ j, HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value (D j)) (b j))
    (hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) τ) :
    Tendsto (fun t ↦ W1p.differenceQuotient le_rfl τ t (hΩ t) u) (𝓝[≠] 0) (𝓝 d) := by
  -- The weak derivative of a Sobolev function along `w` is `⟪w, ∇·⟫`.
  have hgradDeriv : ∀ (v : W1p mu Omega p) (w : E),
      HasWeakLineDerivOn mu Omega (W1p.value v) (fun x ↦ ⟪w, W1p.gradient v x⟫_ℝ) w :=
    fun v w ↦ by
      simpa only [innerSL_apply_apply, real_inner_comm] using
        (W1p.hasWeakFDerivOn v).hasWeakLineDerivOn w
  refine W1p.tendsto_iff_value_gradient.2 ⟨?_, ?_⟩
  -- Values: the difference quotients of `u` converge to `∂_τ u = d`.
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine (W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_gradient hp hΩc hΩ
      u).congr fun t ↦ eLpNorm_congr_ae ?_
    filter_upwards [W1p.value_differenceQuotient_ae le_rfl τ t (hΩ t) u,
      hd.ae_eq (hgradDeriv u τ)] with x h1 h2
    rw [Pi.sub_apply, h1, h2]
  -- Gradients, coordinate by coordinate: the difference quotients of `∂ⱼu` converge to
  -- `∂_τ ∂ⱼu = ∂ⱼd`.
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hj : ∀ j, Tendsto (fun t ↦ eLpNorm (fun x ↦ ⟪b j, (⇑(W1p.gradient
      (W1p.differenceQuotient le_rfl τ t (hΩ t) u)) - ⇑(W1p.gradient d)) x⟫_ℝ) p
      (mu.restrict Omega)) (𝓝[≠] 0) (𝓝 0) := by
    intro j
    have hDj : (fun x ↦ ⟪b j, W1p.gradient u x⟫_ℝ) =ᵐ[mu.restrict Omega] W1p.value (D j) :=
      (hgradDeriv u (b j)).ae_eq (hD j)
    have hτ : (fun x ↦ ⟪τ, W1p.gradient (D j) x⟫_ℝ) =ᵐ[mu.restrict Omega]
        fun x ↦ ⟪b j, W1p.gradient d x⟫_ℝ :=
      (hgradDeriv (D j) τ).ae_eq (hd.comm (hgradDeriv d (b j)) (hD j))
    refine (W1p.tendsto_eLpNorm_inv_mul_value_comp_add_smul_sub_sub_inner_gradient hp hΩc
      hΩ (D j)).congr fun t ↦ eLpNorm_congr_ae ?_
    filter_upwards [W1p.gradient_differenceQuotient_ae le_rfl τ t (hΩ t) u, hDj,
      hDj.comp_add_right_restrict_of_mapsTo (hΩ t), hτ] with x h1 h2 h3 h4
    rw [← h2, ← h3, h4, Pi.sub_apply, h1, inner_sub_right, real_inner_smul_right, inner_sub_right]
  -- A vector field is controlled by its coordinates in the orthonormal basis `b`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using tendsto_finsetSum Finset.univ fun j _ ↦ hj j) (fun _ ↦ bot_le) fun t ↦
      (b.toBasis.eLpNorm_le_sum_enorm_mul_eLpNorm_coord
        ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))).trans_eq
      (Finset.sum_congr rfl fun j _ ↦ ?_)
  rw [b.coe_toBasis, ← ofReal_norm, b.orthonormal.1 j, ENNReal.ofReal_one, one_mul]
  simp only [Module.Basis.coord_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, Pi.sub_apply]

/-- **Tangential derivatives keep zero boundary values.** Let `Ω` be convex and mapped into itself
by every translation along `τ`, and let `1 ≤ p < ∞`. If `u ∈ W^{1,p}_0(Ω)` has its first weak
derivatives `∂ⱼu` along an orthonormal basis in `W^{1,p}(Ω)`, given as `D j`, then its weak
derivative `∂_τ u ∈ W^{1,p}(Ω)` lies in `W^{1,p}_0(Ω)` as well. -/
theorem W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn {ι : Type*} [Fintype ι] (hp : p ≠ ∞)
    (hΩc : Convex ℝ (Omega : Set E)) (hΩ : ∀ s : ℝ, MapsTo (· + s • τ) Omega Omega)
    (b : OrthonormalBasis ι ℝ E) {u d : W1p mu Omega p} {D : ι → W1p mu Omega p}
    (hu : u ∈ w1p0Submodule mu Omega p)
    (hD : ∀ j, HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value (D j)) (b j))
    (hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) τ) :
    d ∈ w1p0Submodule mu Omega p :=
  -- The difference quotients of `u` lie in the closed subspace `W^{1,p}_0(Ω)`.
  (w1p0Submodule mu Omega p).isClosed.mem_of_tendsto
    (W1p.tendsto_differenceQuotient hp hΩc hΩ b hD hd) (Eventually.of_forall fun t ↦
      W1p.differenceQuotient_mem_w1p0Submodule (hΩ t)
        (fun x hx ↦ by simpa [neg_smul] using hΩ (-t) hx) hu)

/-- **Tangential derivatives of `W^{2,p}` functions with zero boundary values.** Let `Ω` be convex
and mapped into itself by every translation along `τ`, and let `1 ≤ p < ∞`. If `u ∈ W^{2,p}(Ω)`
has zero boundary values, in the sense that its first-order part lies in `W^{1,p}_0(Ω)`, then its
weak derivative `∂_τ u` is the value of an element of `W^{1,p}_0(Ω)`. On a half-space
`{x | c < ⟪x, ν⟫}` every `τ` with `⟪τ, ν⟫ = 0` qualifies. -/
theorem Wkp.exists_hasWeakLineDerivOn_value_of_firstOrder_mem_w1p0Submodule (hp : p ≠ ∞)
    (hΩc : Convex ℝ (Omega : Set E)) (hΩ : ∀ s : ℝ, MapsTo (· + s • τ) Omega Omega)
    {u : Wkp mu Omega p 2} (hu : Wkp.firstOrder 1 u ∈ w1p0Submodule mu Omega p) :
    ∃ d : W1p0 mu Omega p,
      HasWeakLineDerivOn mu Omega (Wkp.value 2 u) (W1p.value (d : W1p mu Omega p)) τ := by
  have hv : Wkp.value 2 u = W1p.value (Wkp.firstOrder 1 u) := by
    rw [Wkp.value_succ, Wkp.value_one, Wkp.firstOrder_succ, Wkp.firstOrder_zero]
  set b := stdOrthonormalBasis ℝ E
  -- The first derivatives of `u` along `b` and along `τ` lie in `W^{1,p}(Ω)`.
  choose D hD using fun j => Wkp.exists_hasWeakLineDerivOn_value 1 u (b j)
  obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value 1 u τ
  simp only [Wkp.value_one] at hD hd
  rw [hv] at hD hd ⊢
  exact ⟨⟨d, W1p.mem_w1p0Submodule_of_hasWeakLineDerivOn hp hΩc hΩ b hu hD hd⟩, hd⟩

end TauCeti
