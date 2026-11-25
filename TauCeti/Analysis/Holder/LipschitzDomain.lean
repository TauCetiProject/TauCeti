/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Product
public import TauCeti.Analysis.Sobolev.LipschitzDomain.SegmentChain
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Holder.Interpolation
import TauCeti.Topology.MetricSpace.Bounded
import TauCeti.Analysis.Sobolev.LipschitzDomain.MeasureDensity
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder spaces `C^{k,α}(Ω)` and interpolation inequalities on a bounded Lipschitz domain

On a convex open set, the derivative fields of an element of `C^{k,α}(Ω)` below the top order are
`α`-Hölder for `α ≤ 1`, by the mean value inequality, and so `C^{k+1,α}(Ω) ⊆ C^{k,α}(Ω)`
(`TauCeti.CkHolderSpaceOn.inclusionSuccL`). On a general open set this fails across a slit. This
file proves both statements on a bounded Lipschitz domain, which need not be convex: nearby points
of such a domain are joined inside it by three segments of total length comparable to their
distance (`Set.IsLipschitzDomain.exists_segment_chain`), and the mean value inequality along them
bounds the increments of each lower derivative field at small scales. The same Hölder bounds give
the order-`k` Leibniz estimate `‖B (f, g)‖_{C^{k,α}(Ω)} ≤ C ‖B‖ ‖f‖_{C^{k,α}(Ω)} ‖g‖_{C^{k,α}(Ω)}`
for a continuous bilinear map `B`, so that coefficients in `C^{k,α}(Ω)` act on `C^{k,α}(Ω)` by
bounded multiplication. The domains of the global Schauder theory, bounded domains with
`C^{k,α}` boundary for `k ≥ 1`, are bounded Lipschitz domains.

The same geometry gives the interpolation inequalities up to the boundary: for `u` of class `C²`
on `Ω` with `‖u‖ ≤ M` and `D²u` `α`-Hölder with constant `V` on `Ω`, and every `0 < ε ≤ 1`,

`‖Du(x)‖ ≤ C (ε⁻¹ M + ε^(1 + α) V)` and `‖D²u(x)‖ ≤ C (ε⁻² M + ε^α V)` for `x ∈ Ω`,

with `C` depending only on `Ω`. The interior forms (`HolderOnWith.norm_fderiv_le_of_contDiffOn`,
`HolderOnWith.norm_iteratedFDeriv_two_le_of_contDiffOn`) need a ball of radius comparable to `ε`
about `x` inside `Ω`. Near the boundary, `B(x, ε)` still contains a ball in `Ω` of radius
comparable to `ε` (the interior corkscrew condition,
`Set.IsLipschitzDomain.exists_closedBall_subset_inter_ball`); the Hölder bound on `D²u` carries the
Hessian estimate from its centre back to `x`, and the mean value inequality along a short chain of
segments in `Ω` carries the gradient estimate. With `ε` small, these bounds let a global Schauder
estimate absorb the norms of `Du` and `D²u` on its right side, leaving only the supremum of
`‖u‖` there.

## Main declarations

* `Set.IsLipschitzDomain.exists_holderOnWith_of_norm_fderiv_le`: there is a constant `C`,
  depending only on `Ω` and `α`, such that every map with `‖g‖ ≤ M` and `‖fderiv ℝ g‖ ≤ L` on
  `Ω` is `α`-Hölder on `Ω` with constant `C (L + M)`.
* `Set.IsLipschitzDomain.exists_norm_iteratedFDeriv_two_le` and
  `Set.IsLipschitzDomain.exists_norm_fderiv_le`: the interpolation inequalities for the Hessian
  and the gradient on a bounded Lipschitz domain.
* `TauCeti.CkHolderSpaceOn.exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain`: there is a
  constant `C`, depending only on `Ω` and `α`, such that every derivative field through order `k`
  of every `f ∈ C^{k,α}(Ω)` is `α`-Hölder on `Ω` with constant `C ‖f‖`.
* `TauCeti.CkHolderSpaceOn.inclusionSuccLOfIsLipschitzDomain`: the inclusion
  `C^{k+1,α}(Ω) → C^{k,α}(Ω)` as a continuous linear map, built by
  `TauCeti.CkHolderSpaceOn.inclusionSuccLOfHolderOnWith` from that constant.
* `ContinuousLinearMap.compCkHolderOn₂OfIsLipschitzDomain`: pointwise application of a continuous
  bilinear map `B` to `C^{k,α}(Ω)`, as a continuous bilinear map, built by
  `ContinuousLinearMap.compCkHolderOn₂OfHolderOnWith` from that constant.
* `ContinuousLinearMap.exists_norm_compCkHolderOn₂OfIsLipschitzDomain_apply_le`: the order-`k`
  Leibniz estimate on a bounded Lipschitz domain, with a constant independent of `B` and of the
  factors.

## References

* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1, and Section 6.8 (Lemma 6.35: the global interpolation inequalities, there on
  domains with `C^{k,α}` boundary).
-/

public section

noncomputable section

open Metric TopologicalSpace
open scoped NNReal

universe u v w

variable {α : ℝ≥0} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {E' : Type w} [NormedAddCommGroup E'] [NormedSpace ℝ E']

namespace Set.IsLipschitzDomain

/-- On a bounded Lipschitz domain and for `α ≤ 1`, there is a constant `C`, depending only on `Ω`
and `α`, such that every map `g` differentiable on `Ω` with `‖g‖ ≤ M` and `‖fderiv ℝ g‖ ≤ L` on
`Ω` is `α`-Hölder on `Ω` with constant `C (L + M)`. On a convex set the mean value inequality
gives this directly (`Convex.lipschitzOnWith_of_nnNorm_fderiv_le` and
`LipschitzOnWith.holderOnWith_of_norm_le`). -/
theorem exists_holderOnWith_of_norm_fderiv_le {Ω : Set E} (hΩ : Ω.IsLipschitzDomain E')
    (hb : Bornology.IsBounded Ω) (hα : α ≤ 1) :
    ∃ C : ℝ≥0, ∀ {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : E → G} {M L : ℝ≥0},
      (∀ x ∈ Ω, DifferentiableAt ℝ g x) → (∀ x ∈ Ω, ‖g x‖ ≤ M) →
        (∀ x ∈ Ω, ‖fderiv ℝ g x‖ ≤ L) → HolderOnWith (C * (L + M)) α g Ω := by
  obtain ⟨C₀, δ, hδ, hnear⟩ := hΩ.exists_dist_le_of_norm_fderiv_le hb
  refine ⟨C₀ * δ ^ (1 - (α : ℝ)) + 2 * δ ^ (-(α : ℝ)), fun {G} _ _ g M L hdiff hval hder ↦ ?_⟩
  have hfar : ∀ x ∈ Ω, ∀ y ∈ Ω, dist (g x) (g y) ≤ ((2 * M : ℝ≥0) : ℝ) := by
    intro x hx y hy
    rw [dist_eq_norm]
    push_cast
    linarith [norm_sub_le (g x) (g y), hval x hx, hval y hy]
  refine (HolderOnWith.of_le_of_dist_le (K := L * C₀) (β := 1) (fun x hx y hy hxy ↦ ?_) hfar hα
    hδ).mono_const ?_
  · rw [NNReal.coe_one, Real.rpow_one, NNReal.coe_mul, mul_comm (L : ℝ)]
    exact hnear hdiff hder x hx y hy hxy
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [mul_nonneg (mul_nonneg M.coe_nonneg C₀.coe_nonneg)
      (Real.rpow_nonneg δ.coe_nonneg (1 - (α : ℝ))),
    mul_nonneg L.coe_nonneg (Real.rpow_nonneg δ.coe_nonneg (-(α : ℝ)))]

/-- **Interpolation inequality for the Hessian on a bounded Lipschitz domain.** There is a
constant `C`, depending only on `Ω`, such that for every `u` of class `C²` on `Ω` with `‖u‖ ≤ M`
on `Ω` and `D²u` `α`-Hölder with constant `V` on `Ω`, and every `0 < ε ≤ 1`,

`‖D²u(x)‖ ≤ C (ε⁻² M + ε^α V)` for every `x ∈ Ω`.

Compare `HolderOnWith.norm_iteratedFDeriv_two_le_of_contDiffOn`, the same bound at the centre of
a ball contained in the set: by the interior corkscrew condition
(`Set.IsLipschitzDomain.exists_closedBall_subset_inter_ball`), the ball `B(x, ε)` contains a ball in
`Ω` of radius comparable to `ε`, and the Hölder bound on `D²u` carries the estimate at its centre
back to `x`. -/
theorem exists_norm_iteratedFDeriv_two_le {Ω : Set E} (hΩ : Ω.IsLipschitzDomain E')
    (hb : Bornology.IsBounded Ω) :
    ∃ C : ℝ≥0, ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}
      {α M V : ℝ≥0}, ContDiffOn ℝ 2 u Ω → (∀ x ∈ Ω, ‖u x‖ ≤ M) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) Ω → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ x ∈ Ω,
          ‖iteratedFDeriv ℝ 2 u x‖ ≤ C * (M / ε ^ 2 + V * ε ^ (α : ℝ)) := by
  obtain ⟨c, hc0, hc1, hball⟩ :=
    hΩ.exists_closedBall_subset_inter_ball hb.isCompact_frontier one_pos
  refine ⟨⟨8 / c ^ 2 + 4, by positivity⟩, fun {F} _ _ u α M V hu hM hV ε hε hε1 x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := hball x (subset_closure hx) ε hε hε1
  have hyΩ : y ∈ Ω ∩ ball x ε := hy (mem_closedBall_self (by positivity))
  -- The interior interpolation inequality at the centre `y`, on a ball of radius `2 (c ε / 2)`.
  have hy2 := HolderOnWith.norm_iteratedFDeriv_two_le_of_contDiffOn hΩ.isOpen hu subset_rfl hV
    (fun z hz ↦ hM z hz) (ε := c * ε / 2) (by positivity)
    (by rw [mul_div_cancel₀ _ two_ne_zero]; exact hy.trans inter_subset_left)
  -- The Hölder bound on `D²u` between `x` and `y`.
  have hxy : ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ ≤ V * ε ^ (α : ℝ) := by
    rw [← dist_eq_norm]
    exact (hV.dist_le hx hyΩ.1).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg
      (by simpa [dist_comm] using (mem_ball.1 hyΩ.2).le) α.coe_nonneg) V.coe_nonneg)
  have hpow : (c * ε / 2) ^ (α : ℝ) ≤ ε ^ (α : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) α.coe_nonneg
  have hM2 : 2 * (M : ℝ) / (c * ε / 2) ^ 2 = 8 / c ^ 2 * (M / ε ^ 2) := by
    field_simp
    ring
  have hε2 : 0 ≤ (M : ℝ) / ε ^ 2 := by positivity
  have hεα : 0 ≤ (V : ℝ) * ε ^ (α : ℝ) := by positivity
  calc ‖iteratedFDeriv ℝ 2 u x‖
      ≤ ‖iteratedFDeriv ℝ 2 u y‖ + ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ 8 / c ^ 2 * (M / ε ^ 2) + 3 * V * ε ^ (α : ℝ) + V * ε ^ (α : ℝ) := by
        rw [← hM2]
        nlinarith [mul_le_mul_of_nonneg_left hpow V.coe_nonneg]
    _ ≤ (8 / c ^ 2 + 4) * (M / ε ^ 2 + V * ε ^ (α : ℝ)) := by
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 8 / c ^ 2) hεα]

/-- **Interpolation inequality for the gradient on a bounded Lipschitz domain.** There is a
constant `C`, depending only on `Ω`, such that for every `u` of class `C²` on `Ω` with `‖u‖ ≤ M`
on `Ω` and `D²u` `α`-Hölder with constant `V` on `Ω`, and every `0 < ε ≤ 1`,

`‖Du(x)‖ ≤ C (ε⁻¹ M + ε^(1 + α) V)` for every `x ∈ Ω`.

Compare `HolderOnWith.norm_fderiv_le_of_contDiffOn`, the same bound at the centre of a ball
contained in the set. Here the bound at the centre `y` of a ball in `Ω ∩ B(x, ε)`
(`Set.IsLipschitzDomain.exists_closedBall_subset_inter_ball`) is carried back to `x` along a chain
of segments in `Ω` of length comparable to `‖x - y‖`
(`Set.IsLipschitzDomain.exists_dist_le_of_norm_fderiv_le`), on which `‖D²u‖` is bounded by
`Set.IsLipschitzDomain.exists_norm_iteratedFDeriv_two_le`. -/
theorem exists_norm_fderiv_le {Ω : Set E} (hΩ : Ω.IsLipschitzDomain E')
    (hb : Bornology.IsBounded Ω) :
    ∃ C : ℝ≥0, ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}
      {α M V : ℝ≥0}, ContDiffOn ℝ 2 u Ω → (∀ x ∈ Ω, ‖u x‖ ≤ M) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) Ω → ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ x ∈ Ω,
          ‖fderiv ℝ u x‖ ≤ C * (M / ε + V * ε ^ (1 + (α : ℝ))) := by
  obtain ⟨C₂, hC₂⟩ := hΩ.exists_norm_iteratedFDeriv_two_le hb
  obtain ⟨c, hc0, hc1, hball⟩ :=
    hΩ.exists_closedBall_subset_inter_ball hb.isCompact_frontier one_pos
  obtain ⟨C₀, δ₀, hδ₀, hlip⟩ := hΩ.exists_dist_le_of_norm_fderiv_le hb
  set ρ : ℝ := min (δ₀ : ℝ) 1
  have hρ0 : 0 < ρ := lt_min hδ₀ one_pos
  refine ⟨⟨1 / (c * ρ) + 1 + C₂ * C₀, by positivity⟩,
    fun {F} _ _ u α M V hu hM hV ε hε hε1 x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := hball x (subset_closure hx) (ρ * ε) (by positivity)
    (by nlinarith [min_le_right (δ₀ : ℝ) 1])
  have hyΩ : y ∈ Ω ∩ ball x (ρ * ε) := hy (mem_closedBall_self (by positivity))
  have hdxy : dist x y < ρ * ε := by simpa [dist_comm] using mem_ball.1 hyΩ.2
  -- The interior interpolation inequality at the centre `y`, on a ball of radius `c ρ ε`.
  have hy1 := HolderOnWith.norm_fderiv_le_of_contDiffOn hΩ.isOpen hu subset_rfl hV
    (fun z hz ↦ hM z hz) (by positivity) (hy.trans inter_subset_left)
  -- The Hessian bound at scale `ε` on all of `Ω`, and the mean value inequality along a chain.
  have hD2 : ∀ z ∈ Ω, ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ C₂ * (M / ε ^ 2 + V * ε ^ (α : ℝ)) :=
    fun z hz ↦ by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact hC₂ hu hM hV hε hε1 z hz
  have hmv := hlip (fun z hz ↦
      ((hu.contDiffAt (hΩ.isOpen.mem_nhds hz)).hasFDerivAt_fderiv le_rfl).differentiableAt)
    hD2 x hx y hyΩ.1 (hdxy.trans_le (by nlinarith [min_le_left (δ₀ : ℝ) 1]))
  -- Collect the three terms.
  have hcρ : c * ρ ≤ 1 := by nlinarith [min_le_right (δ₀ : ℝ) 1]
  have hpow : (c * (ρ * ε)) ^ (1 + (α : ℝ)) ≤ ε ^ (1 + (α : ℝ)) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [mul_le_mul_of_nonneg_right hcρ hε.le])
      (by positivity)
  have hM1 : (M : ℝ) / (c * (ρ * ε)) = 1 / (c * ρ) * (M / ε) := by field_simp
  have hexp : (M / ε ^ 2 + V * ε ^ (α : ℝ)) * ε = M / ε + V * ε ^ (1 + (α : ℝ)) := by
    rw [Real.rpow_add hε, Real.rpow_one]
    field_simp
  have hle : dist x y ≤ ε := hdxy.le.trans (by nlinarith [min_le_right (δ₀ : ℝ) 1])
  have hxy : ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ C₂ * C₀ * (M / ε + V * ε ^ (1 + (α : ℝ))) := by
    rw [← dist_eq_norm, ← hexp]
    calc _ ≤ C₀ * (C₂ * (M / ε ^ 2 + V * ε ^ (α : ℝ))) * dist x y := hmv
      _ ≤ C₀ * (C₂ * (M / ε ^ 2 + V * ε ^ (α : ℝ))) * ε := by gcongr
      _ = _ := by ring
  calc ‖fderiv ℝ u x‖
      ≤ ‖fderiv ℝ u y‖ + ‖fderiv ℝ u x - fderiv ℝ u y‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ 1 / (c * ρ) * (M / ε) + V * ε ^ (1 + (α : ℝ)) +
          C₂ * C₀ * (M / ε + V * ε ^ (1 + (α : ℝ))) := by
        rw [← hM1]
        nlinarith [mul_le_mul_of_nonneg_left hpow V.coe_nonneg]
    _ ≤ (1 / (c * ρ) + 1 + C₂ * C₀) * (M / ε + V * ε ^ (1 + (α : ℝ))) := by
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / (c * ρ))
          (by positivity : (0 : ℝ) ≤ V * ε ^ (1 + (α : ℝ))),
          (by positivity : (0 : ℝ) ≤ M / ε)]

end Set.IsLipschitzDomain

namespace TauCeti

namespace CkHolderSpaceOn

variable {k : ℕ} {Ω : Opens E} {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- On a bounded Lipschitz domain and for `α ≤ 1`, there is a constant `C`, depending only on `Ω`
and `α`, such that for every `f ∈ C^{k,α}(Ω)` and every function `g` agreeing with `f` on `Ω`,
each iterated derivative of `g` through order `k` is `α`-Hölder on `Ω` with constant `C ‖f‖`.
Compare `TauCeti.CkHolderSpaceOn.holderOnWith_iteratedFDeriv_of_le`, with constant `3 ‖f‖`, on a
convex open set. -/
theorem exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E))
    (hα : α ≤ 1) :
    ∃ C : ℝ≥0, ∀ {k : ℕ} {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : CkHolderSpaceOn k α Ω F) {g : E → F}, (∀ x : Ω, g x = f x) →
        ∀ {j : ℕ}, j ≤ k → HolderOnWith (C * ‖f‖₊) α (_root_.iteratedFDeriv ℝ j g) Ω := by
  obtain ⟨C, hC⟩ := hΩ.exists_holderOnWith_of_norm_fderiv_le hb hα
  refine ⟨2 * C + 1, fun {k F} _ _ f g hg j hj ↦ ?_⟩
  rcases hj.eq_or_lt with rfl | hj
  · -- The top derivative: the Hölder seminorm of the top field is at most `‖f‖`.
    refine (f.holderOnWith_iteratedFDeriv hg).mono_const ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [f.nnHolderNorm_iteratedFDeriv_le, mul_nonneg C.coe_nonneg (norm_nonneg f)]
  -- Below the top order: the field and the next one are bounded by `‖f‖`.
  have hcd := f.contDiffOn hg
  refine (hC (M := ‖f‖₊) (L := ‖f‖₊)
    (fun x hx ↦ (hcd.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast hj))
    (fun x hx ↦ f.norm_iteratedFDeriv_apply_le hg hj.le ⟨x, hx⟩)
    (fun x hx ↦ by
      rw [norm_fderiv_iteratedFDeriv]
      exact f.norm_iteratedFDeriv_apply_le hg hj ⟨x, hx⟩)).mono_const ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [norm_nonneg f]

/-- On a bounded Lipschitz domain and for `α ≤ 1`, the inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)`, as
a continuous linear map. Compare `TauCeti.CkHolderSpaceOn.inclusionSuccL`, on a convex open set,
which has operator norm at most `3`. -/
def inclusionSuccLOfIsLipschitzDomain (hΩ : (Ω : Set E).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderSpaceOn (k + 1) α Ω F →L[ℝ] CkHolderSpaceOn k α Ω F :=
  have hC := exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain hΩ hb hα
  inclusionSuccLOfHolderOnWith hC.choose fun f ↦ hC.choose_spec f f.extend_apply k.le_succ

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` on a bounded Lipschitz domain does not change
values. -/
@[simp]
theorem inclusionSuccLOfIsLipschitzDomain_apply (hΩ : (Ω : Set E).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1) (f : CkHolderSpaceOn (k + 1) α Ω F)
    (x : Ω) : inclusionSuccLOfIsLipschitzDomain hΩ hb hα f x = f x :=
  inclusionSuccLOfHolderOnWith_apply _ _ f x

/-- The inclusion `C^{k+1,α}(Ω) → C^{k,α}(Ω)` on a bounded Lipschitz domain keeps the derivative
fields through order `k`. -/
@[simp]
theorem iteratedFDeriv_inclusionSuccLOfIsLipschitzDomain (hΩ : (Ω : Set E).IsLipschitzDomain E')
    (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1) (f : CkHolderSpaceOn (k + 1) α Ω F)
    (i : Fin (k + 1)) (x : Ω) :
    (inclusionSuccLOfIsLipschitzDomain hΩ hb hα f).iteratedFDeriv i x =
      f.iteratedFDeriv i.castSucc x :=
  iteratedFDeriv_inclusionSuccLOfHolderOnWith _ _ f i x

end CkHolderSpaceOn

end TauCeti

namespace ContinuousLinearMap

open TauCeti

variable {k : ℕ} {Ω : Opens E} {F₁ : Type*} {F₂ : Type*} {F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]

/-- On a bounded Lipschitz domain and for `α ≤ 1`, pointwise application of a continuous bilinear
map to `C^{k,α}` functions on `Ω`. Fixing the first argument gives bounded multiplication by a
coefficient field in `C^{k,α}(Ω)`. Compare `ContinuousLinearMap.compCkHolderOn₂`, on a convex open
set. -/
def compCkHolderOn₂OfIsLipschitzDomain (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1) :
    CkHolderSpaceOn k α Ω F₁ →L[ℝ] CkHolderSpaceOn k α Ω F₂ →L[ℝ] CkHolderSpaceOn k α Ω F₃ :=
  have hC := CkHolderSpaceOn.exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain hΩ hb hα
  have hD := CkHolderSpaceOn.exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain hΩ hb hα
  B.compCkHolderOn₂OfHolderOnWith hC.choose hD.choose
    (fun f _ hj ↦ hC.choose_spec f f.extend_apply hj)
    (fun g _ hj ↦ hD.choose_spec g g.extend_apply hj)

/-- The lifted bilinear operation on `C^{k,α}(Ω)` of a bounded Lipschitz domain is pointwise the
original one. -/
@[simp]
theorem compCkHolderOn₂OfIsLipschitzDomain_apply (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1)
    (f : CkHolderSpaceOn k α Ω F₁) (g : CkHolderSpaceOn k α Ω F₂) (x : Ω) :
    B.compCkHolderOn₂OfIsLipschitzDomain hΩ hb hα f g x = B (f x) (g x) :=
  compCkHolderOn₂OfHolderOnWith_apply _ _ _ _ _ f g x

/-- On a bounded Lipschitz domain and for `α ≤ 1`, the lifted bilinear map on `C^{k,α}(Ω)` has
operator norm at most `C ‖B‖`, for a constant `C` independent of `B`. -/
theorem exists_norm_compCkHolderOn₂OfIsLipschitzDomain_le
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1) :
    ∃ C : ℝ, ∀ B : F₁ →L[ℝ] F₂ →L[ℝ] F₃,
      ‖B.compCkHolderOn₂OfIsLipschitzDomain (k := k) hΩ hb hα‖ ≤ C * ‖B‖ :=
  ⟨_, fun B ↦ norm_compCkHolderOn₂OfHolderOnWith_le B _ _ _ _⟩

/-- **The order-`k` Leibniz estimate** in `C^{k,α}(Ω)` on a bounded Lipschitz domain, for `α ≤ 1`:
`‖B (f, g)‖_{C^{k,α}(Ω)} ≤ C ‖B‖ ‖f‖_{C^{k,α}(Ω)} ‖g‖_{C^{k,α}(Ω)}` for a constant `C` independent
of `B`, `f` and `g`. Compare `ContinuousLinearMap.norm_compCkHolderOn₂_apply_le`, with the explicit
constant `(k + 7) 2^k`, on a convex open set. -/
theorem exists_norm_compCkHolderOn₂OfIsLipschitzDomain_apply_le
    (hΩ : (Ω : Set E).IsLipschitzDomain E') (hb : Bornology.IsBounded (Ω : Set E)) (hα : α ≤ 1) :
    ∃ C : ℝ, ∀ (B : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (f : CkHolderSpaceOn k α Ω F₁)
      (g : CkHolderSpaceOn k α Ω F₂),
      ‖B.compCkHolderOn₂OfIsLipschitzDomain hΩ hb hα f g‖ ≤ C * ‖B‖ * ‖f‖ * ‖g‖ := by
  obtain ⟨C, hC⟩ := exists_norm_compCkHolderOn₂OfIsLipschitzDomain_le (k := k) (F₁ := F₁)
    (F₂ := F₂) (F₃ := F₃) hΩ hb hα
  exact ⟨C, fun B f g ↦ ((B.compCkHolderOn₂OfIsLipschitzDomain hΩ hb hα).le_opNorm₂ f g).trans
    (by gcongr; exact hC B)⟩

end ContinuousLinearMap
