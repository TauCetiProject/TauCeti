/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet
public import TauCeti.Analysis.Sobolev.LipschitzDomain.SegmentChain
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import TauCeti.Analysis.Calculus.MeanValue
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Hölder spaces `C^{k,α}(Ω)` on a bounded Lipschitz domain

On a convex open set, the derivative fields of an element of `C^{k,α}(Ω)` below the top order are
`α`-Hölder for `α ≤ 1`, by the mean value inequality, and so `C^{k+1,α}(Ω) ⊆ C^{k,α}(Ω)`
(`TauCeti.CkHolderSpaceOn.inclusionSuccL`). On a general open set this fails across a slit. This
file proves both statements on a bounded Lipschitz domain, which need not be convex: nearby points
of such a domain are joined inside it by three segments of total length comparable to their
distance (`Set.IsLipschitzDomain.exists_segment_chain`), and the mean value inequality along them
bounds the increments of each lower derivative field at small scales. The domains of the global
Schauder theory, bounded domains with `C^{k,α}` boundary for `k ≥ 1`, are bounded Lipschitz
domains.

## Main declarations

* `Set.IsLipschitzDomain.exists_holderOnWith_of_norm_fderiv_le`: there is a constant `C`,
  depending only on `Ω` and `α`, such that every map with `‖g‖ ≤ M` and `‖fderiv ℝ g‖ ≤ L` on
  `Ω` is `α`-Hölder on `Ω` with constant `C (L + M)`.
* `TauCeti.CkHolderSpaceOn.exists_holderOnWith_iteratedFDeriv_of_isLipschitzDomain`: there is a
  constant `C`, depending only on `Ω` and `α`, such that every derivative field through order `k`
  of every `f ∈ C^{k,α}(Ω)` is `α`-Hölder on `Ω` with constant `C ‖f‖`.
* `TauCeti.CkHolderSpaceOn.inclusionSuccLOfIsLipschitzDomain`: the inclusion
  `C^{k+1,α}(Ω) → C^{k,α}(Ω)` as a continuous linear map, built by
  `TauCeti.CkHolderSpaceOn.inclusionSuccLOfHolderOnWith` from that constant.

## References

* D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.1.
-/

public section

noncomputable section

open TopologicalSpace
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
  obtain ⟨C₀, δ, hδ, hchain⟩ := hΩ.exists_segment_chain hb
  refine ⟨C₀ * δ ^ (1 - (α : ℝ)) + 2 * δ ^ (-(α : ℝ)), fun {G} _ _ g M L hdiff hval hder ↦ ?_⟩
  -- Lipschitz at scales below `δ`, by the mean value inequality along a chain of segments.
  have hnear : ∀ x ∈ Ω, ∀ y ∈ Ω, dist x y < δ →
      dist (g x) (g y) ≤ ((L * C₀ : ℝ≥0) : ℝ) * dist x y ^ ((1 : ℝ≥0) : ℝ) := by
    intro x hx y hy hxy
    obtain ⟨p, q, h1, h2, h3, hlen⟩ := hchain x hx y hy hxy
    rw [dist_comm, dist_eq_norm, NNReal.coe_one, Real.rpow_one, NNReal.coe_mul, mul_assoc]
    exact (TauCeti.norm_image_sub_le_of_norm_fderiv_le_of_segment_subset hdiff hder h1 h2
      h3).trans (mul_le_mul_of_nonneg_left hlen L.coe_nonneg)
  have hfar : ∀ x ∈ Ω, ∀ y ∈ Ω, dist (g x) (g y) ≤ ((2 * M : ℝ≥0) : ℝ) := by
    intro x hx y hy
    rw [dist_eq_norm]
    push_cast
    linarith [norm_sub_le (g x) (g y), hval x hx, hval y hy]
  refine (HolderOnWith.of_le_of_dist_le hnear hfar hα hδ).mono_const ?_
  rw [← NNReal.coe_le_coe]
  push_cast
  nlinarith [mul_nonneg (mul_nonneg M.coe_nonneg C₀.coe_nonneg)
      (Real.rpow_nonneg δ.coe_nonneg (1 - (α : ℝ))),
    mul_nonneg L.coe_nonneg (Real.rpow_nonneg δ.coe_nonneg (-(α : ℝ)))]

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
