/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Basic
public import TauCeti.Analysis.Calculus.Morse.Prod
import TauCeti.Analysis.Calculus.TangentCone.Prod
import TauCeti.Analysis.Calculus.Gradient

/-!
# The negative-gradient flow of a separated sum

For real functions `f` on `E` and `g` on `F`, the *separated sum*
`TauCeti.separatedSum f g (x, y) = f x + g y` of `TauCeti.Analysis.Calculus.Morse.Prod` lives on the
`L²` product `WithLp 2 (E × F)`, the product of the two inner product spaces with the inner product
`⟪(x, y), (x', y')⟫ = ⟪x, x'⟫ + ⟪y, y'⟫`. With this inner product the gradient of the separated sum
is the pair of gradients, so its negative-gradient flow is the product of the two flows,

`φ t (x, y) = (φ_f t x, φ_g t y)`.

Everything that the mod-two Morse complex is built from therefore splits:

* the nondegenerate critical points of `separatedSum f g` are the pairs of nondegenerate critical
  points, and the Morse index is additive (`TauCeti.Analysis.Calculus.Morse.Prod`);
* the stable and unstable sets of a pair of critical points are the products of the stable and
  unstable sets of its components;
* if `f` and `g` have compact sublevels, so has `separatedSum f g`;
* if `f` and `g` are Morse–Smale, so is `separatedSum f g`, because the span of the tangent cone of
  a product contains the product of the spans of the tangent cones of the factors.

These are the inputs for the comparison of the mod-two Morse complex of the separated sum with
the tensor product of the complexes of `f` and `g`, in
`TauCeti.Analysis.Calculus.Morse.Boundary.Prod`.

## Main declarations

* `TauCeti.negativeGradientFlow_separatedSum_apply`: the negative-gradient flow of the separated
  sum is the product of the two flows.
* `TauCeti.mem_stableSet_separatedSum` and `TauCeti.mem_unstableSet_separatedSum`: stable and
  unstable sets of pairs are products.
* `TauCeti.isCompact_sublevel_separatedSum`: compact sublevels.
* `TauCeti.IsMorseSmale.separatedSum`: the separated sum of Morse–Smale functions is Morse–Smale.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1 (sums of Morse functions on products).
* M. Hutchings, *Lecture notes on Morse homology*, 2002, §3, Exercise 2 (the Morse complex of a
  product).
-/

public section

open Filter Set Topology
open scoped Gradient NNReal

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {f : E → ℝ} {g : F → ℝ}

section Flow

variable [CompleteSpace E] [CompleteSpace F] {K K' K'' : ℝ≥0}

/-- **The negative-gradient flow of a separated sum is the product of the two flows.** -/
theorem negativeGradientFlow_separatedSum_apply (hfd : Differentiable ℝ f)
    (hgd : Differentiable ℝ g) (hf : LipschitzWith K (∇ f)) (hg : LipschitzWith K' (∇ g))
    (hh : LipschitzWith K'' (∇ (separatedSum f g))) (t : ℝ) (z : WithLp 2 (E × F)) :
    negativeGradientFlow (separatedSum f g) hh t z =
      WithLp.toLp 2 (negativeGradientFlow f hf t z.fst, negativeGradientFlow g hg t z.snd) := by
  let γ : ℝ → WithLp 2 (E × F) := fun s ↦
    WithLp.toLp 2 (negativeGradientFlow f hf s z.fst, negativeGradientFlow g hg s z.snd)
  have hγ : IsIntegralCurve γ fun _ y ↦ -∇ (separatedSum f g) y :=
    ((isNegativeGradient_negativeGradientFlow f hf).isIntegralCurve z.fst).separatedSum
      ((isNegativeGradient_negativeGradientFlow g hg).isIntegralCurve z.snd) (fun _ ↦ hfd _)
      (fun _ ↦ hgd _)
  have h0 : γ 0 = z := by
    apply WithLp.ofLp_injective
    ext <;> simp [γ]
  have h := eq_negativeGradientFlow (separatedSum f g) hh hγ t
  rw [h0] at h
  exact h.symm

/-- **Stable sets of a separated sum are products.** A point flows to `z` under the
negative-gradient flow of the separated sum exactly when its components flow to the components of
`z`. -/
theorem mem_stableSet_separatedSum (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    (hf : LipschitzWith K (∇ f)) (hg : LipschitzWith K' (∇ g))
    (hh : LipschitzWith K'' (∇ (separatedSum f g))) {y z : WithLp 2 (E × F)} :
    y ∈ Flow.stableSet (negativeGradientFlow (separatedSum f g) hh) z ↔
      y.fst ∈ Flow.stableSet (negativeGradientFlow f hf) z.fst ∧
        y.snd ∈ Flow.stableSet (negativeGradientFlow g hg) z.snd := by
  rw [Flow.mem_stableSet, Flow.mem_stableSet, Flow.mem_stableSet,
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toHomeomorph.isInducing.tendsto_nhds_iff,
    Prod.tendsto_iff]
  simp [negativeGradientFlow_separatedSum_apply hfd hgd hf hg hh]

/-- **Unstable sets of a separated sum are products.** -/
theorem mem_unstableSet_separatedSum (hfd : Differentiable ℝ f) (hgd : Differentiable ℝ g)
    (hf : LipschitzWith K (∇ f)) (hg : LipschitzWith K' (∇ g))
    (hh : LipschitzWith K'' (∇ (separatedSum f g))) {y z : WithLp 2 (E × F)} :
    y ∈ Flow.unstableSet (negativeGradientFlow (separatedSum f g) hh) z ↔
      y.fst ∈ Flow.unstableSet (negativeGradientFlow f hf) z.fst ∧
        y.snd ∈ Flow.unstableSet (negativeGradientFlow g hg) z.snd := by
  rw [Flow.mem_unstableSet, Flow.mem_unstableSet, Flow.mem_unstableSet,
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toHomeomorph.isInducing.tendsto_nhds_iff,
    Prod.tendsto_iff]
  simp [negativeGradientFlow_separatedSum_apply hfd hgd hf hg hh]

end Flow

/-- **A separated sum of functions with compact sublevels has compact sublevels.** -/
theorem isCompact_sublevel_separatedSum (hfc : Continuous f) (hgc : Continuous g)
    (hcf : ∀ c, IsCompact {x | f x ≤ c}) (hcg : ∀ c, IsCompact {y | g y ≤ c}) (c : ℝ) :
    IsCompact {z : WithLp 2 (E × F) | separatedSum f g z ≤ c} := by
  -- Compact sublevels make `f` and `g` bounded below: they exceed `f 0` and `g 0` off a compact.
  obtain ⟨xf, hxf⟩ := hfc.exists_forall_le' 0
    (Filter.mem_of_superset (hcf (f 0)).compl_mem_cocompact fun x hx ↦ (not_le.1 hx).le)
  obtain ⟨xg, hxg⟩ := hgc.exists_forall_le' 0
    (Filter.mem_of_superset (hcg (g 0)).compl_mem_cocompact fun y hy ↦ (not_le.1 hy).le)
  set mf := f xf
  set mg := g xg
  have hcont : Continuous (separatedSum f g) := by
    rw [separatedSum_eq_comp]
    exact ((hfc.comp continuous_fst).add (hgc.comp continuous_snd)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ E F).continuous
  refine (((hcf (c - mg)).prod (hcg (c - mf))).image
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.continuous).of_isClosed_subset
    (isClosed_le hcont continuous_const) fun z hz ↦ ?_
  rw [mem_ofPred_eq, separatedSum_apply] at hz
  refine ⟨(z.fst, z.snd), mk_mem_prod ?_ ?_, ?_⟩
  · rw [mem_ofPred_eq]
    linarith [hxg z.snd]
  · rw [mem_ofPred_eq]
    linarith [hxf z.fst]
  · apply WithLp.ofLp_injective
    ext <;> simp

section MorseSmale

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {K K' K'' : ℝ≥0}

/-- **The separated sum of Morse–Smale functions is Morse–Smale.** At a point of `W^u(p) ∩ W^s(q)`
for the separated sum, these sets are products. The span of the tangent cone of a product contains
the product of the spans of the tangent cones of the factors, and those already span by the
Morse–Smale condition for `f` and for `g`. -/
theorem IsMorseSmale.separatedSum (hfs : ContDiff ℝ 2 f) (hgs : ContDiff ℝ 2 g)
    {hf : LipschitzWith K (∇ f)} {hg : LipschitzWith K' (∇ g)} (htf : IsMorseSmale f hf)
    (htg : IsMorseSmale g hg) (hh : LipschitzWith K'' (∇ (separatedSum f g))) :
    IsMorseSmale (separatedSum f g) hh := by
  have hfd := hfs.differentiable two_ne_zero
  have hgd := hgs.differentiable two_ne_zero
  refine IsMorseSmale.of_forall fun p q y hp hq ⟨hyu, hys⟩ ↦ ?_
  rw [isNondegenerateCriticalPoint_separatedSum_iff] at hp hq
  obtain ⟨hu₁, hu₂⟩ := (mem_unstableSet_separatedSum hfd hgd hf hg hh).1 hyu
  obtain ⟨hs₁, hs₂⟩ := (mem_stableSet_separatedSum hfd hgd hf hg hh).1 hys
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm
  -- The span of the tangent cone of a product read through `e` contains the image under `e` of
  -- the product of the spans of the tangent cones of the factors.
  have hspan (A : Set E) (B : Set F) (ha : y.fst ∈ A) (hb : y.snd ∈ B) :
      ((Submodule.span ℝ (tangentConeAt ℝ A y.fst)).prod
          (Submodule.span ℝ (tangentConeAt ℝ B y.snd))).map e.toLinearMap ≤
        Submodule.span ℝ (tangentConeAt ℝ {w : WithLp 2 (E × F) | w.fst ∈ A ∧ w.snd ∈ B} y) := by
    have himage : e '' (A ×ˢ B) = {w : WithLp 2 (E × F) | w.fst ∈ A ∧ w.snd ∈ B} := by
      rw [e.image_eq_preimage_symm]
      rfl
    refine (Submodule.map_mono (prod_span_tangentConeAt_le (subset_closure ha)
      (subset_closure hb))).trans ?_
    rw [Submodule.map_span, ← himage]
    exact Submodule.span_mono ((e.hasFDerivAt (x := (y.fst, y.snd))).hasFDerivWithinAt
      |>.mapsTo_tangent_cone).image_subset
  have hU : Flow.unstableSet (negativeGradientFlow (TauCeti.separatedSum f g) hh) p =
      {w | w.fst ∈ Flow.unstableSet (negativeGradientFlow f hf) p.fst ∧
        w.snd ∈ Flow.unstableSet (negativeGradientFlow g hg) p.snd} :=
    Set.ext fun _ ↦ mem_unstableSet_separatedSum hfd hgd hf hg hh
  have hS : Flow.stableSet (negativeGradientFlow (TauCeti.separatedSum f g) hh) q =
      {w | w.fst ∈ Flow.stableSet (negativeGradientFlow f hf) q.fst ∧
        w.snd ∈ Flow.stableSet (negativeGradientFlow g hg) q.snd} :=
    Set.ext fun _ ↦ mem_stableSet_separatedSum hfd hgd hf hg hh
  rw [eq_top_iff, hU, hS]
  calc ⊤ = ((Submodule.span ℝ (tangentConeAt ℝ
          (Flow.unstableSet (negativeGradientFlow f hf) p.fst) y.fst) ⊔
        Submodule.span ℝ (tangentConeAt ℝ
          (Flow.stableSet (negativeGradientFlow f hf) q.fst) y.fst)).prod
        (Submodule.span ℝ (tangentConeAt ℝ
          (Flow.unstableSet (negativeGradientFlow g hg) p.snd) y.snd) ⊔
        Submodule.span ℝ (tangentConeAt ℝ
          (Flow.stableSet (negativeGradientFlow g hg) q.snd) y.snd))).map e.toLinearMap := by
        rw [htf.transverse_at hp.1 hq.1 ⟨hu₁, hs₁⟩, htg.transverse_at hp.2 hq.2 ⟨hu₂, hs₂⟩,
          Submodule.prod_top, Submodule.map_top, LinearEquiv.range]
    _ ≤ _ := by
      rw [← Submodule.prod_sup_prod, Submodule.map_sup]
      exact sup_le_sup (hspan _ _ hu₁ hu₂) (hspan _ _ hs₁ hs₂)

end MorseSmale

end TauCeti
