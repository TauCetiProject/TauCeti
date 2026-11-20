/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Sobolev

/-!
# Composition of quantizations on Sobolev spaces

For symbols `a` and `b` of orders `m'` and `m` with compact spatial support, the composition
symbol `a # b` (`TauCeti.Symbol.sharp`) quantizes on Schwartz functions to `Op(a) ∘ Op(b)`
(`TauCeti.Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue`). This file transfers this
to the bounded extensions `H^s → H^{s - m}` of `TauCeti.Symbol.quantizeSobolev`: the operator
`Op(a # b) : H^s → H^{s - (m' + m)}` is `Op(a) ∘ Op(b)`, as maps of tempered distributions
(`TauCeti.Symbol.toDistr_quantizeSobolev_sharp`).

Combined with the locality of the composition symbol
(`TauCeti.Symbol.isSmoothing_sharp_sub_comp`), this shows that `Op(c) v` only depends on `v` near
the positions where the symbol `c` does not vanish, up to a smoothing operator: if `c` has compact
spatial support and vanishes outside `K`, and `χ` is a compactly supported Schwartz function equal
to `1` on a neighbourhood of `K`, then `Op(c) v = Op(c) (χ v) + Op(e) v` for a smoothing symbol `e`
(`Symbol.exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add`),
and hence `‖Op(c) v‖_{H^{t - m}} ≤ C (‖χ v‖_{H^t} + ‖v‖_{H^r})` for every `r ≤ t`
(`TauCeti.Symbol.exists_norm_quantizeSobolev_le_smulLeftCLM`). Estimates of this form localize the
lower order terms in elliptic estimates.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (2.5)–(2.7) and (3.31).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open scoped SchwartzMap BesselPotentialSpace ContDiff Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]

/-- **Composition of quantizations on Sobolev spaces.** For symbols `a` and `b` with compact
spatial support, the operator `Op(a # b) : H^s → H^{s - (m' + m)}` is the composition of
`Op(b) : H^s → H^{s - m}` and `Op(a) : H^{s - m} → H^{s - m - m'}`. -/
theorem toDistr_quantizeSobolev_sharp {a : Symbol n W U m'} {b : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport) (s : ℝ)
    (u : H^{s}(CoordinateSpace n, V)) :
    ((a.sharp b hb).quantizeSobolev (ha.sharp hb) s u).toDistr =
      (a.quantizeSobolev ha (s - m) (b.quantizeSobolev hb s u)).toDistr := by
  have key : BesselPotentialSpace.inclusion (le_of_eq (by ring) : s - m - m' ≤ s - (m' + m)) ∘L
        (a.sharp b hb).quantizeSobolev (ha.sharp hb) s =
      a.quantizeSobolev ha (s - m) ∘L b.quantizeSobolev hb s := by
    refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ ?_
    -- On a Schwartz function `u`, `Op(b) u` is a compactly supported Schwartz function.
    refine BesselPotentialSpace.ext ?_
    ext φ
    simp [hb.quantizeSobolev_toBesselPotentialSpaceCLM,
      quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hb]
  simpa using congrArg (fun T ↦ (T u).toDistr) key

/-- **Locality modulo smoothing operators.** Let the symbol `c` with compact spatial support vanish
at positions outside `K`, and let the Schwartz function `χ` have compact support and equal `1` on a
neighbourhood of `K`. Then there is a smoothing symbol `e` with compact spatial support such that
`Op(c) v = Op(c) (χ v) + Op(e) v` for every `v ∈ H^t` and every real `t`: the symbol `e` is
`c ∘ χ - c # χ`. -/
theorem exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add
    {c : Symbol n V W m} (hc : c.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)}
    (hcK : ∀ x ∉ K, ∀ ξ, c.coefficient (x, ξ) = 0) {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (hχK : ∀ᶠ x in 𝓝ˢ K, χ x = 1) :
    ∃ (e : Symbol n V W m) (he : e.HasCompactSpatialSupport), e.IsSmoothing ∧
      ∀ (t : ℝ) (v : H^{t}(CoordinateSpace n, V)),
        (c.quantizeSobolev hc t v).toDistr =
          (c.quantizeSobolev hc t (BesselPotentialSpace.smulLeftCLM t χ v)).toDistr +
            (e.quantizeSobolev he t v).toDistr := by
  have hF := hasCompactSpatialSupport_ofSpatial_smul_id (V := V) hχ
  set F := ofSpatial (fun x ↦ χ x • ContinuousLinearMap.id ℂ V) ((χ.smooth ⊤).smul contDiff_const)
  have hχ1 : ∀ x ∈ K, χ x = 1 := fun x hx ↦ hχK.self_of_nhdsSet x hx
  -- `c ∘ χ = c`, and `c ∘ χ - c # χ` is smoothing.
  have hcomp : (c.comp F).coefficient =
      (Symbol.inclusion (le_of_eq (add_zero m).symm) c).coefficient := by
    funext ⟨x, ξ⟩
    by_cases hx : x ∈ K
    · simp [F, hχ1 x hx]
    · simp [F, hcK x hx]
  have hsm : (c.comp F - c.sharp F hF).IsSmoothing := by
    rw [← neg_sub]
    exact (isSmoothing_sharp_sub_comp hF hcK fun x hx ↦
      (hχK.filter_mono (nhds_le_nhdsSet hx)).mono fun y hy ξ ↦ by simp [F, hy, hχ1 x hx]).neg
  have hsmK : (c.comp F - c.sharp F hF).HasCompactSpatialSupport :=
    (hF.comp_left c).sub (hc.sharp hF)
  have hsmK' := hsmK.of_coefficient_eq (coefficient_inclusion (le_of_eq (add_zero m)) _)
  refine ⟨_, hsmK', hsm.inclusion (le_of_eq (add_zero m)), fun t v ↦ ?_⟩
  -- `Op(c) v = Op(c # χ) v + Op(c ∘ χ - c # χ) v` and `Op(c # χ) v = Op(c) (χ v)`.
  have h₁ : (c.quantizeSobolev hc t v).toDistr =
      ((c.sharp F hF).quantizeSobolev (hc.sharp hF) t v).toDistr +
        ((c.comp F - c.sharp F hF).quantizeSobolev hsmK t v).toDistr := by
    rw [toDistr_quantizeSobolev_sub_apply (hF.comp_left c) (hc.sharp hF) hsmK,
      toDistr_quantizeSobolev_congr (hcomp.trans (coefficient_inclusion _ c)) (hF.comp_left c) hc
        rfl, add_sub_cancel]
  have h₂ : ((c.sharp F hF).quantizeSobolev (hc.sharp hF) t v).toDistr =
      (c.quantizeSobolev hc t (BesselPotentialSpace.smulLeftCLM t χ v)).toDistr := by
    rw [toDistr_quantizeSobolev_sharp hc hF]
    exact toDistr_quantizeSobolev_congr rfl hc hc
      (toDistr_quantizeSobolev_ofSpatial_smul_id χ hF t v)
  rw [h₁, h₂, toDistr_quantizeSobolev_congr (coefficient_inclusion _ _).symm hsmK hsmK' rfl]

/-- **Locality modulo smoothing operators, as an estimate.** Let the symbol `c` with compact
spatial support vanish at positions outside `K`, and let the Schwartz function `χ` have compact
support and equal `1` on a neighbourhood of `K`. Then `Op(c) v` is controlled by `χ v` in `H^t`
and by `v` in any weaker norm `H^r`, `r ≤ t`:
`‖Op(c) v‖_{H^{t - m}} ≤ C (‖χ v‖_{H^t} + ‖v‖_{H^r})`. -/
theorem exists_norm_quantizeSobolev_le_smulLeftCLM {c : Symbol n V W m}
    (hc : c.HasCompactSpatialSupport) {K : Set (CoordinateSpace n)}
    (hcK : ∀ x ∉ K, ∀ ξ, c.coefficient (x, ξ) = 0) {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (hχK : ∀ᶠ x in 𝓝ˢ K, χ x = 1) {r t : ℝ} (hrt : r ≤ t) :
    ∃ C, ∀ v : H^{t}(CoordinateSpace n, V),
      ‖c.quantizeSobolev hc t v‖ ≤ C * (‖BesselPotentialSpace.smulLeftCLM t χ v‖ +
        ‖BesselPotentialSpace.inclusion hrt v‖) := by
  obtain ⟨e, he, hsm, hdec⟩ :=
    exists_isSmoothing_and_toDistr_quantizeSobolev_eq_quantizeSobolev_smulLeftCLM_add hc hcK hχ hχK
  obtain ⟨T, hT⟩ := hsm.exists_continuousLinearMap_toDistr_quantizeSobolev_eq he r (t - m)
  set C := ‖T‖
  refine ⟨‖c.quantizeSobolev hc t‖ + C, fun v ↦ ?_⟩
  set w := T (BesselPotentialSpace.inclusion hrt v)
  have hw := hT (BesselPotentialSpace.toDistr_inclusion hrt v).symm
  have hwle : ‖w‖ ≤ C * ‖BesselPotentialSpace.inclusion hrt v‖ := T.le_opNorm _
  -- `Op(c) v = Op(c) (χ v) + w`.
  have hv : c.quantizeSobolev hc t v =
      c.quantizeSobolev hc t (BesselPotentialSpace.smulLeftCLM t χ v) + w := by
    refine BesselPotentialSpace.ext ?_
    rw [hdec t v, hw, BesselPotentialSpace.toDistr_add]
  rw [hv]
  calc ‖c.quantizeSobolev hc t (BesselPotentialSpace.smulLeftCLM t χ v) + w‖
      ≤ ‖c.quantizeSobolev hc t‖ * ‖BesselPotentialSpace.smulLeftCLM t χ v‖ +
          C * ‖BesselPotentialSpace.inclusion hrt v‖ :=
        (norm_add_le _ _).trans (add_le_add ((c.quantizeSobolev hc t).le_opNorm _) hwle)
    _ ≤ (‖c.quantizeSobolev hc t‖ + C) * (‖BesselPotentialSpace.smulLeftCLM t χ v‖ +
          ‖BesselPotentialSpace.inclusion hrt v‖) := by
        nlinarith [norm_nonneg (c.quantizeSobolev hc t), norm_nonneg T,
          norm_nonneg (BesselPotentialSpace.smulLeftCLM t χ v),
          norm_nonneg (BesselPotentialSpace.inclusion hrt v)]

end Symbol

end TauCeti
