/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Laurent.Conj
public import TauCeti.Analysis.LaplaceTransform.Basic
import Mathlib.Analysis.Complex.Convex
import TauCeti.Analysis.Meromorphic.Identity

/-!
# Conjugation of Laplace transforms and their meromorphic continuations

Conjugating a scalar Laplace transform conjugates both the input and the spectral parameter
(`TauCeti.HasLaplace.conj`). For a real input the symmetry persists after meromorphic
continuation to a right half-plane: conjugate points have the same order, and at real poles the
leading Laurent coefficient is real.
Normal form is essential for the pointwise identity, since the transform does not prescribe the
values assigned at removable singularities or poles by an arbitrary meromorphic representative.
-/

public section

open Complex Filter MeasureTheory Set
open scoped ComplexConjugate Topology

namespace TauCeti

/-- A meromorphic continuation of a real Laplace transform agrees with its conjugate reflection
as a punctured germ throughout its half-plane of meromorphicity. -/
theorem eventuallyEq_conj_conj_of_hasLaplace {g : ℝ → ℝ} {F : ℂ → ℂ} {A θ : ℝ}
    (hF : MeromorphicOn F {s | θ < s.re})
    (hL : ∀ s : ℂ, A < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s (F s))
    {s : ℂ} (hs : θ < s.re) : F =ᶠ[𝓝[≠] s] conj ∘ F ∘ conj := by
  let x : ℂ := (max A θ + 1 : ℝ)
  have hx : max A θ < x.re := by simp [x]
  have hR : MeromorphicOn (conj ∘ F ∘ conj) {s | θ < s.re} :=
    meromorphicOn_conj_conj_iff.mpr (by simpa [preimage] using hF)
  refine hF.eventuallyEq_of_isPreconnected hR (convex_halfSpace_re_gt θ).isPreconnected
    ((le_max_right A θ).trans_lt hx) hs ?_
  filter_upwards [nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_re).mem_nhds hx)]
    with z hz
  have hAz : A < z.re := (le_max_left A θ).trans_lt hz
  exact (hL z hAz).unique (by simpa using (hL (conj z) (by simpa using hAz)).conj)

/-- The normal form of a continued real Laplace transform commutes with conjugation everywhere
in its half-plane of meromorphicity, including at poles where normal form has value zero. -/
theorem toMeromorphicNFOn_conj_of_hasLaplace {g : ℝ → ℝ} {F : ℂ → ℂ} {A θ : ℝ}
    (hF : MeromorphicOn F {s | θ < s.re})
    (hL : ∀ s : ℂ, A < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s (F s))
    {s : ℂ} (hs : θ < s.re) :
    toMeromorphicNFOn F {z | θ < z.re} (conj s) = conj (toMeromorphicNFOn F {z | θ < z.re} s) := by
  have hsc : θ < (conj s).re := by simpa using hs
  have hR : MeromorphicOn (conj ∘ F ∘ conj) {s | θ < s.re} :=
    meromorphicOn_conj_conj_iff.mpr (by simpa [preimage] using hF)
  have he := (hF.toMeromorphicNFOn_eq_self_on_nhdsNE hsc).trans
    ((eventuallyEq_conj_conj_of_hasLaplace hF hL hsc).trans
      (hR.toMeromorphicNFOn_eq_self_on_nhdsNE hsc).symm)
  have hf := meromorphicNFOn_toMeromorphicNFOn F {z | θ < z.re} hsc
  have hg := meromorphicNFOn_toMeromorphicNFOn (conj ∘ F ∘ conj) {z | θ < z.re} hsc
  have hv := ((hf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hg).mp he).eq_of_nhds
  simpa [toMeromorphicNFOn_conj_conj, preimage, Function.comp_apply] using hv

/-- A continued real Laplace transform has equal meromorphic orders at conjugate points. -/
theorem meromorphicOrderAt_conj_of_hasLaplace {g : ℝ → ℝ} {F : ℂ → ℂ} {A θ : ℝ}
    (hF : MeromorphicOn F {s | θ < s.re})
    (hL : ∀ s : ℂ, A < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s (F s))
    {s : ℂ} (hs : θ < s.re) : meromorphicOrderAt F (conj s) = meromorphicOrderAt F s := by
  rw [← meromorphicOrderAt_conj_conj]
  exact (meromorphicOrderAt_congr (eventuallyEq_conj_conj_of_hasLaplace hF hL hs)).symm

/-- All Laurent coefficients at a real point of a continued real Laplace transform are real. -/
theorem im_coeff_laurentSeries_eq_zero_of_hasLaplace {g : ℝ → ℝ} {F : ℂ → ℂ} {A θ b : ℝ}
    (hF : MeromorphicOn F {s | θ < s.re})
    (hL : ∀ s : ℂ, A < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s (F s))
    (hb : θ < b) (n : ℤ) :
    ((meromorphicGerms.laurentSeries (b : ℂ)
      (meromorphicGerms.mk F (hF b (by simpa using hb)))).coeff n).im = 0 := by
  have hb' : θ < (b : ℂ).re := by simpa using hb
  have h := meromorphicGerms.coeff_laurentSeries_conj_conj (conj_ofReal b) (hF b hb') n
  have he : meromorphicGerms.mk F (hF b hb') = meromorphicGerms.mk (conj ∘ F ∘ conj)
      (meromorphicAt_conj_conj_iff.mpr ((conj_ofReal b).symm ▸ hF b hb')) :=
    meromorphicGerms.mk_eq_mk_iff.mpr (eventuallyEq_conj_conj_of_hasLaplace hF hL hb')
  rw [← he] at h
  exact conj_eq_iff_im.mp h.symm

/-- The leading Laurent coefficient at a real point of a continued real Laplace transform is
real. At a simple pole this is the reality of the residue. -/
theorem im_meromorphicTrailingCoeffAt_eq_zero_of_hasLaplace {g : ℝ → ℝ} {F : ℂ → ℂ}
    {A θ b : ℝ} (hF : MeromorphicOn F {s | θ < s.re})
    (hL : ∀ s : ℂ, A < s.re → HasLaplace (fun u ↦ (g u : ℂ)) s (F s))
    (hb : θ < b) : (meromorphicTrailingCoeffAt F (b : ℂ)).im = 0 := by
  have h := meromorphicTrailingCoeffAt_congr_nhdsNE
    (eventuallyEq_conj_conj_of_hasLaplace hF hL (s := b) (by simpa using hb))
  exact conj_eq_iff_im.mp (by simpa only [meromorphicTrailingCoeffAt_conj_conj, conj_ofReal]
    using h.symm)

end TauCeti
