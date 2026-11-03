/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Invertibility of pullback on holomorphic stalks

For a function analytic near a point, pullback on holomorphic stalks is an isomorphism
exactly when the derivative is nonzero. In fact, surjectivity alone suffices: a preimage of
the coordinate germ provides a holomorphic left inverse, so the chain rule forces a nonzero
derivative. Conversely, the analytic inverse function theorem supplies preimages of every
germ, and local openness detects equality of pulled-back germs.

These criteria concern the native structure-sheaf stalks, including their entire germ maps,
not merely their residue fields. They recognize inverses of maps on branches of nodal curves.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §1 (holomorphic local coordinates).
-/

public noncomputable section

open Filter Topology
open scoped Manifold ContDiff

namespace TauCeti.holomorphicStructureSheaf

variable {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)

/-- Pullback on holomorphic stalks is surjective exactly when the branch derivative is nonzero.
Surjectivity of the residue-field map alone would not suffice. -/
theorem stalkPullback_surjective_iff :
    Function.Surjective (stalkPullback (eventually_contMDiffAt_of_analyticAt hf)) ↔
      deriv f a ≠ 0 := by
  constructor
  · intro hsurj
    obtain ⟨c, hc⟩ := exists_toFilterGerm_eq_of_analyticAt (analyticAt_id (z := a))
    obtain ⟨t, ht⟩ := hsurj c
    obtain ⟨u, hua, hut⟩ := exists_toFilterGerm_eq_analyticAt (f a) t
    have hcomp := congrArg (toFilterGerm 𝓘(ℂ) ℂ a (𝓝 a) le_rfl) ht
    rw [toFilterGerm_stalkPullback, hut, hc, Germ.coe_compTendsto, Germ.coe_eq] at hcomp
    have hchain := hua.differentiableAt.hasDerivAt.comp a hf.differentiableAt.hasDerivAt
    have hder := hchain.congr_of_eventuallyEq hcomp.symm
    have hmul := hder.unique (hasDerivAt_id a)
    intro hz
    simp [hz] at hmul
  · intro hne t
    let g := hf.hasStrictDerivAt.localInverse f (deriv f a) a hne
    have hga : g (f a) = a := HasStrictFDerivAt.localInverse_apply_image _
    have hg : AnalyticAt ℂ g (f a) := hf.analyticAt_localInverse hne
    have hgf : ∀ᶠ z in 𝓝 a, g (f z) = z :=
      hf.hasStrictDerivAt.eventually_left_inverse hne
    obtain ⟨u, hua, hut⟩ := exists_toFilterGerm_eq_analyticAt a t
    obtain ⟨v, hv⟩ := exists_toFilterGerm_eq_of_analyticAt (hua.comp_of_eq hg hga)
    refine ⟨v, toFilterGerm_nhds_injective a ?_⟩
    rw [toFilterGerm_stalkPullback, hv, hut, Germ.coe_compTendsto, Germ.coe_eq]
    exact hgf.mono fun z hz ↦ congrArg u hz

/-- A local analytic map induces an isomorphism of holomorphic stalks exactly when its
derivative is nonzero. -/
theorem stalkPullback_bijective_iff :
    Function.Bijective (stalkPullback (eventually_contMDiffAt_of_analyticAt hf)) ↔
      deriv f a ≠ 0 := by
  refine ⟨fun h ↦ (stalkPullback_surjective_iff hf).mp h.2, fun hne ↦ ⟨?_,
    (stalkPullback_surjective_iff hf).mpr hne⟩⟩
  intro t u htu
  obtain ⟨v, _, hvt⟩ := exists_toFilterGerm_eq (f a) t
  obtain ⟨w, _, hwu⟩ := exists_toFilterGerm_eq (f a) u
  apply toFilterGerm_nhds_injective (f a)
  have h := congrArg (toFilterGerm 𝓘(ℂ) ℂ a (𝓝 a) le_rfl) htu
  rw [toFilterGerm_stalkPullback, toFilterGerm_stalkPullback, hvt, hwu,
    Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_eq] at h
  rw [hvt, hwu, Germ.coe_eq, ← hf.hasStrictDerivAt.map_nhds_eq hne]
  exact h

/-- The holomorphic-stalk isomorphism induced by an analytic map with nonzero derivative. -/
def stalkPullbackEquiv (hf0 : deriv f a ≠ 0) :
    (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a) ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk a :=
  RingEquiv.ofBijective (stalkPullback (eventually_contMDiffAt_of_analyticAt hf))
    ((stalkPullback_bijective_iff hf).mpr hf0)

/-- The stalk isomorphism acts by pullback of holomorphic germs. -/
@[simp]
theorem stalkPullbackEquiv_apply (hf0 : deriv f a ≠ 0)
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (f a)) :
    stalkPullbackEquiv hf hf0 s = stalkPullback (eventually_contMDiffAt_of_analyticAt hf) s := (rfl)

end TauCeti.holomorphicStructureSheaf
