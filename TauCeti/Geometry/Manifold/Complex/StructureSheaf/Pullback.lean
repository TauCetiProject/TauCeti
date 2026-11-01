/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Pullback
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.MeromorphicGerm

/-!
# Holomorphic stalks inside meromorphic pullback

The embedding of a holomorphic stalk in its meromorphic germ field commutes with pullback.
Even for a map analytic only near the chosen point, meromorphic pullback preserves the
holomorphic subring. A local biholomorphism identifies these subrings in both directions.
Thus the local field equivalence respects regular germs, not merely the ambient fields.

The holomorphic stalk and fraction field are the existing carriers; no new germ or
regularity predicate is introduced.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §1.
-/

public noncomputable section

open Filter Topology Function
open scoped Manifold ContDiff

namespace TauCeti.holomorphicStructureSheaf

/-- Pullback by a locally analytic map preserves the image of the holomorphic stalk. -/
theorem exists_toMeromorphicGerms_pullback {a b : ℂ} (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g a) (hga : g a = b)
    (ht : Tendsto g (𝓝[≠] a) (𝓝[≠] b))
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk b) :
    ∃ t, toMeromorphicGerms a t = meromorphicGerms.pullback g hg hga ht
      (toMeromorphicGerms b s) := by
  obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq b s
  have hfa : AnalyticAt ℂ f b :=
    (contMDiffAt_iff_contDiffAt.mp hf.self_of_nhds).analyticAt
  obtain ⟨t, ht⟩ := exists_toMeromorphicGerms_eq_of_analyticAt (hfa.comp_of_eq hg hga)
  refine ⟨t, Subtype.ext ?_⟩
  rw [ht, meromorphicGerms.coe_pullback, coe_toMeromorphicGerms,
    hfs, Germ.coe_compTendsto]

/-- The holomorphic-stalk embedding intertwines its native pullback with meromorphic
pullback. Here the global analytic hypothesis is exactly that of `stalkPrecomp`. -/
@[simp]
theorem toMeromorphicGerms_stalkPrecomp (g : ℂ → ℂ) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (a : ℂ) (ht : Tendsto g (𝓝[≠] a) (𝓝[≠] g a))
    (s : (holomorphicStructureSheaf 𝓘(ℂ) ℂ).presheaf.stalk (g a)) :
    toMeromorphicGerms a (stalkPrecomp 𝓘(ℂ) ℂ g hg a s) =
      meromorphicGerms.pullback g (contMDiffAt_iff_contDiffAt.mp hg.contMDiffAt).analyticAt rfl ht
        (toMeromorphicGerms (g a) s) := by
  obtain ⟨f, hf, hfs⟩ := exists_toFilterGerm_eq (g a) s
  obtain ⟨k, hk, hkt⟩ := exists_toFilterGerm_eq a (stalkPrecomp 𝓘(ℂ) ℂ g hg a s)
  have h := toFilterGerm_stalkPrecomp g hg a s
  rw [hkt, hfs, Germ.coe_compTendsto, Germ.coe_eq] at h
  apply Subtype.ext
  rw [coe_toMeromorphicGerms, hkt, meromorphicGerms.coe_pullback,
    coe_toMeromorphicGerms, hfs, Germ.coe_compTendsto, Germ.coe_eq]
  exact h.filter_mono nhdsWithin_le_nhds

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

/-- A local biholomorphism pulls back a meromorphic germ to a holomorphic germ exactly when
the original germ is holomorphic. -/
theorem meromorphicGermsEquiv_mem_range_iff (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (he : AnalyticAt ℂ e a)
    (he' : AnalyticAt ℂ e.symm (e a)) (φ : meromorphicGerms ℂ (e a)) :
    e.meromorphicGermsEquiv ha he he' φ ∈ (toMeromorphicGerms a).range ↔
      φ ∈ (toMeromorphicGerms (e a)).range := by
  rw [RingHom.mem_range, RingHom.mem_range]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨s, hs⟩ := exists_toMeromorphicGerms_pullback e.symm he' (e.left_inv ha)
      (by simpa only [e.left_inv ha] using e.symm.tendsto_nhdsNE (e.map_source ha)) t
    refine ⟨s, ?_⟩
    rw [hs, ← meromorphicGermsEquiv_symm_apply e ha he he', ht]
    exact (e.meromorphicGermsEquiv ha he he').symm_apply_apply φ
  · rintro ⟨s, rfl⟩
    simpa only [meromorphicGermsEquiv_apply] using
      exists_toMeromorphicGerms_pullback e he rfl (e.tendsto_nhdsNE ha) s

end OpenPartialHomeomorph
