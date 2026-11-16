/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# Normed-space core transfer for partial linear maps

If `C` is a graph core (`LinearPMap.HasCore`) for a partial linear map `A : E →ₗ.[𝕜] F` between
seminormed spaces and `B : E →ₗ.[𝕜] G` is a closed partial linear map into a complete seminormed
space satisfying `C ≤ B.domain` and `‖B u‖ = ‖A u‖` on `C`, then `A.domain ≤ B.domain` and
`‖B x‖ = ‖A x‖` for every `x ∈ A.domain` (`LinearPMap.HasCore.domain_le_and_norm_eq`).

Approximating `(x, A x)` in `A.graph` by elements `(uₙ, A uₙ)` with `uₙ ∈ C` makes `(A uₙ)` Cauchy;
the isometric relation on `C` makes `(B uₙ)` Cauchy in the complete space `G`, and closedness of `B`
places `x` in `B.domain` with the same norm.

## Main declarations

* `LinearPMap.HasCore.domain_le_and_norm_eq`: domain inclusion `A.domain ≤ B.domain` and pointwise
  norm equality `‖B x‖ = ‖A x‖` transferred from a core `C` of `A` to a closed operator `B`.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §III.5.3.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press (1980), §VIII.1.
-/

public section

open Filter Topology

namespace LinearPMap

variable {𝕜 E F G : Type*} [NormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [Module 𝕜 G] [CompleteSpace G]

/-- If `C` is a core for a partial linear map `A : E →ₗ.[𝕜] F` and `B : E →ₗ.[𝕜] G` is a closed
partial linear map into a complete space with `C ≤ B.domain` and `‖B u‖ = ‖A u‖` on `C`, then
`A.domain ≤ B.domain` and `‖B x‖ = ‖A x‖` on `A.domain`. -/
theorem HasCore.domain_le_and_norm_eq {A : E →ₗ.[𝕜] F} {B : E →ₗ.[𝕜] G}
    {C : Submodule 𝕜 E} (hcore : A.HasCore C) (hB : B.IsClosed)
    (hCB : C ≤ B.domain) (hnorm : ∀ u (hu : u ∈ C), ‖B ⟨u, hCB hu⟩‖ = ‖A ⟨u, hcore.1 hu⟩‖) :
    ∃ h : A.domain ≤ B.domain, ∀ x : A.domain, ‖B ⟨x, h x.2⟩‖ = ‖A x‖ := by
  have key : ∀ x (hx : x ∈ A.domain), ∃ hxB : x ∈ B.domain, ‖B ⟨x, hxB⟩‖ = ‖A ⟨x, hx⟩‖ := by
    intro x hx
    have hmem : (x, A ⟨x, hx⟩) ∈ _root_.closure ((A.domRestrict C).graph : Set (E × F)) :=
      hcore.graph_subset_of_isClosed isClosed_closure subset_closure (A.mem_graph ⟨x, hx⟩)
    obtain ⟨p, hp, hplim⟩ := mem_closure_iff_seq_limit.mp hmem
    have hv : ∀ n, ∃ u : E, ∃ hu : u ∈ C, p n = (u, A ⟨u, hcore.1 hu⟩) := fun n ↦ by
      obtain ⟨v, hv⟩ := (mem_graph_iff' (A.domRestrict C)).mp (hp n)
      have hval : (A.domRestrict C) v = A ⟨v, hcore.1 v.2.1⟩ := A.domRestrict_le.2 rfl
      exact ⟨v, v.2.1, hv.symm.trans (Prod.ext rfl hval)⟩
    choose u hu hp_eq using hv
    have hulim : Tendsto u atTop (𝓝 x) := by
      simpa [Function.comp_def, hp_eq] using (continuous_fst.tendsto _).comp hplim
    have hAlim : Tendsto (fun n ↦ A ⟨u n, hcore.1 (hu n)⟩) atTop (𝓝 (A ⟨x, hx⟩)) := by
      simpa [Function.comp_def, hp_eq] using (continuous_snd.tendsto _).comp hplim
    have hBcauchy : CauchySeq fun n ↦ B ⟨u n, hCB (hu n)⟩ := by
      refine Metric.cauchySeq_iff.mpr fun ε hε ↦ ?_
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hAlim.cauchySeq ε hε
      refine ⟨N, fun m hm n hn ↦ ?_⟩
      have hdist : dist (B ⟨u m, hCB (hu m)⟩) (B ⟨u n, hCB (hu n)⟩) =
          dist (A ⟨u m, hcore.1 (hu m)⟩) (A ⟨u n, hcore.1 (hu n)⟩) := by
        rw [dist_eq_norm, dist_eq_norm, ← B.map_sub, ← A.map_sub]
        exact hnorm (u m - u n) (C.sub_mem (hu m) (hu n))
      exact hdist ▸ hN m hm n hn
    obtain ⟨y, hBlim⟩ := cauchySeq_tendsto_of_complete hBcauchy
    obtain ⟨hxB, hBy⟩ := hB.mem_domain_of_tendsto (fun n ↦ hCB (hu n)) hulim hBlim
    refine ⟨hxB, hBy ▸ tendsto_nhds_unique hBlim.norm ?_⟩
    simpa only [Function.comp_def, hnorm _ (hu _)] using hAlim.norm
  exact ⟨fun x hx ↦ (key x hx).1, fun x ↦ (key x.1 x.2).2⟩

end LinearPMap
