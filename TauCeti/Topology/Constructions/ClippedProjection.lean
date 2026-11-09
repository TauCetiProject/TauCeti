/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Preconnected sets compatible with clipped projections

Let `s ⊆ X × Y` and let `O ⊆ Y`. The *clipped projection* of `s` is the projection to `X` of the
part `s ∩ (X × O)` of `s` lying over `O`. When `O` is a bounded strip, clipped projections of a
locally finite family stay locally finite (`LocallyFinite.image_fst_of_subset`), while the
projections of the members themselves need not. This file shows that, under mild conditions on
`s`, a preconnected set which is contained in or disjoint from the clipped projection of `s` is
already contained in or disjoint from the full projection of `s`.

The conditions are that the projection of `s` is open and that the part of `s` lying over `Oᶜ` is
closed and lies, locally over `X`, over compact subsets of `Y`. The projection of that part is then
closed (`IsClosed.isClosed_image_fst_of_locally_subset_isCompact`, a form of the tube lemma), so
the complement of the clipped projection inside `X` is covered by two disjoint closed sets: the
complement of the projection of `s` and the projection of the part over `Oᶜ`. A preconnected set
missing the clipped projection lies in one of them. No compactness of the complement of the
projection of `s` is needed.

In Łojasiewicz's triangulation of semianalytic sets, `s` is the graph of a function over an open
subset of the base, `O` is the strip `|t| < 2` and the part of the graph with `|t| ≥ 2` is closed
and bounded over bounded subsets of the base
(`IsPreconnected.subset_or_disjoint_image_fst_of_isBounded`). A base triangulation compatible with
the clipped projections of a family of such graphs is then compatible with their projections, so
the graphs can be pulled back over its open simplices.

## Main results

* `IsClosed.isClosed_image_fst_of_locally_subset_isCompact`: the projection of a closed set lying
  locally over compact subsets of the fibre is closed.
* `IsPreconnected.subset_or_disjoint_image_fst`: a preconnected set compatible with the clipped
  projection of `s` is compatible with the projection of `s`.
* `IsPreconnected.subset_or_disjoint_image_fst_of_isBounded`: the same in metric spaces, for `s`
  whose parts over `Oᶜ` and over bounded subsets of `X` are bounded.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §4, step II.
-/

public section

open Set Filter Topology Bornology

variable {X Y : Type*}

section Topology

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The projection to `X` of a closed set `s ⊆ X × Y` is closed if, locally over `X`, the points of
`s` lie over a compact subset of `Y`. -/
theorem IsClosed.isClosed_image_fst_of_locally_subset_isCompact {s : Set (X × Y)}
    (hs : IsClosed s) (h : ∀ x, ∃ V ∈ 𝓝 x, ∃ K, IsCompact K ∧ ∀ p ∈ s, p.1 ∈ V → p.2 ∈ K) :
    IsClosed (Prod.fst '' s) := by
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_)
  obtain ⟨V, hV, K, hK, hVK⟩ := h x
  have hxK : ({x} : Set X) ×ˢ K ⊆ sᶜ := by
    rintro ⟨y, k⟩ ⟨rfl, -⟩ hyk
    exact hx ⟨_, hyk, rfl⟩
  obtain ⟨U, W, hU, -, hxU, hKW, hUW⟩ :=
    generalized_tube_lemma isCompact_singleton hK hs.isOpen_compl hxK
  filter_upwards [hV, hU.mem_nhds (hxU rfl)] with y hyV hyU
  rintro ⟨p, hp, rfl⟩
  exact hUW ⟨hyU, hKW (hVK p hp hyV)⟩ hp

/-- Let `s ⊆ X × Y` have open projection to `X`, and let `O ⊆ Y` be such that the part of `s`
lying over `Oᶜ` is closed and lies, locally over `X`, over compact subsets of `Y`. A preconnected
set which is contained in, or disjoint from, the projection of the part of `s` lying over `O` is
contained in, or disjoint from, the projection of `s`. -/
theorem IsPreconnected.subset_or_disjoint_image_fst {C : Set X} (hC : IsPreconnected C)
    {s : Set (X × Y)} {O : Set Y} (hs : IsOpen (Prod.fst '' s))
    (hsO : IsClosed (s ∩ Prod.snd ⁻¹' Oᶜ))
    (hK : ∀ x, ∃ V ∈ 𝓝 x, ∃ K, IsCompact K ∧ ∀ p ∈ s, p.1 ∈ V → p.2 ∉ O → p.2 ∈ K)
    (h : C ⊆ Prod.fst '' (s ∩ Prod.snd ⁻¹' O) ∨ Disjoint C (Prod.fst '' (s ∩ Prod.snd ⁻¹' O))) :
    C ⊆ Prod.fst '' s ∨ Disjoint C (Prod.fst '' s) := by
  have hsub {t : Set Y} : Prod.fst '' (s ∩ Prod.snd ⁻¹' t) ⊆ Prod.fst '' s :=
    image_mono inter_subset_left
  refine h.elim (fun h ↦ .inl (h.trans hsub)) fun h ↦ ?_
  -- The complement of the clipped projection is covered by the complement of the projection of
  -- `s` and the projection `H` of the part of `s` over `Oᶜ`, which is closed.
  have hH : IsClosed (Prod.fst '' (s ∩ Prod.snd ⁻¹' Oᶜ)) :=
    hsO.isClosed_image_fst_of_locally_subset_isCompact fun x ↦
      let ⟨V, hV, K, hK, hVK⟩ := hK x
      ⟨V, hV, K, hK, fun p hp hpV ↦ hVK p hp.1 hpV hp.2⟩
  have hCH : C ⊆ (Prod.fst '' s)ᶜ ∪ Prod.fst '' (s ∩ Prod.snd ⁻¹' Oᶜ) := by
    rintro x hxC
    refine or_iff_not_imp_left.mpr fun hx ↦ ?_
    obtain ⟨p, hp, rfl⟩ := not_not.mp hx
    exact ⟨p, ⟨hp, fun hpO ↦ h.notMem_of_mem_left hxC ⟨p, ⟨hp, hpO⟩, rfl⟩⟩, rfl⟩
  have hdisj : C ∩ ((Prod.fst '' s)ᶜ ∩ Prod.fst '' (s ∩ Prod.snd ⁻¹' Oᶜ)) = ∅ :=
    eq_empty_of_forall_notMem fun x hx ↦ hx.2.1 (hsub hx.2.2)
  exact (isPreconnected_iff_subset_of_disjoint_closed.mp hC _ _ hs.isClosed_compl hH hCH
    hdisj).symm.imp (·.trans hsub) subset_compl_iff_disjoint_right.mp

end Topology

section Metric

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] [ProperSpace Y]

/-- Let `s ⊆ X × Y` have open projection to `X`, and suppose that the part of `s` lying over `Oᶜ`
is closed and that its part over each bounded subset of `X` is bounded. Then a preconnected set
which is contained in, or disjoint from, the projection of the part of `s` lying over `O` is
contained in, or disjoint from, the projection of `s`. -/
theorem IsPreconnected.subset_or_disjoint_image_fst_of_isBounded {C : Set X}
    (hC : IsPreconnected C) {s : Set (X × Y)} {O : Set Y} (hs : IsOpen (Prod.fst '' s))
    (hsO : IsClosed (s ∩ Prod.snd ⁻¹' Oᶜ))
    (hb : ∀ B : Set X, IsBounded B → IsBounded (s ∩ Prod.snd ⁻¹' Oᶜ ∩ Prod.fst ⁻¹' B))
    (h : C ⊆ Prod.fst '' (s ∩ Prod.snd ⁻¹' O) ∨ Disjoint C (Prod.fst '' (s ∩ Prod.snd ⁻¹' O))) :
    C ⊆ Prod.fst '' s ∨ Disjoint C (Prod.fst '' s) := by
  refine hC.subset_or_disjoint_image_fst hs hsO (fun x ↦ ?_) h
  have hB : IsBounded (Prod.snd '' (s ∩ Prod.snd ⁻¹' Oᶜ ∩ Prod.fst ⁻¹' Metric.ball x 1)) :=
    (hb _ Metric.isBounded_ball).image_snd
  exact ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, _, hB.isCompact_closure,
    fun p hp hpV hpO ↦ subset_closure ⟨p, ⟨⟨hp, hpO⟩, hpV⟩, rfl⟩⟩

end Metric
