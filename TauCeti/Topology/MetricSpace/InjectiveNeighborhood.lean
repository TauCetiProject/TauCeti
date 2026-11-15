/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.ContinuousRadius
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Injective neighbourhoods of a retraction section

Let `s : B → X` be a continuous section of a continuous projection `π : X → B`.
If a continuous map `f : X → Y` induces the topology on the section and is locally
injective there, then it is injective on an open neighbourhood of the entire section.
The section need not be compact or closed. The spaces `X` and `Y` are pseudometrizable.

`Topology.IsInducing.exists_injOn_neighborhood_section` supplies the injective
neighbourhood. `IsLocalHomeomorphOn.exists_isOpenEmbedding_near_section` gives an open
embedding when the map is a local homeomorphism near the section. Applied on the open
local-invertibility locus of a normal exponential, with the bundle projection and zero section,
this is the
passage from local normal coordinates to globally injective tubular coordinates.

The proof uses the continuous subordinate radii of
`Topology.IsInducing.exists_continuous_radius_subordinate`. Comparing the larger of two
radii places both points in one injectivity patch. In addition to their distance from
the section, control the distance of their images from the image of the section.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
Theorem 6.24 (shrinking in the tubular-neighbourhood theorem).
-/

public section

open Set Function Topology

namespace Topology.IsInducing

variable {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace Y]
  [TopologicalSpace.PseudoMetrizableSpace Y]
  {f : X → Y} {s : B → X}

/-- A continuous map that induces the topology on a retraction section and is locally
injective there is injective on an open neighbourhood of the whole section. No compactness
or closedness of the section is required. -/
theorem exists_injOn_neighborhood_section (hind : IsInducing (f ∘ s))
    (hf : Continuous f) (hs : Continuous s) (π : X → B) (hπ : Continuous π)
    (hsect : LeftInverse π s)
    (hloc : ∀ b, ∃ U ∈ 𝓝 (s b), InjOn f U) :
    ∃ U : Set X, IsOpen U ∧ range s ⊆ U ∧ InjOn f U := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric Y
  -- Small balls around the section lie in local injectivity patches.
  have hball : ∀ b, ∃ δ > 0, InjOn f (Metric.ball (s b) (2 * δ)) := by
    intro b
    obtain ⟨U, hU, hinj⟩ := hloc b
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨ε / 2, half_pos hε, ?_⟩
    have heq : 2 * (ε / 2) = ε := by ring
    rw [heq]
    exact hinj.mono hεU
  choose δ hδ hinj using hball
  let W : B → Set B := fun b => s ⁻¹' Metric.ball (s b) (δ b)
  have hW : ∀ b, IsOpen (W b) := fun b => Metric.isOpen_ball.preimage hs
  obtain ⟨r, hr, hsub⟩ := hind.exists_continuous_radius_subordinate W hW
    (fun b => ⟨b, by simpa [W] using hδ b⟩) δ hδ
  let U : Set X := {p | dist p (s (π p)) < r (π p) ∧
    dist (f p) (f (s (π p))) < r (π p)}
  have hrπ : Continuous (fun p => r (π p)) := r.continuous.comp hπ
  have hsπ : Continuous (fun p => s (π p)) := hs.comp hπ
  have hU : IsOpen U :=
    (isOpen_lt (continuous_id.dist hsπ) hrπ).inter
      (isOpen_lt (hf.dist (hf.comp hsπ)) hrπ)
  have hsU : range s ⊆ U := by
    rintro _ ⟨b, rfl⟩
    simp only [U, mem_ofPred_eq, hsect b, dist_self]
    exact ⟨hr b, hr b⟩
  -- A patch chosen using the larger radius contains both points of a collision.
  have hpatch : ∀ p q : X, p ∈ U → q ∈ U → f p = f q → r (π q) ≤ r (π p) → p = q := by
    intro p q hp hq heq hle
    obtain ⟨b, hpb, hrδ, hnear⟩ := hsub (π p)
    have hd : dist (f (s (π p))) (f (s (π q))) < 2 * r (π p) := by
      calc
        dist (f (s (π p))) (f (s (π q))) ≤
            dist (f (s (π p))) (f p) + dist (f p) (f (s (π q))) :=
          dist_triangle _ _ _
        _ < r (π p) + r (π q) := by
          simpa only [heq, dist_comm] using add_lt_add hp.2 hq.2
        _ ≤ 2 * r (π p) := by linarith
    have hqb : π q ∈ W b := hnear (π q) hd
    have hpball : p ∈ Metric.ball (s b) (2 * δ b) := by
      have hbase : dist (s (π p)) (s b) < δ b := hpb
      exact (dist_triangle p (s (π p)) (s b)).trans_lt (by linarith [hp.1])
    have hqball : q ∈ Metric.ball (s b) (2 * δ b) := by
      have hbase : dist (s (π q)) (s b) < δ b := hqb
      exact (dist_triangle q (s (π q)) (s b)).trans_lt (by linarith [hq.1])
    exact hinj b hpball hqball heq
  refine ⟨U, hU, hsU, ?_⟩
  intro p hp q hq heq
  rcases le_total (r (π q)) (r (π p)) with hle | hle
  · exact hpatch p q hp hq heq hle
  · exact (hpatch q p hq hp heq.symm hle).symm

end Topology.IsInducing

namespace IsLocalHomeomorphOn

variable {B X Y : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace Y]
  [TopologicalSpace.PseudoMetrizableSpace Y]
  {f : X → Y} {s : B → X} {O : Set X}

/-- A map that is a local homeomorphism on an open neighbourhood of a continuous retraction
section, and induces the topology on that section, restricts to an open embedding on a
smaller open neighbourhood. The new neighbourhood stays inside the original one. -/
theorem exists_isOpenEmbedding_near_section (hf : IsLocalHomeomorphOn f O)
    (hO : IsOpen O) (hsO : range s ⊆ O) (hs : Continuous s)
    (π : X → B) (hπ : Continuous π) (hsect : LeftInverse π s)
    (hind : IsInducing (f ∘ s)) :
    ∃ U : Set X, IsOpen U ∧ range s ⊆ U ∧ U ⊆ O ∧
      IsOpenEmbedding (U.domRestrict f) := by
  let sO : B → O := fun b => ⟨s b, hsO ⟨b, rfl⟩⟩
  have hsO' : Continuous sO := hs.subtype_mk _
  have hloc : IsLocalHomeomorph (O.domRestrict f) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hf.comp hO.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun p _ => p.property))
  have hindO : IsInducing ((O.domRestrict f) ∘ sO) := hind
  obtain ⟨W, hW, hsW, hinj⟩ := hindO.exists_injOn_neighborhood_section hloc.continuous hsO'
    (π ∘ Subtype.val) (hπ.comp continuous_subtype_val) (fun b => hsect b)
    (fun b => by
      obtain ⟨V, hV, hemb⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hloc (sO b)
      exact ⟨V, hV, Set.injOn_iff_injective.mpr hemb.injective⟩)
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hW
  have hopen : IsOpen (O ∩ V) := hO.inter hV
  have hlocal : IsLocalHomeomorph ((O ∩ V).domRestrict f) :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hf.comp hopen.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun p _ => p.property.1))
  refine ⟨O ∩ V, hopen, ?_, inter_subset_left, hlocal.isOpenEmbedding_of_injective ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨hsO ⟨b, rfl⟩, hsW ⟨b, rfl⟩⟩
  · intro p q hpq
    apply Subtype.ext
    exact congrArg (fun z : O => (z : X))
      (hinj (x₁ := ⟨p.val, p.property.1⟩) p.property.2
        (x₂ := ⟨q.val, q.property.1⟩) q.property.2 hpq)

end IsLocalHomeomorphOn
