/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Topology.FilledHull
import Mathlib.Topology.MetricSpace.Bounded
import TauCeti.Topology.ConnectedComponents

/-!
# Sets filled in an open set

A set `K` is *filled in* a set `Ω` (`TauCeti.IsFilledIn K Ω`) if no connected component of
`Ω \ K` is relatively compact in `Ω`, that is, has compact closure contained in `Ω`. This is the
topological hypothesis of Runge-type approximation theorems, under which functions holomorphic, or
harmonic, near a compact set `K ⊆ Ω` are uniform limits on `K` of functions holomorphic, or
harmonic, on all of `Ω`.

In a proper, locally connected metric space,
`TauCeti.isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset` recasts the
condition through the bounded components of `Kᶜ`, which make up the filled hull
`TauCeti.filledHull K \ K`: for closed `K ⊆ Ω`, the set `K` is filled in `Ω` exactly when every
bounded connected component of `Kᶜ` meets `Ωᶜ`. This is the form in which the condition enters
unique-continuation arguments on the complement of `K`: each component of `Kᶜ` is unbounded or
reaches a point outside `Ω`.
For `Ω` the whole space, being filled in it means being equal to the filled hull
(`TauCeti.isFilledIn_univ_iff`).

Filled compact exhaustions of open sets in proper real normed spaces are constructed in
`TauCeti/Analysis/Normed/Module/Exhaustion.lean`.

## Main declarations

* `TauCeti.IsFilledIn`: no connected component of `Ω \ K` is relatively compact in `Ω`.
* `TauCeti.IsFilledIn.compl_inter_connectedComponentIn_nonempty`: every bounded connected
  component of `Kᶜ` meets `Ωᶜ` (without closedness, openness, or local connectedness).
* `TauCeti.isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset`: the same
  condition through the bounded components of `Kᶜ`.
* `TauCeti.isFilledIn_univ_iff`: a closed set is filled in the whole space exactly when it equals
  its filled hull.
* `TauCeti.fillIn`: `K` together with all connected components of `Ω \ K` having compact closure
  contained in `Ω`, with `TauCeti.fillIn_eq_self_iff_isFilledIn`, `TauCeti.isFilledIn_fillIn`,
  `TauCeti.fillIn_univ`, `TauCeti.fillIn_subset_filledHull`, and `IsClosed.fillIn`.
* `TauCeti.frontier_connectedComponentIn_sdiff_subset` and
  `TauCeti.connectedComponentIn_sdiff_eq_of_closure_subset`: when `Ω \ K` is open, a connected
  component of `Ω \ K` whose closure lies in `Ω` has frontier in `K` and coincides with the
  connected component in `Kᶜ`.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public section

open Bornology Metric Set

namespace TauCeti

section Topology

variable {X : Type*} [TopologicalSpace X] {K Ω : Set X}

/-- A set `K` is **filled in** a set `Ω` if no connected component of `Ω \ K` is relatively compact
in `Ω`: the closure of each such component is noncompact or leaves `Ω`. -/
def IsFilledIn (K Ω : Set X) : Prop :=
  ∀ x ∈ Ω \ K,
    ¬ (IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
      closure (connectedComponentIn (Ω \ K) x) ⊆ Ω)

/-- Unfolding `TauCeti.IsFilledIn`. -/
theorem isFilledIn_iff :
    IsFilledIn K Ω ↔ ∀ x ∈ Ω \ K,
      ¬ (IsCompact (closure (connectedComponentIn (Ω \ K) x)) ∧
        closure (connectedComponentIn (Ω \ K) x) ⊆ Ω) :=
  (Iff.rfl)

/-- The domain-relative filling of `K` in `Ω`: `K` together with all connected components of
`Ω \ K` whose closures are compact subsets of `Ω`. -/
def fillIn (K Ω : Set X) : Set X :=
  K ∪ {z | z ∈ Ω \ K ∧
    IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
    closure (connectedComponentIn (Ω \ K) z) ⊆ Ω}

/-- Unfolding `TauCeti.fillIn`. -/
theorem fillIn_def (K Ω : Set X) :
    fillIn K Ω = K ∪ {z | z ∈ Ω \ K ∧
      IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
      closure (connectedComponentIn (Ω \ K) z) ⊆ Ω} :=
  (rfl)

/-- Membership in `TauCeti.fillIn`. -/
theorem mem_fillIn_iff {z : X} :
    z ∈ fillIn K Ω ↔ z ∈ K ∨ z ∈ Ω \ K ∧
      IsCompact (closure (connectedComponentIn (Ω \ K) z)) ∧
      closure (connectedComponentIn (Ω \ K) z) ⊆ Ω :=
  (Iff.rfl)

/-- Any set `K` is contained in `TauCeti.fillIn K Ω`. -/
theorem subset_fillIn : K ⊆ fillIn K Ω :=
  subset_union_left

/-- When `K ⊆ Ω`, `TauCeti.fillIn K Ω` is contained in `Ω`. -/
theorem fillIn_subset (hKΩ : K ⊆ Ω) : fillIn K Ω ⊆ Ω :=
  union_subset hKΩ fun _ hz => hz.1.1

/-- Monotonicity of `TauCeti.fillIn` in `K`. -/
@[gcongr]
theorem fillIn_mono {K₁ K₂ : Set X} (hK : K₁ ⊆ K₂) : fillIn K₁ Ω ⊆ fillIn K₂ Ω := by
  rintro z (hzK₁ | ⟨hzΩK₁, hcpt, hsub⟩)
  · exact subset_fillIn (hK hzK₁)
  · by_cases hzK₂ : z ∈ K₂
    · exact subset_fillIn hzK₂
    · have hC : connectedComponentIn (Ω \ K₂) z ⊆ connectedComponentIn (Ω \ K₁) z :=
        connectedComponentIn_mono z (sdiff_subset_sdiff Subset.rfl hK)
      exact Or.inr ⟨⟨hzΩK₁.1, hzK₂⟩,
        hcpt.of_isClosed_subset isClosed_closure (closure_mono hC),
        (closure_mono hC).trans hsub⟩

/-- Filling `K` in the empty ambient set leaves `K` unchanged. -/
@[simp]
theorem fillIn_empty_right (K : Set X) : fillIn K ∅ = K := by
  simp [fillIn_def]

/-- Filling `K` in itself leaves `K` unchanged. -/
@[simp]
theorem fillIn_self (K : Set X) : fillIn K K = K := by
  simp [fillIn_def]

/-- `TauCeti.fillIn K Ω` equals `K` if and only if `K` is filled in `Ω`. -/
theorem fillIn_eq_self_iff_isFilledIn : fillIn K Ω = K ↔ IsFilledIn K Ω := by
  rw [fillIn_def, union_eq_left, isFilledIn_iff]
  exact ⟨fun h x hx hcpt => hx.2 (h ⟨hx, hcpt⟩),
    fun h x ⟨hx, hcpt⟩ => (h x hx hcpt).elim⟩

/-- `TauCeti.fillIn K Ω` is always filled in `Ω`. -/
@[simp]
theorem isFilledIn_fillIn (K Ω : Set X) : IsFilledIn (fillIn K Ω) Ω := by
  refine isFilledIn_iff.mpr fun x hx ⟨hcpt, hsub⟩ => hx.2 (Or.inr ?_)
  have hxΩK : x ∈ Ω \ K := ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
  have hcomp_eq : connectedComponentIn (Ω \ fillIn K Ω) x = connectedComponentIn (Ω \ K) x := by
    refine Subset.antisymm
      (connectedComponentIn_mono x (sdiff_subset_sdiff Subset.rfl subset_fillIn)) ?_
    refine isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hxΩK) fun y hy => ⟨(connectedComponentIn_subset _ _ hy).1, ?_⟩
    rintro (hyK | ⟨-, hycpt, hysub⟩)
    · exact (connectedComponentIn_subset _ _ hy).2 hyK
    · have hxy : connectedComponentIn (Ω \ K) y = connectedComponentIn (Ω \ K) x :=
        (connectedComponentIn_eq hy).symm
      exact hx.2 (Or.inr ⟨hxΩK, hxy ▸ hycpt, hxy ▸ hysub⟩)
  exact ⟨hxΩK, hcomp_eq ▸ hcpt, hcomp_eq ▸ hsub⟩

/-- Idempotence of `TauCeti.fillIn` in its first argument. -/
@[simp]
theorem fillIn_idem (K Ω : Set X) : fillIn (fillIn K Ω) Ω = fillIn K Ω :=
  fillIn_eq_self_iff_isFilledIn.mpr (isFilledIn_fillIn K Ω)

/-- If `Ω \ K` is open in a locally connected space and a connected component of `Ω \ K` has
closure contained in `Ω`, then its frontier lies in `K`. -/
theorem frontier_connectedComponentIn_sdiff_subset [LocallyConnectedSpace X]
    (hΩK : IsOpen (Ω \ K)) {x : X} (hsub : closure (connectedComponentIn (Ω \ K) x) ⊆ Ω) :
    frontier (connectedComponentIn (Ω \ K) x) ⊆ K := fun y hy => by
  by_contra hyK
  exact frontier_connectedComponentIn_subset_compl hΩK x hy
    ⟨hsub (frontier_subset_closure hy), hyK⟩

/-- If `Ω \ K` is open in a locally connected space and the connected component of `x ∈ Ω \ K` in
`Ω \ K` has closure contained in `Ω`, then it coincides with the connected component of `x` in
`Kᶜ`. -/
theorem connectedComponentIn_sdiff_eq_of_closure_subset [LocallyConnectedSpace X]
    (hΩK : IsOpen (Ω \ K)) {x : X} (hx : x ∈ Ω \ K)
    (hsub : closure (connectedComponentIn (Ω \ K) x) ⊆ Ω) :
    connectedComponentIn (Ω \ K) x = connectedComponentIn Kᶜ x :=
  Subset.antisymm (connectedComponentIn_mono x (sdiff_subset_compl Ω K)) <|
    isPreconnected_connectedComponentIn.subset_connectedComponentIn_of_inter_closure_subset
      hΩK (mem_connectedComponentIn hx.2) hx
      fun _ hy => ⟨hsub hy.2, connectedComponentIn_subset _ _ hy.1⟩

end Topology

section MetricSpace

variable {X : Type*} [PseudoMetricSpace X] [ProperSpace X] {K Ω : Set X}

/-- If a set `K ⊆ Ω` is filled in `Ω`, then every bounded connected component of `Kᶜ` meets
`Ωᶜ` (without requiring `K` to be closed, `Ω` to be open, or `X` to be locally connected). -/
theorem IsFilledIn.compl_inter_connectedComponentIn_nonempty (hfill : IsFilledIn K Ω)
    (hKΩ : K ⊆ Ω) {x : X} (hx : x ∈ filledHull K \ K) :
    (Ωᶜ ∩ connectedComponentIn Kᶜ x).Nonempty := by
  by_contra h
  rw [← sdiff_eq_compl_inter, sdiff_nonempty, not_not] at h
  have hCD : connectedComponentIn (Ω \ K) x ⊆ connectedComponentIn Kᶜ x :=
    connectedComponentIn_mono x (sdiff_subset_compl _ _)
  have hclD : closure (connectedComponentIn Kᶜ x) ⊆ Ω := fun y hy => by
    by_cases hyK : y ∈ K
    · exact hKΩ hyK
    · exact h ((closure_connectedComponentIn_inter_self Kᶜ x).subset ⟨hy, hyK⟩)
  exact hfill x ⟨h (mem_connectedComponentIn hx.2), hx.2⟩
    ⟨(mem_filledHull_iff.mp hx.1).isCompact_closure.of_isClosed_subset isClosed_closure
      (closure_mono hCD), (closure_mono hCD).trans hclD⟩

variable [LocallyConnectedSpace X]

/-- **Filledness through the filled hull.** For a closed set `K` inside an open set `Ω` of a proper,
locally connected metric space, `K` is filled in `Ω` exactly when no bounded connected component
of `Kᶜ` lies in `Ω`, i.e. every bounded component of `Kᶜ` meets `Ωᶜ`. -/
theorem isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    (hK : IsClosed K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔ ∀ x ∈ filledHull K \ K, ¬ connectedComponentIn Kᶜ x ⊆ Ω := by
  constructor
  · intro h x hx
    simpa only [← sdiff_nonempty, sdiff_eq_compl_inter, inter_comm] using
      h.compl_inter_connectedComponentIn_nonempty hKΩ hx
  · -- A relatively compact component of `Ω \ K` equals the component of `x` in `Kᶜ`.
    rintro h x hx ⟨hcpt, hsub⟩
    have hD : connectedComponentIn (Ω \ K) x = connectedComponentIn Kᶜ x :=
      connectedComponentIn_sdiff_eq_of_closure_subset (hΩ.sdiff hK) hx hsub
    exact h x ⟨mem_filledHull_iff.mpr (hD ▸ hcpt.isBounded.subset subset_closure), hx.2⟩
      (hD ▸ subset_closure.trans hsub)

/-- A closed set is filled in the whole space exactly when it equals its filled hull, i.e. its
complement has no bounded connected component. -/
theorem isFilledIn_univ_iff (hK : IsClosed K) : IsFilledIn K univ ↔ filledHull K = K := by
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset hK isOpen_univ
    (subset_univ K)]
  exact ⟨fun h => Subset.antisymm
      (fun x hx => by_contra fun hxK => h x ⟨hx, hxK⟩ (subset_univ _)) subset_filledHull,
    fun h x hx _ => hx.2 (h ▸ hx.1)⟩

omit [LocallyConnectedSpace X] in
/-- Filling `K` in the whole space `Set.univ` of a proper pseudometric space equals
`TauCeti.filledHull K`. -/
@[simp]
theorem fillIn_univ (K : Set X) : fillIn K univ = filledHull K := by
  ext z
  by_cases hzK : z ∈ K
  · exact ⟨fun _ => subset_filledHull hzK, fun _ => subset_fillIn hzK⟩
  · simp only [mem_fillIn_iff, ← compl_eq_univ_sdiff, mem_compl_iff, hzK, false_or,
      not_false_eq_true, true_and, subset_univ, and_true, mem_filledHull_iff]
    exact ⟨fun hcpt => hcpt.isBounded.subset subset_closure,
      fun hbdd => isCompact_of_isClosed_isBounded isClosed_closure hbdd.closure⟩

omit [ProperSpace X] in
/-- When `Ω \ K` is open in a locally connected pseudometric space, `TauCeti.fillIn K Ω` lies
inside `TauCeti.filledHull K`. -/
theorem fillIn_subset_filledHull (hΩK : IsOpen (Ω \ K)) :
    fillIn K Ω ⊆ filledHull K := by
  rintro z (hzK | ⟨hz, hcpt, hsub⟩)
  · exact subset_filledHull hzK
  · exact subset_filledHull_of_frontier_subset (hcpt.isBounded.subset subset_closure)
      (frontier_connectedComponentIn_sdiff_subset hΩK hsub)
      (mem_connectedComponentIn hz)

omit [ProperSpace X] in
/-- For an open set `Ω` and closed `K` in a locally connected pseudometric space,
`TauCeti.fillIn K Ω` is closed. -/
protected theorem _root_.IsClosed.fillIn (hK : IsClosed K) (hΩ : IsOpen Ω) :
    IsClosed (TauCeti.fillIn K Ω) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  by_cases hzF : z ∈ filledHull K
  · have hzK : z ∉ K := fun h => hz (subset_fillIn h)
    refine ⟨connectedComponentIn Kᶜ z, fun w hw hwK' => ?_,
      hK.isOpen_compl.connectedComponentIn, mem_connectedComponentIn hzK⟩
    rcases hwK' with hwK | ⟨hwΩK, hwcpt, hwsub⟩
    · exact connectedComponentIn_subset Kᶜ z hw hwK
    · have hD : connectedComponentIn (Ω \ K) w = connectedComponentIn Kᶜ z :=
        (connectedComponentIn_sdiff_eq_of_closure_subset (hΩ.sdiff hK) hwΩK hwsub).trans
          (connectedComponentIn_eq hw).symm
      have hzC : z ∈ connectedComponentIn (Ω \ K) w := hD.symm ▸ mem_connectedComponentIn hzK
      have hzC_eq : connectedComponentIn (Ω \ K) z = connectedComponentIn (Ω \ K) w :=
        (connectedComponentIn_eq hzC).symm
      exact hz (Or.inr ⟨connectedComponentIn_subset _ _ hzC, hzC_eq ▸ hwcpt, hzC_eq ▸ hwsub⟩)
  · exact ⟨(filledHull K)ᶜ,
      compl_subset_compl.mpr (fillIn_subset_filledHull (hΩ.sdiff hK)),
      hK.isClosed_filledHull.isOpen_compl, hzF⟩

end MetricSpace

end TauCeti
