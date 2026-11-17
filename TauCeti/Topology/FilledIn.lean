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
* `TauCeti.IsFilledIn.anti`: filledness is antitone in the ambient set when `Ω₁ \ K` is open.
* `TauCeti.IsFilledIn.insert`: inserting a point with arbitrarily small connected punctured
  neighbourhoods preserves filledness.
* `TauCeti.isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset`: the same
  condition through the bounded components of `Kᶜ`.
* `TauCeti.isFilledIn_univ_iff`: a closed set is filled in the whole space exactly when it equals
  its filled hull.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.3.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., Theorem 1.3.9.
-/

public section

open Bornology Metric Set
open scoped Topology

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
  Iff.rfl

/-- Being filled in is antitone in the ambient set: if `K` is filled in `Ω₂` and `Ω₁ ⊆ Ω₂`
with `Ω₁ \ K` open in a locally connected space, then `K` is filled in `Ω₁`. -/
theorem IsFilledIn.anti [LocallyConnectedSpace X] {Ω₁ Ω₂ : Set X} (h : IsFilledIn K Ω₂)
    (hΩ : Ω₁ ⊆ Ω₂) (hΩ₁K : IsOpen (Ω₁ \ K)) : IsFilledIn K Ω₁ := by
  rintro x hx ⟨hcpt, hsub⟩
  have hx₂ : x ∈ Ω₂ \ K := ⟨hΩ hx.1, hx.2⟩
  have hsub₂ : connectedComponentIn (Ω₂ \ K) x ⊆ connectedComponentIn (Ω₁ \ K) x :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn_of_inter_closure_subset hΩ₁K
      (mem_connectedComponentIn hx₂) hx
      fun y hy ↦ ⟨hsub hy.2, (connectedComponentIn_subset _ _ hy.1).2⟩
  exact h x hx₂ ⟨hcpt.of_isClosed_subset isClosed_closure (closure_mono hsub₂),
    (closure_mono hsub₂).trans (hsub.trans hΩ)⟩

/-- Inserting a point that has arbitrarily small neighbourhoods whose punctured versions are
connected preserves filledness in an open complement `Ω \ K`.

The punctured-neighbourhood hypothesis is what fails in `ℝ`, where inserting `0` into `∅` inside
`(-1, 1)` creates relatively compact complementary intervals. -/
protected theorem IsFilledIn.insert [T1Space X] [LocallyConnectedSpace X] (hfill : IsFilledIn K Ω)
    (hΩK : IsOpen (Ω \ K)) {a : X}
    (ha : ∀ U ∈ 𝓝 a, ∃ V ∈ 𝓝 a, V ⊆ U ∧ IsConnected (V \ {a})) :
    IsFilledIn (insert a K) Ω := by
  by_cases haΩK : a ∈ Ω \ K
  · have hEq : Ω \ insert a K = (Ω \ K) \ {a} := by
      ext y; simp [and_comm, and_assoc]
    have hopen : IsOpen (Ω \ insert a K) := hEq ▸ hΩK.sdiff isClosed_singleton
    rintro x hx ⟨hcpt, hsub⟩
    set C := connectedComponentIn (Ω \ insert a K) x
    set D := connectedComponentIn (Ω \ K) x
    have hxK : x ∈ Ω \ K := ⟨hx.1, fun h ↦ hx.2 (Or.inr h)⟩
    have hxD : x ∈ D := mem_connectedComponentIn hxK
    have hclDC : closure D ⊆ closure C := by
      by_cases haC : a ∈ closure C
      · -- A small connected punctured neighbourhood of `a` meets `C`, so it lies in `C`;
        -- adjoining `a` back makes `insert a C` open and traps `D` inside `closure C`.
        obtain ⟨V, hVn, hVsub, hVc⟩ := ha (Ω \ K) (hΩK.mem_nhds haΩK)
        have hVdiff : V \ {a} ⊆ Ω \ insert a K := hEq ▸ sdiff_subset_sdiff_left hVsub
        obtain ⟨y, hyV, hyC⟩ := mem_closure_iff_nhds.1 haC V hVn
        have hyne : y ≠ a := fun hya ↦ (connectedComponentIn_subset _ _ hyC).2 (Or.inl hya)
        have hVC : V \ {a} ⊆ C :=
          (hVc.isPreconnected.subset_connectedComponentIn ⟨hyV, hyne⟩ hVdiff).trans_eq
            (connectedComponentIn_eq hyC).symm
        have hOpenIns : IsOpen (insert a C) := isOpen_iff_mem_nhds.2 fun z hz ↦ by
          rcases hz with rfl | hzC
          · exact Filter.mem_of_superset hVn fun w hw ↦
              (eq_or_ne w z).imp id fun hwz ↦ hVC ⟨hw, hwz⟩
          · exact Filter.mem_of_superset (hopen.connectedComponentIn.mem_nhds hzC)
              (subset_insert a C)
        have hclIns : closure (insert a C) = closure C :=
          (closure_minimal (insert_subset haC subset_closure) isClosed_closure).antisymm
            (closure_mono (subset_insert a C))
        have hDins : D ⊆ insert a C :=
          isPreconnected_connectedComponentIn.subset_of_closure_inter_subset hOpenIns
            ⟨x, hxD, Or.inr (mem_connectedComponentIn hx)⟩ fun y ⟨hycl, hyD⟩ ↦ by
              rw [hclIns] at hycl
              rcases eq_or_ne y a with rfl | hya
              · exact Or.inl rfl
              · have hy_mem : y ∈ Ω \ insert a K :=
                  hEq ▸ ⟨connectedComponentIn_subset _ _ hyD, hya⟩
                exact Or.inr <| interior_subset <| by_contra fun hyi ↦
                  frontier_connectedComponentIn_subset_compl hopen x ⟨hycl, hyi⟩ hy_mem
        exact closure_minimal (hDins.trans (insert_subset haC subset_closure)) isClosed_closure
      · -- `a` is away from `closure C`, so `D` cannot leave `C`.
        exact closure_mono <|
          isPreconnected_connectedComponentIn.subset_connectedComponentIn_of_inter_closure_subset
            hopen hxD hx fun y ⟨hyD, hycl⟩ ↦
              hEq ▸ ⟨connectedComponentIn_subset _ _ hyD, fun hya ↦ haC (hya ▸ hycl)⟩
    exact hfill x hxK ⟨hcpt.of_isClosed_subset isClosed_closure hclDC, hclDC.trans hsub⟩
  · have hEq : Ω \ insert a K = Ω \ K := by
      ext y
      simp only [mem_sdiff, mem_insert_iff, not_or]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩,
        fun h ↦ ⟨h.1, fun hya ↦ haΩK (hya ▸ h), h.2⟩⟩
    rw [isFilledIn_iff, hEq]
    exact hfill

end Topology

section MetricSpace

variable {X : Type*} [PseudoMetricSpace X] [ProperSpace X] [LocallyConnectedSpace X] {K Ω : Set X}

/-- **Filledness through the filled hull.** For a closed set `K` inside an open set `Ω` of a proper,
locally connected metric space, `K` is filled in `Ω` exactly when no bounded connected component
of `Kᶜ` lies in `Ω`, i.e. every bounded component of `Kᶜ` meets `Ωᶜ`. -/
theorem isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset
    (hK : IsClosed K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔ ∀ x ∈ filledHull K \ K, ¬ connectedComponentIn Kᶜ x ⊆ Ω := by
  constructor
  · -- The component `C` of `x` in `Ω \ K` lies in the component `D` of `x` in `Kᶜ`, whose closure
    -- is compact and adds to `D` only points of `K ⊆ Ω`.
    rintro h x ⟨hxH, hxK⟩ hDΩ
    have hCD : connectedComponentIn (Ω \ K) x ⊆ connectedComponentIn Kᶜ x :=
      connectedComponentIn_mono x (sdiff_subset_compl _ _)
    have hclD : closure (connectedComponentIn Kᶜ x) ⊆ Ω := by
      rw [closure_eq_self_union_frontier]
      exact union_subset hDΩ <| (frontier_connectedComponentIn_subset_compl hK.isOpen_compl x).trans
        (by rwa [compl_compl])
    exact h x ⟨hDΩ (mem_connectedComponentIn hxK), hxK⟩
      ⟨(mem_filledHull_iff.mp hxH).isCompact_closure.of_isClosed_subset isClosed_closure
        (closure_mono hCD), (closure_mono hCD).trans hclD⟩
  · -- A relatively compact component of `Ω \ K` would contain the whole component of `x` in `Kᶜ`.
    rintro h x ⟨hxΩ, hxK⟩ ⟨hcpt, hsub⟩
    have hD : connectedComponentIn Kᶜ x ⊆ connectedComponentIn (Ω \ K) x :=
      isPreconnected_connectedComponentIn.subset_connectedComponentIn_of_inter_closure_subset
        (hΩ.sdiff hK) (mem_connectedComponentIn hxK) ⟨hxΩ, hxK⟩
        fun y hy => ⟨hsub hy.2, connectedComponentIn_subset _ _ hy.1⟩
    exact h x ⟨mem_filledHull_iff.mpr (hcpt.isBounded.subset (hD.trans subset_closure)), hxK⟩
      (hD.trans (subset_closure.trans hsub))

/-- A closed set is filled in the whole space exactly when it equals its filled hull, i.e. its
complement has no bounded connected component. -/
theorem isFilledIn_univ_iff (hK : IsClosed K) : IsFilledIn K univ ↔ filledHull K = K := by
  rw [isFilledIn_iff_forall_mem_filledHull_sdiff_not_connectedComponentIn_subset hK isOpen_univ
    (subset_univ K)]
  exact ⟨fun h => Subset.antisymm
      (fun x hx => by_contra fun hxK => h x ⟨hx, hxK⟩ (subset_univ _)) subset_filledHull,
    fun h x hx _ => hx.2 (h ▸ hx.1)⟩

end MetricSpace

end TauCeti
