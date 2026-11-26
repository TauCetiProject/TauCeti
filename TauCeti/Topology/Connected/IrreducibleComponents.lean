/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Irreducible

/-!
# Propagating a property along irreducible components through a preconnected core

Let `X` be a topological space with finitely many irreducible components, and let `TI` and `Good`
be subsets of `X`. This file gives a criterion for every point of `TI` to lie in `Good`, read off
from one irreducible component and from the way the components meet along a preconnected subset
`Core`: if one irreducible component meeting `TI` lies in `Good`, and goodness passes between the
components meeting `TI` that cross at a point of a subset `Cl`, then every component meeting `TI`
lies in `Good`, as soon as `Core` is preconnected, every component meeting `TI` reaches `Core`, and
`Core` is covered by the closure of the points of `Cl` outside an exceptional set `EE`, each lying
on a component meeting `TI`. The unions of the components meeting `TI` that do, respectively do
not, lie in `Good` are then two closed sets covering `Core`, and a common point on `Cl` would
contradict the local hypothesis.

This is the global form of the propagation of a property, such as modularity, along the
irreducible components of the spectrum of a deformation ring: components meeting at suitable points
share the property, and preconnectedness carries it across all of them. For the spectrum of a
Noetherian ring, finiteness of the irreducible components is
`TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`.

## Main results

* `IsPreconnected.subset_of_irreducibleComponents`: under the hypotheses above, `TI ⊆ Good`.

## References

* L. Pan, *The Fontaine–Mazur conjecture in the residually reducible case*, J. Amer. Math. Soc. 35
  (2022): the propagation of modularity across irreducible components by this partition argument.
* The formal proof of the Riemann hypothesis by L. Alpöge (2026), whose propagation statement
  `UpperTheory.V.Pr.globProp` has these hypotheses.
-/

public section

open Set

variable {X : Type*} [TopologicalSpace X]

/-- **Propagation along irreducible components.** Let `X` have finitely many irreducible
components, and let `TI, Good, Core, Cl, EE` be subsets of `X` such that `Core` is preconnected,
every closed set meeting `Core` meets `Cl`, `Core` lies in the closure of `Cl \ EE`, every
irreducible component meeting `TI` meets `Core`, every point of `Cl \ EE` lies on an irreducible
component meeting `TI`, and at each point of `Cl`, if one irreducible component through it meeting
`TI` lies in `Good`, then so does every irreducible component through it meeting `TI`. If some
irreducible component meeting `TI` lies in `Good`, then `TI ⊆ Good`. -/
theorem IsPreconnected.subset_of_irreducibleComponents {TI Good Core Cl EE : Set X}
    (hCore : IsPreconnected Core) (hfin : (irreducibleComponents X).Finite)
    (hCl : ∀ s, IsClosed s → (s ∩ Core).Nonempty → (s ∩ Cl).Nonempty)
    (hCoreCl : Core ⊆ closure (Cl \ EE))
    (hTICore : ∀ C ∈ irreducibleComponents X, (C ∩ TI).Nonempty → (C ∩ Core).Nonempty)
    (hClEE : ∀ x ∈ Cl \ EE, ∃ C ∈ irreducibleComponents X, x ∈ C ∧ (C ∩ TI).Nonempty)
    (hloc : ∀ x ∈ Cl, ∀ C ∈ irreducibleComponents X, ∀ C' ∈ irreducibleComponents X,
      x ∈ C → x ∈ C' → (C ∩ TI).Nonempty → (C' ∩ TI).Nonempty → C ⊆ Good → C' ⊆ Good)
    (hGood : ∃ C ∈ irreducibleComponents X, (C ∩ TI).Nonempty ∧ C ⊆ Good) :
    TI ⊆ Good := by
  -- The components meeting `TI` that lie in `Good`, and those that do not.
  set 𝒜 := {C ∈ irreducibleComponents X | (C ∩ TI).Nonempty ∧ C ⊆ Good}
  set ℬ := {C ∈ irreducibleComponents X | (C ∩ TI).Nonempty ∧ ¬C ⊆ Good}
  have hclosed (𝒮 : Set (Set X)) (h𝒮 : 𝒮 ⊆ irreducibleComponents X) : IsClosed (⋃ C ∈ 𝒮, C) :=
    (hfin.subset h𝒮).isClosed_biUnion fun C hC ↦ isClosed_of_mem_irreducibleComponents C (h𝒮 hC)
  have hA := hclosed 𝒜 fun _ hC ↦ hC.1
  have hB := hclosed ℬ fun _ hC ↦ hC.1
  -- Every component meeting `TI` lies in `Good`.
  have hall : ∀ C ∈ irreducibleComponents X, (C ∩ TI).Nonempty → C ⊆ Good := by
    by_contra! ⟨C', hC', hC'TI, hC'G⟩
    have hcover : Core ⊆ (⋃ C ∈ 𝒜, C) ∪ ⋃ C ∈ ℬ, C := by
      refine hCoreCl.trans (closure_minimal (fun x hx ↦ ?_) (hA.union hB))
      obtain ⟨C, hC, hxC, hCTI⟩ := hClEE x hx
      by_cases hCG : C ⊆ Good
      · exact .inl (mem_biUnion ⟨hC, hCTI, hCG⟩ hxC)
      · exact .inr (mem_biUnion ⟨hC, hCTI, hCG⟩ hxC)
    have hmeet (C : Set X) (hC : C ∈ 𝒜 ∪ ℬ) (𝒮 : Set (Set X)) (hC𝒮 : C ∈ 𝒮) :
        (Core ∩ ⋃ C ∈ 𝒮, C).Nonempty := by
      obtain ⟨x, hxC, hxCore⟩ := hTICore C (hC.elim (·.1) (·.1)) (hC.elim (·.2.1) (·.2.1))
      exact ⟨x, hxCore, mem_biUnion hC𝒮 hxC⟩
    obtain ⟨C, hC, hCTI, hCG⟩ := hGood
    obtain ⟨y, hyCore, hyAB⟩ := isPreconnected_closed_iff.1 hCore _ _ hA hB hcover
      (hmeet C (.inl ⟨hC, hCTI, hCG⟩) 𝒜 ⟨hC, hCTI, hCG⟩)
      (hmeet C' (.inr ⟨hC', hC'TI, hC'G⟩) ℬ ⟨hC', hC'TI, hC'G⟩)
    obtain ⟨x, ⟨hxA, hxB⟩, hxCl⟩ := hCl _ (hA.inter hB) ⟨y, hyAB, hyCore⟩
    obtain ⟨C₁, ⟨hC₁, hC₁TI, hC₁G⟩, hxC₁⟩ := mem_iUnion₂.1 hxA
    obtain ⟨C₂, ⟨hC₂, hC₂TI, hC₂G⟩, hxC₂⟩ := mem_iUnion₂.1 hxB
    exact hC₂G (hloc x hxCl C₁ hC₁ C₂ hC₂ hxC₁ hxC₂ hC₁TI hC₂TI hC₁G)
  intro t ht
  obtain ⟨C, hC, htC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {t}
    isIrreducible_singleton
  exact hall C hC ⟨t, htC rfl, ht⟩ (htC rfl)
