/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Periodic sections of translation-invariant coverings

Let `V` be a topological group which is simply connected and locally path-connected, such as a
finite-dimensional real vector space, and let `E ⊆ V × Y` be a set whose projection `E → V` to the
first factor is a covering map. By the lifting criterion
(`IsCoveringMap.existsUnique_continuousMap_lifts`), the identity of `V` lifts through every point
of `E`: every point of `E` lies on the graph of a continuous map `g : V → Y` whose graph is
contained in `E` (`IsCoveringMap.exists_continuous_forall_prodMk_mem`), and two such maps that
agree at one point are equal (`IsCoveringMap.eq_of_forall_prodMk_mem`). So `E` is the disjoint
union of the graphs of these global sections, one through each point of a fibre.

Suppose that `E` is moreover invariant under the translations of the base by a subgroup `Λ ≤ V`,
and that one fibre of `E` is finite. Translating a section by `ω ∈ Λ` gives another section, and
by uniqueness there are only finitely many sections. Hence every section is periodic for a
subgroup of finite index of `Λ` (`IsCoveringMap.exists_relIndex_ne_zero_forall_add_eq`): the
subgroup of its periods in `Λ`, whose cosets correspond to its distinct translates. This step
only uses that `V` is connected.

For `V = ℂ` and `Λ` a lattice, `E` is the preimage in `ℂ × Y` of a finite covering of the torus
`ℂ ⧸ Λ` sitting inside `(ℂ ⧸ Λ) × Y`, and the subgroup of finite index is the lattice of a finite
covering torus `ℂ ⧸ Λ'` over which each sheet of the covering becomes the graph of a map. This
is how a curve in the normal bundle of a torus which covers the torus without branching is
turned into sections of the normal bundle pulled back to finite covers.

## Main results

* `IsCoveringMap.exists_continuous_forall_prodMk_mem`: every point of `E` lies on the graph of a
  continuous section whose graph is contained in `E`.
* `IsCoveringMap.eq_of_forall_prodMk_mem`: two such sections which agree at one point are equal.
* `IsCoveringMap.exists_relIndex_ne_zero_forall_add_eq`: if `E` is invariant under translation
  by `Λ` and has a finite fibre, every such section is periodic for a subgroup of finite index of
  `Λ`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 1.3, Proposition 1.33 (the lifting criterion) and Proposition 1.34 (unique lifting).
-/

public section

open Set

namespace IsCoveringMap

variable {V Y : Type*} [TopologicalSpace V] [TopologicalSpace Y] {E : Set (V × Y)}

/-- **Global sections through every point.** If the projection to the first factor of a set
`E ⊆ V × Y` is a covering map over a simply connected, locally path-connected space `V`, then
every point `q ∈ E` lies on the graph of a continuous map `g : V → Y` whose graph is contained in
`E`. -/
theorem exists_continuous_forall_prodMk_mem [SimplyConnectedSpace V]
    [LocallyPathConnectedSpace V] (hE : IsCoveringMap fun q : E ↦ (q : V × Y).1) {q : V × Y}
    (hq : q ∈ E) : ∃ g : V → Y, Continuous g ∧ (∀ x, (x, g x) ∈ E) ∧ g q.1 = q.2 := by
  obtain ⟨F, ⟨hF₀, hF⟩, -⟩ :=
    hE.existsUnique_continuousMap_lifts (ContinuousMap.id V) q.1 ⟨q, hq⟩ rfl
  -- The lift `F` of the identity is a section, so `F x` is the point of `E` over `x`.
  have hx (x : V) : (x, ((F x : E) : V × Y).2) = F x := Prod.ext (congrFun hF x).symm rfl
  refine ⟨fun x ↦ ((F x : E) : V × Y).2, by fun_prop, fun x ↦ hx x ▸ (F x).property, ?_⟩
  simp [hF₀]

/-- **Uniqueness of sections.** If the projection to the first factor of a set `E ⊆ V × Y` is a
covering map over a preconnected space `V`, two continuous maps `V → Y` whose graphs are
contained in `E` and which agree at one point are equal. -/
theorem eq_of_forall_prodMk_mem [PreconnectedSpace V]
    (hE : IsCoveringMap fun q : E ↦ (q : V × Y).1) {g₁ g₂ : V → Y} (h₁ : Continuous g₁)
    (h₂ : Continuous g₂) (hg₁ : ∀ x, (x, g₁ x) ∈ E) (hg₂ : ∀ x, (x, g₂ x) ∈ E) {x₀ : V}
    (h : g₁ x₀ = g₂ x₀) : g₁ = g₂ := by
  have hlift := hE.eq_of_comp_eq (g₁ := fun x ↦ (⟨(x, g₁ x), hg₁ x⟩ : E))
    (g₂ := fun x ↦ ⟨(x, g₂ x), hg₂ x⟩) (by fun_prop) (by fun_prop) rfl x₀ (by simp [h])
  funext x
  simpa using congrArg (fun q : E ↦ (q : V × Y).2) (congrFun hlift x)

variable [AddGroup V] [ContinuousAdd V]

/-- **Sections of a translation-invariant covering are periodic.** Let `V` be a preconnected
topological group, and let `E ⊆ V × Y` be a set whose projection to `V` is a covering map, with a
finite fibre, and which is invariant under the translations of `V` by a subgroup `Λ`. Then every
continuous map `g : V → Y` whose graph is contained in `E` is periodic for a subgroup of finite
index of `Λ`. -/
theorem exists_relIndex_ne_zero_forall_add_eq [PreconnectedSpace V]
    (hE : IsCoveringMap fun q : E ↦ (q : V × Y).1)
    {Λ : AddSubgroup V} (hΛ : ∀ ω ∈ Λ, ∀ q ∈ E, (q.1 + ω, q.2) ∈ E) {x₀ : V}
    (hfin : {y | (x₀, y) ∈ E}.Finite) {g : V → Y} (hg : Continuous g)
    (hgE : ∀ x, (x, g x) ∈ E) :
    ∃ L' : AddSubgroup V, L' ≤ Λ ∧ L'.relIndex Λ ≠ 0 ∧ ∀ ω ∈ L', ∀ x, g (x + ω) = g x := by
  -- The sections form a finite set `S`: a section is determined by its value at `x₀`.
  set S : Set (V → Y) := {f | Continuous f ∧ ∀ x, (x, f x) ∈ E}
  have hSfin : S.Finite :=
    Finite.of_finite_image (hfin.subset (image_subset_iff.2 fun f hf ↦ hf.2 x₀))
      fun f₁ hf₁ f₂ hf₂ h ↦ hE.eq_of_forall_prodMk_mem hf₁.1 hf₂.1 hf₁.2 hf₂.2 h
  -- Translating a section by an element of `Λ` gives a section.
  have htrans (ω : Λ) : (fun x ↦ g (x + ω)) ∈ S := by
    refine ⟨by fun_prop, fun x ↦ ?_⟩
    simpa using hΛ (-ω) (neg_mem ω.property) _ (hgE (x + ω))
  -- The periods of `g` in `Λ`.
  let L' : AddSubgroup V :=
    { carrier := {ω | ω ∈ Λ ∧ ∀ x, g (x + ω) = g x}
      zero_mem' := ⟨Λ.zero_mem, by simp⟩
      add_mem' := fun {a b} ha hb ↦ ⟨Λ.add_mem ha.1 hb.1, fun x ↦ by
        rw [← add_assoc, hb.2, ha.2]⟩
      neg_mem' := fun {a} ha ↦ ⟨Λ.neg_mem ha.1, fun x ↦ by
        rw [← ha.2 (x + -a), neg_add_cancel_right]⟩ }
  refine ⟨L', fun ω hω ↦ hω.1, ?_, fun ω hω ↦ hω.2⟩
  -- The translates `x ↦ g (x + ω)` are in bijection with the cosets of `L'` in `Λ`.
  have hcoset (a b : Λ) : -a + b ∈ L'.addSubgroupOf Λ ↔
      (fun x ↦ g (x + a)) = fun x ↦ g (x + b) := by
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨fun h ↦ funext fun x ↦ ?_, fun h ↦ ⟨(-a + b).property, fun x ↦ ?_⟩⟩
    · rw [← h.2 (x + a)]
      simp [add_assoc]
    · have := congrFun h (x + -a)
      simp only [neg_add_cancel_right] at this
      simp [this, ← add_assoc]
  let φ : Λ ⧸ L'.addSubgroupOf Λ → S :=
    Quotient.lift (fun ω ↦ ⟨fun x ↦ g (x + ω), htrans ω⟩) fun a b hab ↦
      Subtype.ext ((hcoset a b).1 (QuotientAddGroup.leftRel_apply.1 hab))
  have hφ : Function.Injective φ := by
    rintro ⟨a⟩ ⟨b⟩ hab
    exact Quotient.sound
      (QuotientAddGroup.leftRel_apply.2 ((hcoset a b).2 (congrArg Subtype.val hab)))
  have : Finite S := hSfin.to_subtype
  have : Finite (Λ ⧸ L'.addSubgroupOf Λ) := Finite.of_injective φ hφ
  exact AddSubgroup.index_ne_zero_of_finite

end IsCoveringMap
