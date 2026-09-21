/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Topology.Separation.Hausdorff
public import TauCeti.Topology.Compactness.Compact
-- Non-public: the functor `ℕᵒᵖ ⥤ Type _` built from the one-step maps of a sequential system,
-- and Mathlib's Kőnig lemma for it, occur only inside the proof of the sequential form.
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Inverse limits of compact spaces are nonempty

An `InverseSystem f` over a preorder consists of types `X i` together with transition maps
`f h : X j → X i` for `i ≤ j`, composing along the order. A *compatible family*, or section, of
the system is an `x : ∀ i, X i` with `f h (x j) = x i` for every `i ≤ j`. The theorems here say
that such a family exists as soon as the index is directed and every `X i` is nonempty and
compact Hausdorff, and specialize that to the finite systems for which it is Kőnig's lemma.

The data stay unbundled: a family of transition maps and the two laws of `InverseSystem`, with
no functor and no category instance on the index. Mathlib's bundled counterparts are
`TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system` and, for finite systems,
`nonempty_sections_of_finite_cofiltered_system` and `nonempty_sections_of_finite_inverse_system`,
all of which take a functor out of the index category — the plumbing the consumers here do not
have. The sequential form is the one case where that plumbing is cheap to supply, so it is
deduced from `nonempty_sections_of_finite_inverse_system` along
`CategoryTheory.Functor.ofOpSequence` rather than reproved.

## Main statements

* `TauCeti.exists_forall_map_eq_of_compact_t2`: an inverse system of nonempty compact Hausdorff
  spaces over a directed index has a compatible family.
* `TauCeti.exists_forall_map_eq_of_finite`: the same for a system of nonempty finite types.
* `TauCeti.exists_forall_map_eq_of_codirected_of_finite`: the finite statement for a
  `DirectedSystem` over a codirected index, the form in which a system of finite quotients is
  usually written.
* `TauCeti.exists_forall_map_succ_eq_of_finite`: the sequential form, where the system is given
  by its one-step maps `β k : S (k + 1) → S k`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Proposition 1.1.4.
-/

public section

namespace TauCeti

section Directed

variable {ι : Type*} [Preorder ι] [IsDirectedOrder ι] {X : ι → Type*}

/-- **Inverse limits of nonempty compact Hausdorff spaces are nonempty.** Let `X` be a family of
nonempty compact Hausdorff spaces indexed by a directed preorder, forming an inverse system whose
transition maps `f h : X j → X i` are continuous. Then some family `x : ∀ i, X i` is compatible
with all of them. -/
theorem exists_forall_map_eq_of_compact_t2 [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)] (f : ∀ ⦃i j⦄, i ≤ j → X j → X i)
    [InverseSystem f] (hf : ∀ ⦃i j⦄ (h : i ≤ j), Continuous (f h)) :
    ∃ x : ∀ i, X i, ∀ ⦃i j⦄ (h : i ≤ j), f h (x j) = x i := by
  classical
  cases isEmpty_or_nonempty ι
  · exact ⟨fun i ↦ isEmptyElim i, fun i ↦ isEmptyElim i⟩
  -- `C i` collects the families that are compatible with the transition maps into the `X j`
  -- for `j ≤ i`; a point of `⋂ i, C i` is a compatible family.
  set C : ι → Set (∀ i, X i) := fun i ↦ {x | ∀ j, ∀ h : j ≤ i, f h (x i) = x j} with hC
  have hclosed (i : ι) : IsClosed (C i) := by
    have : C i = ⋂ j, ⋂ h : j ≤ i, {x : ∀ i, X i | f h (x i) = x j} := by
      ext x; simp [hC]
    rw [this]
    exact isClosed_iInter fun j ↦ isClosed_iInter fun h ↦
      isClosed_eq ((hf h).comp (continuous_apply i)) (continuous_apply j)
  have hne (i : ι) : (C i).Nonempty := by
    -- Push a single point of `X i` down to every `X j` with `j ≤ i`.
    refine ⟨fun j ↦ if h : j ≤ i then f h (Classical.arbitrary (X i))
      else Classical.arbitrary (X j), fun j h ↦ ?_⟩
    simp only [dite_eq_left h, dite_eq_left (le_refl i), InverseSystem.map_self]
  have hmono ⦃i k : ι⦄ (hik : i ≤ k) : C k ⊆ C i := by
    intro x hx j hji
    rw [← hx i hik, InverseSystem.map_map (f := f), hx j (hji.trans hik)]
  have hdir : Directed (· ⊇ ·) C := fun i₁ i₂ ↦
    let ⟨k, hk₁, hk₂⟩ := exists_ge_ge i₁ i₂
    ⟨k, hmono hk₁, hmono hk₂⟩
  obtain ⟨x, hx⟩ := nonempty_iInter_of_directed_nonempty_isClosed C hdir hne hclosed
  exact ⟨x, fun i j h ↦ Set.mem_iInter.mp hx j i h⟩

/-- **Kőnig's lemma for a directed index.** An inverse system of nonempty finite types over a
directed preorder has a compatible family. -/
theorem exists_forall_map_eq_of_finite [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (f : ∀ ⦃i j⦄, i ≤ j → X j → X i) [InverseSystem f] :
    ∃ x : ∀ i, X i, ∀ ⦃i j⦄ (h : i ≤ j), f h (x j) = x i := by
  let _ : ∀ i, TopologicalSpace (X i) := fun _ ↦ ⊥
  have : ∀ i, DiscreteTopology (X i) := fun _ ↦ ⟨rfl⟩
  exact exists_forall_map_eq_of_compact_t2 f fun _ _ _ ↦ continuous_of_discreteTopology

end Directed

section Codirected

variable {ι : Type*} [Preorder ι] [IsCodirectedOrder ι] {X : ι → Type*}

/-- **Kőnig's lemma for a codirected index.** A `DirectedSystem` of nonempty finite types over a
codirected preorder has a compatible family. This is `exists_forall_map_eq_of_finite` read on the
order dual, and is the form taken by a system of finite quotients indexed by, say, the open
normal subgroups of a profinite group ordered by inclusion: there the maps run along the order
and the index is directed downwards. -/
theorem exists_forall_map_eq_of_codirected_of_finite [∀ i, Finite (X i)] [∀ i, Nonempty (X i)]
    (f : ∀ ⦃i j⦄, i ≤ j → X i → X j) [DirectedSystem X f] :
    ∃ x : ∀ i, X i, ∀ ⦃i j⦄ (h : i ≤ j), f h (x i) = x j := by
  let g : ∀ ⦃i j : ιᵒᵈ⦄, i ≤ j → X (OrderDual.ofDual j) → X (OrderDual.ofDual i) :=
    fun _ _ h ↦ f h
  have : InverseSystem g :=
    { map_self := fun _ x ↦ DirectedSystem.map_self (f := f) x
      map_map := fun _ _ _ hkj hji x ↦ DirectedSystem.map_map (f := f) hji hkj x }
  obtain ⟨x, hx⟩ := exists_forall_map_eq_of_finite g
  exact ⟨fun i ↦ x (OrderDual.toDual i), fun _ _ h ↦ hx (OrderDual.toDual_le_toDual.mpr h)⟩

end Codirected

section Sequence

variable {S : ℕ → Type*} (β : ∀ k, S (k + 1) → S k)

open CategoryTheory in
/-- **Kőnig's lemma, sequential form.** A sequence of nonempty finite types `S k` with one-step
maps `β k : S (k + 1) → S k` has a compatible family: some `s : ∀ k, S k` satisfies
`β k (s (k + 1)) = s k` for every `k`. -/
theorem exists_forall_map_succ_eq_of_finite [∀ k, Finite (S k)] [∀ k, Nonempty (S k)] :
    ∃ s : ∀ k, S k, ∀ k, β k (s (k + 1)) = s k := by
  -- The one-step maps already assemble into a functor `ℕᵒᵖ ⥤ Type _`, so the composites along
  -- `i ≤ j` need not be built by hand; `ℕ` is directed, so Mathlib's Kőnig lemma applies.
  have : ∀ j : ℕᵒᵖ, Finite ((Functor.ofOpSequence fun k ↦ ↾(β k)).obj j) :=
    fun j ↦ inferInstanceAs (Finite (S j.unop))
  have : ∀ j : ℕᵒᵖ, Nonempty ((Functor.ofOpSequence fun k ↦ ↾(β k)).obj j) :=
    fun j ↦ inferInstanceAs (Nonempty (S j.unop))
  obtain ⟨s, hs⟩ :=
    nonempty_sections_of_finite_inverse_system (Functor.ofOpSequence fun k ↦ ↾(β k))
  refine ⟨fun k ↦ s (Opposite.op k), fun k ↦ ?_⟩
  have h := hs (homOfLE (Nat.le_add_right k 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  -- Both the object part of the functor and `↾` are definitional wrappers; see
  -- `CategoryTheory.Functor.ofOpSequence_obj` and `TypeCat.ofHom_apply`.
  exact h

end Sequence

end TauCeti
