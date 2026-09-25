/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Topology.Separation.Hausdorff
-- Non-public: the functors out of the index category that the unbundled data assemble into, and
-- Mathlib's limit theorems for them, occur only inside the proofs.
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Topology.Category.TopCat.Limits.Konig

/-!
# Inverse limits of compact spaces are nonempty

An `InverseSystem f` over a preorder consists of types `X i` together with transition maps
`f h : X j → X i` for `i ≤ j`, composing along the order. A *compatible family*, or section, of
the system is an `x : ∀ i, X i` with `f h (x j) = x i` for every `i ≤ j`. The theorems here say
that such a family exists as soon as the index is directed and every `X i` is nonempty and
compact Hausdorff, and specialize that to the finite systems for which it is Kőnig's lemma.

The data stay unbundled: a family of transition maps and the two laws of `InverseSystem`, with
no functor and no category instance on the index. That is the shape such a system has when it
arises — the finite quotients of a profinite group and the maps between them, or the sets of
Sylow subgroups of those quotients — and a compatible family is then exactly a point of the
inverse limit, so these are the statements a construction of such a point applies directly. The
mathematics is Mathlib's Kőnig lemma for cofiltered systems and is not reproved here.

## Main statements

* `TauCeti.exists_forall_map_eq_of_compact_t2`: an inverse system of nonempty compact Hausdorff
  spaces over a directed index has a compatible family.
* `TauCeti.exists_forall_map_eq_of_finite`: the same for a system of nonempty finite types.
* `TauCeti.exists_forall_map_eq_of_codirected_of_finite`: the finite statement for a
  `DirectedSystem` over a codirected index, the form in which a system of finite quotients is
  usually written.
* `TauCeti.exists_forall_map_succ_eq_of_compact_t2`, `TauCeti.exists_forall_map_succ_eq_of_finite`:
  the sequential forms, where the system is given by its one-step maps `β k : S (k + 1) → S k`.
* `TauCeti.exists_forall_map_succ_eq_and_forall_eq_of_compact_t2`: along a map of sequential
  towers of compact Hausdorff spaces that is surjective at every level, compatible families lift;
  that is, the inverse limit of levelwise surjections of compact spaces is surjective.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Proposition 1.1.4.
-/

public section

namespace TauCeti

section Directed

universe u w

variable {ι : Type u} [Preorder ι] [IsDirectedOrder ι] {X : ι → Type w}

open CategoryTheory in
/-- An inverse system of topological spaces, read as a functor `ιᵒᵖ ⥤ TopCat`. The spaces are
`ULift`ed into the universe `max w u` in which Mathlib's limit theorem expects them. -/
private def topCatFunctor [∀ i, TopologicalSpace (X i)] (f : ∀ ⦃i j⦄, i ≤ j → X j → X i)
    [InverseSystem f] (hf : ∀ ⦃i j⦄ (h : i ≤ j), Continuous (f h)) : ιᵒᵖ ⥤ TopCat.{max w u} where
  obj i := TopCat.of (ULift.{u} (X i.unop))
  map h := TopCat.ofHom ⟨fun x ↦ ULift.up (f (leOfHom h.unop) x.down),
    continuous_uliftUp.comp ((hf _).comp continuous_uliftDown)⟩
  map_id i := by ext x; exact InverseSystem.map_self (f := f) x.down
  map_comp g h := by ext x; exact (InverseSystem.map_map (f := f) _ _ x.down).symm

open CategoryTheory in
/-- **Inverse limits of nonempty compact Hausdorff spaces are nonempty.** Let `X` be a family of
nonempty compact Hausdorff spaces indexed by a directed preorder, forming an inverse system whose
transition maps `f h : X j → X i` are continuous. Then some family `x : ∀ i, X i` is compatible
with all of them. -/
theorem exists_forall_map_eq_of_compact_t2 [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, T2Space (X i)] [∀ i, Nonempty (X i)] (f : ∀ ⦃i j⦄, i ≤ j → X j → X i)
    [InverseSystem f] (hf : ∀ ⦃i j⦄ (h : i ≤ j), Continuous (f h)) :
    ∃ x : ∀ i, X i, ∀ ⦃i j⦄ (h : i ≤ j), f h (x j) = x i := by
  -- The index is directed, so `ιᵒᵖ` is cofiltered and Mathlib's Kőnig lemma for compact
  -- Hausdorff systems applies to the functor the data assemble into.
  have : ∀ i : ιᵒᵖ, Nonempty ((topCatFunctor f hf).obj i) :=
    fun i ↦ inferInstanceAs (Nonempty (ULift (X i.unop)))
  have : ∀ i : ιᵒᵖ, CompactSpace ((topCatFunctor f hf).obj i) :=
    fun i ↦ inferInstanceAs (CompactSpace (ULift (X i.unop)))
  have : ∀ i : ιᵒᵖ, T2Space ((topCatFunctor f hf).obj i) :=
    fun i ↦ inferInstanceAs (T2Space (ULift (X i.unop)))
  obtain ⟨⟨x, hx⟩⟩ := TopCat.nonempty_limitCone_of_compact_t2_cofiltered_system (topCatFunctor f hf)
  -- A point of the limit is a compatible family, once the `ULift` wrapper is removed.
  exact ⟨fun i ↦ (x (Opposite.op i)).down, fun i j h ↦ congrArg ULift.down (hx (homOfLE h).op)⟩

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
/-- **Inverse limits of compact spaces, sequential form.** A sequence of nonempty compact
Hausdorff spaces `S k` with continuous one-step maps `β k : S (k + 1) → S k` has a compatible
family: some `s : ∀ k, S k` satisfies `β k (s (k + 1)) = s k` for every `k`. -/
theorem exists_forall_map_succ_eq_of_compact_t2 [∀ k, TopologicalSpace (S k)]
    [∀ k, CompactSpace (S k)] [∀ k, T2Space (S k)] [∀ k, Nonempty (S k)]
    (hβ : ∀ k, Continuous (β k)) : ∃ s : ∀ k, S k, ∀ k, β k (s (k + 1)) = s k := by
  -- The one-step maps already assemble into a functor `F : ℕᵒᵖ ⥤ TopCat`, so the transition maps
  -- along `i ≤ j` need not be built by hand: they are `F` on morphisms, continuous because they
  -- are morphisms of `TopCat`, and the two laws of an inverse system are the functoriality of `F`,
  -- `F.map_id_apply` and `F.map_comp_apply`. The index `ℕ` is directed, so the directed statement
  -- above applies to them.
  let F := Functor.ofOpSequence (X := fun k ↦ TopCat.of (S k)) fun k ↦ TopCat.ofHom ⟨β k, hβ k⟩
  let f : ∀ ⦃i j : ℕ⦄, i ≤ j → S j → S i := fun _ _ h x ↦ F.map (homOfLE h).op x
  have : InverseSystem f :=
    { map_self := fun i x ↦ F.map_id_apply (Opposite.op i) x
      map_map := fun _ _ _ hkj hji x ↦
        (F.map_comp_apply (homOfLE hji).op (homOfLE hkj).op x).symm }
  obtain ⟨s, hs⟩ :=
    exists_forall_map_eq_of_compact_t2 f fun _ _ h ↦ (F.map (homOfLE h).op).hom.continuous
  refine ⟨s, fun k ↦ ?_⟩
  -- Along `k ≤ k + 1` the transition map is `β k` itself.
  have hk := hs (Nat.le_add_right k 1)
  change F.map (homOfLE (Nat.le_add_right k 1)).op (s (k + 1)) = s k at hk
  have hF_apply (x : S (k + 1)) :
      F.map (homOfLE (Nat.le_add_right k 1)).op x = β k x := by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact TopCat.ofHom_apply _ _
  exact (hF_apply _).symm.trans hk

/-- **Kőnig's lemma, sequential form.** A sequence of nonempty finite types `S k` with one-step
maps `β k : S (k + 1) → S k` has a compatible family: some `s : ∀ k, S k` satisfies
`β k (s (k + 1)) = s k` for every `k`. -/
theorem exists_forall_map_succ_eq_of_finite [∀ k, Finite (S k)] [∀ k, Nonempty (S k)] :
    ∃ s : ∀ k, S k, ∀ k, β k (s (k + 1)) = s k := by
  let _ : ∀ k, TopologicalSpace (S k) := fun _ ↦ ⊥
  have : ∀ k, DiscreteTopology (S k) := fun _ ↦ ⟨rfl⟩
  exact exists_forall_map_succ_eq_of_compact_t2 β fun _ ↦ continuous_of_discreteTopology

/-- **Compatible families lift along a map of compact towers.** Let `α k : A (k + 1) → A k` and
`β k : B (k + 1) → B k` be two towers, the first of compact Hausdorff spaces with continuous
maps, and let `g k : A k → B k` be continuous maps into T1 spaces commuting with them. Then a
compatible family `b` of the second tower lifts to a compatible family of the first as soon as
each `b k` lifts on its own.

In the language of inverse limits: `lim A → lim B` is surjective when every `A k → B k` is.
No surjectivity of the transition maps `α k` is needed, because compactness of the levels
replaces the Mittag-Leffler condition. -/
theorem exists_forall_map_succ_eq_and_forall_eq_of_compact_t2 {A B : ℕ → Type*}
    [∀ k, TopologicalSpace (A k)] [∀ k, CompactSpace (A k)] [∀ k, T2Space (A k)]
    [∀ k, TopologicalSpace (B k)] [∀ k, T1Space (B k)]
    (α : ∀ k, A (k + 1) → A k) (β : ∀ k, B (k + 1) → B k) (g : ∀ k, A k → B k)
    (hα : ∀ k, Continuous (α k)) (hg : ∀ k, Continuous (g k))
    (hαβ : ∀ k a, g k (α k a) = β k (g (k + 1) a)) {b : ∀ k, B k}
    (hb : ∀ k, β k (b (k + 1)) = b k) (hbg : ∀ k, ∃ a, g k a = b k) :
    ∃ a : ∀ k, A k, (∀ k, α k (a (k + 1)) = a k) ∧ ∀ k, g k (a k) = b k := by
  -- The fibres `g k ⁻¹' {b k}` are closed, hence compact, nonempty, and `α` maps them into each
  -- other; a compatible family of fibre points is the required lift.
  have hS (k : ℕ) : IsClosed (g k ⁻¹' {b k}) := isClosed_singleton.preimage (hg k)
  have (k : ℕ) : CompactSpace (g k ⁻¹' {b k}) := isCompact_iff_compactSpace.mp (hS k).isCompact
  have (k : ℕ) : Nonempty (g k ⁻¹' {b k}) :=
    let ⟨a, ha⟩ := hbg k
    ⟨⟨a, ha⟩⟩
  let γ (k : ℕ) (a : g (k + 1) ⁻¹' {b (k + 1)}) : g k ⁻¹' {b k} :=
    ⟨α k a, by
      rw [Set.mem_preimage, Set.mem_singleton_iff, hαβ,
        Set.mem_singleton_iff.mp (Set.mem_preimage.mp a.2), hb]⟩
  have hγ (k : ℕ) : Continuous (γ k) := ((hα k).comp continuous_subtype_val).subtype_mk _
  obtain ⟨s, hs⟩ :=
    exists_forall_map_succ_eq_of_compact_t2 (S := fun k ↦ g k ⁻¹' {b k}) γ hγ
  exact ⟨fun k ↦ s k, fun k ↦ congrArg Subtype.val (hs k), fun k ↦ (s k).2⟩

end Sequence

end TauCeti
