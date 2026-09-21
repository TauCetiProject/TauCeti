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
* `TauCeti.exists_forall_map_succ_eq_of_finite`: the sequential form, where the system is given
  by its one-step maps `β k : S (k + 1) → S k`.

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
/-- **Kőnig's lemma, sequential form.** A sequence of nonempty finite types `S k` with one-step
maps `β k : S (k + 1) → S k` has a compatible family: some `s : ∀ k, S k` satisfies
`β k (s (k + 1)) = s k` for every `k`. -/
theorem exists_forall_map_succ_eq_of_finite [∀ k, Finite (S k)] [∀ k, Nonempty (S k)] :
    ∃ s : ∀ k, S k, ∀ k, β k (s (k + 1)) = s k := by
  -- The one-step maps already assemble into a functor `F : ℕᵒᵖ ⥤ Type _`, so the transition maps
  -- along `i ≤ j` need not be built by hand: they are `F` on morphisms, and the two laws of an
  -- inverse system are its functoriality, `F.map_id_apply` and `F.map_comp_apply`. The index `ℕ`
  -- is directed, so the finite statement above applies to them.
  let F := Functor.ofOpSequence fun k ↦ ↾(β k)
  let f : ∀ ⦃i j : ℕ⦄, i ≤ j → S j → S i := fun _ _ h x ↦ F.map (homOfLE h).op x
  have : InverseSystem f :=
    { map_self := fun i x ↦ F.map_id_apply (Opposite.op i) x
      map_map := fun _ _ _ hkj hji x ↦
        (F.map_comp_apply (homOfLE hji).op (homOfLE hkj).op x).symm }
  obtain ⟨s, hs⟩ := exists_forall_map_eq_of_finite f
  refine ⟨s, fun k ↦ ?_⟩
  -- Along `k ≤ k + 1` the transition map is `β k` itself.
  rw [← TypeCat.ofHom_apply (β k) (s (k + 1)),
    ← Functor.ofOpSequence_map_homOfLE_succ (fun k ↦ ↾(β k)) k]
  exact hs (Nat.le_add_right k 1)

end Sequence

end TauCeti
