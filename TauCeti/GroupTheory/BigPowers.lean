/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.GroupAlgGeom.Discrimination

/-!
# The big powers property

A group has the *big powers property* (is a *BP group*) when every finite nonempty tuple
`(u₀, …, u_k)` of nonidentity elements, in which consecutive entries do not commute, has a bound
`N` such that `u₀ ^ e₀ * ⋯ * u_k ^ e_k ≠ 1` whenever every exponent `eᵢ` is at least `N`.

The singleton tuples say that a BP group is torsion-free; for a commutative group, where every
tuple of length at least two is excluded, this is the whole condition. Free groups are BP groups
(`FreeGroup.isBP`), and the property passes from a group `H` to every group `G` whose finite
families of nonidentity elements each survive under one homomorphism `G →* H`. In particular it
passes to subgroups and to groups discriminated by a BP group, such as fully residually free
groups. Big powers are the input to the discrimination of extensions of centralizers by the
retractions `t ↦ u ^ k`.

## Main definitions

* `Group.IsBP`: the big powers property.

## Main results

* `Group.IsBP.of_forall_finset_exists_monoidHom`: the big powers property passes along
  homomorphisms that keep any given finite family of nonidentity elements nontrivial.
* `Group.IsBP.of_injective`, `Group.IsBP.of_isDiscriminatedBy`: subgroups of BP groups, and groups
  discriminated by a BP group, are BP groups.
* `Group.IsBP.isMulTorsionFree`: BP groups are torsion-free.
* `Group.isBP_iff_isMulTorsionFree`: a commutative group is a BP group exactly when it is
  torsion-free.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5, Definition 1 and the paragraph following it.
* G. Baumslag, *On generalised free products*, Math. Z. 78 (1962), 423–438.
-/

public section

open scoped commutatorElement

namespace Group

variable (G : Type*) [Group G]

/-- A group has the *big powers property* when for every nonempty tuple `u` of nonidentity
elements whose consecutive entries do not commute there is a bound `N` such that the product
`u 0 ^ e 0 * ⋯ * u k ^ e k` is nontrivial whenever every exponent `e i` is at least `N`. -/
def IsBP : Prop :=
  ∀ ⦃k : ℕ⦄ (u : Fin (k + 1) → G), (∀ i, u i ≠ 1) →
    (∀ i : Fin k, ¬Commute (u i.castSucc) (u i.succ)) →
    ∃ N : ℕ, ∀ e : Fin (k + 1) → ℕ, (∀ i, N ≤ e i) → (List.ofFn fun i => u i ^ e i).prod ≠ 1

/-- The defining condition of the big powers property. -/
theorem isBP_iff : IsBP G ↔
    ∀ ⦃k : ℕ⦄ (u : Fin (k + 1) → G), (∀ i, u i ≠ 1) →
      (∀ i : Fin k, ¬Commute (u i.castSucc) (u i.succ)) →
      ∃ N : ℕ, ∀ e : Fin (k + 1) → ℕ, (∀ i, N ≤ e i) →
        (List.ofFn fun i => u i ^ e i).prod ≠ 1 :=
  Iff.rfl

variable {G}

namespace IsBP

/-- The big powers property passes from `H` to `G` when every finite family of nonidentity
elements of `G` survives under one homomorphism `G →* H`. -/
theorem of_forall_finset_exists_monoidHom {H : Type*} [Group H] (hH : IsBP H)
    (h : ∀ s : Finset G, (∀ g ∈ s, g ≠ 1) → ∃ φ : G →* H, ∀ g ∈ s, φ g ≠ 1) : IsBP G := by
  classical
  intro k u hu hcomm
  -- One homomorphism keeps every entry and every commutator of consecutive entries nontrivial.
  obtain ⟨φ, hφ⟩ := h (Finset.univ.image u ∪ Finset.univ.image fun i : Fin k =>
      ⁅u i.castSucc, u i.succ⁆) (by
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hu i
    · rw [Ne, commutatorElement_eq_one_iff_commute]
      exact hcomm i)
  obtain ⟨N, hN⟩ := hH (fun i => φ (u i))
    (fun i => hφ _ (Finset.mem_union_left _ (Finset.mem_image_of_mem u (Finset.mem_univ i))))
    (fun i hi => by
      refine hφ ⁅u i.castSucc, u i.succ⁆ (Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_univ i))) ?_
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact hi)
  refine ⟨N, fun e he hprod => hN e he ?_⟩
  simpa [map_list_prod, List.map_ofFn, Function.comp_def] using congrArg φ hprod

/-- A group with an injective homomorphism to a BP group is a BP group. In particular subgroups
of BP groups are BP groups. -/
theorem of_injective {H : Type*} [Group H] (hH : IsBP H) {f : G →* H}
    (hf : Function.Injective f) : IsBP G :=
  hH.of_forall_finset_exists_monoidHom fun _ hs =>
    ⟨f, fun g hg => (map_ne_one_iff f hf).2 (hs g hg)⟩

/-- A group discriminated by a BP group, relative to any coefficient group, is a BP group. -/
theorem of_isDiscriminatedBy {C K H : Type*} [Group C] [Group K] [Group H] (hH : IsBP H)
    {ιK : C →* K} {ιH : C →* H} (h : TauCeti.GroupAlgGeom.IsDiscriminatedBy ιK ιH) : IsBP K :=
  hH.of_forall_finset_exists_monoidHom fun s hs =>
    let ⟨φ, hφ⟩ := (TauCeti.GroupAlgGeom.isDiscriminatedBy_def ιK ιH).1 h s hs
    ⟨φ, hφ⟩

/-- A BP group is torsion-free: the condition for a singleton tuple `(g)` says that the powers
`g ^ e` are nontrivial for all large `e`. -/
theorem isMulTorsionFree (hG : IsBP G) : IsMulTorsionFree G := by
  rw [isMulTorsionFree_iff_not_isOfFinOrder]
  intro g hg hfin
  obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  obtain ⟨N, hN⟩ := hG (k := 0) (fun _ => g) (fun _ => hg) (fun i => i.elim0)
  refine hN (fun _ => n * N.succ) (fun _ => ?_) ?_
  · exact le_trans (Nat.le_succ N) (Nat.le_mul_of_pos_left _ hn)
  · simp [pow_mul, hgn]

end IsBP

/-- A trivial group is a BP group: it has no nonidentity elements. -/
theorem isBP_of_subsingleton [Subsingleton G] : IsBP G :=
  fun _ _ hu _ => ((hu 0) (Subsingleton.elim _ _)).elim

/-- A commutative group is a BP group exactly when it is torsion-free: consecutive entries always
commute, so only singleton tuples need to be checked. -/
theorem isBP_iff_isMulTorsionFree {A : Type*} [CommGroup A] : IsBP A ↔ IsMulTorsionFree A := by
  refine ⟨IsBP.isMulTorsionFree, fun _ k u hu hcomm => ⟨1, fun e he => ?_⟩⟩
  cases k with
  | zero =>
    have h := (IsMulTorsionFree.pow_right_inj (hu 0) (n := e 0) (m := 0)).not.2
      (by have := he 0; omega)
    simpa using h
  | succ k => exact (hcomm 0 (Commute.all _ _)).elim

end Group
