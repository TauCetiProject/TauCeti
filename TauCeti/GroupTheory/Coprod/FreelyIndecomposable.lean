/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.GroupTheory.Coprod.Commute

/-!
# Freely indecomposable groups and Grushko decompositions

A group `G` is *freely indecomposable* when it is not the free product of two nontrivial
subgroups: whenever the homomorphism `A ∗ B →* G` induced by the inclusions of two subgroups
`A`, `B` is bijective, one of `A`, `B` is trivial. Commutative groups are freely indecomposable,
and a free product of two nontrivial groups is not.

A *Grushko decomposition* of `G` is an internal free product decomposition
`G = G₁ ∗ ⋯ ∗ G_p ∗ F_q` into finitely many subgroups `G_i`, each nontrivial, freely
indecomposable and not infinite cyclic, and a free group `F_q` of finite rank `q`. For instance
`ℤ² ∗ F₂` has a Grushko decomposition with `p = 1`, `G₁ = ℤ²` and `q = 2`. These are the objects
of Grushko's theorem: every finitely generated group has a Grushko decomposition, the rank `q` is
determined by the group and the factors `G_i` are determined up to conjugacy and permutation.

## Main definitions

* `TauCeti.IsFreelyIndecomposable G`: `G` is not an internal free product of two nontrivial
  subgroups.
* `TauCeti.GrushkoDecomposition G`: a Grushko decomposition `G = G₁ ∗ ⋯ ∗ G_p ∗ F_q`.

## Main results

* `Monoid.Coprod.bijective_lift_subtype_range_iff`: for injective `f : A →* G`, `g : B →* G`, the
  group `G` is the internal free product of the images of `f` and `g` exactly when `f` and `g`
  exhibit `G` as `A ∗ B`.
* `MulEquiv.isFreelyIndecomposable_iff`: free indecomposability is invariant under isomorphism.
* `TauCeti.isFreelyIndecomposable_of_commGroup`: commutative groups are freely indecomposable.
* `TauCeti.not_isFreelyIndecomposable_coprod`: `A ∗ B` is not freely indecomposable for
  nontrivial `A`, `B`.
* `TauCeti.exists_grushkoDecomposition_coprod_freeGroup`: if `H` is nontrivial, freely
  indecomposable and not infinite cyclic, then `H ∗ F_n` is a Grushko decomposition with `p = 1`
  and `q = n`.
* `TauCeti.exists_grushkoDecomposition_int_prod_int_coprod_freeGroup`: `ℤ² ∗ F₂` has a Grushko
  decomposition with `p = 1`, `G₁ = ℤ²` and `q = 2`.

## References

* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), Introduction
  (definition of a Grushko decomposition, p. 1) and §3.2 (p. 30).
-/

public section

open Monoid
open scoped Monoid.Coprod

namespace Monoid.Coprod

variable {A B G : Type*} [Group A] [Group B] [Group G]

/-- For injective homomorphisms `f : A →* G` and `g : B →* G`, the group `G` is the free product
of the images of `f` and `g` exactly when it is the free product of `A` and `B` via `f` and `g`. -/
theorem bijective_lift_subtype_range_iff {f : A →* G} {g : B →* G} (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Bijective (lift f.range.subtype g.range.subtype) ↔ Function.Bijective (lift f g) := by
  have : lift f g = (lift f.range.subtype g.range.subtype).comp
      (MulEquiv.coprodCongr (MonoidHom.ofInjective hf) (MonoidHom.ofInjective hg)).toMonoidHom := by
    ext <;> simp [MulEquiv.coprodCongr, MonoidHom.ofInjective_apply]
  rw [this, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact (Function.Bijective.of_comp_iff _ (MulEquiv.bijective _)).symm

end Monoid.Coprod

namespace TauCeti

/-- A group is freely indecomposable when it is not the internal free product of two nontrivial
subgroups: if the homomorphism `A ∗ B →* G` induced by the inclusions of two subgroups is
bijective, then one of them is trivial.

This is the convention of the introduction of Guirardel–Levitt: the trivial group and `ℤ` are
freely indecomposable. Since `ℤ` splits as an HNN extension over the trivial group, the
tree-theoretic notion of their §1.3 and §3.2 counts `ℤ` as freely decomposable; a Grushko
decomposition therefore excludes infinite cyclic factors separately. -/
def IsFreelyIndecomposable (G : Type*) [Group G] : Prop :=
  ∀ A B : Subgroup G, Function.Bijective (Coprod.lift A.subtype B.subtype) → A = ⊥ ∨ B = ⊥

/-- Unfolding `IsFreelyIndecomposable`. -/
theorem isFreelyIndecomposable_iff {G : Type*} [Group G] :
    IsFreelyIndecomposable G ↔ ∀ A B : Subgroup G,
      Function.Bijective (Coprod.lift A.subtype B.subtype) → A = ⊥ ∨ B = ⊥ :=
  Iff.rfl

private theorem isFreelyIndecomposable_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsFreelyIndecomposable H) : IsFreelyIndecomposable G := by
  intro A B hAB
  have key := (Coprod.bijective_lift_subtype_range_iff
    (f := (e : G →* H).comp A.subtype) (g := (e : G →* H).comp B.subtype)
    (e.injective.comp A.subtype_injective) (e.injective.comp B.subtype_injective)).2
    (by simpa [← Coprod.comp_lift] using e.bijective.comp hAB)
  rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
    Subgroup.range_subtype] at key
  exact (h _ _ key).imp (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1
    (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1

/-- Free indecomposability is invariant under isomorphism. -/
theorem _root_.MulEquiv.isFreelyIndecomposable_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    IsFreelyIndecomposable G ↔ IsFreelyIndecomposable H :=
  ⟨isFreelyIndecomposable_of_mulEquiv e.symm, isFreelyIndecomposable_of_mulEquiv e⟩

/-- A commutative group is freely indecomposable. -/
theorem isFreelyIndecomposable_of_commGroup (G : Type*) [CommGroup G] :
    IsFreelyIndecomposable G := by
  intro A B hAB
  by_contra! h
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.1
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.2
  have : Commute (Coprod.inl a : A ∗ B) (Coprod.inr b) := hAB.1 (by simp [mul_comm])
  simp_all

/-- A free product of two nontrivial groups is not freely indecomposable. -/
theorem not_isFreelyIndecomposable_coprod (A B : Type*) [Group A] [Group B] [Nontrivial A]
    [Nontrivial B] : ¬IsFreelyIndecomposable (A ∗ B) := fun h => by
  -- the two factors form an internal free product decomposition of `A ∗ B`
  simpa [MonoidHom.range_eq_map, Subgroup.map_eq_bot_iff_of_injective, Coprod.inl_injective,
    Coprod.inr_injective] using h _ _ <| (Coprod.bijective_lift_subtype_range_iff
      Coprod.inl_injective Coprod.inr_injective).2 (by simpa using Function.bijective_id)

/-- A Grushko decomposition of a group: an internal free product decomposition into finitely
many nontrivial freely indecomposable subgroups, none of them infinite cyclic, and a free group
of finite rank. -/
structure GrushkoDecomposition (G : Type*) [Group G] where
  /-- The number of freely indecomposable factors. -/
  p : ℕ
  /-- The rank of the free factor. -/
  q : ℕ
  /-- The freely indecomposable factors. -/
  factor : Fin p → Subgroup G
  /-- The free factor. -/
  free : FreeGroup (Fin q) →* G
  /-- The factors are nontrivial. -/
  nontrivial : ∀ i, Nontrivial (factor i)
  /-- The factors are freely indecomposable. -/
  isFreelyIndecomposable : ∀ i, IsFreelyIndecomposable (factor i)
  /-- No factor is infinite cyclic. -/
  not_int : ∀ i, IsEmpty (factor i ≃* Multiplicative ℤ)
  /-- The group is the free product of the factors and of the free factor. -/
  bijective : Function.Bijective
    (Coprod.lift (CoprodI.lift fun i => (factor i).subtype) free)

/-- The free product `H ∗ F_n` of a nontrivial freely indecomposable group `H` which is not
infinite cyclic with the free group of rank `n` has a Grushko decomposition with one freely
indecomposable factor, the image of `H`, and a free factor of rank `n`. -/
theorem exists_grushkoDecomposition_coprod_freeGroup {H : Type*} [Group H] [Nontrivial H]
    (hH : IsFreelyIndecomposable H) (hZ : IsEmpty (H ≃* Multiplicative ℤ)) (n : ℕ) :
    ∃ D : GrushkoDecomposition (H ∗ FreeGroup (Fin n)),
      D.p = 1 ∧ D.q = n ∧ ∀ i, D.factor i = (Coprod.inl : H →* H ∗ FreeGroup (Fin n)).range := by
  set R := (Coprod.inl : H →* H ∗ FreeGroup (Fin n)).range
  let e : H ≃* R := MonoidHom.ofInjective Coprod.inl_injective
  -- the free product of the one-element family `R` is `R`
  let E : CoprodI (fun _ : Fin 1 => R) ≃* R :=
    MonoidHom.toMulEquiv (CoprodI.lift fun _ => .id R)
      (CoprodI.of (M := fun _ : Fin 1 => R) (i := 0))
      (CoprodI.ext_hom _ _ fun i => by obtain rfl := Subsingleton.elim i 0; ext; simp)
      (by ext; simp)
  let Ψ := MulEquiv.coprodCongr (e.trans E.symm) (MulEquiv.refl (FreeGroup (Fin n)))
  refine ⟨⟨1, n, fun _ => R, Coprod.inr, fun _ => e.injective.nontrivial,
    fun _ => e.isFreelyIndecomposable_iff.1 hH, fun _ => ⟨fun f => hZ.false (e.trans f)⟩, ?_⟩,
    rfl, rfl, fun _ => rfl⟩
  have : (Coprod.lift (CoprodI.lift fun _ : Fin 1 => R.subtype) Coprod.inr).comp
      Ψ.toMonoidHom = .id _ :=
    Coprod.hom_ext
      (by ext; simpa [Ψ, E, e, MulEquiv.coprodCongr] using MonoidHom.ofInjective_apply _)
      (by ext; simp [Ψ, MulEquiv.coprodCongr])
  refine (Function.Bijective.of_comp_iff _ Ψ.bijective).1 ?_
  rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.coe_comp, this]
  exact Function.bijective_id

/-- The free product `ℤ² ∗ F₂` has a Grushko decomposition with one freely indecomposable factor,
the image of `ℤ²`, and a free factor of rank `2`. -/
theorem exists_grushkoDecomposition_int_prod_int_coprod_freeGroup :
    ∃ D : GrushkoDecomposition (Multiplicative (ℤ × ℤ) ∗ FreeGroup (Fin 2)), D.p = 1 ∧ D.q = 2 ∧
      ∀ i, D.factor i = (Coprod.inl : Multiplicative (ℤ × ℤ) →* _ ∗ FreeGroup (Fin 2)).range :=
  exists_grushkoDecomposition_coprod_freeGroup (isFreelyIndecomposable_of_commGroup _)
    ⟨fun e => not_isAddCyclic_prod_of_infinite_nontrivial ℤ ℤ <|
      isCyclic_multiplicative_iff.1 <| isCyclic_of_surjective e.symm e.symm.surjective⟩ 2

end TauCeti
