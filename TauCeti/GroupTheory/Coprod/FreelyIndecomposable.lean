/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import TauCeti.GroupTheory.Coprod.Commute
public import TauCeti.GroupTheory.CoprodI

/-!
# Freely indecomposable groups and Grushko decompositions

A group `G` is *freely indecomposable* when it is not the free product of two nontrivial
subgroups: whenever the homomorphism `A ∗ B →* G` induced by the inclusions of two subgroups
`A`, `B` is bijective, one of `A`, `B` is trivial. Commutative groups are freely indecomposable,
and a free product of two nontrivial groups is not.

A *Grushko decomposition* of `G` is an internal free product decomposition
`G = G₁ ∗ ⋯ ∗ G_p ∗ F_q` into finitely many subgroups `G_i`, each nontrivial, freely
indecomposable and not infinite cyclic, and a free group `F_q` of finite rank `q`. These are the
objects of Grushko's theorem: every finitely generated group has a Grushko decomposition, the rank
`q` is determined by the group and the factors `G_i` are determined up to conjugacy and
permutation.

## Main definitions

* `TauCeti.IsFreelyIndecomposable G`: `G` is not an internal free product of two nontrivial
  subgroups.
* `TauCeti.GrushkoDecomposition G`: a Grushko decomposition `G = G₁ ∗ ⋯ ∗ G_p ∗ F_q`.
* `TauCeti.GrushkoDecomposition.mulEquiv`: the isomorphism `G₁ ∗ ⋯ ∗ G_p ∗ F_q ≃* G` from the
  external free product.
* `TauCeti.GrushkoDecomposition.coprodFreeGroup`: if `H` is nontrivial, freely indecomposable and
  not infinite cyclic, then `H ∗ F_n` is a Grushko decomposition with `p = 1` and `q = n`.

## Main results

* `Monoid.Coprod.bijective_lift_subtype_range_iff`: for injective `f : A →* G`, `g : B →* G`, the
  group `G` is the internal free product of the images of `f` and `g` exactly when `f` and `g`
  exhibit `G` as `A ∗ B`.
* `MulEquiv.isFreelyIndecomposable_iff`: free indecomposability is invariant under isomorphism.
* `TauCeti.IsFreelyIndecomposable.subsingleton_or_subsingleton`: if a freely indecomposable group
  is isomorphic to `A ∗ B`, then `A` or `B` is trivial.
* `TauCeti.isFreelyIndecomposable_of_isMulCommutative`: commutative groups are freely
  indecomposable.
* `TauCeti.not_isFreelyIndecomposable_coprod`: `A ∗ B` is not freely indecomposable for
  nontrivial `A`, `B`.

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

namespace IsFreelyIndecomposable

variable {G H : Type*} [Group G] [Group H]

/-- In a freely indecomposable group, one of the two subgroups of an internal free product
decomposition is trivial. -/
theorem eq_bot_or_eq_bot (h : IsFreelyIndecomposable G) {A B : Subgroup G}
    (hAB : Function.Bijective (Coprod.lift A.subtype B.subtype)) : A = ⊥ ∨ B = ⊥ :=
  h A B hAB

/-- A group isomorphic to a freely indecomposable group is freely indecomposable. -/
theorem map_mulEquiv (h : IsFreelyIndecomposable G) (e : G ≃* H) : IsFreelyIndecomposable H := by
  intro A B hAB
  have key := (Coprod.bijective_lift_subtype_range_iff
    (f := (e.symm : H →* G).comp A.subtype) (g := (e.symm : H →* G).comp B.subtype)
    (e.symm.injective.comp A.subtype_injective) (e.symm.injective.comp B.subtype_injective)).2
    (by simpa [← Coprod.comp_lift] using e.symm.bijective.comp hAB)
  rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
    Subgroup.range_subtype] at key
  exact (h.eq_bot_or_eq_bot key).imp (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1
    (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1

/-- If a freely indecomposable group is isomorphic to a free product `A ∗ B`, then one of `A`,
`B` is trivial. -/
theorem subsingleton_or_subsingleton {A B : Type*} [Group A] [Group B]
    (h : IsFreelyIndecomposable G) (e : A ∗ B ≃* G) : Subsingleton A ∨ Subsingleton B := by
  -- the images of the two factors form an internal free product decomposition of `A ∗ B`
  simpa [MonoidHom.range_eq_map, Subgroup.map_eq_bot_iff_of_injective, Coprod.inl_injective,
    Coprod.inr_injective, eq_comm (a := (⊤ : Subgroup _)), subsingleton_iff_bot_eq_top,
    Subgroup.subsingleton_iff]
    using (h.map_mulEquiv e.symm).eq_bot_or_eq_bot <| (Coprod.bijective_lift_subtype_range_iff
      Coprod.inl_injective Coprod.inr_injective).2 (by simpa using Function.bijective_id)

end IsFreelyIndecomposable

/-- Free indecomposability is invariant under isomorphism. -/
theorem _root_.MulEquiv.isFreelyIndecomposable_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    IsFreelyIndecomposable G ↔ IsFreelyIndecomposable H :=
  ⟨fun h => h.map_mulEquiv e, fun h => h.map_mulEquiv e.symm⟩

/-- A commutative group is freely indecomposable. -/
theorem isFreelyIndecomposable_of_isMulCommutative (G : Type*) [Group G] [IsMulCommutative G] :
    IsFreelyIndecomposable G := by
  intro A B hAB
  by_contra! h
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.1
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.2
  have : Commute (Coprod.inl a : A ∗ B) (Coprod.inr b) := hAB.1 (by simp [mul_comm' (a : G)])
  simp_all

/-- A free product of two nontrivial groups is not freely indecomposable. -/
theorem not_isFreelyIndecomposable_coprod (A B : Type*) [Group A] [Group B] [Nontrivial A]
    [Nontrivial B] : ¬IsFreelyIndecomposable (A ∗ B) := fun h =>
  (h.subsingleton_or_subsingleton (.refl _)).elim (not_subsingleton A) (not_subsingleton B)

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
  isEmpty_mulEquiv_int : ∀ i, IsEmpty (factor i ≃* Multiplicative ℤ)
  /-- The group is the free product of the factors and of the free factor. -/
  bijective : Function.Bijective
    (Coprod.lift (CoprodI.lift fun i => (factor i).subtype) free)

namespace GrushkoDecomposition

attribute [instance] nontrivial

variable {G : Type*} [Group G] (D : GrushkoDecomposition G)

/-- The factors of a Grushko decomposition are nontrivial subgroups. -/
@[simp]
theorem factor_ne_bot (i : Fin D.p) : D.factor i ≠ ⊥ :=
  (Subgroup.nontrivial_iff_ne_bot _).1 (D.nontrivial i)

/-- The isomorphism onto `G` from the external free product `G₁ ∗ ⋯ ∗ G_p ∗ F_q` of the factors
and the free group of rank `q`. -/
noncomputable def mulEquiv : (CoprodI fun i => D.factor i) ∗ FreeGroup (Fin D.q) ≃* G :=
  MulEquiv.ofBijective _ D.bijective

theorem coe_mulEquiv :
    ⇑D.mulEquiv = Coprod.lift (CoprodI.lift fun i => (D.factor i).subtype) D.free :=
  (rfl)

@[simp]
theorem mulEquiv_inl_of {i : Fin D.p} (x : D.factor i) :
    D.mulEquiv (Coprod.inl (CoprodI.of x)) = x := by
  simp [coe_mulEquiv]

@[simp]
theorem mulEquiv_inr (w : FreeGroup (Fin D.q)) : D.mulEquiv (Coprod.inr w) = D.free w := by
  simp [coe_mulEquiv]

/-- The homomorphism from the free group of rank `q` onto the free factor is injective: the free
factor of a Grushko decomposition is free of rank `q`. -/
theorem free_injective : Function.Injective D.free := fun x y hxy =>
  Coprod.inr_injective <| D.mulEquiv.injective <| by simpa using hxy

/-- The Grushko decomposition of `H ∗ F_n` with one freely indecomposable factor, the image of
`H`, and the free factor `F_n`, for a nontrivial freely indecomposable group `H` which is not
infinite cyclic. -/
@[expose] def coprodFreeGroup {H : Type*} [Group H] [Nontrivial H] (hH : IsFreelyIndecomposable H)
    (hZ : IsEmpty (H ≃* Multiplicative ℤ)) (n : ℕ) :
    GrushkoDecomposition (H ∗ FreeGroup (Fin n)) where
  p := 1
  q := n
  factor _ := (Coprod.inl : H →* H ∗ FreeGroup (Fin n)).range
  free := Coprod.inr
  nontrivial _ := (MonoidHom.ofInjective Coprod.inl_injective).injective.nontrivial
  isFreelyIndecomposable _ := hH.map_mulEquiv (MonoidHom.ofInjective Coprod.inl_injective)
  isEmpty_mulEquiv_int _ :=
    ⟨fun f => hZ.false ((MonoidHom.ofInjective Coprod.inl_injective).trans f)⟩
  bijective := by
    set R := (Coprod.inl : H →* H ∗ FreeGroup (Fin n)).range
    let Ψ := MulEquiv.coprodCongr ((MonoidHom.ofInjective Coprod.inl_injective).trans
      (MulEquiv.coprodIUnique fun _ : Fin 1 => R).symm) (MulEquiv.refl (FreeGroup (Fin n)))
    have : (Coprod.lift (CoprodI.lift fun _ : Fin 1 => R.subtype) Coprod.inr).comp
        Ψ.toMonoidHom = .id _ :=
      Coprod.hom_ext
        (by ext; simpa [Ψ, MulEquiv.coprodCongr] using MonoidHom.ofInjective_apply _)
        (by ext; simp [Ψ, MulEquiv.coprodCongr])
    refine (Function.Bijective.of_comp_iff _ Ψ.bijective).1 ?_
    rw [← MulEquiv.coe_toMonoidHom, ← MonoidHom.coe_comp, this]
    exact Function.bijective_id

section coprodFreeGroup

variable {H : Type*} [Group H] [Nontrivial H] (hH : IsFreelyIndecomposable H)
  (hZ : IsEmpty (H ≃* Multiplicative ℤ)) (n : ℕ)

@[simp]
theorem coprodFreeGroup_p : (coprodFreeGroup hH hZ n).p = 1 :=
  (rfl)

@[simp]
theorem coprodFreeGroup_q : (coprodFreeGroup hH hZ n).q = n :=
  (rfl)

@[simp]
theorem coprodFreeGroup_factor (i : Fin (coprodFreeGroup hH hZ n).p) :
    (coprodFreeGroup hH hZ n).factor i = (Coprod.inl : H →* H ∗ FreeGroup (Fin n)).range :=
  (rfl)

@[simp]
theorem coprodFreeGroup_free : (coprodFreeGroup hH hZ n).free = Coprod.inr :=
  (rfl)

end coprodFreeGroup

end GrushkoDecomposition

end TauCeti
