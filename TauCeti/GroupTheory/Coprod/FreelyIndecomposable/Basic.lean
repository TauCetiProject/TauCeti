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
* `TauCeti.GrushkoDecomposition.map`: the transport of a Grushko decomposition along an
  isomorphism.
* `TauCeti.GrushkoDecomposition.freeGroup`: the free group `F_n` is a Grushko decomposition with
  `p = 0` and `q = n`.
* `TauCeti.GrushkoDecomposition.ofIsFreelyIndecomposable`: a nontrivial freely indecomposable
  group which is not infinite cyclic is a Grushko decomposition with `p = 1` and `q = 0`.
* `TauCeti.GrushkoDecomposition.coprodFreeGroup`: if `H` is nontrivial, freely indecomposable and
  not infinite cyclic, then `H ∗ F_n` is a Grushko decomposition with `p = 1` and `q = n`.

## Main results

* `Monoid.Coprod.lift_subtype_range_bijective_iff`: for injective `f : A →* G`, `g : B →* G`, the
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
theorem lift_subtype_range_bijective_iff {f : A →* G} {g : B →* G} (hf : Function.Injective f)
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
theorem of_mulEquiv (h : IsFreelyIndecomposable G) (e : G ≃* H) : IsFreelyIndecomposable H := by
  intro A B hAB
  have key := (Coprod.lift_subtype_range_bijective_iff
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
    using (h.of_mulEquiv e.symm).eq_bot_or_eq_bot <| (Coprod.lift_subtype_range_bijective_iff
      Coprod.inl_injective Coprod.inr_injective).2 (by simpa using Function.bijective_id)

end IsFreelyIndecomposable

/-- Free indecomposability is invariant under isomorphism. -/
theorem _root_.MulEquiv.isFreelyIndecomposable_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    IsFreelyIndecomposable G ↔ IsFreelyIndecomposable H :=
  ⟨fun h => h.of_mulEquiv e, fun h => h.of_mulEquiv e.symm⟩

/-- A commutative group is freely indecomposable. -/
theorem isFreelyIndecomposable_of_isMulCommutative (G : Type*) [Group G] [IsMulCommutative G] :
    IsFreelyIndecomposable G := by
  intro A B hAB
  by_contra! h
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.1
  obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.2
  have : Commute (Coprod.inl a : A ∗ B) (Coprod.inr b) := hAB.1 (by simp [mul_comm' (a : G)])
  simp_all

/-- The trivial group is freely indecomposable. -/
@[simp]
theorem isFreelyIndecomposable_of_subsingleton (G : Type*) [Group G] [Subsingleton G] :
    IsFreelyIndecomposable G :=
  fun A _ _ => .inl (Subsingleton.elim A ⊥)

/-- A free product of two nontrivial groups is not freely indecomposable. -/
@[simp]
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

attribute [instance] nontrivial isEmpty_mulEquiv_int

variable {G : Type*} [Group G]

/-- Two Grushko decompositions are equal when they have the same number `p` of factors, the same
rank `q` of free factor, the same factors, and free factors agreeing on the generators, up to the
reindexing along the equalities of `p` and of `q`. -/
@[ext (iff := false)]
theorem ext {D₁ D₂ : GrushkoDecomposition G} (hp : D₁.p = D₂.p) (hq : D₁.q = D₂.q)
    (hfactor : ∀ i, D₁.factor i = D₂.factor (i.cast hp))
    (hfree : ∀ j, D₁.free (.of j) = D₂.free (.of (j.cast hq))) : D₁ = D₂ := by
  obtain ⟨p, q, factor, free⟩ := D₁
  obtain ⟨p', q', factor', free'⟩ := D₂
  obtain rfl : p = p' := hp
  obtain rfl : q = q' := hq
  obtain rfl : factor = factor' := funext fun i => by simpa using hfactor i
  obtain rfl : free = free' := FreeGroup.ext_hom _ _ fun j => by simpa using hfree j
  rfl

variable (D : GrushkoDecomposition G)

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
theorem mulEquiv_apply_inl_of {i : Fin D.p} (x : D.factor i) :
    D.mulEquiv (Coprod.inl (CoprodI.of x)) = x := by
  simp [coe_mulEquiv]

@[simp]
theorem mulEquiv_apply_inr (w : FreeGroup (Fin D.q)) : D.mulEquiv (Coprod.inr w) = D.free w := by
  simp [coe_mulEquiv]

@[simp]
theorem mulEquiv_symm_apply_coe {i : Fin D.p} (x : D.factor i) :
    D.mulEquiv.symm x = Coprod.inl (CoprodI.of (M := fun j => D.factor j) x) :=
  D.mulEquiv.symm_apply_eq.2 (D.mulEquiv_apply_inl_of x).symm

@[simp]
theorem mulEquiv_symm_apply_free (w : FreeGroup (Fin D.q)) :
    D.mulEquiv.symm (D.free w) = Coprod.inr w :=
  D.mulEquiv.symm_apply_eq.2 (D.mulEquiv_apply_inr w).symm

/-- The homomorphism from the free group of rank `q` onto the free factor is injective: the free
factor of a Grushko decomposition is free of rank `q`. -/
theorem free_injective : Function.Injective D.free := fun x y hxy =>
  Coprod.inr_injective <| D.mulEquiv.injective <| by simpa using hxy

/-- The Grushko decomposition of `H` obtained by transporting one of `G` along an isomorphism
`G ≃* H`. -/
@[expose, simps p q factor free]
def map {H : Type*} [Group H] (e : G ≃* H) : GrushkoDecomposition H where
  p := D.p
  q := D.q
  factor i := (D.factor i).map (e : G →* H)
  free := (e : G →* H).comp D.free
  nontrivial i := (e.subgroupMap (D.factor i)).injective.nontrivial
  isFreelyIndecomposable i := (D.isFreelyIndecomposable i).of_mulEquiv (e.subgroupMap _)
  isEmpty_mulEquiv_int i := ⟨fun f => isEmptyElim ((e.subgroupMap (D.factor i)).trans f)⟩
  bijective := by
    let Ψ := (MulEquiv.coprodCongr
      (MulEquiv.coprodICongr fun i => (e.subgroupMap (D.factor i)).symm) (.refl _)).trans
      (D.mulEquiv.trans e)
    have : Coprod.lift (CoprodI.lift fun i => ((D.factor i).map (e : G →* H)).subtype)
        ((e : G →* H).comp D.free) = Ψ.toMonoidHom := by
      ext <;> simp [Ψ, MulEquiv.coprodCongr]
    exact this ▸ Ψ.bijective

/-- Transporting a Grushko decomposition along the identity does not change it. -/
@[simp]
theorem map_refl : D.map (.refl G) = D :=
  -- `map` keeps `p` and `q`, so the reindexing casts in `ext` are along `rfl`
  ext rfl rfl (fun _ => Subgroup.map_id _) fun _ => rfl

/-- Transporting a Grushko decomposition along two isomorphisms in turn is transporting it along
their composite. -/
@[simp]
theorem map_trans {H K : Type*} [Group H] [Group K] (e₁ : G ≃* H) (e₂ : H ≃* K) :
    (D.map e₁).map e₂ = D.map (e₁.trans e₂) :=
  ext rfl rfl (fun _ => Subgroup.map_map _ _ _) fun _ => rfl

/-- The Grushko decomposition of the free group of rank `n`, with no freely indecomposable
factor and the whole group as free factor. -/
@[expose, simps p q free]
def freeGroup (n : ℕ) : GrushkoDecomposition (FreeGroup (Fin n)) where
  p := 0
  q := n
  factor := Fin.elim0
  free := .id _
  nontrivial i := i.elim0
  isFreelyIndecomposable i := i.elim0
  isEmpty_mulEquiv_int i := i.elim0
  bijective := by
    let Ψ := (MulEquiv.coprodCongr (MulEquiv.ofUnique (M := CoprodI fun i : Fin 0 =>
      (Fin.elim0 i : Subgroup (FreeGroup (Fin n)))) (N := PUnit.{1})) (.refl _)).trans
      (MulEquiv.punitCoprod (FreeGroup (Fin n)))
    have : Coprod.lift (CoprodI.lift fun i : Fin 0 => (Fin.elim0 i : Subgroup _).subtype)
        (.id _) = Ψ.toMonoidHom :=
      Coprod.hom_ext (Subsingleton.elim _ _) (by ext; simp [Ψ, MulEquiv.coprodCongr])
    exact this ▸ Ψ.bijective

/-- A nontrivial freely indecomposable group which is not infinite cyclic is its own Grushko
decomposition, with the single factor `⊤` and a free factor of rank `0`. -/
@[expose, simps p q factor free]
def ofIsFreelyIndecomposable [Nontrivial G] (hG : IsFreelyIndecomposable G)
    (hZ : IsEmpty (G ≃* Multiplicative ℤ)) : GrushkoDecomposition G where
  p := 1
  q := 0
  factor _ := ⊤
  free := 1
  nontrivial _ := Subgroup.topEquiv.injective.nontrivial
  isFreelyIndecomposable _ := hG.of_mulEquiv Subgroup.topEquiv.symm
  isEmpty_mulEquiv_int _ := ⟨fun f => hZ.false (Subgroup.topEquiv.symm.trans f)⟩
  bijective := by
    let Ψ := (MulEquiv.coprodCongr (MulEquiv.coprodIUnique fun _ : Fin 1 => (⊤ : Subgroup G))
      (MulEquiv.ofUnique (M := FreeGroup (Fin 0)) (N := PUnit.{1}))).trans
      ((MulEquiv.coprodPUnit _).trans Subgroup.topEquiv)
    have : Coprod.lift (CoprodI.lift fun _ : Fin 1 => (⊤ : Subgroup G).subtype)
        (1 : FreeGroup (Fin 0) →* G) = Ψ.toMonoidHom :=
      Coprod.hom_ext (CoprodI.ext_hom _ _ fun i => by
        obtain rfl := Unique.eq_default i; ext; simp [Ψ, MulEquiv.coprodCongr])
        (Subsingleton.elim _ _)
    exact this ▸ Ψ.bijective

/-- The Grushko decomposition of `H ∗ F_n` with one freely indecomposable factor, the image of
`H`, and the free factor `F_n`, for a nontrivial freely indecomposable group `H` which is not
infinite cyclic. -/
@[expose, simps p q factor free]
def coprodFreeGroup {H : Type*} [Group H] [Nontrivial H] (hH : IsFreelyIndecomposable H)
    (hZ : IsEmpty (H ≃* Multiplicative ℤ)) (n : ℕ) :
    GrushkoDecomposition (H ∗ FreeGroup (Fin n)) where
  p := 1
  q := n
  factor _ := (Coprod.inl : H →* H ∗ FreeGroup (Fin n)).range
  free := Coprod.inr
  nontrivial _ := (MonoidHom.ofInjective Coprod.inl_injective).injective.nontrivial
  isFreelyIndecomposable _ := hH.of_mulEquiv (MonoidHom.ofInjective Coprod.inl_injective)
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

end GrushkoDecomposition

end TauCeti
