/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Induced
import TauCeti.RepresentationTheory.FiniteIndex

/-!
# General facts about induced representations

Mathlib's `Rep.ind φ` induces a representation along an arbitrary homomorphism of groups
`φ : G →* H`, and `Rep.indMap φ` induces an intertwiner along it. This file collects the
general properties of that construction that Mathlib does not record and that the rest of
`TauCeti/RepresentationTheory/Induction/` needs, independently of any finiteness assumption
on the groups or on the representations.

## Main definitions

* `Representation.IntertwiningMap.ind`: induction of an intertwining map along `φ`, the unbundled
  form of `Rep.indMap`.
* `Representation.Equiv.ind`: induction of an equivalence of representations along `φ`.

## Main statements

* `Rep.indMap_hom_mk`: an induced intertwiner acts on the coefficient of each generator.
* `Rep.indMap_add`: inducing an intertwiner along `φ` is additive, and `Rep.indFunctor_additive`:
  the same fact as a `CategoryTheory.Functor.Additive` instance for `Rep.indFunctor`.
* `Rep.indMap_smul` and `Rep.indFunctor_linear`: induction is linear over the coefficient ring.
* `Representation.IndV.mk_one_injective`: the generator map `a ↦ ⟦1 ⊗ a⟧` is injective for a
  subgroup.
* `Rep.indMap_injective` and `Rep.indFunctor_faithful`: induction from a subgroup is faithful.
* `Representation.IntertwiningMap.ind_id`, `Representation.IntertwiningMap.ind_comp`: induction
  of intertwining maps is functorial.

## Implementation notes

As in `TauCeti/RepresentationTheory/Induction/Projection.lean`, the generator lemmas
`Representation.IntertwiningMap.ind_mk`, `Representation.Equiv.ind_mk` and
`Representation.Equiv.ind_symm_mk` are stated with the reducible abbreviation
`Representation.IndV.mk`, which `simp` unfolds, so they are not `simp` lemmas and are applied by
`rw`.
-/

public section

open CategoryTheory Representation

universe u v w w' t

namespace Rep

/-- An induced intertwiner applies the original intertwiner to each generator's coefficient. -/
@[simp↓]
theorem indMap_hom_mk {k : Type u} {G : Type v} {H : Type w}
    [CommRing k] [Group G] [Group H] (φ : G →* H)
    {A B : Rep.{w'} k G} (f : A ⟶ B) (h : H) (a : A) :
    (indMap φ f).hom (IndV.mk φ A.ρ h a) = IndV.mk φ B.ρ h (f.hom a) := by
  simp [indMap]

/-- Induction–restriction reciprocity evaluates a morphism on the tensor generator at `1`. -/
theorem indResHomEquiv_hom_apply {k : Type u} {G : Type v} {H : Type w}
    [CommRing k] [Group G] [Group H] (φ : G →* H)
    (A : Rep.{max t w u} k G) (B : Rep.{max t w u} k H)
    (f : ind φ A ⟶ B) (a : A) :
    (indResHomEquiv.{t, u, v, w} φ A B f).hom a = f.hom (IndV.mk φ A.ρ 1 a) :=
  rfl

/-- **Induction of intertwiners is additive**: for any homomorphism of groups `φ : G →* H`,
`Rep.indMap φ (f + g) = Rep.indMap φ f + Rep.indMap φ g`. -/
theorem indMap_add {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G] [Group H]
    (φ : G →* H) {A B : Rep.{w'} k G} (f g : A ⟶ B) :
    indMap φ (f + g) = indMap φ f + indMap φ g := by
  ext h a
  simp [indMap, add_hom]

/-- **Induction along a homomorphism of groups is an additive functor**, the functorial form of
`Rep.indMap_add`. -/
instance indFunctor_additive {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G]
    [Group H] (φ : G →* H) :
    ((indFunctor k φ : Rep.{w'} k G ⥤ Rep k H)).Additive where
  map_add {_ _} f g := indMap_add φ f g

/-- Inducing an intertwiner commutes with scalar multiplication. -/
@[simp]
theorem indMap_smul {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G]
    [Group H] (φ : G →* H) {A B : Rep.{w'} k G} (r : k) (f : A ⟶ B) :
    indMap φ (r • f) = r • indMap φ f := by
  ext h a
  simp [indMap, smul_hom]

/-- Induction along a group homomorphism is linear over the coefficient ring. -/
instance indFunctor_linear {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G]
    [Group H] (φ : G →* H) :
    Functor.Linear k (indFunctor k φ : Rep.{w'} k G ⥤ Rep k H) where
  map_smul f r := indMap_smul φ r f

end Rep

namespace Representation

/-- The generator map `a ↦ ⟦1 ⊗ a⟧` from a representation `A` of a subgroup `S` into the carrier
`(k[G] ⊗ A)_S` of its induced representation is injective. -/
theorem IndV.mk_one_injective {k : Type u} {G : Type v} [CommRing k] [Group G] (S : Subgroup G)
    {A : Type w} [AddCommGroup A] [Module k A] (ρ : Representation k S A) :
    Function.Injective (IndV.mk S.subtype ρ 1) := by
  classical
  -- Mathlib's induction-to-coinduction map, evaluated at `1`, is a left inverse.
  have key (x : A) : (Rep.indToCoind (Rep.of ρ) (IndV.mk S.subtype ρ 1 x)).1 1 = x :=
    congrFun (TauCeti.indToCoind_mk (A := Rep.of ρ) 1 x) 1 |>.trans
      (Rep.indToCoindAux_self (A := Rep.of ρ) 1 x)
  intro a b h
  rw [← key a, ← key b, h]

section Ind

variable {k G H A B : Type*} [CommRing k] [Group G] [Group H] (φ : G →* H)
  [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  {ρ : Representation k G A} {σ : Representation k G B}

namespace IntertwiningMap

/-- **Induction of an intertwining map** along `φ : G →* H`: the map `⟦h ⊗ₜ a⟧ ↦ ⟦h ⊗ₜ f a⟧`.
This is the unbundled form of `Rep.indMap`. -/
noncomputable def ind (f : IntertwiningMap ρ σ) :
    IntertwiningMap (Representation.ind φ ρ) (Representation.ind φ σ) where
  toLinearMap := Coinvariants.map _ _ ⟨f.toLinearMap.lTensor _, by
    simp [LinearMap.lTensor_comp_map, f.2, LinearMap.map_comp_lTensor]⟩
  isIntertwining' _ := by ext; simp

theorem ind_mk (f : IntertwiningMap ρ σ) (h : H) (a : A) :
    f.ind φ (IndV.mk φ ρ h a) = IndV.mk φ σ h (f a) :=
  (rfl)

@[simp]
theorem ind_id : (IntertwiningMap.id ρ).ind φ = IntertwiningMap.id (Representation.ind φ ρ) :=
  IntertwiningMap.ext <| IndV.hom_ext φ _ fun _ => rfl

theorem ind_comp {C : Type*} [AddCommGroup C] [Module k C] {τ : Representation k G C}
    (f : IntertwiningMap σ τ) (g : IntertwiningMap ρ σ) :
    (f.comp g).ind φ = (f.ind φ).comp (g.ind φ) :=
  IntertwiningMap.ext <| IndV.hom_ext φ _ fun _ => rfl

end IntertwiningMap

namespace Equiv

/-- **Induction of an equivalence of representations** along `φ : G →* H`: the equivalence
`⟦h ⊗ₜ a⟧ ↦ ⟦h ⊗ₜ e a⟧`, with inverse induced by `e.symm`. -/
noncomputable def ind (e : Equiv ρ σ) : Equiv (Representation.ind φ ρ) (Representation.ind φ σ) :=
  .mk (LinearEquiv.ofLinearMap (e.toIntertwiningMap.ind φ).toLinearMap
      (e.symm.toIntertwiningMap.ind φ).toLinearMap
      (by ext; simp [IntertwiningMap.ind])
      (by ext; simp [IntertwiningMap.ind]))
    (e.toIntertwiningMap.ind φ).isIntertwining'

theorem ind_mk (e : Equiv ρ σ) (h : H) (a : A) :
    e.ind φ (IndV.mk φ ρ h a) = IndV.mk φ σ h (e a) :=
  (rfl)

theorem ind_symm_mk (e : Equiv ρ σ) (h : H) (b : B) :
    (e.ind φ).symm (IndV.mk φ σ h b) = IndV.mk φ ρ h (e.symm b) :=
  (rfl)

end Equiv

end Ind

end Representation

namespace Rep

/-- Induction from a subgroup is injective on intertwining spaces. -/
theorem indMap_injective {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G}
    {V W : Rep.{w'} k S} : Function.Injective (indMap S.subtype : (V ⟶ W) → _) := by
  intro f g h
  apply hom_ext
  ext x
  apply IndV.mk_one_injective S W.ρ
  simpa using congrArg (fun m : ind S.subtype V ⟶ ind S.subtype W ↦
    m.hom (IndV.mk S.subtype V.ρ 1 x)) h

/-- Induction from a subgroup is a faithful functor, the functorial form of
`Rep.indMap_injective`. -/
instance indFunctor_faithful {k : Type u} {G : Type v} [CommRing k] [Group G] (S : Subgroup G) :
    (indFunctor k S.subtype : Rep.{w'} k S ⥤ Rep k G).Faithful where
  map_injective h := indMap_injective h

end Rep
