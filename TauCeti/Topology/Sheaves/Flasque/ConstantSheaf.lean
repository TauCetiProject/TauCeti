/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
import TauCeti.Topology.Sheaves.Presheaf

/-!
# Constant sheaves on irreducible spaces are flasque

Let `X` be a topological space and `A` an object of a concrete category `D` in which
sheafification is computed by a locally bijective map (as for abelian groups, modules or types).
The constant sheaf `A_X` is the sheafification of the constant presheaf with value `A`, and in
general its sections over an open `U` are the locally constant `A`-valued functions on `U`.

When `U` is irreducible, every two nonempty opens of `U` meet, so a locally constant function on
`U` is constant: the canonical map `A ⟶ A_X(U)` is a bijection. In particular, on an irreducible
space `X` every nonempty open has sections `A`, and the restriction maps between nonempty opens
are identities under these identifications. Over the empty open the sections are a terminal
object (a zero object when `D` has one, by `TopCat.Sheaf.isZero_obj_of_eq_bot`). Hence, when
`D` has a zero object, the constant sheaf on an irreducible space is flasque. For sheaves of
abelian groups its cohomology therefore vanishes in positive degrees, by the instance
`TauCeti.Topology.subsingleton_H_succ_of_isFlasque` from `TauCeti.Topology.Sheaves.Flasque.Basic`,
which callers import themselves. This does not happen automatically:
`TauCeti.Topology.isFlasque_constantSheaf` is a theorem rather than an instance (instance search
for it times out for abelian groups), so callers first write `have := isFlasque_constantSheaf A`.
A spectral space with a generic point is irreducible, so this applies to it.

## Main declarations

* `TauCeti.toSheafify_app_const_comp_map`: on any site, restricting the image of `A` in the
  sections of the constant sheaf over `U` to `V` gives its image over `V`.
* `TauCeti.Topology.injective_toSheafify_app_const`: on any space, the map `A ⟶ A_X(U)` is
  injective when `U` is nonempty.
* `TauCeti.Topology.bijective_toSheafify_app_const`: the map `A ⟶ A_X(U)` is bijective when `U`
  is irreducible.
* `TauCeti.Topology.constantSheafSectionsIso`: the isomorphism `A ≅ A_X(U)` for irreducible `U`;
  by `TauCeti.Topology.constantSheafSectionsIso_hom_comp_map`, it turns restriction maps into
  the identity of `A`.
* `TauCeti.Topology.isFlasque_constantSheaf`: on an irreducible space, the constant sheaf is
  flasque.

## References

* The Stacks Project, tag 02UW, proof of Lemma 20.20.2, *Cohomology of irreducible spaces*.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TauCeti

section Site

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {D : Type*} [Category* D]
  [HasWeakSheafify J D]

/-- On any site, restricting the image of `A` in the sections of the constant sheaf over `U`
along `i : U ⟶ V` gives the image of `A` over `V`, since the constant presheaf has identity
restrictions. -/
@[reassoc]
theorem toSheafify_app_const_comp_map (A : D) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (toSheafify J ((Functor.const _).obj A)).app U ≫ ((constantSheaf J D).obj A).obj.map i =
      (toSheafify J ((Functor.const _).obj A)).app V :=
  -- `((constantSheaf J D).obj A).obj` is by definition the sheafification of the constant
  -- presheaf, whose restriction maps are identities.
  ((toSheafify J ((Functor.const _).obj A)).naturality i).symm.trans (by simp)

/-- The elementwise form of `toSheafify_app_const_comp_map`: restricting the image of `a : A` in
the sections of the constant sheaf over `U` along `i : U ⟶ V` gives the image of `a` over `V`. -/
@[simp]
theorem toSheafify_app_const_map_apply {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    (A : D) {U V : Cᵒᵖ} (i : U ⟶ V) (a : ToType A) :
    ((constantSheaf J D).obj A).obj.map i ((toSheafify J ((Functor.const _).obj A)).app U a) =
      (toSheafify J ((Functor.const _).obj A)).app V a := by
  rw [← ConcreteCategory.comp_apply, toSheafify_app_const_comp_map]

end Site

namespace Topology

variable {X : TopCat.{u}} {D : Type*} [Category* D] {FD : D → D → Type*} {CD : D → Type*}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
  [HasWeakSheafify (Opens.grothendieckTopology X) D]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective D]

/-- Over a nonempty open `U`, the canonical map from `A` to the sections of the constant sheaf
`A_X` over `U` is injective. -/
theorem injective_toSheafify_app_const (A : D) {U : Opens X} (hU : (U : Set X).Nonempty) :
    Function.Injective
      ((toSheafify (Opens.grothendieckTopology X) ((Functor.const _).obj A)).app (op U)) := by
  intro a b h
  obtain ⟨x, hx⟩ := hU
  obtain ⟨V, f, hf, -⟩ :=
    Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X) _ a b h x hx
  simpa using hf

/-- Over an irreducible open `U`, the canonical map from `A` to the sections of the constant
sheaf `A_X` over `U` is bijective: a locally constant function on an irreducible space is
constant. -/
theorem bijective_toSheafify_app_const [(Opens.grothendieckTopology X).HasSheafCompose (forget D)]
    (A : D) {U : Opens X} (hU : IsIrreducible (U : Set X)) :
    Function.Bijective
      ((toSheafify (Opens.grothendieckTopology X) ((Functor.const _).obj A)).app (op U)) := by
  let J := Opens.grothendieckTopology X
  let F := (presheafToSheaf J D).obj ((Functor.const _).obj A)
  let φ := toSheafify J ((Functor.const _).obj A)
  refine ⟨injective_toSheafify_app_const A hU.nonempty, fun s ↦ ?_⟩
  -- The sheaf `A_X`, viewed as a sheaf of types.
  have hF : Presieve.IsSheaf J (F.obj ⋙ forget D) :=
    (isSheaf_iff_isSheaf_of_type J _).1 ((sheafCompose J (forget D)).obj F).property
  -- Near a point `x₀ ∈ U` the section `s` is the image of some `a : A`; we show `s = φ a`.
  obtain ⟨x₀, hx₀⟩ := hU.nonempty
  obtain ⟨V₀, f₀, ⟨a, ha⟩, hxV₀⟩ := Presheaf.imageSieve_mem J φ s x₀ hx₀
  refine ⟨a, (hF.isSeparated _ (Presheaf.imageSieve_mem J φ s)).ext fun W g ⟨b, hb⟩ ↦ ?_⟩
  -- The separatedness goal is stated for `F.obj ⋙ forget D`; restate it with restriction maps.
  change F.obj.map g.op (φ.app (op U) a) = F.obj.map g.op s
  rw [← hb]
  refine (toSheafify_app_const_map_apply J A g.op a).trans ?_
  rcases (W : Set X).eq_empty_or_nonempty with hW | hW
  · -- Over the empty open the sections of a sheaf form a terminal object.
    exact (Types.isTerminalEquivUnique _ (TopCat.Sheaf.isTerminalOfEqEmpty
      ((sheafCompose J (forget D)).obj F) (SetLike.coe_injective hW))).instSubsingleton.elim _ _
  · -- Otherwise `W` meets `V₀` inside the irreducible `U`, and `a = b` near a common point.
    obtain ⟨w, hw⟩ := hW
    obtain ⟨y, -, hyW, hyV₀⟩ := hU.2 _ _ W.isOpen V₀.isOpen ⟨w, g.le hw, hw⟩ ⟨x₀, hx₀, hxV₀⟩
    suffices a = b by rw [this]
    refine injective_toSheafify_app_const (U := W ⊓ V₀) A ⟨y, hyW, hyV₀⟩ ?_
    rw [← toSheafify_app_const_map_apply J A (homOfLE (inf_le_right : W ⊓ V₀ ≤ V₀)).op,
      ← toSheafify_app_const_map_apply J A (homOfLE (inf_le_left : W ⊓ V₀ ≤ W)).op, ha, hb]
    exact TopCat.Presheaf.map_map_apply_eq_map_map_apply _ _ _ _ _ s

/-- Over an irreducible open `U`, the sections of the constant sheaf `A_X` over `U` are `A`. -/
noncomputable def constantSheafSectionsIso
    [(Opens.grothendieckTopology X).HasSheafCompose (forget D)] [(forget D).ReflectsIsomorphisms]
    (A : D) {U : Opens X} (hU : IsIrreducible (U : Set X)) :
    A ≅ ((constantSheaf (Opens.grothendieckTopology X) D).obj A).obj.obj (op U) :=
  haveI := (ConcreteCategory.isIso_iff_bijective _).2 (bijective_toSheafify_app_const A hU)
  asIso ((toSheafify (Opens.grothendieckTopology X) ((Functor.const _).obj A)).app (op U))

@[simp]
theorem constantSheafSectionsIso_hom
    [(Opens.grothendieckTopology X).HasSheafCompose (forget D)] [(forget D).ReflectsIsomorphisms]
    (A : D) {U : Opens X} (hU : IsIrreducible (U : Set X)) :
    (constantSheafSectionsIso A hU).hom =
      (toSheafify (Opens.grothendieckTopology X) ((Functor.const _).obj A)).app (op U) :=
  (rfl)

/-- Under the identifications `A ≅ A_X(U)` of `constantSheafSectionsIso`, the restriction maps
between irreducible opens are the identity of `A`. -/
@[reassoc]
theorem constantSheafSectionsIso_hom_comp_map
    [(Opens.grothendieckTopology X).HasSheafCompose (forget D)] [(forget D).ReflectsIsomorphisms]
    (A : D) {U V : Opens X} (hU : IsIrreducible (U : Set X)) (hV : IsIrreducible (V : Set X))
    (i : op U ⟶ op V) :
    (constantSheafSectionsIso A hU).hom ≫
        ((constantSheaf (Opens.grothendieckTopology X) D).obj A).obj.map i =
      (constantSheafSectionsIso A hV).hom := by
  rw [constantSheafSectionsIso_hom, constantSheafSectionsIso_hom, toSheafify_app_const_comp_map]

/-- On an irreducible space, the constant sheaf with values in a concrete category with a zero
object is flasque.

This is a theorem rather than an instance, because instance search for it times out for
`AddCommGrpCat`. To get the vanishing of positive-degree cohomology from
`TauCeti.Topology.subsingleton_H_succ_of_isFlasque`, first bring it into scope with
`have := isFlasque_constantSheaf A`. -/
theorem isFlasque_constantSheaf [IrreducibleSpace X]
    [(Opens.grothendieckTopology X).HasSheafCompose (forget D)] [HasZeroObject D] (A : D) :
    TopCat.Presheaf.IsFlasque ((constantSheaf (Opens.grothendieckTopology X) D).obj A).obj where
  epi {U V} i := by
    induction V with | op V
    let φ := toSheafify (Opens.grothendieckTopology X) ((Functor.const _).obj A)
    rcases (V : Set X).eq_empty_or_nonempty with hV | hV
    · exact (TopCat.Sheaf.isZero_obj_of_eq_bot _ (SetLike.coe_injective hV)).epi _
    · -- Both `A ⟶ A_X(V)` and `A ⟶ A_X(U)` are bijective, and they commute with restriction.
      refine ConcreteCategory.epi_of_surjective _ fun t ↦ ?_
      obtain ⟨a, rfl⟩ := (bijective_toSheafify_app_const A
        ⟨hV, (IrreducibleSpace.isIrreducible_univ X).2.open_subset V.isOpen
          (Set.subset_univ _)⟩).2 t
      exact ⟨φ.app U a, toSheafify_app_const_map_apply _ A i a⟩

end Topology

end TauCeti
