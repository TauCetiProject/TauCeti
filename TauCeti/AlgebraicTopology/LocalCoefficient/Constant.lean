/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.CategoryTheory.HomCongr

/-!
# Constant local coefficient systems and global trivializations

Over a path-connected space `X`, `FundamentalGroupoid X` is connected as a category
(`FundamentalGroupoid.instIsConnected`), so `TauCeti.LocalCoefficientSystem.constantFunctor` is
fully faithful and every isomorphism between constant local systems is induced by its component at
a point (`constantFunctor_iso_eq_mapIso`). Consequently, once a local system `L` admits a
reference trivialization `e₀ : L ≅ (constantFunctor X).obj M`, all trivializations
`L ≅ (constantFunctor X).obj N` correspond bijectively to linear equivalences `M ≃ₗ[R] N`
(`trivializationEquivLinearEquiv`); in particular, global markings by `M` form a principal
homogeneous set under `M ≃ₗ[R] M`.

Without any connectedness hypothesis on `X`, any trivializable local system has trivial path
endomorphisms and trivial monodromy representation at every basepoint
(`monodromyRepresentation_eq_trivial_of_iso_constant`, `monodromyIsoTrivial`).

## Main definitions

* `TauCeti.LocalCoefficientSystem.constantMonodromyIso`,
  `TauCeti.LocalCoefficientSystem.monodromyIsoTrivial`: the monodromy of a constant or
  trivializable local system at `x` is isomorphic in `Rep` to the trivial representation.
* `TauCeti.LocalCoefficientSystem.trivializationEquivLinearEquiv`: over a path-connected space,
  equivalence `(L ≅ (constantFunctor X).obj N) ≃ (M ≃ₗ[R] N)` induced by a reference
  trivialization `e₀ : L ≅ (constantFunctor X).obj M`.

## Main results

* `TauCeti.LocalCoefficientSystem.monodromyRepresentation_eq_trivial_of_iso_constant`: a
  trivializable local system has trivial monodromy representation at every point.
* `TauCeti.LocalCoefficientSystem.constantFunctor_iso_eq_mapIso`: over a path-connected space,
  every isomorphism between constant local systems is induced by its component at a point.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}

/-- Under a trivialization `e : L ≅ (constantFunctor X).obj M`, transport along any path class `p`
factors through `M` as `(e.app x).hom ≫ (e.app y).inv`. -/
theorem map_eq_of_iso_constant {L : LocalCoefficientSystem.{u, v, w} R X} {M : ModuleCat.{w} R}
    (e : L ≅ (constantFunctor (R := R) X).obj M) {x y : FundamentalGroupoid X} (p : x ⟶ y) :
    L.map p = (e.app x).hom ≫ (e.app y).inv := by
  ext a
  have h : (e.app y).hom (L.map p a) = (e.app x).hom a := e.hom.naturality_apply p a
  exact ((e.app y).hom_inv_id_apply (L.map p a)).symm.trans (congrArg (e.app y).inv h)

/-- Under a trivialization of `L`, every loop class acts as the identity on its fiber. -/
theorem map_end_eq_id_of_iso_constant {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e : L ≅ (constantFunctor (R := R) X).obj M)
    {x : FundamentalGroupoid X} (p : x ⟶ x) :
    L.map p = 𝟙 (L.obj x) := by
  rw [map_eq_of_iso_constant e p, Iso.hom_inv_id]

/-- A local system admitting a trivialization has trivial monodromy representation at every
basepoint. -/
theorem monodromyRepresentation_eq_trivial_of_iso_constant
    {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X) :
    monodromyRepresentation L x =
      Representation.trivial R (FundamentalGroup X x) (L.obj (.mk x)) := by
  ext g a
  simp [map_end_eq_id_of_iso_constant e g.asHom]

/-- The monodromy representation of a trivializable local system is trivial in the sense of
`Representation.IsTrivial`. -/
theorem isTrivial_monodromyRepresentation_of_iso_constant
    {L : LocalCoefficientSystem.{u, v, w} R X} {M : ModuleCat.{w} R}
    (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X) :
    (monodromyRepresentation L x).IsTrivial := by
  rw [monodromyRepresentation_eq_trivial_of_iso_constant e x]
  infer_instance

/-- The monodromy object of a constant local system at `x` is canonically isomorphic in `Rep` to
`(Rep.trivialFunctor R (FundamentalGroup X x)).obj M`. -/
def constantMonodromyIso (X : TopCat.{v}) (M : ModuleCat.{w} R) (x : X) :
    (monodromyFunctor R X x).obj ((constantFunctor (R := R) X).obj M) ≅
      (Rep.trivialFunctor R (FundamentalGroup X x)).obj M where
  hom := Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩
  inv := Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩

theorem constantMonodromyIso_hom_apply (X : TopCat.{v}) (M : ModuleCat.{w} R) (x : X) (m : M) :
    (constantMonodromyIso X M x).hom m = m :=
  (rfl)

theorem constantMonodromyIso_inv_apply (X : TopCat.{v}) (M : ModuleCat.{w} R) (x : X) (m : M) :
    (constantMonodromyIso X M x).inv m = m :=
  (rfl)

/-- A trivialization `e : L ≅ (constantFunctor X).obj M` identifies the monodromy representation
`(monodromyFunctor R X x).obj L` in `Rep` with the trivial representation on `M`. -/
def monodromyIsoTrivial {L : LocalCoefficientSystem.{u, v, w} R X} {M : ModuleCat.{w} R}
    (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X) :
    (monodromyFunctor R X x).obj L ≅ (Rep.trivialFunctor R (FundamentalGroup X x)).obj M :=
  (monodromyFunctor R X x).mapIso e ≪≫ constantMonodromyIso X M x

theorem monodromyIsoTrivial_hom_apply {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X)
    (a : L.obj (.mk x)) :
    (monodromyIsoTrivial e x).hom a = e.hom.app (.mk x) a :=
  (rfl)

theorem monodromyIsoTrivial_inv_apply {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e : L ≅ (constantFunctor (R := R) X).obj M) (x : X) (m : M) :
    (monodromyIsoTrivial e x).inv m = e.inv.app (.mk x) m :=
  (rfl)

instance [Nonempty X] :
    (constantFunctor (R := R) X :
      ModuleCat.{w} R ⥤ LocalCoefficientSystem.{u, v, w} R X).Faithful :=
  inferInstanceAs (Functor.const (FundamentalGroupoid X)).Faithful

section PathConnected

variable [PathConnectedSpace X]

instance :
    (constantFunctor (R := R) X :
      ModuleCat.{w} R ⥤ LocalCoefficientSystem.{u, v, w} R X).Full :=
  inferInstanceAs (Functor.const (FundamentalGroupoid X)).Full

private theorem preimageIso_constantFunctor_eq_app {M N : ModuleCat.{w} R}
    (e : (constantFunctor (R := R) X).obj M ≅ (constantFunctor (R := R) X).obj N)
    (x : FundamentalGroupoid X) :
    (Functor.FullyFaithful.ofFullyFaithful (constantFunctor (R := R) X)).preimageIso e =
      e.app x := by
  let hF := Functor.FullyFaithful.ofFullyFaithful (constantFunctor (R := R) X)
  exact Iso.ext <| (constantFunctor_map_app X (hF.preimage e.hom) x).symm.trans
    (congrArg (fun η ↦ η.app x) (hF.map_preimage e.hom))

/-- Over a path-connected space, every isomorphism between constant local systems is induced by its
component at any chosen point. -/
theorem constantFunctor_iso_eq_mapIso {M N : ModuleCat.{w} R}
    (e : (constantFunctor (R := R) X).obj M ≅ (constantFunctor (R := R) X).obj N)
    (x : FundamentalGroupoid X) :
    e = (constantFunctor (R := R) X).mapIso (e.app x) := by
  let hF := Functor.FullyFaithful.ofFullyFaithful (constantFunctor (R := R) X)
  exact (hF.isoEquiv.apply_symm_apply e).symm.trans
    (congrArg (constantFunctor (R := R) X).mapIso (preimageIso_constantFunctor_eq_app e x))

/-- Given a reference trivialization `e₀ : L ≅ (constantFunctor X).obj M` over a path-connected
space `X`, all trivializations `L ≅ (constantFunctor X).obj N` correspond bijectively to linear
equivalences `M ≃ₗ[R] N`. When `N = M`, this exhibits the set of global markings of `L` by `M` as
a torsor under `M ≃ₗ[R] M`. -/
def trivializationEquivLinearEquiv {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) (N : ModuleCat.{w} R) :
    (L ≅ (constantFunctor (R := R) X).obj N) ≃ (M ≃ₗ[R] N) :=
  (Iso.isoCongrLeft e₀).trans <|
    (Functor.FullyFaithful.ofFullyFaithful (constantFunctor (R := R) X)).isoEquiv.symm.trans
      -- `linearEquivIsoModuleIso` restricts carriers to the ring universe `u` of `R : Type u`,
      -- whereas `M N : ModuleCat.{w} R` live in an independent universe `w`.
      { toFun := Iso.toLinearEquiv
        invFun := LinearEquiv.toModuleIso
        left_inv i := by ext; rfl
        right_inv α := by ext; rfl }

/-- Evaluating `trivializationEquivLinearEquiv` agrees with comparing the two trivializations at
any point of the path-connected base. -/
theorem trivializationEquivLinearEquiv_apply {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) (N : ModuleCat.{w} R)
    (e : L ≅ (constantFunctor (R := R) X).obj N) (x : FundamentalGroupoid X) :
    trivializationEquivLinearEquiv e₀ N e =
      ((e₀.app x).symm ≪≫ e.app x).toLinearEquiv := by
  ext m
  exact ConcreteCategory.congr_hom
    (congrArg Iso.hom (preimageIso_constantFunctor_eq_app (Iso.isoCongrLeft e₀ e) x)) m

@[simp]
theorem trivializationEquivLinearEquiv_symm_apply {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) (N : ModuleCat.{w} R)
    (α : M ≃ₗ[R] N) :
    (trivializationEquivLinearEquiv e₀ N).symm α =
      e₀ ≪≫ (constantFunctor (R := R) X).mapIso α.toModuleIso := by
  ext x m
  simp [trivializationEquivLinearEquiv, Iso.isoCongrLeft]

@[simp]
theorem trivializationEquivLinearEquiv_self {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) :
    trivializationEquivLinearEquiv e₀ M e₀ = LinearEquiv.refl R M := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  ext m
  exact (LinearEquiv.congr_fun (trivializationEquivLinearEquiv_apply e₀ M e₀ (.mk x)) m).trans
    ((e₀.app (.mk x)).inv_hom_id_apply m)

theorem trivializationEquivLinearEquiv_symm_refl {L : LocalCoefficientSystem.{u, v, w} R X}
    {M : ModuleCat.{w} R} (e₀ : L ≅ (constantFunctor (R := R) X).obj M) :
    (trivializationEquivLinearEquiv e₀ M).symm (LinearEquiv.refl R M) = e₀ :=
  (trivializationEquivLinearEquiv e₀ M).symm_apply_eq.mpr
    (trivializationEquivLinearEquiv_self e₀).symm

end PathConnected

end TauCeti.LocalCoefficientSystem
