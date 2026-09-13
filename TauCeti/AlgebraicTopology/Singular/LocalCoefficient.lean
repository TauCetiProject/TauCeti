/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Local coefficient systems on topological spaces

A local coefficient system of modules on a space `X` is a functor from the fundamental
groupoid of `X` to `ModuleCat`.  Thus a path class supplies a linear transport map, and the
groupoid laws give all compatibility with concatenation and reversal of paths.

This file provides the categorical operations needed before constructing singular chains with
local coefficients: constant systems, pullback along continuous maps, evaluation at a point,
path transport, and the monodromy representation of the fundamental group.  It also proves that
these constructions interact in the expected way.  In particular, a morphism of local systems
induces an intertwining map on monodromy representations, and transport along a path identifies
the monodromy at its endpoints.

The functorial definition and the monodromy interpretation follow Hatcher, *Algebraic Topology*,
Section 3.H.
-/

public section

noncomputable section

open CategoryTheory

universe u v w v₁ v₂ v₃

namespace TauCeti

/-- An `R`-module-valued local coefficient system on `X` is a functor from the fundamental
groupoid of `X` to `ModuleCat R`. -/
abbrev LocalCoefficientSystem (R : Type u) [Ring R] (X : TopCat.{v}) :=
  FundamentalGroupoid X ⥤ ModuleCat.{w} R

namespace LocalCoefficientSystem

variable {R : Type u} [Ring R]
variable {X : TopCat.{v}}

/-- The constant local coefficient system with fibre `M`. -/
@[expose] def constantFunctor (X : TopCat.{v}) :
    ModuleCat.{w} R ⥤ LocalCoefficientSystem.{u, v, w} R X :=
  Functor.const (FundamentalGroupoid X)

@[simp]
theorem constantFunctor_obj_obj (X : TopCat.{v}) (M : ModuleCat.{w} R)
    (x : FundamentalGroupoid X) :
    ((constantFunctor (R := R) X).obj M).obj x = M :=
  rfl

@[simp]
theorem constantFunctor_obj_map (X : TopCat.{v}) (M : ModuleCat.{w} R)
    {x y : FundamentalGroupoid X} (p : x ⟶ y) :
    ((constantFunctor (R := R) X).obj M).map p = 𝟙 M := by
  simp [constantFunctor]

/-- Pull back local coefficient systems along a continuous map. -/
@[expose] def pullback {X : TopCat.{v₁}} {Y : TopCat.{v₂}} (f : C(X, Y)) :
    LocalCoefficientSystem.{u, v₂, w} R Y ⥤ LocalCoefficientSystem.{u, v₁, w} R X :=
  (Functor.whiskeringLeft _ _ _).obj (FundamentalGroupoid.map f)

@[simp]
theorem pullback_obj_obj {X : TopCat.{v₁}} {Y : TopCat.{v₂}} (f : C(X, Y))
    (L : LocalCoefficientSystem.{u, v₂, w} R Y)
    (x : FundamentalGroupoid X) :
    ((pullback (R := R) f).obj L).obj x = L.obj ((FundamentalGroupoid.map f).obj x) :=
  rfl

@[simp]
theorem pullback_obj_map {X : TopCat.{v₁}} {Y : TopCat.{v₂}} (f : C(X, Y))
    (L : LocalCoefficientSystem.{u, v₂, w} R Y)
    {x y : FundamentalGroupoid X} (p : x ⟶ y) :
    ((pullback (R := R) f).obj L).map p = L.map ((FundamentalGroupoid.map f).map p) :=
  rfl

@[simp]
theorem pullback_map_app {X : TopCat.{v₁}} {Y : TopCat.{v₂}} (f : C(X, Y))
    {L K : LocalCoefficientSystem.{u, v₂, w} R Y}
    (η : L ⟶ K) (x : FundamentalGroupoid X) :
    ((pullback (R := R) f).map η).app x =
      η.app ((FundamentalGroupoid.map f).obj x) :=
  rfl

/-- Pullback along the identity map is naturally isomorphic to the identity functor. -/
def pullbackIdIso (X : TopCat.{v}) :
    pullback (R := R) (.id X) ≅ 𝟭 (LocalCoefficientSystem.{u, v, w} R X) :=
  NatIso.ofComponents (fun L ↦
    Functor.isoWhiskerRight (eqToIso FundamentalGroupoid.map_id) L ≪≫ L.leftUnitor)
    (naturality := by
    intro L K η
    ext x a
    simp [pullback])

/-- Pullback along a composite is naturally isomorphic to the composite of the two pullback
functors, in contravariant order. -/
def pullbackCompIso {X : TopCat.{v₁}} {Y : TopCat.{v₂}} {Z : TopCat.{v₃}}
    (f : C(X, Y)) (g : C(Y, Z)) :
    pullback (R := R) (g.comp f) ≅ pullback (R := R) g ⋙ pullback (R := R) f :=
  NatIso.ofComponents (fun L ↦
    Functor.isoWhiskerRight (eqToIso (FundamentalGroupoid.map_comp g f)) L ≪≫
      Functor.associator _ _ L)
    (naturality := by
    intro L K η
    ext x a
    simp [pullback])

/-- Pulling back a constant local coefficient system leaves it constant. -/
def pullbackConstantIso {X : TopCat.{v₁}} {Y : TopCat.{v₂}} (f : C(X, Y))
    (M : ModuleCat.{w} R) :
    (pullback (R := R) f).obj ((constantFunctor (R := R) Y).obj M) ≅
      (constantFunctor (R := R) X).obj M :=
  Iso.refl _

/-- Evaluation of a local coefficient system at a point of the space. -/
@[expose] def fiberFunctor (R : Type u) [Ring R] (X : TopCat.{v}) (x : X) :
    LocalCoefficientSystem.{u, v, w} R X ⥤ ModuleCat.{w} R :=
  (evaluation _ _).obj (FundamentalGroupoid.mk x)

@[simp]
theorem fiberFunctor_obj (x : X) (L : LocalCoefficientSystem.{u, v, w} R X) :
    (fiberFunctor R X x).obj L = L.obj (FundamentalGroupoid.mk x) :=
  rfl

@[simp]
theorem fiberFunctor_map (x : X) {L K : LocalCoefficientSystem.{u, v, w} R X}
    (η : L ⟶ K) :
    (fiberFunctor R X x).map η = η.app (FundamentalGroupoid.mk x) :=
  rfl

/-- Parallel transport along a path class, as a linear equivalence between the endpoint fibres. -/
def transport {x y : X} (L : LocalCoefficientSystem.{u, v, w} R X)
    (p : Path.Homotopic.Quotient x y) :
    L.obj (FundamentalGroupoid.mk x) ≃ₗ[R] L.obj (FundamentalGroupoid.mk y) :=
  (L.mapIso ((Groupoid.isoEquivHom _ _).symm p)).toLinearEquiv

@[simp]
theorem transport_apply {x y : X} (L : LocalCoefficientSystem.{u, v, w} R X)
    (p : Path.Homotopic.Quotient x y) (a : L.obj (FundamentalGroupoid.mk x)) :
    transport L p a = L.map p a :=
  by simp [transport]

@[simp]
theorem transport_refl (L : LocalCoefficientSystem.{u, v, w} R X) (x : X) :
    transport L (Path.Homotopic.Quotient.refl x) = LinearEquiv.refl R _ := by
  ext a
  rw [transport_apply, LinearEquiv.refl_apply]
  have h : Path.Homotopic.Quotient.refl x = 𝟙 (FundamentalGroupoid.mk x) :=
    (FundamentalGroupoid.id_eq_path_refl _).symm
  rw [h]
  exact L.map_id_apply _ a

@[simp]
theorem transport_trans {x y z : X} (L : LocalCoefficientSystem.{u, v, w} R X)
    (p : Path.Homotopic.Quotient x y) (q : Path.Homotopic.Quotient y z) :
    transport L (p.trans q) = (transport L p).trans (transport L q) := by
  ext a
  exact L.map_comp_apply p q a

@[simp]
theorem transport_symm {x y : X} (L : LocalCoefficientSystem.{u, v, w} R X)
    (p : Path.Homotopic.Quotient x y) :
    transport L p.symm = (transport L p).symm := by
  ext a
  apply (transport L p).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [transport_apply, ← L.map_comp_apply]
  -- Expose the path concatenation underlying composition in the fundamental groupoid.
  change L.map (p.symm.trans p) a = a
  rw [Path.Homotopic.Quotient.symm_trans]
  have h : Path.Homotopic.Quotient.refl y = 𝟙 (FundamentalGroupoid.mk y) :=
    (FundamentalGroupoid.id_eq_path_refl _).symm
  rw [h]
  exact L.map_id_apply _ a

/-- Transport commutes with a morphism of local coefficient systems. -/
theorem transport_naturality {x y : X} {L K : LocalCoefficientSystem.{u, v, w} R X}
    (η : L ⟶ K) (p : Path.Homotopic.Quotient x y)
    (a : L.obj (FundamentalGroupoid.mk x)) :
    η.app (FundamentalGroupoid.mk y) (transport L p a) =
      transport K p (η.app (FundamentalGroupoid.mk x) a) := by
  exact η.naturality_apply p a

/-- Pullback transport is transport along the image path. -/
@[simp]
theorem pullback_transport {X : TopCat.{v₁}} {Y : TopCat.{v₂}} (f : C(X, Y))
    (L : LocalCoefficientSystem.{u, v₂, w} R Y)
    {x y : X} (p : Path.Homotopic.Quotient x y) :
    transport ((pullback (R := R) f).obj L) p = transport L (p.map f) := by
  ext a
  -- Expose precomposition by the induced fundamental-groupoid functor.
  change L.map ((FundamentalGroupoid.map f).map p) a = L.map (p.map f) a
  rfl

/-- The monodromy representation of a local coefficient system at a basepoint. -/
@[expose] def monodromyRepresentation (L : LocalCoefficientSystem.{u, v, w} R X) (x : X) :
    Representation R (FundamentalGroup X x) (L.obj (FundamentalGroupoid.mk x)) where
  toFun g := (L.map g).hom
  map_one' := by
    ext a
    simp
  map_mul' g h := by
    ext a
    exact L.map_comp_apply h g a

@[simp]
theorem monodromyRepresentation_apply
    (L : LocalCoefficientSystem.{u, v, w} R X) (x : X)
    (g : FundamentalGroup X x) (a : L.obj (FundamentalGroupoid.mk x)) :
    monodromyRepresentation L x g a = L.map g a :=
  rfl

@[simp]
theorem constant_monodromyRepresentation (X : TopCat.{v}) (M : ModuleCat.{w} R) (x : X) :
    monodromyRepresentation ((constantFunctor (R := R) X).obj M) x =
      Representation.trivial R (FundamentalGroup X x) M := by
  ext g a
  rfl

@[simp]
theorem pullback_monodromyRepresentation {X : TopCat.{v₁}} {Y : TopCat.{v₂}}
    (f : C(X, Y)) (L : LocalCoefficientSystem.{u, v₂, w} R Y) (x : X) :
    monodromyRepresentation ((pullback (R := R) f).obj L) x =
      (monodromyRepresentation L (f x)).comp (FundamentalGroup.map f x) :=
  rfl

/-- A morphism of local coefficient systems induces an intertwining map between the monodromy
representations on each fibre. -/
@[expose] def monodromyMap {L K : LocalCoefficientSystem.{u, v, w} R X}
    (η : L ⟶ K) (x : X) :
    (monodromyRepresentation L x).IntertwiningMap (monodromyRepresentation K x) where
  toLinearMap := (η.app (FundamentalGroupoid.mk x)).hom
  isIntertwining' g := by
    ext a
    exact η.naturality_apply g a

@[simp]
theorem monodromyMap_apply {L K : LocalCoefficientSystem.{u, v, w} R X} (η : L ⟶ K)
    (x : X) (a : L.obj (FundamentalGroupoid.mk x)) :
    monodromyMap η x a = η.app (FundamentalGroupoid.mk x) a :=
  rfl

/-- Evaluation at a basepoint, equipped with monodromy, is a functor from local coefficient
systems to representations of the fundamental group. -/
@[expose] def monodromyFunctor (R : Type u) [Ring R] (X : TopCat.{v}) (x : X) :
    LocalCoefficientSystem.{u, v, w} R X ⥤ Rep.{w} R (FundamentalGroup X x) where
  obj L := Rep.of (monodromyRepresentation L x)
  map η := Rep.ofHom (monodromyMap η x)
  map_id L := by
    ext a
    rfl
  map_comp η θ := by
    ext a
    rfl

@[simp]
theorem monodromyFunctor_obj_V (x : X) (L : LocalCoefficientSystem.{u, v, w} R X) :
    ((monodromyFunctor R X x).obj L).V =
      L.obj (FundamentalGroupoid.mk x) :=
  rfl

@[simp]
theorem monodromyFunctor_obj_ρ (x : X) (L : LocalCoefficientSystem.{u, v, w} R X) :
    ((monodromyFunctor R X x).obj L).ρ = monodromyRepresentation L x :=
  rfl

@[simp]
theorem monodromyFunctor_map_hom (x : X) {L K : LocalCoefficientSystem.{u, v, w} R X}
    (η : L ⟶ K) :
    ((monodromyFunctor R X x).map η).hom = monodromyMap η x :=
  rfl

/-- Transport along a path intertwines monodromy after changing the basepoint along that path. -/
@[expose] def basepointChangeEquiv (L : LocalCoefficientSystem.{u, v, w} R X) {x y : X}
    (p : Path x y) :
    (monodromyRepresentation L x).Equiv
      ((monodromyRepresentation L y).comp
        (FundamentalGroup.fundamentalGroupMulEquivOfPath p).toMonoidHom) :=
  Representation.Equiv.mk (transport L ⟦p⟧) fun g => by
    ext a
    let α := (Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
      (FundamentalGroupoid.mk y)).symm (⟦p⟧ : Path.Homotopic.Quotient x y)
    -- Expose the underlying module maps so that functoriality of conjugation applies.
    change L.map α.hom (L.map g a) = L.map (α.conj g) (L.map α.hom a)
    rw [L.map_conj]
    simp only [Iso.conj_apply, ModuleCat.comp_apply, Functor.mapIso_hom, Functor.mapIso_inv]
    have h : L.map α.inv (L.map α.hom a) = a := by
      rw [← L.map_comp_apply, α.hom_inv_id]
      exact L.map_id_apply _ a
    rw [h]

@[simp]
theorem basepointChangeEquiv_apply (L : LocalCoefficientSystem.{u, v, w} R X) {x y : X}
    (p : Path x y) (a : L.obj (FundamentalGroupoid.mk x)) :
    basepointChangeEquiv L p a = transport L ⟦p⟧ a :=
  rfl

end LocalCoefficientSystem

end TauCeti
