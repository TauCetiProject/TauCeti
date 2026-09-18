/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Invertible sheaves on a scheme

This file begins the scheme-level line-bundle lane of the Jacobian challenge. An invertible
sheaf on a scheme `X` is an `𝒪_X`-module which is locally free of rank one.

The rank-one condition itself is not specific to schemes: it is
`TauCeti.SheafOfModules.IsInvertible` from
`TauCeti/Algebra/Category/ModuleCat/Sheaf/Invertible/Basic.lean`, stated for a sheaf of modules
over an arbitrary site. This file only packages it over a scheme:

* `TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X` is the `ObjectProperty` on `X.Modules`
  cut out by the predicate (closed under isomorphisms, by the site-level transport theorem, so
  `ObjectProperty.prop_of_iso` and `ObjectProperty.prop_iff_of_iso` apply to it);
* `TauCeti.AlgebraicGeometry.InvertibleSheaf X` is the full subcategory it cuts out;
* `InvertibleSheaf.free X I` is the free sheaf on an indexing type with exactly one element, and
  `InvertibleSheaf.trivial X` is the globally free rank-one sheaf;
* `SheafOfModules.isInvertible_unit` records that the structure sheaf `𝒪_X`, as a sheaf of
  modules over itself, is invertible.

A free rank-one trivialization of an `𝒪_X`-module `M` over an open `V` gives local coordinates:

* `Scheme.Modules.trivializationCoordinate` is the linear isomorphism `Γ(M, W) ≃ Γ(X, W)` it
  induces on every open `W ≤ V`, and `Scheme.Modules.trivializationGenerator` is the basis
  section of `M` over `V` with coordinate one;
* `Scheme.Modules.existsUnique_eq_smul_map_trivializationGenerator` writes every section over
  `W ≤ V` uniquely as a regular multiple of the restricted basis section, and
  `Scheme.Modules.existsUnique_map_trivializationGenerator_eq_smul` shows that the basis sections
  of two trivializations differ by a unique regular unit on any common open subset.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible sheaves on a
scheme; the Picard group `Pic X` under `⊗`". The tensor product and Picard group require a
monoidal structure on sheaves of modules and are left to subsequent files. No formalization is
vendored.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SheafOfModules

variable (X : Scheme.{u})

/-- The object property of being an invertible sheaf on a scheme. -/
abbrev isInvertible : ObjectProperty X.Modules :=
  TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf)

instance : (isInvertible X).IsClosedUnderIsomorphisms where
  of_iso e hM := by
    have := hM
    exact TauCeti.SheafOfModules.IsInvertible.of_iso (R := X.ringCatSheaf) e

/-- The structure sheaf, regarded as a sheaf of modules over itself, is an invertible sheaf: it is
the free sheaf on one generator. -/
instance isInvertible_unit :
    isInvertible X (_root_.SheafOfModules.unit X.ringCatSheaf) :=
  TauCeti.SheafOfModules.IsInvertible.of_iso
    (M := _root_.SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1})
    (N := _root_.SheafOfModules.unit X.ringCatSheaf)
    (TauCeti.SheafOfModules.freePUnitIsoUnit X.ringCatSheaf)

end SheafOfModules

variable {X : Scheme.{u}}

/-- The full category of invertible sheaves on `X`. Its morphisms are morphisms of
`𝒪_X`-modules. -/
abbrev InvertibleSheaf (X : Scheme.{u}) : Type _ :=
  ObjectProperty.FullSubcategory (SheafOfModules.isInvertible X)

namespace InvertibleSheaf

instance (L : InvertibleSheaf X) : SheafOfModules.isInvertible X L.obj :=
  L.property

/-- The invertible sheaf given by the free sheaf on an indexing type with exactly one element. -/
def free (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    InvertibleSheaf X :=
  ⟨SheafOfModules.free (R := X.ringCatSheaf) I, inferInstance⟩

@[simp]
lemma free_obj (X : Scheme.{u}) (I : Type u) [Nonempty I] [Subsingleton I] :
    (free X I).obj = SheafOfModules.free (R := X.ringCatSheaf) I :=
  (rfl)

/-- The globally free rank-one invertible sheaf. -/
def trivial (X : Scheme.{u}) : InvertibleSheaf X :=
  free X PUnit

@[simp]
lemma trivial_obj (X : Scheme.{u}) :
    (trivial X).obj = SheafOfModules.free (R := X.ringCatSheaf) PUnit :=
  (rfl)

end InvertibleSheaf

end

end AlgebraicGeometry

namespace SheafOfModules.LocalTrivializations

universe u

variable {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- A free rank-one trivialization over an open is an isomorphism from the structure sheaf of
the open subscheme to the restricted module sheaf. -/
noncomputable def unitIsoRestrict
    (e : _root_.SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    _root_.SheafOfModules.unit (U : AlgebraicGeometry.Scheme).ringCatSheaf ≅
      M.restrict (AlgebraicGeometry.Scheme.Opens.ι U) :=
  (AlgebraicGeometry.Scheme.Modules.overEquiv U).functor.mapIso
      ((TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)).symm ≪≫ e) ≪≫
    (AlgebraicGeometry.Scheme.Modules.overFunctorEquiv U).app M

end SheafOfModules.LocalTrivializations

end TauCeti

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Opposite

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- The coordinate isomorphism from a locally trivial rank-one module sheaf to the structure
sheaf on the trivializing open subset. -/
@[expose]
def trivializationCoordinateIso (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  e.symm ≪≫ TauCeti.SheafOfModules.freePUnitIsoUnit (X.ringCatSheaf.over U)

/-- The coordinate of a free rank-one trivialization over `U`, read on an open subset `W ≤ U`:
the linear isomorphism between sections of the module sheaf and regular functions on `W`. -/
@[expose]
def trivializationCoordinate (M : X.Modules) {U W : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U) (i : W ⟶ U) :
    Γ(M, W) ≃ₗ[Γ(X, W)] Γ(X, W) where
  -- Sections of `M.over U` and of the unit sheaf over `Over.mk i` are, by definition of the
  -- pushforward along `Over.forget U`, sections of `M` and of `𝒪_X` over `W`; over each open the
  -- unit sheaf is the ring of sections as a module over itself.
  toFun s := (trivializationCoordinateIso M e).hom.val.app (op (Over.mk i)) s
  invFun r := (trivializationCoordinateIso M e).inv.val.app (op (Over.mk i)) r
  map_add' := map_add _
  map_smul' := ((trivializationCoordinateIso M e).hom.val.app (op (Over.mk i))).hom.map_smul
  left_inv s := Iso.hom_inv_id_apply ((SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _).mapIso (trivializationCoordinateIso M e) |>.app
      (op (Over.mk i))) (s : Γ(M, W))
  right_inv r := Iso.inv_hom_id_apply ((SheafOfModules.forget _ ⋙
    PresheafOfModules.toPresheaf _).mapIso (trivializationCoordinateIso M e) |>.app
      (op (Over.mk i))) (r : Γ(X, W))

/-- The basis section of a line bundle over an open subset carrying a chosen rank-one
trivialization. -/
def trivializationGenerator (M : X.Modules) {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) : Γ(M, V) :=
  (trivializationCoordinate M t (𝟙 V)).symm 1

/-- The chosen trivialization reads the restriction of its basis section to any open subset
`W ≤ V` as the constant coordinate one. -/
@[simp]
theorem trivializationCoordinate_map_trivializationGenerator (M : X.Modules) {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V) :
    trivializationCoordinate M t i (M.presheaf.map i.op (trivializationGenerator M t)) = 1 := by
  let c := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
    (trivializationCoordinateIso M t).inv
  have h := c.naturality_apply (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op (1 : Γ(X, V))
  -- Restriction in `M.over V` and in the unit sheaf along `Over.homMk i` is, by definition of
  -- the pushforward along `Over.forget V`, restriction in `M` and in `𝒪_X` along `i`.
  have h' : M.presheaf.map i.op (trivializationGenerator M t) =
      (trivializationCoordinate M t i).symm (X.presheaf.map i.op 1) := by
    have hM : M.presheaf.map i.op (trivializationGenerator M t) =
        (M.over V).val.presheaf.map (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op
          (trivializationGenerator M t) := rfl
    have hX : (X.presheaf.map i.op 1 : Γ(X, W)) =
        (SheafOfModules.unit (X.ringCatSheaf.over V)).val.presheaf.map
          (Over.homMk i : Over.mk i ⟶ Over.mk (𝟙 V)).op (1 : Γ(X, V)) := rfl
    rw [hM, hX]
    exact h.symm
  rw [h', map_one, LinearEquiv.apply_symm_apply]

/-- On an open subset `W ≤ V`, every section is a unique regular-function multiple of the
restriction of the basis section of a rank-one trivialization over `V`. -/
theorem existsUnique_eq_smul_map_trivializationGenerator (M : X.Modules) {V W : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V) (i : W ⟶ V)
    (s : Γ(M, W)) :
    ∃! r : Γ(X, W), s = r • M.presheaf.map i.op (trivializationGenerator M t) := by
  have hcoord (r : Γ(X, W)) :
      trivializationCoordinate M t i (r • M.presheaf.map i.op (trivializationGenerator M t)) =
        r := by
    rw [LinearEquiv.map_smul, trivializationCoordinate_map_trivializationGenerator,
      smul_eq_mul, mul_one]
  refine ⟨trivializationCoordinate M t i s, ?_, ?_⟩
  · exact (trivializationCoordinate M t i).injective (hcoord _).symm
  · rintro r rfl
    exact (hcoord r).symm

/-- Every section on a rank-one trivializing open subset is a unique regular-function multiple of
the distinguished basis section. -/
theorem existsUnique_eq_smul_trivializationGenerator (M : X.Modules) {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    (s : Γ(M, V)) :
    ∃! r : Γ(X, V), s = r • trivializationGenerator M t := by
  simpa only [op_id, M.presheaf.map_id, ConcreteCategory.id_apply] using
    existsUnique_eq_smul_map_trivializationGenerator M t (𝟙 V) s

/-- On an open subset `W` contained in the domains of two rank-one trivializations, the
restrictions of their basis sections differ by a unique unit of the regular functions on `W`. -/
theorem existsUnique_map_trivializationGenerator_eq_smul (M : X.Modules) {V₁ V₂ W : X.Opens}
    (t₁ : SheafOfModules.free (R := X.ringCatSheaf.over V₁) PUnit ≅ M.over V₁)
    (t₂ : SheafOfModules.free (R := X.ringCatSheaf.over V₂) PUnit ≅ M.over V₂)
    (i₁ : W ⟶ V₁) (i₂ : W ⟶ V₂) :
    ∃! u : Γ(X, W)ˣ, M.presheaf.map i₁.op (trivializationGenerator M t₁) =
      (u : Γ(X, W)) • M.presheaf.map i₂.op (trivializationGenerator M t₂) := by
  obtain ⟨r, hr, hr_unique⟩ := existsUnique_eq_smul_map_trivializationGenerator M t₂ i₂
    (M.presheaf.map i₁.op (trivializationGenerator M t₁))
  obtain ⟨s, hs, -⟩ := existsUnique_eq_smul_map_trivializationGenerator M t₁ i₁
    (M.presheaf.map i₂.op (trivializationGenerator M t₂))
  obtain ⟨r₁, -, h_unique⟩ := existsUnique_eq_smul_map_trivializationGenerator M t₁ i₁
    (M.presheaf.map i₁.op (trivializationGenerator M t₁))
  have hrs : r * s = 1 := by
    refine (h_unique (r * s) ?_).trans (h_unique 1 (one_smul _ _).symm).symm
    beta_reduce
    rw [mul_smul, ← hs, ← hr]
  refine ⟨Units.mkOfMulEqOne r s hrs, hr, fun u hu ↦ Units.ext ?_⟩
  rw [Units.val_mkOfMulEqOne]
  exact hr_unique _ hu

/-- The distinguished basis section of a rank-one trivialization is nonzero on a nonempty open
subset. -/
theorem trivializationGenerator_ne_zero (M : X.Modules) {V : X.Opens}
    (t : SheafOfModules.free (R := X.ringCatSheaf.over V) PUnit ≅ M.over V)
    [Nonempty V] :
    trivializationGenerator M t ≠ 0 := by
  intro h
  have hcoord := trivializationCoordinate_map_trivializationGenerator M t (𝟙 V)
  rw [op_id, M.presheaf.map_id, ConcreteCategory.id_apply, h, map_zero] at hcoord
  exact zero_ne_one (α := Γ(X, V)) hcoord

end

end AlgebraicGeometry.Scheme.Modules
