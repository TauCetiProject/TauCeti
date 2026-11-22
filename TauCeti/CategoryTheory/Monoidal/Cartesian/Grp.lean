/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Group-object homomorphisms and integer power maps in cartesian monoidal categories

This file complements `TauCeti.CategoryTheory.Monoidal.Cartesian.Mon` for group objects in a
cartesian monoidal category `C`:

* `CategoryTheory.isMonHom_iff_forall_mul_comp`: a morphism `f : M ⟶ H` from a monoid object to
  a group object is a monoid-object homomorphism if and only if postcomposition by `f` preserves
  multiplication on `X`-valued points for every `X : C` (unit preservation is automatic by
  cancellation);
* `CategoryTheory.GrpObj.zpowMap`: the canonical integer power endomorphism `𝟙 G ^ n : G ⟶ G` on
  a group object `G` (additive `AddGrpObj.zsmulMap`), sending every point `x : X ⟶ G` to `x ^ n`
  (`GrpObj.comp_zpowMap`), satisfying arithmetic identities (`zpowMap_zero`, `zpowMap_one`,
  `zpowMap_neg_one`, `zpowMap_add`, `zpowMap_neg`, `zpowMap_sub`, `zpowMap_mul`), naturality with
  respect to homomorphisms (`zpowMap_comp`) and monoidal functors (`Functor.map_zpowMap`), and
  forming a monoid-object homomorphism whenever `G` is commutative (`isMonHom_zpowMap`).
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.AddMonObj

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism `f : M ⟶ H` from a monoid object to a group object in a cartesian monoidal category
is a monoid-object homomorphism if and only if postcomposition by `f` preserves multiplication on
`X`-points for every `X : C`. -/
@[to_additive
/-- A morphism `f : M ⟶ H` from an additive monoid object to an additive group object in a
cartesian monoidal category is an additive monoid-object homomorphism if and only if postcomposition
by `f` preserves addition on `X`-points for every `X : C`. -/]
theorem isMonHom_iff_forall_mul_comp {M H : C} [MonObj M] [GrpObj H] (f : M ⟶ H) :
    IsMonHom f ↔ ∀ (X : C) (x y : X ⟶ M), (x * y) ≫ f = x ≫ f * y ≫ f := by
  rw [isMonHom_iff_forall_one_comp_mul_comp]
  refine ⟨fun h X x y ↦ (h X).2 x y, fun hmul X ↦ ⟨?_, hmul X⟩⟩
  have h1 : ((1 : X ⟶ M) ≫ f) * ((1 : X ⟶ M) ≫ f) = (1 : X ⟶ M) ≫ f := by
    rw [← hmul X 1 1, _root_.mul_one]
  exact mul_left_cancel (h1.trans (_root_.mul_one _).symm)

namespace GrpObj

/-- The `n`-th power endomorphism `𝟙 G ^ n : G ⟶ G` of a group object in a cartesian monoidal
category. On `X`-valued points it acts by raising each point to the `n`-th power
(`GrpObj.comp_zpowMap`). -/
@[to_additive
/-- The `n`-th scalar-multiple endomorphism `n • 𝟙 G : G ⟶ G` of an additive group object in a
cartesian monoidal category. On `X`-valued points it acts by `n • -`
(`AddGrpObj.comp_zsmulMap`). -/]
noncomputable def zpowMap (G : C) [GrpObj G] (n : ℤ) : G ⟶ G :=
  𝟙 G ^ n

/-- `zpowMap G n` is the `n`-th power of `𝟙 G` in `G ⟶ G`. -/
@[to_additive /-- `zsmulMap G n` is `n • 𝟙 G` in `G ⟶ G`. -/]
theorem zpowMap_eq_zpow (G : C) [GrpObj G] (n : ℤ) : zpowMap G n = 𝟙 G ^ n := by
  unfold zpowMap
  rfl

/-- Postcomposing a point `x : X ⟶ G` with `zpowMap G n` raises `x` to the `n`-th power. -/
@[to_additive (attr := reassoc (attr := simp))]
theorem comp_zpowMap {X G : C} [GrpObj G] (x : X ⟶ G) (n : ℤ) :
    x ≫ zpowMap G n = x ^ n := by
  rw [zpowMap_eq_zpow, GrpObj.comp_zpow, Category.comp_id]

/-- `zpowMap G 0` is the constant unit morphism `1 : G ⟶ G`. -/
@[to_additive (attr := simp)]
theorem zpowMap_zero (G : C) [GrpObj G] : zpowMap G 0 = 1 :=
  zpow_zero (𝟙 G)

/-- `zpowMap G 1` is the identity morphism on `G`. -/
@[to_additive (attr := simp) zsmulMap_one]
theorem zpowMap_one (G : C) [GrpObj G] : zpowMap G 1 = 𝟙 G :=
  zpow_one (𝟙 G)

/-- `zpowMap G (-1)` is the inversion morphism `ι[G]`. -/
@[to_additive (attr := simp) zsmulMap_neg_one]
theorem zpowMap_neg_one (G : C) [GrpObj G] : zpowMap G (-1) = ι[G] := by
  rw [zpowMap_eq_zpow, zpow_neg_one, Hom.inv_def, Category.id_comp]

/-- `zpowMap G (m + n)` is the pointwise product `zpowMap G m * zpowMap G n`. -/
@[to_additive (attr := simp)]
theorem zpowMap_add (G : C) [GrpObj G] (m n : ℤ) :
    zpowMap G (m + n) = zpowMap G m * zpowMap G n :=
  zpow_add (𝟙 G) m n

/-- `zpowMap G (-n)` is the pointwise inverse `(zpowMap G n)⁻¹`. -/
@[to_additive]
theorem zpowMap_neg (G : C) [GrpObj G] (n : ℤ) :
    zpowMap G (-n) = (zpowMap G n)⁻¹ :=
  zpow_neg (𝟙 G) n

/-- `zpowMap G (m - n)` is the pointwise quotient `zpowMap G m / zpowMap G n`. -/
@[to_additive (attr := simp)]
theorem zpowMap_sub (G : C) [GrpObj G] (m n : ℤ) :
    zpowMap G (m - n) = zpowMap G m / zpowMap G n :=
  zpow_sub (𝟙 G) m n

/-- `zpowMap G (m * n)` is the composite `zpowMap G n ≫ zpowMap G m`. -/
@[to_additive zsmulMap_mul]
theorem zpowMap_mul (G : C) [GrpObj G] (m n : ℤ) :
    zpowMap G (m * n) = zpowMap G n ≫ zpowMap G m := by
  rw [comp_zpowMap, zpowMap_eq_zpow, zpowMap_eq_zpow, zpow_mul']

/-- Every homomorphism of group objects commutes with `zpowMap _ n`. -/
@[to_additive (attr := reassoc)]
theorem zpowMap_comp {G H : C} [GrpObj G] [GrpObj H] (n : ℤ) (f : G ⟶ H) [IsMonHom f] :
    zpowMap G n ≫ f = f ≫ zpowMap H n := by
  rw [zpowMap_eq_zpow, GrpObj.zpow_comp, comp_zpowMap, Category.id_comp]

/-- On a commutative group object, `zpowMap G n` is a monoid-object homomorphism. -/
@[to_additive]
instance isMonHom_zpowMap [BraidedCategory C] (G : C) [GrpObj G] [IsCommMonObj G] (n : ℤ) :
    IsMonHom (zpowMap G n) := by
  rw [isMonHom_iff_forall_mul_comp]
  intro X x y
  simp [mul_zpow]

/-- On a terminal group object, every `zpowMap` is the identity. -/
@[to_additive]
theorem zpowMap_eq_id_of_isTerminal {G : C} [GrpObj G] (hG : Limits.IsTerminal G) (n : ℤ) :
    zpowMap G n = 𝟙 G :=
  hG.hom_ext _ _

end GrpObj

namespace Functor

open scoped CategoryTheory.Obj

/-- A monoidal functor between cartesian monoidal categories sends `zpowMap G n` to
`zpowMap (F.obj G) n`. -/
@[to_additive (attr := simp)]
theorem map_zpowMap {D : Type*} [Category* D] [CartesianMonoidalCategory D] (F : C ⥤ D)
    [F.Monoidal] (G : C) [GrpObj G] (n : ℤ) :
    F.map (GrpObj.zpowMap G n) = GrpObj.zpowMap (F.obj G) n := by
  simpa [GrpObj.zpowMap_eq_zpow] using F.homMonoidHom.map_zpow (𝟙 G) n

end Functor

end CategoryTheory
