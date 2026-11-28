/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.CategoryTheory.Monoidal.SiftedColimits
public import TauCeti.Topology.Category.CompactlyGenerated.CartesianClosed

/-!
# Monoid and group objects in `CompactlyGenerated` and their sifted colimits

A topological monoid or topological group whose underlying space is `u`-compactly generated is a
monoid or group object in the Cartesian closed category `CompactlyGenerated.{u, w}`.

Because `CompactlyGenerated.{u, w}` is braided and monoidal closed, both `tensorLeft X` and
`tensorRight X` preserve all colimits, so by `TauCeti.CategoryTheory.Monoidal.SiftedColimits` the
forgetful functors from `Mon CompactlyGenerated.{u, w}`, `CommMon CompactlyGenerated.{u, w}`,
`Grp CompactlyGenerated.{u, w}`, and `CommGrp CompactlyGenerated.{u, w}` create all sifted colimits
(in particular filtered and sequential colimits). Conversely, a group object `X` whose ordinary
Cartesian square `X × X` is `u`-compactly generated yields a `Group` and `IsTopologicalGroup`
structure on `X`.

## Main declarations

* `CompactlyGenerated.instMonObjOf`, `CompactlyGenerated.instIsCommMonObjOf`,
  `CompactlyGenerated.instGrpObjOf`, `CompactlyGenerated.instIsMonHomOfHom`: topological monoids
  and groups of `u`-compactly generated spaces as monoid and group objects.
* `CompactlyGenerated.groupOfGrpObj`, `CompactlyGenerated.isTopologicalGroup_of_grpObj`,
  `CompactlyGenerated.monoidHomOfIsMonHom`: extracting a `Group` and `IsTopologicalGroup` from a
  `GrpObj` whose Cartesian square is compactly generated.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj Topology

universe u w

namespace CompactlyGenerated

section OfTopologicalGroup

variable (M : Type w) [Monoid M] [TopologicalSpace M] [UCompactlyGeneratedSpace.{u} M]
  [ContinuousMul M]

/-- A `u`-compactly generated topological monoid is a monoid object in `CompactlyGenerated.{u, w}`,
with multiplication `(x, y) ↦ x * y` and unit `1`. -/
instance instMonObjOf : MonObj (of.{u, w} M) where
  one := ofHom ⟨fun _ ↦ (1 : M), continuous_const⟩
  mul := InducedCategory.homMk <|
    adj.{u, w}.counit.app (TopCat.of (M × M)) ≫
      TopCat.ofHom ⟨fun p : M × M ↦ p.1 * p.2, continuous_mul⟩
  one_mul := ConcreteCategory.hom_ext _ _ fun p ↦ _root_.one_mul p.2
  mul_one := ConcreteCategory.hom_ext _ _ fun p ↦ _root_.mul_one p.1
  mul_assoc := ConcreteCategory.hom_ext _ _ fun p ↦ _root_.mul_assoc p.1.1 p.1.2 p.2

variable {M}

@[simp]
theorem of_one_apply (p : ↑(𝟙_ CompactlyGenerated.{u, w})) : η[of.{u, w} M] p = 1 := rfl

@[simp]
theorem of_mul_apply (p : ↑(of.{u, w} M ⊗ of.{u, w} M)) : μ[of.{u, w} M] p = p.1 * p.2 := rfl

/-- A `u`-compactly generated commutative topological monoid is a commutative monoid object in
`CompactlyGenerated.{u, w}`. -/
instance instIsCommMonObjOf (M : Type w) [CommMonoid M] [TopologicalSpace M]
    [UCompactlyGeneratedSpace.{u} M] [ContinuousMul M] : IsCommMonObj (of.{u, w} M) where
  mul_comm := ConcreteCategory.hom_ext _ _ fun p ↦ _root_.mul_comm p.2 p.1

/-- A `u`-compactly generated topological group is a group object in
`CompactlyGenerated.{u, w}`. -/
instance instGrpObjOf (M : Type w) [Group M] [TopologicalSpace M] [UCompactlyGeneratedSpace.{u} M]
    [IsTopologicalGroup M] : GrpObj (of.{u, w} M) where
  inv := ofHom ⟨fun x : M ↦ x⁻¹, continuous_inv⟩
  left_inv := ConcreteCategory.hom_ext _ _ fun x ↦ _root_.inv_mul_cancel x
  right_inv := ConcreteCategory.hom_ext _ _ fun x ↦ _root_.mul_inv_cancel x

@[simp]
theorem of_inv_apply {M : Type w} [Group M] [TopologicalSpace M] [UCompactlyGeneratedSpace.{u} M]
    [IsTopologicalGroup M] (x : M) :
    (ι[of.{u, w} M] : of.{u, w} M ⟶ of.{u, w} M) x = x⁻¹ := rfl

/-- A continuous monoid homomorphism between `u`-compactly generated topological monoids is a
morphism of monoid objects in `CompactlyGenerated.{u, w}`. -/
instance instIsMonHomOfHom {M N : Type w} [Monoid M] [TopologicalSpace M]
    [UCompactlyGeneratedSpace.{u} M] [ContinuousMul M] [Monoid N] [TopologicalSpace N]
    [UCompactlyGeneratedSpace.{u} N] [ContinuousMul N] (φ : M →ₜ* N) :
    IsMonHom (ofHom (φ : C(M, N)) : of.{u, w} M ⟶ of.{u, w} N) where
  one_hom := ConcreteCategory.hom_ext _ _ fun _ ↦ map_one φ
  mul_hom := ConcreteCategory.hom_ext _ _ fun p ↦ map_mul φ p.1 p.2

end OfTopologicalGroup

section FromGrpObj

/-- The `Monoid` structure on the underlying type of a monoid object in
`CompactlyGenerated.{u, w}`. -/
@[instance_reducible, expose]
def monoidOfMonObj (X : CompactlyGenerated.{u, w}) [MonObj X] : Monoid X where
  mul x y := μ[X] (x, y)
  one := η[X] PUnit.unit
  mul_assoc x y z := by
    -- `X ⊗ X` and `(X ⊗ X) ⊗ X` have underlying types `X × X` and `(X × X) × X`.
    change μ[X] (μ[X] (x, y), z) = μ[X] (x, μ[X] (y, z))
    exact ConcreteCategory.congr_hom (MonObj.mul_assoc (X := X))
      (((x, y), z) : ↑((X ⊗ X) ⊗ X))
  one_mul x := by
    -- `𝟙_ CompactlyGenerated ⊗ X` has underlying type `PUnit × X`.
    change μ[X] (η[X] PUnit.unit, x) = x
    exact ConcreteCategory.congr_hom (MonObj.one_mul (X := X))
      ((PUnit.unit, x) : ↑(𝟙_ _ ⊗ X))
  mul_one x := by
    -- `X ⊗ 𝟙_ CompactlyGenerated` has underlying type `X × PUnit`.
    change μ[X] (x, η[X] PUnit.unit) = x
    exact ConcreteCategory.congr_hom (MonObj.mul_one (X := X))
      ((x, PUnit.unit) : ↑(X ⊗ 𝟙_ _))

/-- The `Group` structure on the underlying type of a group object in
`CompactlyGenerated.{u, w}`. -/
@[instance_reducible, expose]
def groupOfGrpObj (X : CompactlyGenerated.{u, w}) [GrpObj X] : Group X where
  __ := monoidOfMonObj X
  inv x := (ι[X] : X ⟶ X) x
  inv_mul_cancel x := by
    -- `groupOfGrpObj`'s `mul` and `inv` unfold to `μ[X]` and `ι[X]` on `X × X`.
    change μ[X] ((ι[X] : X ⟶ X) x, x) = η[X] PUnit.unit
    have h := ConcreteCategory.congr_hom (GrpObj.left_inv X) x
    exact h.trans (congrArg η[X] (Subsingleton.elim _ PUnit.unit))

@[simp]
theorem groupOfGrpObj_one (X : CompactlyGenerated.{u, w}) [GrpObj X] :
    (letI := groupOfGrpObj X; (1 : X)) = η[X] PUnit.unit := rfl

@[simp]
theorem groupOfGrpObj_mul (X : CompactlyGenerated.{u, w}) [GrpObj X] (x y : X) :
    (letI := groupOfGrpObj X; x * y) = μ[X] (x, y) := rfl

@[simp]
theorem groupOfGrpObj_inv (X : CompactlyGenerated.{u, w}) [GrpObj X] (x : X) :
    (letI := groupOfGrpObj X; x⁻¹) = (ι[X] : X ⟶ X) x := rfl

/-- When the ordinary Cartesian square `X × X` of a group object `X` in `CompactlyGenerated.{u, w}`
is `u`-compactly generated, `X` is a topological group for its underlying topology. -/
theorem isTopologicalGroup_of_grpObj (X : CompactlyGenerated.{u, w}) [GrpObj X]
    (hprod : UCompactlyGeneratedSpace.{u} (X × X)) :
    @IsTopologicalGroup X _ (groupOfGrpObj X) := by
  let _ := groupOfGrpObj X
  refine
    { continuous_mul := ?_
      continuous_inv := (ι[X] : X ⟶ X).hom.hom.continuous }
  -- `counitHomeomorph (TopCat.of (X × X))` is the identity on points
  -- (`counitHomeomorph_symm_apply`), and `X ⊗ X` is
  -- `TopCat.toCompactlyGenerated.obj (TopCat.of (X × X))`.
  have hmul : (fun p : X × X ↦ p.1 * p.2) =
      ⇑(μ[X] : X ⊗ X ⟶ X) ∘ ⇑(counitHomeomorph.{u, w} (TopCat.of (X × X))).symm :=
    funext fun p ↦ (groupOfGrpObj_mul X p.1 p.2).trans
      (congrArg (μ[X] : X ⊗ X ⟶ X) (counitHomeomorph_symm_apply (TopCat.of (X × X)) p).symm)
  rw [hmul]
  exact μ[X].hom.hom.continuous.comp (counitHomeomorph.{u, w} (TopCat.of (X × X))).symm.continuous

/-- A morphism of monoid objects in `CompactlyGenerated.{u, w}` is a monoid homomorphism with
respect to `monoidOfMonObj`. -/
def monoidHomOfIsMonHom {X Y : CompactlyGenerated.{u, w}} [MonObj X] [MonObj Y] (f : X ⟶ Y)
    [IsMonHom f] :
    @MonoidHom X Y (monoidOfMonObj X).toMulOne (monoidOfMonObj Y).toMulOne :=
  letI := monoidOfMonObj X
  letI := monoidOfMonObj Y
  { toFun := f
    map_one' := ConcreteCategory.congr_hom (IsMonHom.one_hom f) PUnit.unit
    map_mul' x y := ConcreteCategory.congr_hom (IsMonHom.mul_hom f) (x, y) }

@[simp]
theorem monoidHomOfIsMonHom_apply {X Y : CompactlyGenerated.{u, w}} [MonObj X] [MonObj Y]
    (f : X ⟶ Y) [IsMonHom f] (x : X) : monoidHomOfIsMonHom f x = f x := (rfl)

end FromGrpObj

end CompactlyGenerated

end
