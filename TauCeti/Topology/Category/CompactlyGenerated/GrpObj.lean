/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.CategoryTheory.Monoidal.SiftedColimits
public import TauCeti.Topology.Category.CompactlyGenerated.CartesianClosed

/-!
# Monoid and group objects in `CompactlyGenerated` and their sifted colimits

A topological monoid or topological group whose underlying space is `u`-compactly generated is a
monoid or group object in the Cartesian closed category `CompactlyGenerated.{u, w}`. More generally,
applying the coreflector `TopCat.toCompactlyGenerated.{u, w}` turns any topological monoid or
topological group into a monoid or group object in `CompactlyGenerated.{u, w}`.

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
* `CompactlyGenerated.instMonObjToCompactlyGeneratedOf`,
  `CompactlyGenerated.instGrpObjToCompactlyGeneratedOf`,
  `CompactlyGenerated.instIsMonHomAdjHomEquivOfHom`: arbitrary topological monoids and groups
  coreflected into `CompactlyGenerated.{u, w}`.
* `CompactlyGenerated.groupOfGrpObj`, `CompactlyGenerated.isTopologicalGroup_of_grpObj`,
  `CompactlyGenerated.monoidHomOfIsMonHom`: extracting a `Group` and `IsTopologicalGroup` from a
  `GrpObj` whose Cartesian square is compactly generated.
* `CompactlyGenerated.instPreservesColimitsOfShapeTensorRight`: `tensorRight X` preserves all
  colimits in `CompactlyGenerated.{u, w}`, unlocking `Grp.forgetCreatesColimitsOfShape` and
  `HasColimitsOfShape` for sifted shapes.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj Topology

universe u w v v'

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

section ToCompactlyGenerated

variable (M : Type w) [Monoid M] [TopologicalSpace M] [ContinuousMul M]

/-- Applying the coreflector `TopCat.toCompactlyGenerated.{u, w}` to any topological monoid yields
a monoid object in `CompactlyGenerated.{u, w}`. -/
instance instMonObjToCompactlyGeneratedOf :
    MonObj (TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M)) where
  one := adj.{u, w}.homEquiv (𝟙_ CompactlyGenerated.{u, w}) (TopCat.of M)
    (TopCat.ofHom ⟨fun _ ↦ (1 : M), continuous_const⟩)
  mul :=
    let kM := TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M)
    let f₁ : (kM ⊗ kM).toTop ⟶ TopCat.of M :=
      (CartesianMonoidalCategory.fst kM kM).hom ≫ adj.{u, w}.counit.app (TopCat.of M)
    let f₂ : (kM ⊗ kM).toTop ⟶ TopCat.of M :=
      (CartesianMonoidalCategory.snd kM kM).hom ≫ adj.{u, w}.counit.app (TopCat.of M)
    let fmul : @ContinuousMap (kM ⊗ kM).toTop M (kM ⊗ kM).toTop.str _ :=
      ContinuousMap.comp ⟨fun q : M × M ↦ q.1 * q.2, continuous_mul⟩
        (f₁.hom.prodMk f₂.hom)
    adj.{u, w}.homEquiv (kM ⊗ kM) (TopCat.of M)
      (@TopCat.ofHom (kM ⊗ kM).toTop M (kM ⊗ kM).toTop.str _ fmul)
  one_mul := ConcreteCategory.hom_ext _ _ fun p ↦ _root_.one_mul (p.2 : M)
  mul_one := ConcreteCategory.hom_ext _ _ fun p ↦ _root_.mul_one (p.1 : M)
  mul_assoc := ConcreteCategory.hom_ext _ _ fun p ↦
    _root_.mul_assoc (p.1.1 : M) (p.1.2 : M) (p.2 : M)

variable {M}

@[simp]
theorem toCompactlyGenerated_of_one_apply (p : ↑(𝟙_ CompactlyGenerated.{u, w})) :
    (η[TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M)] p : M) = (1 : M) := rfl

@[simp]
theorem toCompactlyGenerated_of_mul_apply
    (p : ↑(TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M) ⊗
      TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M))) :
    (μ[TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M)] p : M) =
      @HMul.hMul M M M _ p.1 p.2 := rfl

/-- Applying the coreflector `TopCat.toCompactlyGenerated.{u, w}` to a commutative topological
monoid yields a commutative monoid object in `CompactlyGenerated.{u, w}`. -/
instance instIsCommMonObjToCompactlyGeneratedOf (M : Type w) [CommMonoid M] [TopologicalSpace M]
    [ContinuousMul M] : IsCommMonObj (TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M)) where
  mul_comm := ConcreteCategory.hom_ext _ _ fun p ↦ _root_.mul_comm (p.2 : M) (p.1 : M)

/-- Applying the coreflector `TopCat.toCompactlyGenerated.{u, w}` to any topological group yields a
group object in `CompactlyGenerated.{u, w}`. -/
instance instGrpObjToCompactlyGeneratedOf (M : Type w) [Group M] [TopologicalSpace M]
    [IsTopologicalGroup M] : GrpObj (TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M)) where
  inv :=
    adj.{u, w}.homEquiv (TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M)) (TopCat.of M)
      (adj.{u, w}.counit.app (TopCat.of M) ≫
        TopCat.ofHom ⟨fun x : M ↦ x⁻¹, continuous_inv⟩)
  left_inv := ConcreteCategory.hom_ext _ _ fun x ↦ _root_.inv_mul_cancel (x : M)
  right_inv := ConcreteCategory.hom_ext _ _ fun x ↦ _root_.mul_inv_cancel (x : M)

@[simp]
theorem toCompactlyGenerated_of_inv_apply {M : Type w} [Group M] [TopologicalSpace M]
    [IsTopologicalGroup M] (x : TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M)) :
    (ι[TopCat.toCompactlyGenerated.{u, w}.obj (TopCat.of M)] x : M) =
      (let x' : M := x; x'⁻¹) := rfl

/-- The adjoint transpose to `CompactlyGenerated.{u, w}` of a continuous monoid homomorphism out of
a `u`-compactly generated topological monoid is a morphism of monoid objects. -/
instance instIsMonHomAdjHomEquivOfHom {M N : Type w} [Monoid M] [TopologicalSpace M]
    [UCompactlyGeneratedSpace.{u} M] [ContinuousMul M] [Monoid N] [TopologicalSpace N]
    [ContinuousMul N] (φ : M →ₜ* N) :
    IsMonHom (adj.{u, w}.homEquiv (of.{u, w} M) (TopCat.of N) (TopCat.ofHom (φ : C(M, N)))) where
  one_hom := ConcreteCategory.hom_ext _ _ fun _ ↦ by
    change φ 1 = 1
    exact map_one φ
  mul_hom := ConcreteCategory.hom_ext _ _ fun p ↦ by
    change φ (p.1 * p.2) = φ p.1 * φ p.2
    exact map_mul φ p.1 p.2

end ToCompactlyGenerated

section FromGrpObj

/-- The `Monoid` structure on the underlying type of a monoid object in
`CompactlyGenerated.{u, w}`. -/
@[instance_reducible, expose]
def monoidOfMonObj (X : CompactlyGenerated.{u, w}) [MonObj X] : Monoid X where
  mul x y := μ[X] (x, y)
  one := η[X] PUnit.unit
  mul_assoc x y z := by
    change μ[X] (μ[X] (x, y), z) = μ[X] (x, μ[X] (y, z))
    exact ConcreteCategory.congr_hom (MonObj.mul_assoc (X := X))
      (((x, y), z) : ↑((X ⊗ X) ⊗ X))
  one_mul x := by
    change μ[X] (η[X] PUnit.unit, x) = x
    exact ConcreteCategory.congr_hom (MonObj.one_mul (X := X))
      ((PUnit.unit, x) : ↑(𝟙_ _ ⊗ X))
  mul_one x := by
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
  have hmul : (fun p : X × X ↦ p.1 * p.2) =
      ⇑(μ[X] : X ⊗ X ⟶ X) ∘ ⇑(counitHomeomorph.{u, w} (TopCat.of (X × X))).symm := rfl
  rw [hmul]
  exact μ[X].hom.hom.continuous.comp (counitHomeomorph.{u, w} (TopCat.of (X × X))).symm.continuous

/-- A morphism of monoid objects between group objects in `CompactlyGenerated.{u, w}` is a monoid
homomorphism with respect to `groupOfGrpObj`. -/
@[expose]
def monoidHomOfIsMonHom {X Y : CompactlyGenerated.{u, w}} [GrpObj X] [GrpObj Y] (f : X ⟶ Y)
    [IsMonHom f] :
    @MonoidHom X Y (groupOfGrpObj X).toMulOne (groupOfGrpObj Y).toMulOne :=
  letI := groupOfGrpObj X
  letI := groupOfGrpObj Y
  { toFun := f
    map_one' := ConcreteCategory.congr_hom (IsMonHom.one_hom f) PUnit.unit
    map_mul' x y := ConcreteCategory.congr_hom (IsMonHom.mul_hom f) (x, y) }

@[simp]
theorem monoidHomOfIsMonHom_apply {X Y : CompactlyGenerated.{u, w}} [GrpObj X] [GrpObj Y]
    (f : X ⟶ Y) [IsMonHom f] (x : X) : monoidHomOfIsMonHom f x = f x := rfl

end FromGrpObj

section SiftedColimits

instance instPreservesColimitsOfShapeTensorRight (J : Type v) [Category.{v'} J]
    (X : CompactlyGenerated.{u, w}) :
    PreservesColimitsOfShape J (MonoidalCategory.tensorRight X) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- A cocone in `Grp CompactlyGenerated.{u, w}` over a sifted diagram whose underlying cocone in
`TopCat.{w}` is colimiting is itself a colimit cocone. -/
def isColimitGrpOfTopCat {J : Type v} [Category.{v'} J] [IsSifted J]
    (F : J ⥤ Grp CompactlyGenerated.{u, w}) (c : Cocone F)
    (hc : IsColimit
      ((Grp.forget CompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w}).mapCocone c)) :
    IsColimit c :=
  Grp.isColimitOfForget F c (isColimitOfReflects compactlyGeneratedToTop.{u, w} hc)

/-- A cocone in `CommGrp CompactlyGenerated.{u, w}` over a sifted diagram whose underlying cocone
in `TopCat.{w}` is colimiting is itself a colimit cocone. -/
def isColimitCommGrpOfTopCat {J : Type v} [Category.{v'} J] [IsSifted J]
    (F : J ⥤ CommGrp CompactlyGenerated.{u, w}) (c : Cocone F)
    (hc : IsColimit
      ((CommGrp.forget CompactlyGenerated.{u, w} ⋙ compactlyGeneratedToTop.{u, w}).mapCocone c)) :
    IsColimit c :=
  CommGrp.isColimitOfForget F c (isColimitOfReflects compactlyGeneratedToTop.{u, w} hc)

end SiftedColimits

end CompactlyGenerated

end
