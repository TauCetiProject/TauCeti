/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
public import TauCeti.AlgebraicGeometry.Morphisms.OverTensorUnit

/-!
# Abelian schemes

An **abelian scheme** over a scheme `S` is a group object `A` in `Over S` whose structure
morphism is proper and smooth with geometrically connected fibres. No commutativity, relative
dimension or ample line bundle is part of the data: commutativity is a theorem, the relative
dimension is a locally constant function on `S`, and a polarization is extra structure. The base
`S` is arbitrary, nonreduced bases included.

The structure `AbelianScheme S` bundles the underlying object `toOver : Over S` with its group
law and the three properties of its structure morphism. The underlying scheme is `toScheme` and
the zero section is `zeroSection`, a section of the structure morphism.

The file also provides:

* `AbelianScheme.baseChange`: for `f : T ⟶ S`, the pullback of `A` along `f`, with the group law
  transported by the monoidal pullback functor. Its group object is
  `(Over.pullback f).mapGrp.obj (Grp.mk A.toOver)` (`grpMk_baseChange_toOver`), so the point-group
  identification `TauCeti.GroupScheme.baseChangePointMulEquiv` applies to it directly.
* `AbelianScheme.identity`: the base `S ⟶ S` with its trivial group law, the abelian scheme of
  relative dimension zero.
* the category of abelian schemes over `S`, whose morphisms are morphisms of `Over S` preserving
  the group law (`IsMonHom`), and the base-change functor `AbelianScheme.baseChangeFunctor`.

A smooth morphism with geometrically connected fibres is geometrically integral
(`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`). That instance lives in
`TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral`, which this file does not
import; once it is imported, as in `TauCeti.AlgebraicGeometry.AbelianScheme.AbelianVariety`, the
structure morphism of an abelian scheme is geometrically integral by instance search. Together
with properness this is what identifies abelian schemes over a field with Tau Ceti's
`AbelianVariety`, in that file.

## References

* S. Kass, *Notes on abelian schemes*, §1.
* G. Faltings and C.-L. Chai, *Degeneration of abelian varieties*, Chapter I, §1.
* M. Olsson, *Compactifications of moduli of abelian varieties: an introduction*, §2.1.4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- An **abelian scheme** over a scheme `S`: a group object in `Over S` whose structure morphism
is proper and smooth with geometrically connected fibres.

The group-object structure lives on `toOver : Over S`; the underlying scheme is
`toScheme = toOver.left`. No commutativity, dimension or ample line bundle is part of the data. -/
structure AbelianScheme (S : Scheme.{u}) where
  /-- The underlying group scheme over `S`. -/
  toOver : Over S
  /-- The group law. -/
  grpObj : GrpObj toOver
  /-- The structure morphism is proper. -/
  isProper : IsProper toOver.hom
  /-- The structure morphism is smooth. -/
  smooth : Smooth toOver.hom
  /-- The structure morphism has geometrically connected fibres. -/
  geometricallyConnected : GeometricallyConnected toOver.hom

namespace AbelianScheme

variable {S T : Scheme.{u}}

attribute [instance] AbelianScheme.grpObj AbelianScheme.isProper AbelianScheme.smooth
  AbelianScheme.geometricallyConnected

/-- The underlying scheme of an abelian scheme. -/
noncomputable abbrev toScheme (A : AbelianScheme S) : Scheme.{u} :=
  A.toOver.left

/-- Two abelian schemes over `S` are equal when their underlying group objects are equal. -/
lemma ext {A B : AbelianScheme S} (h : Grp.mk A.toOver = Grp.mk B.toOver) : A = B := by
  cases A
  cases B
  cases h
  rfl

/-! ### The zero section -/

/-- The zero section `S ⟶ A` of an abelian scheme, that is, the unit of its group law. -/
noncomputable abbrev zeroSection (A : AbelianScheme S) : S ⟶ A.toScheme :=
  η[A.toOver].left

/-- The zero section is a section of the structure morphism. Not a simp lemma: `Over.w` and
`Over.tensorUnit_hom` already prove it. -/
@[reassoc]
lemma zeroSection_comp_toOver_hom (A : AbelianScheme S) :
    A.zeroSection ≫ A.toOver.hom = 𝟙 S := by
  simpa only [Over.tensorUnit_hom] using η[A.toOver].w

/-! ### Base change -/

/-- The base change of an abelian scheme along a morphism `f : T ⟶ S`, obtained by pulling back
the group scheme along `f`.

Properness, smoothness and geometric connectedness are stable under base change, and the monoidal
pullback functor carries the group-object structure (`Functor.grpObjObj`). -/
@[expose] noncomputable def baseChange (A : AbelianScheme S) (f : T ⟶ S) : AbelianScheme T where
  toOver := (Over.pullback f).obj A.toOver
  grpObj := Functor.grpObjObj
  isProper := inferInstanceAs (IsProper (pullback.snd A.toOver.hom f))
  smooth := inferInstanceAs (Smooth (pullback.snd A.toOver.hom f))
  geometricallyConnected := inferInstanceAs (GeometricallyConnected (pullback.snd A.toOver.hom f))

@[simp]
lemma baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).toOver = (Over.pullback f).obj A.toOver :=
  (rfl)

/-- The underlying scheme of a base change is the fibre product of `A` with `T` over `S`. -/
lemma baseChange_toScheme (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).toScheme = pullback A.toOver.hom f :=
  (rfl)

/-- The group object underlying a base change is the image of the group object of `A` under the
pullback functor on group objects. In particular the points of the base change are identified
with points of `A` by `TauCeti.GroupScheme.baseChangePointMulEquiv`. -/
lemma grpMk_baseChange_toOver (A : AbelianScheme S) (f : T ⟶ S) :
    Grp.mk (A.baseChange f).toOver = (Over.pullback f).mapGrp.obj (Grp.mk A.toOver) :=
  (rfl)

/-- The zero section of a base change is the pullback of the zero section of `A`: the point of
`pullback A.toOver.hom f` given by `f ≫ A.zeroSection` and `𝟙 T`. -/
lemma zeroSection_baseChange (A : AbelianScheme S) (f : T ⟶ S) :
    (A.baseChange f).zeroSection = pullback.lift (f ≫ A.zeroSection) (𝟙 T) (by
      rw [Category.assoc, zeroSection_comp_toOver_hom, Category.comp_id, Category.id_comp]) := by
  refine pullback.hom_ext ?_ ((A.baseChange f).zeroSection_comp_toOver_hom.trans
    (pullback.lift_snd _ _ _).symm)
  -- The unit of the transported group law is `ε (Over.pullback f) ≫ (Over.pullback f).map η`.
  have hη : η[(A.baseChange f).toOver] =
      Functor.LaxMonoidal.ε (Over.pullback f) ≫ (Over.pullback f).map η[A.toOver] :=
    Functor.obj.η_def _
  rw [zeroSection, hη, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    pullback.lift_fst]
  simp only [Over.pullback_map_left, pullback.lift_fst, Over.tensorUnit_hom]
  rw [← pullback.condition_assoc, Category.id_comp]

/-! ### The identity abelian scheme -/

/-- The **identity abelian scheme** over `S`: the base `S ⟶ S` with its trivial group law. It is
the abelian scheme of relative dimension zero. -/
@[expose] noncomputable def identity (S : Scheme.{u}) : AbelianScheme S where
  toOver := 𝟙_ (Over S)
  grpObj := inferInstance
  isProper := inferInstance
  smooth := inferInstance
  geometricallyConnected := inferInstance

@[simp]
lemma identity_toOver (S : Scheme.{u}) : (identity S).toOver = 𝟙_ (Over S) :=
  (rfl)

/-- The group object underlying the identity abelian scheme is the trivial group object. -/
lemma grpMk_identity_toOver (S : Scheme.{u}) :
    Grp.mk (identity S).toOver = Grp.trivial (Over S) :=
  (rfl)

/-- The zero section of the identity abelian scheme is the identity of `S`. -/
@[simp]
lemma zeroSection_identity (S : Scheme.{u}) : (identity S).zeroSection = 𝟙 S :=
  (rfl)

/-! ### Homomorphisms -/

noncomputable section

/-- Abelian schemes over `S` form a category whose morphisms are the morphisms of the underlying
group schemes over `S`, that is, morphisms of `Over S` preserving the group law. -/
instance : Category (AbelianScheme S) :=
  inferInstanceAs (Category (InducedCategory _ (fun A : AbelianScheme S ↦ Grp.mk A.toOver)))

/-- Construct a homomorphism of abelian schemes from a morphism over `S` and proofs that it
preserves the unit and multiplication. -/
def homMk {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) : A ⟶ B :=
  InducedCategory.homMk (Grp.homMk'' f one_f mul_f)

/-- The forgetful functor from abelian schemes over `S` to schemes over `S`. -/
@[expose] def toOverFunctor : AbelianScheme S ⥤ Over S :=
  inducedFunctor (fun A : AbelianScheme S ↦ Grp.mk A.toOver) ⋙ Grp.forget (Over S)

@[simp]
lemma toOverFunctor_obj (A : AbelianScheme S) : toOverFunctor.obj A = A.toOver :=
  (rfl)

/-- The underlying morphism over `S` of a homomorphism of abelian schemes. -/
abbrev toOverHom {A B : AbelianScheme S} (f : A ⟶ B) : A.toOver ⟶ B.toOver :=
  toOverFunctor.map f

/-- `toOverHom` is definitionally the underlying-morphism projection through the induced category
and `Grp`. -/
private lemma toOverHom_def {A B : AbelianScheme S} (f : A ⟶ B) :
    toOverHom f = f.hom.hom.hom :=
  rfl

/-- `toOverHom` sends the identity homomorphism to the identity over `S`. Not a simp lemma:
`toOverHom` is reducible, so `Functor.map_id` and `toOverFunctor_obj` already prove it. -/
lemma toOverHom_id (A : AbelianScheme S) : toOverHom (𝟙 A) = 𝟙 A.toOver :=
  toOverFunctor.map_id A

/-- `toOverHom` sends composition to composition over `S`. Not a simp lemma: `toOverHom` is
reducible, so `Functor.map_comp` already proves it. -/
@[reassoc]
lemma toOverHom_comp {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    toOverHom (f ≫ g) = toOverHom f ≫ toOverHom g :=
  toOverFunctor.map_comp f g

/-- The underlying morphism of a homomorphism of abelian schemes preserves the group law. -/
instance {A B : AbelianScheme S} (f : A ⟶ B) : IsMonHom (toOverHom f) :=
  toOverHom_def f ▸ inferInstance

/-- A homomorphism of abelian schemes preserves the zero section. -/
@[reassoc]
lemma one_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    η[A.toOver] ≫ toOverHom f = η[B.toOver] :=
  IsMonHom.one_hom _

/-- A homomorphism of abelian schemes preserves multiplication. -/
@[reassoc]
lemma mul_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    μ[A.toOver] ≫ toOverHom f = (toOverHom f ⊗ₘ toOverHom f) ≫ μ[B.toOver] :=
  IsMonHom.mul_hom _

/-- A homomorphism of abelian schemes preserves inverses. -/
@[reassoc]
lemma inv_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    ι[A.toOver] ≫ toOverHom f = toOverHom f ≫ ι[B.toOver] :=
  GrpObj.inv_hom _

/-- A homomorphism of abelian schemes carries the zero section of its source to the zero section
of its target. -/
@[reassoc]
lemma zeroSection_comp {A B : AbelianScheme S} (f : A ⟶ B) :
    A.zeroSection ≫ (toOverHom f).left = B.zeroSection := by
  rw [← Over.comp_left, one_hom]

/-- The underlying morphism over `S` of a homomorphism built by `homMk` is the supplied
morphism. -/
@[simp]
lemma toOverHom_homMk {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) :
    toOverHom (homMk f one_f mul_f) = f :=
  (rfl)

/-- Two homomorphisms of abelian schemes are equal when their underlying scheme morphisms are
equal. -/
@[ext]
lemma hom_ext {A B : AbelianScheme S} {f g : A ⟶ B}
    (h : (toOverHom f).left = (toOverHom g).left) : f = g := by
  simp only [toOverHom_def] at h
  exact InducedCategory.hom_ext (Grp.hom_ext _ _ (Over.OverMorphism.ext h))

/-- Forgetting a homomorphism of abelian schemes to its underlying morphism over `S` is
faithful. -/
instance : (toOverFunctor (S := S)).Faithful where
  map_injective h := hom_ext (congrArg Over.Hom.left h)

/-- Two homomorphisms of abelian schemes with the same underlying morphism over `S` are equal. -/
lemma toOverHom_injective {A B : AbelianScheme S} {f g : A ⟶ B}
    (h : toOverHom f = toOverHom g) : f = g :=
  toOverFunctor.map_injective h

/-- A homomorphism of abelian schemes is a morphism over `S` that preserves the group law. -/
def homEquivIsMonHom (A B : AbelianScheme S) :
    (A ⟶ B) ≃ {f : A.toOver ⟶ B.toOver // IsMonHom f} where
  toFun f := ⟨toOverHom f, inferInstance⟩
  invFun f :=
    have := f.property
    homMk f.val (IsMonHom.one_hom f.val) (IsMonHom.mul_hom f.val)
  left_inv _ := hom_ext rfl
  right_inv _ := rfl

@[simp]
lemma homEquivIsMonHom_apply_coe {A B : AbelianScheme S} (f : A ⟶ B) :
    (homEquivIsMonHom A B f : A.toOver ⟶ B.toOver) = toOverHom f :=
  (rfl)

/-- The homomorphism attached to a morphism over `S` preserving the group law has that morphism
as its morphism over `S`. -/
@[simp]
lemma toOverHom_homEquivIsMonHom_symm_apply {A B : AbelianScheme S}
    (g : {f : A.toOver ⟶ B.toOver // IsMonHom f}) :
    toOverHom ((homEquivIsMonHom A B).symm g) = g.val :=
  (rfl)

/-- Construct an isomorphism of abelian schemes from an isomorphism of the underlying schemes over
`S` that preserves the group law. -/
def isoMk {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] : A ≅ B where
  hom := homMk e.hom (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
  inv := homMk e.inv (IsMonHom.one_hom _) (IsMonHom.mul_hom _)
  hom_inv_id := toOverHom_injective ((toOverHom_comp _ _).trans
    (e.hom_inv_id.trans (toOverHom_id A).symm))
  inv_hom_id := toOverHom_injective ((toOverHom_comp _ _).trans
    (e.inv_hom_id.trans (toOverHom_id B).symm))

@[simp]
lemma toOverHom_isoMk_hom {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] :
    toOverHom (isoMk e).hom = e.hom :=
  (rfl)

@[simp]
lemma toOverHom_isoMk_inv {A B : AbelianScheme S} (e : A.toOver ≅ B.toOver) [IsMonHom e.hom] :
    toOverHom (isoMk e).inv = e.inv :=
  (rfl)

/-- The base-change functor along `f : T ⟶ S`, sending an abelian scheme `A` to `A.baseChange f`
and a homomorphism to its pullback. -/
@[expose] def baseChangeFunctor (f : T ⟶ S) : AbelianScheme S ⥤ AbelianScheme T where
  obj A := A.baseChange f
  map g := InducedCategory.homMk ((Over.pullback f).mapGrp.map g.hom)
  map_id A := InducedCategory.hom_ext ((Over.pullback f).mapGrp.map_id (Grp.mk A.toOver))
  map_comp g h := InducedCategory.hom_ext ((Over.pullback f).mapGrp.map_comp g.hom h.hom)

@[simp]
lemma baseChangeFunctor_obj (f : T ⟶ S) (A : AbelianScheme S) :
    (baseChangeFunctor f).obj A = A.baseChange f :=
  (rfl)

/-- The base change of a homomorphism is its image under the pullback functor of `Over S`. -/
@[simp]
lemma toOverHom_baseChangeFunctor_map (f : T ⟶ S) {A B : AbelianScheme S} (g : A ⟶ B) :
    toOverHom ((baseChangeFunctor f).map g) = (Over.pullback f).map (toOverHom g) :=
  (rfl)

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
