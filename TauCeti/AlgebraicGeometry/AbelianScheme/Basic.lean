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
(`TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`), so the structure morphism of an
abelian scheme is geometrically integral by instance search; together with properness this is
what identifies abelian schemes over a field with Tau Ceti's `AbelianVariety`, in
`TauCeti.AlgebraicGeometry.AbelianScheme.AbelianVariety`.

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

/-! ### The identity abelian scheme -/

/-- The structure morphism of the monoidal unit of `Over S` is proper: it is the identity. -/
private lemma isProper_tensorUnit_hom (S : Scheme.{u}) : IsProper (𝟙_ (Over S)).hom := by
  rw [Over.tensorUnit_hom]
  exact inferInstanceAs (IsProper (𝟙 S))

/-- The structure morphism of the monoidal unit of `Over S` is smooth: it is the identity. -/
private lemma smooth_tensorUnit_hom (S : Scheme.{u}) : Smooth (𝟙_ (Over S)).hom := by
  rw [Over.tensorUnit_hom]
  exact inferInstanceAs (Smooth (𝟙 S))

/-- The structure morphism of the monoidal unit of `Over S` is geometrically connected: it is
the identity, an isomorphism, hence geometrically integral. -/
private lemma geometricallyConnected_tensorUnit_hom (S : Scheme.{u}) :
    GeometricallyConnected (𝟙_ (Over S)).hom := by
  have : GeometricallyIntegral (𝟙 S) := geometricallyIntegral_of_isIso _
  rw [Over.tensorUnit_hom]
  infer_instance

/-- The **identity abelian scheme** over `S`: the base `S ⟶ S` with its trivial group law. It is
the abelian scheme of relative dimension zero. -/
noncomputable def identity (S : Scheme.{u}) : AbelianScheme S where
  toOver := 𝟙_ (Over S)
  grpObj := inferInstance
  isProper := isProper_tensorUnit_hom S
  smooth := smooth_tensorUnit_hom S
  geometricallyConnected := geometricallyConnected_tensorUnit_hom S

@[simp]
lemma identity_toOver (S : Scheme.{u}) : (identity S).toOver = 𝟙_ (Over S) :=
  (rfl)

/-- The group object underlying the identity abelian scheme is the trivial group object. -/
lemma grpMk_identity_toOver (S : Scheme.{u}) :
    Grp.mk (identity S).toOver = Grp.trivial (Over S) :=
  (rfl)

/-! ### Homomorphisms -/

noncomputable section

/-- Abelian schemes over `S` form a category whose morphisms are the morphisms of the underlying
group schemes over `S`, that is, morphisms of `Over S` preserving the group law. -/
instance : Category (AbelianScheme S) :=
  inferInstanceAs (Category (InducedCategory _ (fun A : AbelianScheme S ↦ Grp.mk A.toOver)))

/-- Construct a homomorphism of abelian schemes from a morphism over `S` and proofs that it
preserves the unit and multiplication. -/
def Hom.mk' {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) : A ⟶ B :=
  InducedCategory.homMk (Grp.homMk'' f one_f mul_f)

/-- The forgetful functor from abelian schemes over `S` to schemes over `S`. -/
@[expose] def Hom.toOverFunctor : AbelianScheme S ⥤ Over S :=
  inducedFunctor (fun A : AbelianScheme S ↦ Grp.mk A.toOver) ⋙ Grp.forget (Over S)

/-- The underlying morphism over `S` of a homomorphism of abelian schemes. -/
abbrev Hom.toOverHom {A B : AbelianScheme S} (f : A ⟶ B) : A.toOver ⟶ B.toOver :=
  Hom.toOverFunctor.map f

/-- `toOverHom` is definitionally the underlying-morphism projection through the induced category
and `Grp`. -/
private lemma Hom.toOverHom_def {A B : AbelianScheme S} (f : A ⟶ B) :
    Hom.toOverHom f = f.hom.hom.hom :=
  rfl

/-- `toOverHom` sends the identity homomorphism to the identity over `S`. -/
lemma Hom.toOverHom_id (A : AbelianScheme S) : Hom.toOverHom (𝟙 A) = 𝟙 A.toOver :=
  Hom.toOverFunctor.map_id A

/-- `toOverHom` sends composition to composition over `S`. -/
@[reassoc]
lemma Hom.toOverHom_comp {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    Hom.toOverHom (f ≫ g) = Hom.toOverHom f ≫ Hom.toOverHom g :=
  Hom.toOverFunctor.map_comp f g

/-- The underlying morphism of a homomorphism of abelian schemes preserves the group law. -/
instance {A B : AbelianScheme S} (f : A ⟶ B) : IsMonHom (Hom.toOverHom f) :=
  Hom.toOverHom_def f ▸ inferInstance

/-- A homomorphism of abelian schemes preserves the zero section. -/
@[reassoc]
lemma Hom.one_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    η[A.toOver] ≫ Hom.toOverHom f = η[B.toOver] :=
  IsMonHom.one_hom _

/-- A homomorphism of abelian schemes preserves multiplication. -/
@[reassoc]
lemma Hom.mul_hom {A B : AbelianScheme S} (f : A ⟶ B) :
    μ[A.toOver] ≫ Hom.toOverHom f = (Hom.toOverHom f ⊗ₘ Hom.toOverHom f) ≫ μ[B.toOver] :=
  IsMonHom.mul_hom _

/-- The underlying morphism over `S` of a homomorphism built by `Hom.mk'` is the supplied
morphism. -/
@[simp]
lemma Hom.toOverHom_mk' {A B : AbelianScheme S} (f : A.toOver ⟶ B.toOver)
    (one_f : η[A.toOver] ≫ f = η[B.toOver] := by cat_disch)
    (mul_f : μ[A.toOver] ≫ f = (f ⊗ₘ f) ≫ μ[B.toOver] := by cat_disch) :
    Hom.toOverHom (Hom.mk' f one_f mul_f) = f :=
  (rfl)

/-- Two homomorphisms of abelian schemes are equal when their underlying scheme morphisms are
equal. -/
@[ext]
lemma Hom.ext {A B : AbelianScheme S} {f g : A ⟶ B}
    (h : (Hom.toOverHom f).left = (Hom.toOverHom g).left) : f = g := by
  simp only [Hom.toOverHom_def] at h
  exact InducedCategory.hom_ext (Grp.hom_ext _ _ (Over.OverMorphism.ext h))

/-- Forgetting a homomorphism of abelian schemes to its underlying morphism over `S` is
faithful. -/
instance : (Hom.toOverFunctor (S := S)).Faithful where
  map_injective h := Hom.ext (congrArg Over.Hom.left h)

/-- Two homomorphisms of abelian schemes with the same underlying morphism over `S` are equal. -/
lemma Hom.toOverHom_injective {A B : AbelianScheme S} {f g : A ⟶ B}
    (h : Hom.toOverHom f = Hom.toOverHom g) : f = g :=
  Hom.toOverFunctor.map_injective h

/-- A homomorphism of abelian schemes is a morphism over `S` that preserves the group law. -/
def Hom.equivIsMonHom (A B : AbelianScheme S) :
    (A ⟶ B) ≃ {f : A.toOver ⟶ B.toOver // IsMonHom f} where
  toFun f := ⟨Hom.toOverHom f, inferInstance⟩
  invFun f :=
    have := f.2
    Hom.mk' f.1 (IsMonHom.one_hom f.1) (IsMonHom.mul_hom f.1)
  left_inv _ := Hom.ext rfl
  right_inv _ := rfl

@[simp]
lemma Hom.equivIsMonHom_apply_coe {A B : AbelianScheme S} (f : A ⟶ B) :
    (Hom.equivIsMonHom A B f : A.toOver ⟶ B.toOver) = Hom.toOverHom f :=
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
lemma Hom.toOverHom_baseChangeFunctor_map (f : T ⟶ S) {A B : AbelianScheme S} (g : A ⟶ B) :
    Hom.toOverHom ((baseChangeFunctor f).map g) = (Over.pullback f).map (Hom.toOverHom g) :=
  (rfl)

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
