/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.AlgebraicGeometry.Geometrically.Irreducible
public import TauCeti.AlgebraicGeometry.Morphisms.OverTensorUnit
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Grp

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

* `AbelianScheme.mulBy`: the multiplication-by-`n` endomorphism `[n]` of the underlying group
  scheme over `S`, defined via `CategoryTheory.GrpObj.zpowMap`.
* `AbelianScheme.ofGroupScheme`: constructor packaging a proper, smooth, geometrically connected
  group scheme over `S` as an abelian scheme.
* `AbelianScheme.identity`: the base `S ⟶ S` with its trivial group law, the abelian scheme of
  relative dimension zero.
* the category of abelian schemes over `S`, whose morphisms are morphisms of `Over S` preserving
  the group law (`IsMonHom`).

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
open scoped CategoryTheory.MonObj

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

variable {S : Scheme.{u}}

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

/-- Multiplication by `n` on an abelian scheme, `[n] = GrpObj.zpowMap A.toOver n` on the
underlying group object in `Over S`. -/
noncomputable def mulBy (A : AbelianScheme S) (n : ℤ) : A.toOver ⟶ A.toOver :=
  GrpObj.zpowMap A.toOver n

/-- `A.mulBy n` is `GrpObj.zpowMap A.toOver n`. -/
lemma mulBy_eq_zpowMap (A : AbelianScheme S) (n : ℤ) :
    A.mulBy n = GrpObj.zpowMap A.toOver n := by
  unfold mulBy
  rfl

/-- Multiplication by `n` is the `n`-th power of the identity morphism in `End A.toOver`. -/
lemma mulBy_eq_zpow (A : AbelianScheme S) (n : ℤ) :
    A.mulBy n = 𝟙 A.toOver ^ n :=
  GrpObj.zpowMap_eq_zpow A.toOver n

/-- Multiplication by `0` is the constant morphism through the zero section. -/
@[simp]
lemma mulBy_zero (A : AbelianScheme S) : A.mulBy 0 = 1 :=
  GrpObj.zpowMap_zero A.toOver

/-- Multiplication by `1` is the identity morphism. -/
@[simp]
lemma mulBy_one (A : AbelianScheme S) : A.mulBy 1 = 𝟙 A.toOver :=
  GrpObj.zpowMap_one A.toOver

/-- Multiplication by `-1` is the inversion morphism of the group law. -/
@[simp]
lemma mulBy_neg_one (A : AbelianScheme S) : A.mulBy (-1) = ι[A.toOver] :=
  GrpObj.zpowMap_neg_one A.toOver

/-- Multiplication by a sum is the pointwise product of the multiplication maps. -/
lemma mulBy_add (A : AbelianScheme S) (m n : ℤ) :
    A.mulBy (m + n) = A.mulBy m * A.mulBy n :=
  GrpObj.zpowMap_add A.toOver m n

/-- Multiplication by `-n` is the pointwise inverse of multiplication by `n`. -/
lemma mulBy_neg (A : AbelianScheme S) (n : ℤ) :
    A.mulBy (-n) = (A.mulBy n)⁻¹ :=
  GrpObj.zpowMap_neg A.toOver n

/-- Multiplication by a difference is the pointwise quotient of the multiplication maps. -/
lemma mulBy_sub (A : AbelianScheme S) (m n : ℤ) :
    A.mulBy (m - n) = A.mulBy m / A.mulBy n :=
  GrpObj.zpowMap_sub A.toOver m n

/-- Multiplication by a product of integers is the composition of the multiplication maps. -/
lemma mulBy_mul (A : AbelianScheme S) (m n : ℤ) :
    A.mulBy (m * n) = A.mulBy n ≫ A.mulBy m :=
  GrpObj.zpowMap_mul A.toOver m n

/-- Every homomorphism of group objects commutes with multiplication by `n`. -/
@[reassoc]
lemma mulBy_comp (A : AbelianScheme S) {H : Over S} [GrpObj H] (n : ℤ) (f : A.toOver ⟶ H)
    [IsMonHom f] : A.mulBy n ≫ f = f ≫ GrpObj.zpowMap H n :=
  GrpObj.zpowMap_comp n f

/-- Postcomposing a `T`-point with `[n]` raises that point to the `n`-th power. -/
@[simp]
lemma comp_mulBy (A : AbelianScheme S) {T : Over S} (x : T ⟶ A.toOver) (n : ℤ) :
    x ≫ A.mulBy n = x ^ n :=
  GrpObj.comp_zpowMap x n

/-- Construct an abelian scheme from a group object in `Over S` whose structure morphism is proper
and smooth with geometrically connected fibres. -/
@[expose] noncomputable def ofGroupScheme (G : Over S) [GrpObj G] [IsProper G.hom] [Smooth G.hom]
    [GeometricallyConnected G.hom] : AbelianScheme S where
  toOver := G
  grpObj := inferInstance
  isProper := inferInstance
  smooth := inferInstance
  geometricallyConnected := inferInstance

@[simp]
lemma ofGroupScheme_toOver (G : Over S) [GrpObj G] [IsProper G.hom] [Smooth G.hom]
    [GeometricallyConnected G.hom] : (ofGroupScheme G).toOver = G :=
  (rfl)

/-- The unit of `ofGroupScheme G` is the unit of `G`. -/
@[simp]
lemma ofGroupScheme_one (G : Over S) [GrpObj G] [IsProper G.hom] [Smooth G.hom]
    [GeometricallyConnected G.hom] :
    η[(ofGroupScheme G).toOver] ≫ eqToHom (ofGroupScheme_toOver G) = η[G] :=
  Category.comp_id η[G]

/-- The multiplication of `ofGroupScheme G` is the multiplication of `G`. -/
@[simp]
lemma ofGroupScheme_mul (G : Over S) [GrpObj G] [IsProper G.hom] [Smooth G.hom]
    [GeometricallyConnected G.hom] :
    μ[(ofGroupScheme G).toOver] ≫ eqToHom (ofGroupScheme_toOver G) =
      (eqToHom (ofGroupScheme_toOver G) ⊗ₘ eqToHom (ofGroupScheme_toOver G)) ≫ μ[G] :=
  (Category.comp_id μ[G]).trans (by simp : μ[G] = (𝟙 G ⊗ₘ 𝟙 G) ≫ μ[G])

/-- The inversion of `ofGroupScheme G` is the inversion of `G`. -/
@[simp]
lemma ofGroupScheme_inv (G : Over S) [GrpObj G] [IsProper G.hom] [Smooth G.hom]
    [GeometricallyConnected G.hom] :
    ι[(ofGroupScheme G).toOver] ≫ eqToHom (ofGroupScheme_toOver G) =
      eqToHom (ofGroupScheme_toOver G) ≫ ι[G] :=
  (Category.comp_id ι[G]).trans (Category.id_comp ι[G]).symm

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

/-- The scheme underlying the identity abelian scheme is the base `S`. -/
@[simp]
lemma identity_toScheme (S : Scheme.{u}) : (identity S).toScheme = S := by
  simp only [toScheme, identity_toOver, Over.tensorUnit_left]

/-- The scheme over `S` underlying the identity abelian scheme is terminal. -/
noncomputable def isTerminalIdentityToOver (S : Scheme.{u}) : IsTerminal (identity S).toOver :=
  IsTerminal.ofIso isTerminalTensorUnit (eqToIso (identity_toOver S).symm)

/-- The unit section of the identity abelian scheme is the identity of `𝟙_ (Over S)`. -/
@[simp]
lemma identity_one (S : Scheme.{u}) :
    η[(identity S).toOver] ≫ eqToHom (identity_toOver S) = η[𝟙_ (Over S)] :=
  Category.comp_id η[𝟙_ (Over S)]

/-- The multiplication of the identity abelian scheme is that of `𝟙_ (Over S)`. -/
@[simp]
lemma identity_mul (S : Scheme.{u}) :
    μ[(identity S).toOver] ≫ eqToHom (identity_toOver S) =
      (eqToHom (identity_toOver S) ⊗ₘ eqToHom (identity_toOver S)) ≫ μ[𝟙_ (Over S)] :=
  (Category.comp_id μ[𝟙_ (Over S)]).trans (by simp : μ[𝟙_ (Over S)] = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _)

/-- The inversion of the identity abelian scheme is that of `𝟙_ (Over S)`. -/
@[simp]
lemma identity_inv (S : Scheme.{u}) :
    ι[(identity S).toOver] ≫ eqToHom (identity_toOver S) =
      eqToHom (identity_toOver S) ≫ ι[𝟙_ (Over S)] :=
  (Category.comp_id ι[𝟙_ (Over S)]).trans (Category.id_comp _).symm

/-- Every integer multiplication map on the identity abelian scheme is the identity. -/
@[simp]
lemma identity_mulBy (S : Scheme.{u}) (n : ℤ) : (identity S).mulBy n = 𝟙 (identity S).toOver :=
  (isTerminalIdentityToOver S).hom_ext _ _

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

/-- A homomorphism of abelian schemes commutes with multiplication by `n`. -/
@[reassoc]
lemma mulBy_comp_toOverHom {A B : AbelianScheme S} (f : A ⟶ B) (n : ℤ) :
    A.mulBy n ≫ toOverHom f = toOverHom f ≫ B.mulBy n := by
  rw [mulBy_eq_zpowMap, mulBy_eq_zpowMap, GrpObj.zpowMap_comp]

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

end

end AbelianScheme

end AlgebraicGeometry

end TauCeti
