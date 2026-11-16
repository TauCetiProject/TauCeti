/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral

/-!
# Abelian schemes

This file defines an **abelian scheme** over an arbitrary base scheme `S`: a group object in
`Over S` whose structure morphism is proper and smooth with geometrically connected fibres. No
commutativity axiom, dimension, or ample line bundle is part of the bundled structure.

From smoothness and geometric connectedness we derive geometric integrality of the structure
morphism (`AbelianScheme.geometricallyIntegral`) and integrality of every scheme-theoretic fibre
(`AbelianScheme.isIntegral_fiber`). The file also supplies:

* `AbelianScheme.toScheme`, `AbelianScheme.zeroSection`, and
  `AbelianScheme.zeroSection_comp_toOver_hom`: the underlying scheme and unit section;
* `AbelianScheme.mulBy`: integer multiplication `[n] = 𝟙 ^ n` in the group of endomorphisms of the
  underlying group scheme over `S`;
* `AbelianScheme.ofGroupScheme`: a constructor from a group object in `Over S` satisfying the
  standing geometric hypotheses;
* `AbelianScheme.identity`: the identity group scheme `S ⟶ S` carried by `𝟙_ (Over S)`, the
  dimension-zero abelian scheme over `S`.

## References

* G. Faltings and C.-L. Chai, *Degeneration of Abelian Varieties*, Chapter I, §§1.1–1.2.
* J. L. Kass, *Notes on abelian schemes*, §1.
* M. Olsson, *Compactifications of moduli of abelian varieties: an introduction*, §2.1.4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj
open scoped CategoryTheory.MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- An **abelian scheme** over a scheme `S`: a group object in `Over S` whose structure morphism is
proper and smooth with geometrically connected fibres.

No commutativity, relative dimension, or ample line bundle is part of the data. -/
@[ext]
structure AbelianScheme (S : Scheme.{u}) where
  /-- The underlying group scheme over `S`. -/
  toOver : Over S
  /-- The group-object structure on `toOver`. -/
  grpObj : GrpObj toOver
  /-- The structure morphism to `S` is proper. -/
  isProper : IsProper toOver.hom
  /-- The structure morphism to `S` is smooth. -/
  smooth : Smooth toOver.hom
  /-- The structure morphism to `S` has geometrically connected fibres. -/
  geometricallyConnected : GeometricallyConnected toOver.hom

namespace AbelianScheme

variable {S : Scheme.{u}}

attribute [instance] AbelianScheme.grpObj AbelianScheme.isProper AbelianScheme.smooth
  AbelianScheme.geometricallyConnected

/-- An abelian scheme is geometrically integral over its base, being smooth with geometrically
connected fibres. -/
instance geometricallyIntegral (A : AbelianScheme S) : GeometricallyIntegral A.toOver.hom :=
  Smooth.geometricallyIntegral A.toOver.hom

/-- Every scheme-theoretic fibre of an abelian scheme is integral. -/
instance isIntegral_fiber (A : AbelianScheme S) (s : S) :
    IsIntegral (A.toOver.hom.fiber s) :=
  have : GeometricallyIntegral (A.toOver.hom.fiberToSpecResidueField s) :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd A.toOver.hom (S.fromSpecResidueField s)))
  GeometricallyIntegral.isIntegral_of_subsingleton (A.toOver.hom.fiberToSpecResidueField s)

/-- The underlying scheme of an abelian scheme. -/
noncomputable abbrev toScheme (A : AbelianScheme S) : Scheme.{u} :=
  A.toOver.left

/-- The zero section `S ⟶ A` of an abelian scheme, that is, the unit of its group law. -/
noncomputable abbrev zeroSection (A : AbelianScheme S) : S ⟶ A.toScheme :=
  η[A.toOver].left

/-- The zero section is a section of the structure morphism of `A`. -/
@[reassoc]
lemma zeroSection_comp_toOver_hom (A : AbelianScheme S) :
    A.zeroSection ≫ A.toOver.hom = 𝟙 S := by
  simpa only [Over.tensorUnit_hom] using η[A.toOver].w

/-- Multiplication by `n` on an abelian scheme, `[n] = 𝟙 ^ n` in the group of endomorphisms of the
underlying group object in `Over S`. -/
noncomputable def mulBy (A : AbelianScheme S) (n : ℤ) : A.toOver ⟶ A.toOver :=
  𝟙 A.toOver ^ n

/-- Multiplication by `0` is the constant morphism through the zero section. -/
@[simp]
lemma mulBy_zero (A : AbelianScheme S) : A.mulBy 0 = 1 :=
  zpow_zero (𝟙 A.toOver)

/-- Multiplication by `1` is the identity morphism. -/
@[simp]
lemma mulBy_one (A : AbelianScheme S) : A.mulBy 1 = 𝟙 A.toOver :=
  zpow_one (𝟙 A.toOver)

/-- Multiplication by `-1` is the inversion morphism of the group law. -/
@[simp]
lemma mulBy_neg_one (A : AbelianScheme S) : A.mulBy (-1) = ι[A.toOver] := by
  rw [mulBy, zpow_neg_one, Hom.inv_def, Category.id_comp]

/-- Multiplication by a sum is the pointwise product of the multiplication maps. -/
lemma mulBy_add (A : AbelianScheme S) (m n : ℤ) :
    A.mulBy (m + n) = A.mulBy m * A.mulBy n :=
  zpow_add (𝟙 A.toOver) m n

/-- Multiplication by `-n` is the pointwise inverse of multiplication by `n`. -/
lemma mulBy_neg (A : AbelianScheme S) (n : ℤ) :
    A.mulBy (-n) = (A.mulBy n)⁻¹ :=
  zpow_neg (𝟙 A.toOver) n

/-- Postcomposing a `T`-point with `[n]` raises that point to the `n`-th power. -/
@[simp]
lemma comp_mulBy (A : AbelianScheme S) {T : Over S} (x : T ⟶ A.toOver) (n : ℤ) :
    x ≫ A.mulBy n = x ^ n := by
  rw [mulBy, GrpObj.comp_zpow, Category.comp_id]

/-- Construct an abelian scheme from a group object in `Over S` whose structure morphism is proper
and smooth with geometrically connected fibres. -/
noncomputable def ofGroupScheme (G : Over S) [GrpObj G] [IsProper G.hom] [Smooth G.hom]
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

section Identity

variable (S)

/-- The **identity abelian scheme** over `S`: the base scheme `S ⟶ S` regarded as a group scheme
over itself, carried by the monoidal unit `𝟙_ (Over S)`. -/
noncomputable def identity : AbelianScheme S where
  toOver := 𝟙_ (Over S)
  grpObj := inferInstance
  isProper := by rw [Over.tensorUnit_hom]; exact inferInstanceAs (IsProper (𝟙 S))
  smooth := by rw [Over.tensorUnit_hom]; exact inferInstanceAs (Smooth (𝟙 S))
  geometricallyConnected := by
    rw [Over.tensorUnit_hom]; exact geometricallyConnected_of_isIso (𝟙 S)

/-- The group scheme underlying the identity abelian scheme is the monoidal unit of `Over S`. -/
@[simp]
lemma identity_toOver : (identity S).toOver = 𝟙_ (Over S) :=
  (rfl)

/-- The scheme underlying the identity abelian scheme is the base `S`. -/
@[simp]
lemma identity_toScheme : (identity S).toScheme = S := by
  simp only [toScheme, identity_toOver, Over.tensorUnit_left]

/-- The scheme over `S` underlying the identity abelian scheme is terminal. -/
noncomputable def isTerminalIdentityToOver : IsTerminal (identity S).toOver :=
  IsTerminal.ofIso isTerminalTensorUnit (eqToIso (identity_toOver S).symm)

/-- The unit section of the identity abelian scheme is the identity of `𝟙_ (Over S)`. -/
@[simp]
lemma identity_one :
    η[(identity S).toOver] ≫ eqToHom (identity_toOver S) = η[𝟙_ (Over S)] :=
  Category.comp_id η[𝟙_ (Over S)]

/-- The multiplication of the identity abelian scheme is that of `𝟙_ (Over S)`. -/
@[simp]
lemma identity_mul :
    μ[(identity S).toOver] ≫ eqToHom (identity_toOver S) =
      (eqToHom (identity_toOver S) ⊗ₘ eqToHom (identity_toOver S)) ≫ μ[𝟙_ (Over S)] :=
  (Category.comp_id μ[𝟙_ (Over S)]).trans (by simp : μ[𝟙_ (Over S)] = (𝟙 _ ⊗ₘ 𝟙 _) ≫ _)

/-- The inversion of the identity abelian scheme is that of `𝟙_ (Over S)`. -/
@[simp]
lemma identity_inv :
    ι[(identity S).toOver] ≫ eqToHom (identity_toOver S) =
      eqToHom (identity_toOver S) ≫ ι[𝟙_ (Over S)] :=
  (Category.comp_id ι[𝟙_ (Over S)]).trans (Category.id_comp _).symm

/-- Every integer multiplication map on the identity abelian scheme is the identity. -/
@[simp]
lemma identity_mulBy (n : ℤ) : (identity S).mulBy n = 𝟙 (identity S).toOver :=
  (isTerminalIdentityToOver S).hom_ext _ _

end Identity

end AbelianScheme

end AlgebraicGeometry

end TauCeti
