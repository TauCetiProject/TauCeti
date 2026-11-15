/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.LineBundle.Ample
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality

/-!
# Relatively ample line bundles

Let `f : X ⟶ S` be a morphism of schemes. A line-bundle class `a` on `X` is *relatively ample*
for `f`, or `f`-ample, if for every affine open `V` of `S` its restriction to the open subscheme
`f⁻¹ V` of `X` is ample. This is the positivity notion for families: a family of curves is stable
when its (log-)dualizing sheaf is relatively ample, and schemes over a base are recovered from a
relatively ample line bundle as the relative `Proj` of its section algebra.

Ampleness of the restrictions forces the preimages of affine opens to be quasi-compact and
quasi-separated, so a morphism with a relatively ample line bundle is quasi-compact
(`LineBundleClass.IsRelativelyAmple.quasiCompact`) and quasi-separated
(`LineBundleClass.IsRelativelyAmple.quasiSeparated`). For this reason the quasi-compactness of
`f`, which is part of the usual statement of the definition, is not imposed separately.

The preimage of an affine open under an affine morphism is affine, and every line bundle on an
affine scheme is ample, so every line-bundle class is relatively ample for an affine morphism
(`LineBundleClass.isRelativelyAmple_of_isAffineHom`). The trivial class is relatively ample
exactly when the preimages of affine opens are quasi-affine, that is, when `f` is quasi-affine
(`LineBundleClass.isRelativelyAmple_one_iff`).

## Main definitions

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple f a`: the line-bundle class `a` on
  `X` is relatively ample for `f : X ⟶ S`.

## Main results

* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.quasiCompact` and
  `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.quasiSeparated`: a morphism with a
  relatively ample line bundle is quasi-compact and quasi-separated.
* `TauCeti.AlgebraicGeometry.LineBundleClass.IsRelativelyAmple.of_pow`: if a positive power `aⁿ`
  is relatively ample, then so is `a`.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_of_isAffineHom`: every line-bundle
  class is relatively ample for an affine morphism.
* `TauCeti.AlgebraicGeometry.LineBundleClass.isRelativelyAmple_one_iff`: the trivial class is
  relatively ample exactly when the preimage of every affine open is quasi-affine.

## References

* The Stacks Project, *Morphisms of Schemes*, Section *Relatively ample sheaves*: the definition
  of a relatively ample invertible sheaf and its first properties.
* A. Grothendieck, *EGA II*, Section 4.6.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {X S : Scheme.{u}}

/-- A line-bundle class `a` on `X` is **relatively ample** for a morphism `f : X ⟶ S`, or
`f`-ample, if for every affine open `V` of `S` the restriction of `a` to the open subscheme `f⁻¹ V`
of `X` is ample. Such an `f` is automatically quasi-compact
(`LineBundleClass.IsRelativelyAmple.quasiCompact`). -/
structure IsRelativelyAmple (f : X ⟶ S) (a : LineBundleClass X) : Prop where
  /-- The restriction of `a` to the preimage of every affine open of the base is ample. -/
  isAmple_pullback (V : S.Opens) (hV : IsAffineOpen V) : (pullback (f ⁻¹ᵁ V).ι a).IsAmple

/-- Relative ampleness is ampleness over every affine open of the base. -/
theorem isRelativelyAmple_iff {f : X ⟶ S} {a : LineBundleClass X} :
    a.IsRelativelyAmple f ↔
      ∀ V : S.Opens, IsAffineOpen V → (pullback (f ⁻¹ᵁ V).ι a).IsAmple :=
  ⟨fun h ↦ h.isAmple_pullback, fun h ↦ ⟨h⟩⟩

/-- A morphism with a relatively ample line-bundle class is quasi-compact: the preimage of every
affine open carries an ample line bundle, so it is quasi-compact. -/
theorem IsRelativelyAmple.quasiCompact {f : X ⟶ S} {a : LineBundleClass X}
    (h : a.IsRelativelyAmple f) : QuasiCompact f :=
  quasiCompact_iff_forall_isAffineOpen.mpr fun V hV ↦
    isCompact_iff_compactSpace.mpr (h.isAmple_pullback V hV).compactSpace

/-- A morphism with a relatively ample line-bundle class is quasi-separated: the preimage of every
affine open carries an ample line bundle, so it is quasi-separated. -/
theorem IsRelativelyAmple.quasiSeparated {f : X ⟶ S} {a : LineBundleClass X}
    (h : a.IsRelativelyAmple f) : QuasiSeparated f :=
  -- Instance search cannot use Mathlib's instance `HasAffineProperty @QuasiSeparated _`: its affine
  -- property is stored at a dependent function type, not at `AffineTargetMorphismProperty`, so it
  -- cannot be assigned to that out-parameter. The instance is therefore supplied explicitly.
  @HasAffineProperty.of_iSup_eq_top _ _
    instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat _ _ f _
    (fun V : S.affineOpens ↦ V) (iSup_affineOpens_eq_top S)
    fun V ↦ (h.isAmple_pullback V V.2).quasiSeparatedSpace

/-- If a positive power `aⁿ` of a line-bundle class is relatively ample, then so is `a`. -/
theorem IsRelativelyAmple.of_pow {f : X ⟶ S} {a : LineBundleClass X} {n : ℕ} (hn : 0 < n)
    (h : (a ^ n).IsRelativelyAmple f) : a.IsRelativelyAmple f where
  isAmple_pullback V hV := IsAmple.of_pow hn (pullback_pow _ a n ▸ h.isAmple_pullback V hV)

/-- **Every line bundle is relatively ample for an affine morphism.** The preimage of an affine
open under an affine morphism is affine, and every line bundle on an affine scheme is ample. -/
theorem isRelativelyAmple_of_isAffineHom (f : X ⟶ S) [IsAffineHom f] (a : LineBundleClass X) :
    a.IsRelativelyAmple f where
  isAmple_pullback V hV :=
    have : IsAffine (f ⁻¹ᵁ V) := hV.preimage f
    isAmple_of_isAffine _

/-- **The structure sheaf is relatively ample exactly for quasi-affine morphisms**: the trivial
class is relatively ample for `f` if and only if the preimage of every affine open of the base is
quasi-affine. -/
@[simp]
theorem isRelativelyAmple_one_iff {f : X ⟶ S} :
    (1 : LineBundleClass X).IsRelativelyAmple f ↔
      ∀ V : S.Opens, IsAffineOpen V → (f ⁻¹ᵁ V).toScheme.IsQuasiAffine := by
  simp only [isRelativelyAmple_iff, pullback_one, isAmple_one_iff]

end TauCeti.AlgebraicGeometry.LineBundleClass
