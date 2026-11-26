/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.Algebra.Bialgebra.Augmentation
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.AlgebraicGeometry.TangentSpace.Affine
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-!
# Tangent schemes and the Zariski cotangent space at the augmentation point

For a commutative bialgebra, specializing the generic augmented-algebra comparison from
`TauCeti.AlgebraicGeometry.TangentSpace.Affine` to the counit identifies the cotangent space at the
identity of the represented affine monoid with the corresponding Zariski cotangent space. With an
additional Hopf-algebra structure, its `k`-dual is the Hopf-algebra model of `Lie(G)` for the
represented affine group.

Over a commutative base ring, the symmetric algebra of the augmentation cotangent space defines
the affine scheme of tangent vectors. For a reflexive cotangent space, evaluation into the
double dual identifies it with the spectrum of polynomial functions on the dual.

## Main declarations

* `TauCeti.lieAlgebraScheme`: the affine scheme of tangent vectors at the identity.
* `TauCeti.lieAlgebraSchemeIso`: its reflexive comparison with the spectrum of polynomial
  functions on the dual cotangent space.
* `TauCeti.lieAlgebraOver` and `TauCeti.lieAlgebraOverIso`: the corresponding object and
  polynomial presentation in the category of schemes over the base ring.
* `Bialgebra.cotangentLinearEquivZariski`: the augmentation cotangent space is the Zariski
  cotangent space at the augmentation point.
* `Bialgebra.finrank_cotangentSpace_eq_finrank_zariskiCotangentSpace`: equality of their
  dimensions over the ground field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Opposite

namespace TauCeti

universe u

/-- The affine scheme of tangent vectors at the identity of the monoid represented by `H`. -/
abbrev lieAlgebraScheme (k : Type u) [CommRing k] (H : Type u) [CommRing H] [Bialgebra k H] :
    Scheme :=
  Spec (.of (SymmetricAlgebra k (Bialgebra.CotangentSpace k H)))

/-- For a reflexive cotangent space, evaluation into the double dual identifies the tangent
scheme with the spectrum of polynomial functions on its dual. In particular, this applies to
finite-dimensional cotangent spaces over a field. -/
abbrev lieAlgebraSchemeIso (k : Type u) [CommRing k] (H : Type u) [CommRing H]
    [Bialgebra k H] [Module.IsReflexive k (Bialgebra.CotangentSpace k H)] :
    lieAlgebraScheme k H ≅ Spec (.of (SymmetricAlgebra k
      (Module.Dual k (Module.Dual k (Bialgebra.CotangentSpace k H))))) :=
  Scheme.Spec.mapIso (SymmetricAlgebra.mapEquiv k
    (Module.evalEquiv k (Bialgebra.CotangentSpace k H))).symm.toRingEquiv.toCommRingCatIso.op

section Over

variable (k : Type u) [CommRing k] (H : Type u) [CommRing H] [Bialgebra k H]
  [Module.IsReflexive k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)
local notation "P" => SymmetricAlgebra k (Module.Dual k 𝔤)

/-- The tangent scheme over the base ring, using its polynomial presentation. -/
abbrev lieAlgebraOver : Over (Spec (.of k)) :=
  Over.mk ((lieAlgebraSchemeIso k H).hom ≫ Spec.algebraMap k P)

/-- The polynomial-coordinate presentation of the tangent scheme over the base ring. -/
def lieAlgebraOverIso : (algSpec (.of k)).obj (op (CommAlgCat.of k P)) ≅
    lieAlgebraOver k H :=
  TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk _ ≪≫
    Over.isoMk (lieAlgebraSchemeIso k H).symm (by
      -- Expose the over-category equation while retaining the named scheme isomorphism.
      change (lieAlgebraSchemeIso k H).inv ≫ ((lieAlgebraSchemeIso k H).hom ≫ _) = _
      simp only [Iso.inv_hom_id_assoc, Over.mk_hom])

/-- The polynomial presentation sends a point back through the existing tangent comparison. -/
@[simp]
theorem lieAlgebraOverIso_hom_left : (lieAlgebraOverIso k H).hom.left =
    (lieAlgebraSchemeIso k H).inv := by
  simp only [lieAlgebraOverIso, Iso.trans_hom, Over.comp_left,
    TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk_hom_left, Over.isoMk_hom_left,
    Iso.symm_hom]
  exact Category.id_comp _

/-- The inverse polynomial presentation is the existing tangent comparison. -/
@[simp]
theorem lieAlgebraOverIso_inv_left : (lieAlgebraOverIso k H).inv.left =
    (lieAlgebraSchemeIso k H).hom := by
  simp only [lieAlgebraOverIso, Iso.trans_inv, Over.comp_left,
    TauCeti.AlgebraicGeometry.algSpecObjIsoOverMk_inv_left, Over.isoMk_inv_left,
    Iso.symm_inv]
  exact Category.comp_id _

end Over

end TauCeti

namespace TauCeti.Bialgebra

universe u v

variable (k : Type u) [Field k]
variable (H : Type v) [CommRing H] [Bialgebra k H]

/-- The augmentation cotangent space of a commutative bialgebra is canonically the Zariski
cotangent space of its affine spectrum at the augmentation point. -/
noncomputable def cotangentLinearEquivZariski :
    CotangentSpace k H ≃ₗ[k]
      TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
        (Spec (CommRingCat.of H)) (augmentationPoint k H) :=
  _root_.AlgHom.kernelCotangentLinearEquivZariski (_root_.Bialgebra.counitAlgHom k H)

/-- On an element of the augmentation ideal, the cotangent comparison is induced by the map from
the coordinate ring to its stalk at the augmentation point. -/
@[simp]
theorem cotangentLinearEquivZariski_toCotangent (a : AugmentationIdeal k H) :
    cotangentLinearEquivZariski k H ((AugmentationIdeal k H).toCotangent a) =
      (maximalIdeal
          ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))).toCotangent
        ⟨algebraMap H
            ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H)) a,
          by
            let _ : (AugmentationIdeal k H).IsMaximal :=
              _root_.AlgHom.ker_isMaximal (_root_.Bialgebra.counitAlgHom k H)
            let _ : IsLocalization.AtPrime
                ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))
                (AugmentationIdeal k H) :=
              _root_.AlgHom.isLocalization_atPrime_kernelStalk (_root_.Bialgebra.counitAlgHom k H)
            rw [← Ideal.mem_under,
              IsLocalization.AtPrime.under_maximalIdeal
                ((Spec (CommRingCat.of H)).presheaf.stalk (augmentationPoint k H))
                (AugmentationIdeal k H)]
            exact a.property⟩ :=
  _root_.AlgHom.kernelCotangentLinearEquivZariski_toCotangent
    (_root_.Bialgebra.counitAlgHom k H) a

/-- The augmentation cotangent space and the Zariski cotangent space at the augmentation point
have the same dimension over the ground field. -/
theorem finrank_cotangentSpace_eq_finrank_zariskiCotangentSpace :
    Module.finrank k (CotangentSpace k H) =
      Module.finrank k
        (TauCeti.AlgebraicGeometry.ZariskiCotangentSpace
          (Spec (CommRingCat.of H)) (augmentationPoint k H)) :=
  _root_.AlgHom.finrank_kernelCotangent_eq_finrank_zariskiCotangentSpace
    (_root_.Bialgebra.counitAlgHom k H)

end TauCeti.Bialgebra
