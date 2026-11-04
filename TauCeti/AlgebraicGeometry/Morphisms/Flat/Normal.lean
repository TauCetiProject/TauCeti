/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite
public import TauCeti.RingTheory.RegularLocalRing.MiracleFlatness
import TauCeti.RingTheory.RegularLocalRing.DimensionTwo

/-!
# Flatness of quasi-finite morphisms from normal surfaces

A quasi-finite morphism is flat at a point if the target local ring is regular, the source
local ring is Cohen–Macaulay, and the two local rings have the same dimension. This is miracle
flatness with zero-dimensional closed fibre; it does not require the morphism to be finite.

In dimension at most two, a Noetherian normal local domain is Cohen–Macaulay. Thus a dominant,
locally quasi-finite morphism of integral schemes, locally of finite type, from a normal scheme
to a regular locally Noetherian scheme whose local rings have dimension at most two is flat.
The pointwise version assumes only normality at the chosen source point and equality of the
local dimensions. These results
supply flatness before applying ramification criteria for étaleness.

## References

* The Stacks Project, Lemma 10.128.1 (00R4), miracle flatness.
* The Stacks Project, Lemma 58.21.3 (0BMA), the flatness step in dimension two.

The closed-fibre identification follows the one in Mathlib's private
`Algebra.QuasiFinite.finite_of_isArtinianRing_of_isLocalRing`.
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A quasi-finite morphism is flat at a point with Cohen–Macaulay source local ring and regular
target local ring of the same dimension. No finiteness assumption on the morphism is needed. -/
theorem flat_stalkMap_of_isCohenMacaulay_of_quasiFiniteAt {x : X}
    [IsNoetherianRing (X.presheaf.stalk x)] [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hx : f.QuasiFiniteAt x) (hcm : Module.IsCohenMacaulay (X.presheaf.stalk x)
      (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x))) :
    (f.stalkMap x).hom.Flat := by
  algebraize [(f.stalkMap x).hom]
  -- `QuasiFiniteAt` is quasi-finiteness of this stalk map, with its induced algebra structure.
  have : Algebra.QuasiFinite (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hx
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  -- Over a local base the closed fibre is the tensor-product fibre. It is Artinian by
  -- quasi-finiteness and nonzero because the stalk map is local.
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
        (maximalIdeal R)).symm.restrictScalars _)
  have : IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    e.toRingEquiv.isArtinianRing
  have : Nontrivial (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top (algebraMap R S)).ne
  have hfibre : ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  exact TauCeti.Algebra.flat_of_isCohenMacaulay hcm (by rw [hfibre, add_zero]; exact hdim)

/-- A quasi-finite morphism is flat at a point with Noetherian normal source local ring and
regular target local ring of the same dimension, provided that dimension is at most two. -/
theorem flat_stalkMap_of_isIntegrallyClosed_of_quasiFiniteAt_of_ringKrullDim_le_two {x : X}
    [IsNoetherianRing (X.presheaf.stalk x)] [IsDomain (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)] [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hx : f.QuasiFiniteAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hle : ringKrullDim (Y.presheaf.stalk (f x)) ≤ 2) : (f.stalkMap x).hom.Flat := by
  have : Ring.KrullDimLE 2 (X.presheaf.stalk x) := Ring.krullDimLE_iff.mpr (hdim.trans_le hle)
  exact f.flat_stalkMap_of_isCohenMacaulay_of_quasiFiniteAt hx
    Module.isCohenMacaulay_self_of_isIntegrallyClosed_of_krullDimLE_two hdim

/-- At a quasi-finite point of a dominant morphism of integral schemes, locally of finite type,
a Noetherian normal source local ring is flat over a regular target local ring of dimension
at most two. -/
theorem flat_stalkMap_of_isDominant_of_quasiFiniteAt_of_ringKrullDim_le_two
    [IsIntegral X] [IsIntegral Y]
    [IsDominant f] [LocallyOfFiniteType f] {x : X} [IsNoetherianRing (X.presheaf.stalk x)]
    [IsIntegrallyClosed (X.presheaf.stalk x)] [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hx : f.QuasiFiniteAt x) (hle : ringKrullDim (Y.presheaf.stalk (f x)) ≤ 2) :
    (f.stalkMap x).hom.Flat := by
  have : UniqueFactorizationMonoid (Y.presheaf.stalk (f x)) :=
    TauCeti.IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two hle
  exact f.flat_stalkMap_of_isIntegrallyClosed_of_quasiFiniteAt_of_ringKrullDim_le_two hx
    (f.ringKrullDim_stalk_eq_of_quasiFiniteAt hx) hle

/-- A dominant locally quasi-finite morphism of integral schemes, locally of finite type, from
a normal scheme to a regular locally Noetherian scheme of local dimension at most two is flat. -/
theorem flat_of_isDominant_of_locallyQuasiFinite_of_ringKrullDim_le_two
    [IsIntegral X] [IsIntegral Y]
    [TauCeti.AlgebraicGeometry.IsNormalScheme X] [IsLocallyNoetherian Y]
    [IsDominant f] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)]
    (hdim : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) : Flat f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact .of_stalkMap f fun x ↦
    f.flat_stalkMap_of_isDominant_of_quasiFiniteAt_of_ringKrullDim_le_two
      (f.quasiFiniteAt x) (hdim (f x))

end AlgebraicGeometry.Scheme.Hom
