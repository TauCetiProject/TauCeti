/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.Geometry.Toric.Algebraic.BaseChange.Fan
public import TauCeti.Geometry.Toric.Algebraic.Normal
import TauCeti.AlgebraicGeometry.Morphisms.Dominant

/-!
# Field fibres of toric schemes

The zero-cone chart is dense in the toric scheme over any coefficient ring. Over a domain it
is irreducible and all affine charts are reduced, so a nonempty fan gives an integral scheme.
Since coefficient change is cartesian, the structure morphism of a nonempty fan has
geometrically integral fibres over any base. Normality over integrally closed domains follows
from normality of the saturated dual-semigroup algebras.

Over fields, these results and Noetherianity give the properties needed for Weil divisors,
even for singular cones.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.1.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.Toric.Fan

universe u

variable (R : Type u) [CommRing R] {N : Type u} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (Φ : Fan i)

/-- A nonempty finite fan over a domain defines an integral scheme. -/
instance isIntegral_finiteFanScheme [IsDomain R] [hΦ : Nonempty Φ.cones] :
    IsIntegral (Φ.finiteFanScheme R) := by
  have h₀ := Φ.bot_mem hΦ.some.property
  have : IsDominant (Φ.affineChartι R ⟨⊥, h₀⟩) := ⟨Φ.denseRange_affineChartι_bot R h₀⟩
  refine (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr
    ⟨(Φ.affineChartι R ⟨⊥, h₀⟩).irreducibleSpace_of_isDominant, ?_⟩
  refine (IsReduced.iff_of_openCover _ (Φ.affineChartOpenCover R)).mpr fun (σ : Φ.cones) ↦ ?_
  rw [affineChartOpenCover_X]
  infer_instance

/-- The toric scheme of a finite fan over an integrally closed domain is normal. -/
instance isNormalScheme_finiteFanScheme [IsDomain R] [IsIntegrallyClosed R] :
    TauCeti.AlgebraicGeometry.IsNormalScheme (Φ.finiteFanScheme R) := by
  refine (TauCeti.AlgebraicGeometry.isNormalScheme_iff_openCover
    (Φ.affineChartOpenCover R)).mpr fun (σ : Φ.cones) ↦ ?_
  rw [affineChartOpenCover_X]
  exact TauCeti.AlgebraicGeometry.isNormalScheme_Spec (.of (affineChartRing R Φ.lattice σ.val))

/-- The structure morphism of a nonempty finite fan has geometrically integral fibres. -/
instance geometricallyIntegral_finiteFanSchemeToSpec [Nonempty Φ.cones] :
    GeometricallyIntegral (Φ.finiteFanSchemeToSpec R) where
  geometrically_isIntegral := by
    rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
    intro K _ _
    exact IsIntegral.of_isIso (Φ.isPullback_finiteFanSchemeMap R K).isoPullback.hom

end TauCeti.Toric.Fan
