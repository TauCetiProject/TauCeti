/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity

/-!
# Effective Cartier divisors on models over a discrete valuation ring

Along any morphism of models `f : N ⟶ M` of a scheme `C` over the fraction field of a discrete
valuation ring `R`, every effective Cartier divisor on `M.total` pulls back to an effective Cartier
divisor on `N.total` (`TauCeti.Model.isEffectiveCartier_comap_hom`). No flatness of `f.hom`,
integrality of `N.total`, or support condition is needed: `N.genericι` is quasi-compact and
scheme-theoretically dominant, while `N.genericι ≫ f.hom = M.genericι` is an open immersion and
hence flat.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Model

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- Along any morphism of models `f : N ⟶ M`, every effective Cartier divisor `E` on `M.total`
pulls back to an effective Cartier divisor on `N.total`. Neither flatness of `f.hom`, integrality
of `N.total`, nor a support restriction is required: local equations remain regular on the common
generic fibre by flatness of `M.genericι`, and the generic fibre is scheme-theoretically dense in
`N.total`. -/
theorem isEffectiveCartier_comap_hom {M N : Model R K C toK} (f : N ⟶ M)
    {E : M.total.IdealSheafData} (hE : E.IsEffectiveCartier) :
    (E.comap f.hom).IsEffectiveCartier := by
  have : Flat (N.genericι ≫ f.hom) := by
    rw [genericι_hom]
    have := M.isOpenImmersion_genericι
    infer_instance
  exact hE.comap_of_isSchemeTheoreticallyDominant_of_flat_comp f.hom N.genericι

end TauCeti.Model
