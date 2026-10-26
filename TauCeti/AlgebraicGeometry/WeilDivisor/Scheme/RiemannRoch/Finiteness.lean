/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Scheme.DiscreteValuationStalk

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Scheme.FunctionField
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.RepartitionCohomology

/-!
# Finiteness of the first cohomology of a proper curve

Let `X` be an integral scheme of dimension one, proper over a field `k`, whose codimension-one
local rings are discrete valuation rings. Then `H¹(X, 𝒪_X)` is finite-dimensional over `k`.

This is the finiteness hypothesis under which the genus `g = dim_k H¹(X, 𝒪_X)`
(`AlgebraicGeometry.Scheme.genus`) and the Riemann–Roch theorem
(`SchemeWeilDivisor.eulerCharBelow_sheaf_eq_relativeDegree_add_one_sub_genus`) are stated, so
both apply to every such curve.

## Main declarations

* `TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_one_trivial_of_isProper`:
  `H¹(X, 𝒪_X)` is finite-dimensional for a proper integral curve over `k` whose codimension-one
  local rings are discrete valuation rings.
* `TauCeti.AlgebraicGeometry.finiteDimensional_cohomology_one_trivial_of_smooth`:
  the same finiteness holds for a smooth proper connected curve over `k`.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §5, Proposition 3.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 5.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [IsProper (X ↘ Spec (.of k))]

/-- **The first cohomology of the structure sheaf of a proper curve is finite-dimensional.** Let
`X` be an integral scheme of dimension one, proper over a field `k`, whose codimension-one local
rings are discrete valuation rings. Then `H¹(X, 𝒪_X)` is finite-dimensional over `k`. -/
theorem finiteDimensional_cohomology_one_trivial_of_isProper (hX : topologicalKrullDim X = 1) :
    FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) := by
  have hdim (x : X) : coheight x ≤ 1 := by
    exact_mod_cast (coheight_le_topologicalKrullDim x).trans hX.le
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := (quasiCompact_iff_compactSpace (X ↘ Spec (.of k))).mp inferInstance
  have : IsNoetherian X := {}
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from (X ↘ Spec (.of k))]; infer_instance⟩
  have hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)) := by
    have := UniversallyClosed.eq_valuativeCriterion ▸
      (inferInstance : UniversallyClosed (X ↘ Spec (.of k)))
    exact this.1
  exact (Scheme.Modules.finiteDimensional_cohomology_congr k
    (SchemeWeilDivisor.sheafZeroIsoTrivial hdim) 1).mp
      (SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField hex hdim
        ((isFunctionField_functionField_iff k).mpr hX) 0)

/-- The first structure-sheaf cohomology of a smooth proper connected curve is
finite-dimensional. -/
theorem finiteDimensional_cohomology_one_trivial_of_smooth
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [ConnectedSpace X] :
    FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1) := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have : ∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X)) :=
    fun _ ↦ inferInstance
  exact finiteDimensional_cohomology_one_trivial_of_isProper k
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)))

end AlgebraicGeometry

end TauCeti
