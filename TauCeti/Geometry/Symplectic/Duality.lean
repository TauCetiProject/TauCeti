/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.AlmostComplex
public import TauCeti.Topology.Algebra.Module.BilinearForm
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Contraction with a symplectic form

On a finite-dimensional real normed space, contraction with a symplectic form is an
invertible continuous linear map to the continuous dual. This identifies covectors with
vectors and allows the contraction equation in Moser's deformation argument to be solved
using the continuous-linear-map inverse. The symplectic pairing of two continuous maps is
continuous.

See McDuff--Salamon, *Introduction to Symplectic Topology*, Section 3.2.
-/

public section

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Contraction with a finite-dimensional symplectic form is an isomorphism to the
continuous dual. -/
@[simp]
theorem isInvertible_toContinuousBilinearMap (ω : SymplecticForm V) :
    ω.toBilinForm.toContinuousBilinearMap.IsInvertible :=
  TauCeti.isInvertible_toContinuousBilinearMap_iff_separatingLeft.mpr
    ω.nondegenerate.1

section Continuity

variable {X : Type*} [TopologicalSpace X] {p q : X → V} {s : Set X}

/-- The symplectic pairing of two maps continuous on a set is continuous on that set. -/
theorem continuousOn_apply_comp (ω : SymplecticForm V) (hp : ContinuousOn p s)
    (hq : ContinuousOn q s) : ContinuousOn (fun z ↦ ω (p z) (q z)) s := by
  simpa only [Function.comp_apply, LinearMap.toContinuousBilinearMap_apply] using
    ContinuousOn.clm_apply (ω.toBilinForm.toContinuousBilinearMap.continuous.comp_continuousOn hp)
      hq

/-- The symplectic pairing of two continuous maps is continuous. -/
theorem continuous_apply_comp (ω : SymplecticForm V) (hp : Continuous p) (hq : Continuous q) :
    Continuous fun z ↦ ω (p z) (q z) :=
  continuousOn_univ.mp <| ω.continuousOn_apply_comp hp.continuousOn hq.continuousOn

end Continuity

end TauCeti.SymplecticForm
