/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ConnectedComponents.Basic
public import TauCeti.AlgebraicGeometry.Curves.Cohomology.Basic
import TauCeti.AlgebraicGeometry.Modules.Restriction.FiniteType
import TauCeti.AlgebraicGeometry.Morphisms.Proper
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Restrict
import TauCeti.AlgebraicGeometry.Noetherian

/-!
# Cohomology of disconnected smooth proper curves

A smooth proper curve has finitely many clopen connected components. Each component is a smooth
proper connected curve, so native curve finiteness and vanishing apply there. The base-linear
cohomology comparison with the finite product of component cohomologies assembles these results
for the whole curve. No connectedness, nonemptiness, rational point or perfect-field hypothesis
is imposed. The empty curve is covered by the empty component product.

## Main results

* `AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_of_smooth`: finite-dimensional
  cohomology of finite-type quasi-coherent modules in every degree;
* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_smooth`: vanishing of
  quasi-coherent cohomology in degrees at least two.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]

/-- Every finite-type quasi-coherent module on a smooth proper curve has finite-dimensional
cohomology in every degree, including for disconnected or empty curves. -/
theorem AlgebraicGeometry.Scheme.Modules.finiteDimensional_cohomology_of_smooth
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] (n : ℕ) :
    FiniteDimensional k (Cohomology M n) := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have (C : ConnectedComponents X) :
      FiniteDimensional k (Cohomology ((restrictFunctor (Scheme.Opens.ι C.opens)).obj M) n) := by
    have := isQuasicoherent_restrictFunctor (Scheme.Opens.ι C.opens) M
    have := isFiniteType_restrict (Scheme.Opens.ι C.opens) M
    exact finiteDimensional_cohomology_of_smooth_of_connected k _ n
  exact Module.Finite.equiv (cohomologyConnectedComponentsLinearEquiv k M n).symm

variable (k) in
include k in
/-- A quasi-coherent module on a smooth proper curve has zero cohomology in degrees at least
two, including for disconnected or empty curves. -/
theorem AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_of_two_le_of_smooth
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (Cohomology M n) := by
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have (C : ConnectedComponents X) :
      Subsingleton (Cohomology ((restrictFunctor (Scheme.Opens.ι C.opens)).obj M) n) := by
    have := isQuasicoherent_restrictFunctor (Scheme.Opens.ι C.opens) M
    exact subsingleton_cohomology_of_two_le_of_smooth_of_connected k _ n hn
  exact (cohomologyConnectedComponentsLinearEquiv k M n).toEquiv.subsingleton_congr.mpr
    inferInstance
