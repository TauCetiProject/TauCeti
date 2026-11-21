/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.CWApproximation.Sigma
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
import TauCeti.Topology.ContinuousMap.Sigma

/-!
# Singular homology of CW approximations

The CW approximation map `TauCeti.sigmaCWApproximationMap X : TauCeti.sigmaCWApproximation X ⟶ X`
is a weak homotopy equivalence (`TauCeti.isWeakHomotopyEquivalence_sigmaCWApproximationMap`), so it
induces isomorphisms on singular homology with coefficients in any module. Since the summand
`TauCeti.cwApproximation X x₀` corresponding to the path component of a point `y : X` is a retract
of `TauCeti.sigmaCWApproximation X`, vanishing of singular homology of `X` transfers to that
path-connected, Hausdorff CW approximation
(`TauCeti.isZero_singularHomology_cwApproximation_of_isZero`, and more generally for arbitrary
module coefficients `TauCeti.isZero_singularHomologyFunctor_cwApproximation_of_isZero`).

## Main results

* `TauCeti.isZero_singularHomologyFunctor_cwApproximation_of_isZero`: singular homology vanishing
  with arbitrary module coefficients transfers to the CW approximation of the path component of a
  point.
* `TauCeti.isZero_singularHomology_cwApproximation_of_isZero`: ring-coefficient specialization for
  `TauCeti.singularChains`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe u v

namespace TauCeti

/-- The CW approximation of the path component of `y` inherits singular homology vanishing from
`Y`, since it is a retract of `TauCeti.sigmaCWApproximation`. -/
theorem isZero_singularHomologyFunctor_cwApproximation_of_isZero {Y : Type v}
    [TopologicalSpace Y] (y : Y) {R : Type u} [Ring R] (M : ModuleCat.{v} R) (q : ℕ)
    (hY : IsZero (((singularHomologyFunctor (ModuleCat.{v} R) q).obj M).obj (TopCat.of Y))) :
    IsZero (((singularHomologyFunctor (ModuleCat.{v} R) q).obj M).obj
      (cwApproximation (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y)))) := by
  let c : ZerothHomotopy (TopCat.of Y) := ZerothHomotopy.mk y
  let x₀ : TopCat.of Y := Quotient.out c
  let Z := cwApproximation (TopCat.of Y) x₀
  let H := (singularHomologyFunctor (ModuleCat.{v} R) q).obj M
  have : IsIso (H.map (sigmaCWApproximationMap (TopCat.of Y))) :=
    (isWeakHomotopyEquivalence_sigmaCWApproximationMap (TopCat.of Y)).isIso_singularHomologyMap M q
  let e := asIso (H.map (sigmaCWApproximationMap (TopCat.of Y)))
  have hS : IsZero (H.obj (sigmaCWApproximation (TopCat.of Y))) := hY.of_iso e
  let ι : Z ⟶ sigmaCWApproximation (TopCat.of Y) :=
    TopCat.ofHom (ContinuousMap.sigmaMk
      (X := fun d : ZerothHomotopy (TopCat.of Y) ↦ cwApproximation (TopCat.of Y) (Quotient.out d))
      c)
  let r : sigmaCWApproximation (TopCat.of Y) ⟶ Z :=
    TopCat.ofHom (ContinuousMap.sigmaRetraction
      (Z := fun d : ZerothHomotopy (TopCat.of Y) ↦ cwApproximation (TopCat.of Y) (Quotient.out d))
      c (cwApproximationBasepoint (TopCat.of Y) x₀))
  have hcomp : ι ≫ r = 𝟙 Z := by
    ext p
    exact ContinuousMap.sigmaRetraction_sigmaMk
      (Z := fun d : ZerothHomotopy (TopCat.of Y) ↦ cwApproximation (TopCat.of Y) (Quotient.out d))
      c (cwApproximationBasepoint (TopCat.of Y) x₀) p
  refine (IsZero.iff_id_eq_zero (H.obj Z)).2 ?_
  rw [← H.map_id, ← hcomp, H.map_comp, hS.eq_of_tgt (H.map ι) 0, Limits.zero_comp]

/-- The CW approximation of the path component of `y` inherits singular homology vanishing from
`Y`, for `TauCeti.singularChains R`. -/
theorem isZero_singularHomology_cwApproximation_of_isZero {Y : Type u} [TopologicalSpace Y]
    (y : Y) (R : Type u) [Ring R] (q : ℕ)
    (hY : IsZero (((singularChains R).obj (TopCat.of Y)).homology q)) :
    IsZero (((singularChains R).obj
      (cwApproximation (TopCat.of Y) (Quotient.out (ZerothHomotopy.mk y)))).homology q) :=
  isZero_singularHomologyFunctor_cwApproximation_of_isZero y (ModuleCat.of R R) q hY

end TauCeti
