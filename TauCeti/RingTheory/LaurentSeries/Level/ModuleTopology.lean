/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.Topology
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# The base-field module topology on a ramified Laurent level

For the extension `L = K⸨u⸩` of `F = K⸨t⸩` given by `t = u ^ d`, the valuation topology
on `L` agrees with its `F`-module topology. The exponent-congruence coordinates in the basis
`1, u, ..., u ^ (d - 1)` give a continuous linear equivalence with `Fin d → F`: contraction
extracts each coordinate, while a finite sum reconstructs the series.

Consequently linear maps from a level to topological `F`-modules are continuous by
`IsModuleTopology.continuous_of_linearMap`. In particular, an algebraic level chart from an
extension carrying the `F`-module topology can be upgraded using
`LinearEquiv.toContinuousLinearEquivOfIsModuleTopology`. These comparisons require neither
algebraic closedness nor a restriction on the characteristic of `K`.

The valuation topology on the continuous one-forms of a level is also the `F`-module topology,
by restriction of scalars along this finite extension. Thus scalar-extended forms and their
level presentations can be compared in the category of topological modules, not just
algebraically.
-/

public section

open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Level

variable (K : Type*) [Field K] (d : ℕ+)

/-- The congruence-class coordinates of a ramified level are a continuous linear equivalence
for the valuation topology, with inverse the finite sum in the basis `1, u, ..., u^(d - 1)`. -/
noncomputable def basisContinuousLinearEquiv :
    Level K d ≃L[K⸨X⸩] (Fin d → K⸨X⸩) where
  toLinearEquiv := (basis K d).equivFun
  continuous_toFun := continuous_pi fun r ↦ by
    simpa [Function.comp_def, Module.Basis.equivFun_apply] using
      (_root_.LaurentSeries.continuous_contract (K := K) d r).comp
        (homeomorphLaurentSeries K d).continuous
  continuous_invFun :=
    IsModuleTopology.continuous_of_linearMap (basis K d).equivFun.symm.toLinearMap

/-- Each coordinate is the corresponding exponent-congruence component. -/
@[simp]
theorem basisContinuousLinearEquiv_apply (x : Level K d) (r : Fin d) :
    basisContinuousLinearEquiv K d x r =
      _root_.LaurentSeries.contract d (ringEquivLaurentSeries K d x) r := by
  exact basis_repr_apply K d x r

/-- Reconstruction multiplies the coordinates by the powers of the level parameter. -/
@[simp]
theorem basisContinuousLinearEquiv_symm_apply (f : Fin d → K⸨X⸩) :
    (basisContinuousLinearEquiv K d).symm f =
      ∑ r : Fin d, f r • parameter K d ^ (r : ℕ) := by
  exact (basis K d).equivFun_symm_apply f |>.trans (by simp)

/-- The underlying linear equivalence is the coordinate equivalence of the level basis. -/
@[simp]
theorem toLinearEquiv_basisContinuousLinearEquiv :
    (basisContinuousLinearEquiv K d).toLinearEquiv = (basis K d).equivFun := (rfl)

/-- The valuation topology on a ramified level is its module topology over the base Laurent
field. This includes inseparable ramification degrees. -/
instance : IsModuleTopology K⸨X⸩ (Level K d) :=
  IsModuleTopology.iso (basisContinuousLinearEquiv K d).symm

/-- The valuation topology on level one-forms is also their module topology over the base
Laurent field, by restriction of scalars along the finite level extension. -/
instance : IsModuleTopology K⸨X⸩ (Level.ContinuousKaehlerDifferential K d) :=
  IsModuleTopology.restrictScalars K⸨X⸩ (Level K d) _

end TauCeti.LaurentSeries.Level
