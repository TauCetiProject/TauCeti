/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Dual
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The hyperbolic form on a module and its dual

The polar form of `QuadraticForm.dualProd K M` pairs the two coordinate summands by evaluation.
It is nondegenerate whenever the linear functionals on `M` separate points, with no assumption
on the characteristic of `K` or the dimension of `M`.
-/

public section

namespace TauCeti

open QuadraticMap

variable {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]

/-! ## The polar form of the hyperbolic form -/

/-- **The polar form of the hyperbolic quadratic form** `Q (f, m) = f m` pairs each coordinate
summand with the other and neither with itself. -/
@[simp]
theorem polar_dualProd (p q : Module.Dual K M × M) :
    polar (QuadraticForm.dualProd K M) p q = p.1 q.2 + q.1 p.2 := by
  simp only [polar, QuadraticForm.dualProd_apply, Prod.fst_add, Prod.snd_add,
    LinearMap.add_apply, map_add]
  ring

/-- The hyperbolic form is nondegenerate whenever the functionals on `M` separate points. -/
theorem nondegenerate_dualProd (hM : Function.Injective (Module.Dual.eval K M)) :
    (QuadraticForm.dualProd K M).Nondegenerate := by
  have hpolar : (QuadraticForm.dualProd K M).polarBilin = LinearMap.dualProd K M := by
    apply LinearMap.ext₂
    intro p q
    simp only [polarBilin_apply_apply, polar_dualProd, LinearMap.dualProd_apply_apply, add_comm]
  apply QuadraticMap.nondegenerate_of_ker_polarBilin_eq_bot
  rw [hpolar]
  exact LinearMap.separatingLeft_iff_ker_eq_bot.mp
    ((LinearMap.separatingLeft_dualProd K M).mpr hM)

end TauCeti
