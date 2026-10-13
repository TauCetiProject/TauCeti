/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Meromorphic
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Order

/-!
# Laurent coefficients compute orders at compactifying cusps

If a function on the compactified Fuchsian quotient pulls back to `f` on the upper half-plane,
its order at a cusp is the least exponent with a nonzero coefficient in the Laurent q-expansion
of `f`. This applies to functions holomorphic sufficiently high with controlled exponential
growth. All normalized cusp data representing the given cusp orbit compute the same order.

The comparison combines the existing q-chart order formula
`Subgroup.CompactifiedQuotient.meromorphicOrderAt_ofCusp` with the order of the convergent Laurent
expansion. It allows local orders of descended functions to be read directly from coefficients,
including poles, zeros, and the zero germ.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.4–2.5.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Asymptotics Filter IsManifold MulAction TauCeti TauCeti.Subgroup.CuspDatum Topology
  UpperHalfPlane
open scoped Manifold MatrixGroups

namespace Subgroup.CompactifiedQuotient

variable {Γ : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ]
  {F : Γ.CompactifiedQuotient → ℂ} {f : ℍ → ℂ}

/-- The order of a descended function at a compactifying cusp is the order of the Laurent
q-expansion of its pullback, for any normalized cusp datum representing the cusp. -/
theorem meromorphicOrderAt_ofCusp_eq_orderTop_laurentQExpansion (D : Γ.CuspDatum) (k : ℤ)
    (hF : ∀ z, F (ofQuotient (Quotient.mk _ z)) = f z)
    (hhol : ∀ᶠ z in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (D.scaling⁻¹ • z))
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    RiemannSurface.meromorphicOrderAt F (ofCusp D.cuspOrbit) =
      (laurentQExpansion D k f).orderTop := by
  have hf (g : stabilizer Γ D.cusp) (z : ℍ) : f (g • z) = f z := by
    rw [← hF, ← hF]
    exact congrArg (fun p ↦ F (ofQuotient p))
      (Quotient.sound (orbitRel_apply.mpr (mem_orbit z (g : Γ))))
  rw [meromorphicOrderAt_ofCusp D hF]
  exact meromorphicOrderAt_cuspExtension_eq_orderTop_laurentQExpansion D k f hf
    (analyticAt_twistedExtension_zero D k f hf hhol hbound)

end Subgroup.CompactifiedQuotient
