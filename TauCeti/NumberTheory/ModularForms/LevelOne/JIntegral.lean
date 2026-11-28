/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Pointwise specialization of functions integral over `ℤ[j]`

If a function `F : ℍ → ℂ` is integral over `ℤ[j] = Algebra.adjoin ℤ {j}` (for instance, a modular
function satisfying a monic polynomial over `ℤ[j]`), then its value `F τ` at any `τ ∈ ℍ` is
integral over any commutative ring `R` over which `j τ` is integral (`IsIntegral.eval_of_adjoin_j`).
In particular, when `j τ` is an algebraic integer (`R = ℤ`), so is `F τ`.

## Main results

* `TauCeti.ModularForm.isIntegral_adjoin_j`: `j` is integral over `ℤ[j]`.
* `IsIntegral.eval_of_adjoin_j`: function-level integrality over `ℤ[j]` specializes pointwise to
  integrality over any ring over which `j τ` is integral.
-/

public section

open UpperHalfPlane

namespace TauCeti.ModularForm

/-- The modular invariant `j` is integral over `ℤ[j]`. -/
theorem isIntegral_adjoin_j : IsIntegral (Algebra.adjoin ℤ ({j} : Set (ℍ → ℂ))) j :=
  isIntegral_algebraMap
    (x := (⟨j, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin ℤ ({j} : Set (ℍ → ℂ))))

/-- **Pointwise integrality from function-level integrality over `ℤ[j]`.** If `F : ℍ → ℂ` is
integral over `ℤ[j]` and `j(τ)` is integral over `R`, then `F(τ)` is integral over `R`. -/
theorem _root_.IsIntegral.eval_of_adjoin_j {R : Type*} [CommRing R] [Algebra R ℂ] {F : ℍ → ℂ}
    (hF : IsIntegral (Algebra.adjoin ℤ ({j} : Set (ℍ → ℂ))) F) (τ : ℍ)
    (hj : IsIntegral R (j τ)) : IsIntegral R (F τ) :=
  hF.map_of_adjoin_singleton (Pi.evalRingHom (fun _ : ℍ ↦ ℂ) τ) (RingHom.ext_int _ _) hj

end TauCeti.ModularForm
