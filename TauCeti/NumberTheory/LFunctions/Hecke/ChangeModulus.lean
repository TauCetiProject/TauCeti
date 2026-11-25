/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic

/-!
# Meromorphic orders under ray class induction

Inducing a ray class character deletes finitely many Euler factors. Their correction is entire
and nonvanishing off `Re s = 0`. Thus changing the presentation preserves the order, including
at a pole, at every point off that line. In particular, a zero-free right half-plane can be
checked at the primitive conductor. For a trivial character this reduces to Dedekind zeta.
-/

public section

open scoped NumberField Topology
open TauCeti TauCeti.GlobalNumberFields TauCeti.LFunctions

namespace TauCeti.LFunctions

/-- At the trivial modulus the trivial character's continued L-function is the Dedekind zeta
function in meromorphic normal form. -/
@[simp] theorem heckeLFunctionC_one_modulus_one (K : Type*) [Field K] [NumberField K] :
    heckeLFunctionC (1 : RayClassCharacter (Modulus.one K)) = dedekindZetaC K := by
  rw [heckeLFunctionC_def, RayClassCharacter.toUnitaryIdealWeight_one,
    UnitaryIdealWeight.toIdealArithmeticFunction_one, dedekindZetaC_def]
  exact congrArg (meromorphicContinuation 1)
    (funext fun s ↦ (dedekindZeta_eq_LSeries_normCoeff_one K s).symm)

end TauCeti.LFunctions

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-- Induction preserves the order of the continued Hecke L-function off the imaginary axis. -/
@[simp] theorem meromorphicOrderAt_heckeLFunctionC_induced (χ : RayClassCharacter 𝔪)
    (h : 𝔪 ∣ 𝔫) {s : ℂ} (hs : s.re ≠ 0) :
    meromorphicOrderAt (heckeLFunctionC (χ.induced h)) s =
      meromorphicOrderAt (heckeLFunctionC χ) s := by
  have he : heckeLFunctionC (χ.induced h) =ᶠ[𝓝[≠] s]
      χ.eulerCorrection 𝔫 * heckeLFunctionC χ := by
    filter_upwards [heckeLFunctionC_induced_eventuallyEq h χ s] with z hz
    simpa only [Pi.mul_apply, mul_comm] using hz
  rw [meromorphicOrderAt_congr he,
    meromorphicOrderAt_mul_of_ne_zero ((χ.differentiable_eulerCorrection 𝔫).analyticAt s)
      (χ.eulerCorrection_ne_zero 𝔫 hs)]

/-- Inducing a ray class character does not affect zero-freeness right of a nonnegative
threshold. -/
@[simp] theorem zeroFreeRightOf_heckeLFunctionC_induced (χ : RayClassCharacter 𝔪)
    (h : 𝔪 ∣ 𝔫) {σ : ℝ} (hσ : 0 ≤ σ) :
    ZeroFreeRightOf σ (heckeLFunctionC (χ.induced h)) ↔ ZeroFreeRightOf σ (heckeLFunctionC χ) := by
  simp only [zeroFreeRightOf_iff]
  exact forall₂_congr fun _ hs ↦ by
    rw [χ.meromorphicOrderAt_heckeLFunctionC_induced h (hσ.trans_lt hs).ne']

/-- Above a nonnegative threshold, a presented Hecke L-function and its primitive source have
the same zero-freeness property. -/
theorem zeroFreeRightOf_heckeLFunctionC_primitive (χ : RayClassCharacter 𝔪)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    ZeroFreeRightOf σ (heckeLFunctionC χ) ↔
      ZeroFreeRightOf σ (heckeLFunctionC (PrimitiveRayClassCharacter.of χ).character) := by
  conv_lhs => rw [← PrimitiveRayClassCharacter.induced_character_of χ]
  exact zeroFreeRightOf_heckeLFunctionC_induced _ _ hσ

/-- At an arbitrary presentation modulus the trivial character has the same zero-free right
half-planes with nonnegative threshold as the Dedekind zeta function. -/
@[simp] theorem zeroFreeRightOf_heckeLFunctionC_one {σ : ℝ} (hσ : 0 ≤ σ) :
    ZeroFreeRightOf σ (heckeLFunctionC (1 : RayClassCharacter 𝔪)) ↔
      ZeroFreeRightOf σ (dedekindZetaC K) := by
  simpa only [map_one, heckeLFunctionC_one_modulus_one] using
    zeroFreeRightOf_heckeLFunctionC_induced (1 : RayClassCharacter (Modulus.one K))
      (Modulus.one_dvd 𝔪) hσ

end TauCeti.GlobalNumberFields.RayClassCharacter
