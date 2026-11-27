/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Basic
public import TauCeti.Analysis.Meromorphic.ZeroFree
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.Basic
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic

/-!
# Meromorphic orders, divisors, and zero counts under ray class induction

Inducing a ray class character deletes finitely many Euler factors. Their correction is entire
and nonvanishing off `Re s = 0`. Thus wherever the correction is nonzero (in particular at every
point off the imaginary axis), changing the presentation preserves the meromorphic order, divisor,
and zero count, including at a pole. In particular, a zero-free right half-plane can be checked at
the primitive conductor. For a trivial character this reduces to Dedekind zeta.
-/

public section

open Filter Set
open scoped NumberField Topology
open TauCeti TauCeti.GlobalNumberFields TauCeti.LFunctions

namespace TauCeti.LFunctions

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-- At the trivial modulus the trivial character's continued L-function is the Dedekind zeta
function in meromorphic normal form. -/
@[simp] theorem heckeLFunctionC_one_modulus_one (K : Type*) [Field K] [NumberField K] :
    heckeLFunctionC (1 : RayClassCharacter (Modulus.one K)) = dedekindZetaC K := by
  rw [heckeLFunctionC_def, RayClassCharacter.toUnitaryIdealWeight_one,
    UnitaryIdealWeight.toIdealArithmeticFunction_one, dedekindZetaC_def]
  exact congrArg (meromorphicContinuation 1)
    (funext fun s ↦ (dedekindZeta_eq_LSeries_normCoeff_one K s).symm)

/-- Wherever the deleted Euler correction is nonzero, inducing a ray class character to a larger
modulus does not change the meromorphic order of `heckeLFunctionC`. -/
theorem meromorphicOrderAt_heckeLFunctionC_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪)
    {s : ℂ} (hs : χ.eulerCorrection 𝔫 s ≠ 0) :
    meromorphicOrderAt (heckeLFunctionC (χ.induced h)) s =
      meromorphicOrderAt (heckeLFunctionC χ) s := by
  have hev : heckeLFunctionC (χ.induced h) =ᶠ[𝓝[≠] s]
      χ.eulerCorrection 𝔫 * heckeLFunctionC χ := by
    filter_upwards [heckeLFunctionC_induced_eventuallyEq h χ s] with z hz
    rw [hz, Pi.mul_apply, mul_comm]
  rw [meromorphicOrderAt_congr hev,
    meromorphicOrderAt_mul_of_ne_zero ((χ.differentiable_eulerCorrection 𝔫).analyticAt s) hs]

/-- Off the imaginary axis, inducing a ray class character to a larger modulus does not change the
meromorphic order of `heckeLFunctionC`. -/
theorem meromorphicOrderAt_heckeLFunctionC_induced_of_re_ne_zero (h : 𝔪 ∣ 𝔫)
    (χ : RayClassCharacter 𝔪) {s : ℂ} (hs : s.re ≠ 0) :
    meromorphicOrderAt (heckeLFunctionC (χ.induced h)) s =
      meromorphicOrderAt (heckeLFunctionC χ) s :=
  meromorphicOrderAt_heckeLFunctionC_induced h χ (χ.eulerCorrection_ne_zero 𝔫 hs)

/-- Wherever the deleted Euler correction is nonzero, inducing does not change the divisor of
`heckeLFunctionC` on any domain `U`. -/
theorem divisor_heckeLFunctionC_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪)
    (U : Set ℂ) {s : ℂ} (hs : χ.eulerCorrection 𝔫 s ≠ 0) :
    MeromorphicOn.divisor (heckeLFunctionC (χ.induced h)) U s =
      MeromorphicOn.divisor (heckeLFunctionC χ) U s := by
  by_cases hsU : s ∈ U
  · rw [MeromorphicOn.divisor_apply
        (fun z _ ↦ (meromorphicNFOn_heckeLFunctionC _).meromorphicOn z (mem_univ z)) hsU,
      MeromorphicOn.divisor_apply
        (fun z _ ↦ (meromorphicNFOn_heckeLFunctionC _).meromorphicOn z (mem_univ z)) hsU,
      meromorphicOrderAt_heckeLFunctionC_induced h χ hs]
  · simp only [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hsU]

/-- Off the imaginary axis, inducing does not change the divisor of `heckeLFunctionC` on any
domain `U`. -/
theorem divisor_heckeLFunctionC_induced_of_re_ne_zero (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪)
    (U : Set ℂ) {s : ℂ} (hs : s.re ≠ 0) :
    MeromorphicOn.divisor (heckeLFunctionC (χ.induced h)) U s =
      MeromorphicOn.divisor (heckeLFunctionC χ) U s :=
  divisor_heckeLFunctionC_induced h χ U (χ.eulerCorrection_ne_zero 𝔫 hs)

/-- On any region `R` and divisor domain `U` such that the deleted Euler correction is nonzero on
`R ∩ U`, inducing does not change the zero count of `heckeLFunctionC`. -/
theorem zeroCount_heckeLFunctionC_induced (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪)
    {U R : Set ℂ} (hR : ∀ s ∈ R ∩ U, χ.eulerCorrection 𝔫 s ≠ 0) :
    zeroCount (heckeLFunctionC (χ.induced h)) U R =
      zeroCount (heckeLFunctionC χ) U R :=
  zeroCount_congr_divisor fun s hsR ↦ by
    by_cases hsU : s ∈ U
    · rw [divisor_heckeLFunctionC_induced h χ U (hR s ⟨hsR, hsU⟩)]
    · simp only [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hsU]

/-- On any region `R` and divisor domain `U` whose intersection avoids the imaginary axis, inducing
does not change the zero count of `heckeLFunctionC`. -/
theorem zeroCount_heckeLFunctionC_induced_of_re_ne_zero (h : 𝔪 ∣ 𝔫) (χ : RayClassCharacter 𝔪)
    {U R : Set ℂ} (hR : ∀ s ∈ R ∩ U, s.re ≠ 0) :
    zeroCount (heckeLFunctionC (χ.induced h)) U R =
      zeroCount (heckeLFunctionC χ) U R :=
  zeroCount_heckeLFunctionC_induced h χ fun s hs ↦ χ.eulerCorrection_ne_zero 𝔫 (hR s hs)

/-- On any region `R` and divisor domain `U` whose intersection avoids the imaginary axis, a
presented Hecke L-function has the same zero count as its underlying primitive character. -/
theorem zeroCount_heckeLFunctionC_eq_primitive (χ : RayClassCharacter 𝔪)
    {U R : Set ℂ} (hR : ∀ s ∈ R ∩ U, s.re ≠ 0) :
    zeroCount (heckeLFunctionC χ) U R =
      zeroCount (heckeLFunctionC (PrimitiveRayClassCharacter.of χ).character) U R := by
  conv_lhs => rw [← PrimitiveRayClassCharacter.induced_character_of χ]
  exact zeroCount_heckeLFunctionC_induced_of_re_ne_zero _ _ hR

end TauCeti.LFunctions

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 𝔫 : Modulus K}

/-- Induction preserves the order of the continued Hecke L-function off the imaginary axis. -/
@[simp] theorem meromorphicOrderAt_heckeLFunctionC_induced (χ : RayClassCharacter 𝔪)
    (h : 𝔪 ∣ 𝔫) {s : ℂ} (hs : s.re ≠ 0) :
    meromorphicOrderAt (heckeLFunctionC (χ.induced h)) s =
      meromorphicOrderAt (heckeLFunctionC χ) s :=
  TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_induced_of_re_ne_zero h χ hs

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
