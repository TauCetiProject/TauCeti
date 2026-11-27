/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic

/-!
# Multiplicative indicators on finite adeles

A multiplicative indicator keeps the components on a set of places and replaces all other
components by one. The set need not be finite: replacing components by one preserves the
restricted product condition. Applied to a diagonal idele, this gives a principal component on a
chosen set of primes without introducing any new denominators elsewhere.
-/

public noncomputable section

namespace IsDedekindDomain.FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

open scoped FiniteAdeleRing

/-- Keep the components of a finite adele in `S` and replace the rest by one. -/
def mulIndicator (S : Set (HeightOneSpectrum R)) : 𝔸ᶠ[R, K] →* 𝔸ᶠ[R, K] := by
  classical
  let f (a : 𝔸ᶠ[R, K]) : 𝔸ᶠ[R, K] := ⟨fun v ↦ if v ∈ S then a v else 1, by
    filter_upwards [a.cofinite_mem_adicCompletionIntegers] with v hv
    by_cases h : v ∈ S <;> simp [h, hv]⟩
  exact {
    toFun := f
    map_one' := ext K fun v ↦ by
      -- Evaluate the dependent tuple at `v` before simplifying the indicator.
      change (if v ∈ S then (1 : 𝔸ᶠ[R, K]) v else 1) = (1 : 𝔸ᶠ[R, K]) v
      simp
    map_mul' := fun a b ↦ ext K fun v ↦ by
      -- The two sides are coordinatewise products by definition of the restricted product.
      change (if v ∈ S then (a * b) v else 1) =
        (if v ∈ S then a v else 1) * (if v ∈ S then b v else 1)
      by_cases h : v ∈ S <;> simp [h] }

open Classical in
/-- The coordinate of a multiplicative indicator is the original coordinate on `S`, and one
elsewhere. -/
theorem mulIndicator_apply (S : Set (HeightOneSpectrum R)) (a : 𝔸ᶠ[R, K])
    (v : HeightOneSpectrum R) : mulIndicator S a v = if v ∈ S then a v else 1 := (rfl)

/-- On the selected places the multiplicative indicator keeps the original component. -/
@[simp] theorem mulIndicator_apply_of_mem {S : Set (HeightOneSpectrum R)} (a : 𝔸ᶠ[R, K])
    {v : HeightOneSpectrum R} (hv : v ∈ S) : mulIndicator S a v = a v := by
  classical
  rw [mulIndicator_apply, ite_eq_left hv]

/-- Off the selected places the multiplicative indicator has component one. -/
@[simp] theorem mulIndicator_apply_of_notMem {S : Set (HeightOneSpectrum R)} (a : 𝔸ᶠ[R, K])
    {v : HeightOneSpectrum R} (hv : v ∉ S) : mulIndicator S a v = 1 := by
  classical
  rw [mulIndicator_apply, ite_eq_right hv]

/-- The indicator is integral exactly when the selected components are integral. -/
theorem mulIndicator_mem_integralAdeles {S : Set (HeightOneSpectrum R)}
    {a : 𝔸ᶠ[R, K]} : mulIndicator S a ∈ integralAdeles R K ↔
      ∀ v ∈ S, a v ∈ v.adicCompletionIntegers K := by
  rw [mem_integralAdeles]
  refine ⟨fun h v hv ↦ by simpa [hv] using h v, fun h v ↦ ?_⟩
  by_cases hv : v ∈ S
  · simpa [hv] using h v hv
  · simp [hv]

end IsDedekindDomain.FiniteAdeleRing
