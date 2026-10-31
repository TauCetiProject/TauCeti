/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Roth.ApproximationClass
public import TauCeti.NumberTheory.Height.Independent

/-!
# Independent sequences in one approximation class

Combined with the approximation classes of
`TauCeti.NumberTheory.DiophantineApproximation.Roth.ApproximationClass`, the `(L, M)`-independent
sequences of `TauCeti.NumberTheory.Height.Independent` give the reduction the proof of Roth's
theorem over a number field opens with: an infinite set of solutions contains an
`(L, M)`-independent sequence all of whose terms share one label `c` with `∑ a, c a ≤ N`, which
for `0 < N` is one approximation class of side `1 / N`.

## Main results

* `Set.Infinite.exists_cellIndex_eq_and_isHeightIndependent`: the two reductions at once.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), 6.4.4.
* The statements follow Ralf Stephan's formalization
  `DiophantineApproximation/IndependentHeights.lean` in `rwst/Subspace-Theorems` (Apache 2.0).
-/

public section

open Height

namespace Set.Infinite

open TauCeti

variable {K : Type*} [Field K] [AdmissibleAbsValues K] [Northcott (logHeight₁ (K := K))]

/-- **Bombieri–Gubler 6.4.4.** An infinite set `X`, in a field whose logarithmic height has the
Northcott property, contains an `(L, M)`-independent sequence all of whose terms share one label
`c` with `∑ a, c a ≤ N` for a family of maps from `X` into the standard simplex; for `0 < N` this
is one approximation class of side `1 / N`. -/
theorem exists_cellIndex_eq_and_isHeightIndependent {A : Type*} [Fintype A] {X : Set K}
    (hX : X.Infinite) (φ : A → K → ℝ) (hφ₀ : ∀ a, ∀ x ∈ X, 0 ≤ φ a x)
    (hφ₁ : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) (L M : ℝ) :
    ∃ c : A → ℕ, ∑ a, c a ≤ N ∧ ∃ β : ℕ → K, (∀ j, β j ∈ X) ∧
      (∀ j, cellIndex N (fun a ↦ φ a (β j)) = c) ∧ IsHeightIndependent L M β := by
  obtain ⟨c, hc, hinf⟩ := hX.exists_cellIndex_eq φ hφ₀ hφ₁ N
  obtain ⟨β, hβX, hβ⟩ := hinf.exists_isHeightIndependent L M
  exact ⟨c, hc, β, fun j ↦ (hβX j).1, fun j ↦ (hβX j).2, hβ⟩

end Set.Infinite
