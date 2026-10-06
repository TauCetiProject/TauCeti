/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.FiniteHasse
import TauCeti.NumberTheory.HilbertSymbol.Binary
import TauCeti.NumberTheory.QuadraticForm.Global.ArchimedeanSymbol

/-!
# The correction planes `⟨1, -β⟩` and `⟨α, -αβ⟩`

For units `α, β` of a number field `K`, the binary forms

```text
P = ⟨1, -β⟩,        P' = ⟨α, -αβ⟩ = α P
```

have the same dimension, and their discriminants `-β` and `-α²β` agree modulo squares. This file
computes how they differ place by place. Their Hasse signs at a finite place `v` are

```text
s_v(P) = (1, -β)_v = 1,        s_v(P') = (α, -αβ)_v = (α, β)_v,
```

and at every finite place and every real place the two localizations are isometric exactly when
the local Hilbert symbol `(α, β)` is trivial there. In particular, if `β` is positive at a real
place then the two planes are isometric there.

Replacing `P` by `P'` therefore preserves dimension and discriminant and changes the local
isometry class exactly at the places where `(α, β) = -1`. This is the substitution in O'Meara's
construction of a global form with prescribed localizations: when `α` is chosen with `(α, β)_v = -1`
exactly on a finite set `R` of places, swapping `P` for `P'` inside an orthogonal sum flips the
finite Hasse sign exactly at the finite places of `R`.

## Main results

* `QuadraticForm.finiteHasse_weightedSumSquares_one_neg`: `s_v(⟨1, -β⟩) = 1`.
* `QuadraticForm.finiteHasse_weightedSumSquares_neg_self_mul`: `s_v(⟨α, -αβ⟩) = (α, β)_v`.
* `QuadraticForm.equivalent_atFinitePlace_binary_one_neg_iff_hilbertSymbol_eq_one`: at a finite
  place `v`, `⟨1, -β⟩ ≅ ⟨α, -αβ⟩` over `K_v` exactly when `(α, β)_v = 1`.
* `QuadraticForm.equivalent_atRealPlace_binary_one_neg_iff_hilbertSymbol_eq_one`: the same at a
  real place.
* `QuadraticForm.equivalent_atRealPlace_binary_one_neg_of_pos`: the two planes are isometric at
  every real place at which `β` is positive.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), 72:1.
-/

public section

open IsDedekindDomain NumberField NumberField.InfinitePlace QuadraticMap TauCeti

namespace QuadraticForm

variable {K : Type*} [Field K] [NumberField K]

/-- The finite Hasse sign of the norm plane `⟨1, -β⟩` is trivial at every finite place. -/
@[simp]
theorem finiteHasse_weightedSumSquares_one_neg (b : Kˣ)
    (h : (weightedSumSquares K ![1, -(b : K)]).Nondegenerate) (v : HeightOneSpectrum (𝓞 K)) :
    finiteHasse (weightedSumSquares K ![1, -(b : K)]) h v = 1 := by
  simpa using finiteHasse_weightedSumSquares_binary 1 (-b) (by simpa using h) v

/-- The finite Hasse sign of the scaled norm plane `⟨α, -αβ⟩` at a finite place `v` is the
Hilbert symbol `(α, β)_v`. -/
@[simp]
theorem finiteHasse_weightedSumSquares_neg_self_mul (a b : Kˣ)
    (h : (weightedSumSquares K ![(a : K), -(a * b : K)]).Nondegenerate)
    (v : HeightOneSpectrum (𝓞 K)) :
    finiteHasse (weightedSumSquares K ![(a : K), -(a * b : K)]) h v =
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) := by
  let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have hneg : v.unitAtFinitePlace (-(a * b)) =
      -(v.unitAtFinitePlace a * v.unitAtFinitePlace b) := Units.ext (by simp)
  have := finiteHasse_weightedSumSquares_binary a (-(a * b)) (by simpa using h) v
  rw [hneg, hilbertSymbol_neg_self_mul two_ne_zero] at this
  simpa using this

/-- **The correction planes at a finite place.** Over the completion `K_v`, the planes
`⟨1, -β⟩` and `⟨α, -αβ⟩` are isometric exactly when the Hilbert symbol `(α, β)_v` is `1`. -/
theorem equivalent_atFinitePlace_binary_one_neg_iff_hilbertSymbol_eq_one (a b : Kˣ)
    (v : HeightOneSpectrum (𝓞 K)) :
    (atFinitePlace (weightedSumSquares K ![1, -(b : K)]) v).Equivalent
        (atFinitePlace (weightedSumSquares K ![(a : K), -(a * b : K)]) v) ↔
      hilbertSymbol (v.unitAtFinitePlace a) (v.unitAtFinitePlace b) = 1 := by
  let _ : Invertible (2 : v.adicCompletion K) := invertibleOfNonzero two_ne_zero
  -- Localize both diagonal forms coefficientwise, then apply the criterion over `K_v`.
  have key (x y : K) : (atFinitePlace (weightedSumSquares K ![x, y]) v).Equivalent
      (weightedSumSquares (v.adicCompletion K)
        ![algebraMap K (v.adicCompletion K) x, algebraMap K (v.adicCompletion K) y]) := by
    have hc : (fun i => algebraMap K (v.adicCompletion K) (![x, y] i)) =
        ![algebraMap K (v.adicCompletion K) x, algebraMap K (v.adicCompletion K) y] := by
      ext i; fin_cases i <;> rfl
    rw [← hc]
    exact ⟨atFinitePlaceWeightedSumSquares v _⟩
  have h₁ := key 1 (-b)
  have h₂ := key a (-(a * b))
  rw [← hilbertSymbol_comm, ← equivalent_binary_one_neg_iff_hilbertSymbol_eq_one]
  simp only [map_one, map_neg, map_mul, HeightOneSpectrum.unitAtFinitePlace_apply] at h₁ h₂ ⊢
  exact ⟨fun h => h₁.symm.trans (h.trans h₂), fun h => h₁.trans (h.trans h₂.symm)⟩

omit [NumberField K] in
/-- **The correction planes at a real place.** Over `ℝ`, the planes `⟨1, -β⟩` and `⟨α, -αβ⟩`
are isometric at the real place `w` exactly when the real Hilbert symbol `(α, β)_w` is `1`. -/
theorem equivalent_atRealPlace_binary_one_neg_iff_hilbertSymbol_eq_one (a b : Kˣ)
    (w : {w : InfinitePlace K // w.IsReal}) :
    (atRealPlace (weightedSumSquares K ![1, -(b : K)]) w).Equivalent
        (atRealPlace (weightedSumSquares K ![(a : K), -(a * b : K)]) w) ↔
      hilbertSymbol (unitAtRealPlace w a) (unitAtRealPlace w b) = 1 := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  -- Evaluate both diagonal forms at the real embedding, then apply the criterion over `ℝ`.
  have key (x y : K) : (atRealPlace (weightedSumSquares K ![x, y]) w).Equivalent
      (weightedSumSquares ℝ ![embedding_of_isReal w.2 x, embedding_of_isReal w.2 y]) := by
    have hc : (fun i => embedding_of_isReal w.2 (![x, y] i)) =
        ![embedding_of_isReal w.2 x, embedding_of_isReal w.2 y] := by
      ext i; fin_cases i <;> rfl
    rw [← hc]
    exact ⟨atRealPlaceWeightedSumSquares w _⟩
  have h₁ := key 1 (-b)
  have h₂ := key a (-(a * b))
  rw [← hilbertSymbol_comm, ← equivalent_binary_one_neg_iff_hilbertSymbol_eq_one]
  simp only [map_one, map_neg, map_mul, unitAtRealPlace_apply] at h₁ h₂ ⊢
  exact ⟨fun h => h₁.symm.trans (h.trans h₂), fun h => h₁.trans (h.trans h₂.symm)⟩

omit [NumberField K] in
/-- At a real place where `β` is positive, the planes `⟨1, -β⟩` and `⟨α, -αβ⟩` are isometric:
both are hyperbolic there. -/
theorem equivalent_atRealPlace_binary_one_neg_of_pos (a : Kˣ) {b : Kˣ}
    {w : {w : InfinitePlace K // w.IsReal}} (hb : 0 < embedding_of_isReal w.2 (b : K)) :
    (atRealPlace (weightedSumSquares K ![1, -(b : K)]) w).Equivalent
      (atRealPlace (weightedSumSquares K ![(a : K), -(a * b : K)]) w) :=
  (equivalent_atRealPlace_binary_one_neg_iff_hilbertSymbol_eq_one a b w).mpr
    ((hilbertSymbol_unitAtRealPlace_eq_one_iff w a b).mpr (.inr hb))

end QuadraticForm
