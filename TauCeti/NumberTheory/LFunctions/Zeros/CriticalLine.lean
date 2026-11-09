/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Certificate
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta

/-!
# Zeros on the critical line

`TauCeti.LFunctions.AllOnCriticalLine f U R` says that every zero of `f` in `R`, in the sense of
a positive value of the divisor of `f` on `U`, has real part `1/2`. Poles and points where `f`
has order `0` are not zeros, whatever value the representative `f` takes there.

The predicate passes from the rectangles of a certified list of zeros
(`TauCeti.HasZerosInRects`) to the whole certified rectangle, and a region symmetric under
`s ↦ 1 - conj s` containing exactly one zero, counted with multiplicity, has that zero on the
critical line. This is the usual way a numerical verification places zeros on the line: the
divisor of a completed L-function with real coefficients is invariant under this reflection,
which combines the functional equation with complex conjugation.

Over the whole plane the predicate is the Riemann hypothesis: for the completed Riemann zeta
function and for its entire completion `zetaEntireCompletion` it is equivalent to Mathlib's
`RiemannHypothesis`. Stating it through the divisor of the completed function, rather than
through the zeros of `riemannZeta`, removes the trivial zeros and the junk value at the pole
without listing them as exceptions.

## Main results

* `TauCeti.HasZerosInRects.allOnCriticalLine`: a certificate whose rectangles have all their
  zeros on the critical line places every zero of the certified rectangle there.
* `TauCeti.LFunctions.allOnCriticalLine_of_zeroCount_eq_one`: the symmetry criterion.
* `TauCeti.LFunctions.allOnCriticalLine_completedRiemannZeta_iff`,
  `TauCeti.LFunctions.allOnCriticalLine_zetaEntireCompletion_iff`: the Riemann hypothesis.
-/

public section

open Set Complex ComplexConjugate

namespace TauCeti.LFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {U R S : Set ℂ}

/-- Every zero of `f` in `R`, that is every point of `R` where the divisor of `f` on `U` is
positive, lies on the critical line `re s = 1/2`. -/
def AllOnCriticalLine (f : ℂ → E) (U R : Set ℂ) : Prop :=
  ∀ ρ ∈ R, 0 < MeromorphicOn.divisor f U ρ → ρ.re = 1 / 2

/-- Unfolding `AllOnCriticalLine`. -/
theorem allOnCriticalLine_iff :
    AllOnCriticalLine f U R ↔ ∀ ρ ∈ R, 0 < MeromorphicOn.divisor f U ρ → ρ.re = 1 / 2 :=
  Iff.rfl

/-- The property passes to a smaller region. -/
theorem AllOnCriticalLine.mono (h : AllOnCriticalLine f U S) (hRS : R ⊆ S) :
    AllOnCriticalLine f U R :=
  fun ρ hρ ↦ h ρ (hRS hρ)

/-- **The symmetry criterion.** If a region `R` and the divisor of `f` on it are invariant under
the reflection `s ↦ 1 - conj s` in the critical line, and `R` contains exactly one zero of `f`
counted with multiplicity, then that zero lies on the critical line. A zero off the line would
come with its distinct mirror image. -/
theorem allOnCriticalLine_of_zeroCount_eq_one (hR : ∀ s ∈ R, 1 - conj s ∈ R)
    (hdiv : ∀ s ∈ R, MeromorphicOn.divisor f U (1 - conj s) = MeromorphicOn.divisor f U s)
    (hcount : zeroCount f U R = 1) : AllOnCriticalLine f U R := by
  intro ρ hρ hpos
  by_contra hre
  have hne : ρ ≠ 1 - conj ρ := by
    intro h
    apply hre
    have := congrArg re h
    simp only [sub_re, one_re, conj_re] at this
    linarith
  -- The count is finite, since an infinite `finsum` would be `0`.
  have hfin : (R ∩ Function.support (fun s ↦ (MeromorphicOn.divisor f U s).toNat)).Finite := by
    by_contra hinf
    rw [zeroCount_def, finsum_mem_eq_zero_of_infinite hinf] at hcount
    exact zero_ne_one hcount
  have hle := zeroCount_mono (f := f) (U := U) (pair_subset hρ (hR ρ hρ)) hfin
  rw [zeroCount_def, finsum_mem_pair hne, hdiv ρ hρ, hcount] at hle
  omega

end TauCeti.LFunctions

namespace TauCeti.HasZerosInRects

open LFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {U : Set ℂ} {z w : ℂ} {Bs : List (ℂ × ℂ)} {ms : List ℕ}

/-- If every certified rectangle has all its zeros on the critical line, then so does the whole
certified rectangle. -/
theorem allOnCriticalLine (h : HasZerosInRects f U z w Bs ms)
    (hBs : ∀ B ∈ Bs, AllOnCriticalLine f U (Rectangle B.1 B.2)) :
    AllOnCriticalLine f U (Rectangle z w) := by
  intro ρ hρ hpos
  obtain ⟨B, hB, hρB⟩ := h.exists_mem_interior hρ hpos
  exact hBs B hB ρ (interior_subset hρB) hpos

end TauCeti.HasZerosInRects

namespace TauCeti.LFunctions

/-- **The Riemann hypothesis** says exactly that every zero of the completed Riemann zeta
function lies on the critical line. -/
theorem allOnCriticalLine_completedRiemannZeta_iff :
    AllOnCriticalLine completedRiemannZeta univ univ ↔ RiemannHypothesis := by
  refine ⟨fun h s hs htriv hs1 ↦ ?_, fun h ρ _ hpos ↦ ?_⟩
  · exact h s (mem_univ s) (zero_lt_divisor_completedRiemannZeta_iff.2 ⟨hs, htriv, hs1⟩)
  · obtain ⟨hζ, htriv, hρ1⟩ := zero_lt_divisor_completedRiemannZeta_iff.1 hpos
    exact h ρ hζ htriv hρ1

/-- **The Riemann hypothesis** says exactly that every zero of `zetaEntireCompletion`, twice
Riemann's ξ-function, lies on the critical line. -/
theorem allOnCriticalLine_zetaEntireCompletion_iff :
    AllOnCriticalLine zetaEntireCompletion univ univ ↔ RiemannHypothesis := by
  rw [← allOnCriticalLine_completedRiemannZeta_iff]
  simp only [allOnCriticalLine_iff, zero_lt_divisor_zetaEntireCompletion_iff]

end TauCeti.LFunctions
