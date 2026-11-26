/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Counting.Certificate
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.GRH
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros

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
`RiemannHypothesis`, and for a primitive Dirichlet character's completed L-function and entire
completion it is equivalent to `TauCeti.DirichletGRH`. Stating it through the divisor of the
completed function, rather than through the zeros of `riemannZeta` or
`DirichletCharacter.LFunction`, removes the trivial zeros and the junk value at the pole without
listing them as exceptions.

## Main results

* `TauCeti.HasZerosInRects.allOnCriticalLine`: a certificate whose rectangles have all their
  zeros on the critical line places every zero of the certified rectangle there.
* `TauCeti.LFunctions.allOnCriticalLine_of_zeroCount_eq_one`: the symmetry criterion.
* `TauCeti.LFunctions.allOnCriticalLine_Icc_reProdIm_Icc_iff`: the predicate on the box
  `Icc 0 1 ×ℂ Icc (-H) H`, for a function whose zeros are the open-strip points of a predicate.
* `TauCeti.LFunctions.allOnCriticalLine_completedRiemannZeta_iff`,
  `TauCeti.LFunctions.allOnCriticalLine_zetaEntireCompletion_iff`: the Riemann hypothesis.
* `TauCeti.LFunctions.allOnCriticalLine_completedLFunction_iff`,
  `TauCeti.LFunctions.allOnCriticalLine_dirichletData_entireCompletion_iff`: the generalized
  Riemann hypothesis for a primitive Dirichlet character.
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

/-- **Bounded-height form.** If the zeros of `f` (the points of positive divisor on `univ`) are
exactly the points of the open strip `0 < re ρ < 1` satisfying `Z`, then `f` has all its zeros in
the box `Icc 0 1 ×ℂ Icc (-H) H` on the critical line if and only if every `ρ` satisfying `Z` in the
open strip with `|im ρ| ≤ H` has `re ρ = 1/2`. -/
theorem allOnCriticalLine_Icc_reProdIm_Icc_iff {Z : ℂ → Prop}
    (hf : ∀ ρ, 0 < MeromorphicOn.divisor f univ ρ ↔ Z ρ ∧ ρ.re ∈ Ioo 0 1) {H : ℝ} :
    AllOnCriticalLine f univ (Icc 0 1 ×ℂ Icc (-H) H) ↔
      ∀ ρ : ℂ, Z ρ → 0 < ρ.re → ρ.re < 1 → |ρ.im| ≤ H → ρ.re = 1 / 2 := by
  simp only [allOnCriticalLine_iff, mem_reProdIm, mem_Icc, ← abs_le, hf, mem_Ioo]
  exact ⟨fun h ρ h0 hre0 hre1 him ↦ h ρ ⟨⟨hre0.le, hre1.le⟩, him⟩ ⟨h0, hre0, hre1⟩,
    fun h ρ ⟨_, him⟩ ⟨h0, hre0, hre1⟩ ↦ h ρ h0 hre0 hre1 him⟩

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

/-- **The generalized Riemann hypothesis** for a primitive Dirichlet character `χ` says exactly
that every zero of `χ.completedLFunction` lies on the critical line. -/
theorem allOnCriticalLine_completedLFunction_iff {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    AllOnCriticalLine χ.completedLFunction univ univ ↔ DirichletGRH χ := by
  rw [allOnCriticalLine_iff, χ.dirichletGRH_iff_mem_Ioo]
  exact forall_congr' fun s ↦ ⟨fun h h0 hre ↦ h (mem_univ s)
    (hχ.zero_lt_divisor_completedLFunction_iff.2 ⟨h0, hre⟩),
    fun h _ hpos ↦
      let ⟨h0, hre⟩ := hχ.zero_lt_divisor_completedLFunction_iff.1 hpos
      h h0 hre⟩

/-- **The generalized Riemann hypothesis** for a primitive Dirichlet character `χ` says exactly
that every zero of `(dirichletData χ hχ).entireCompletion` lies on the critical line. -/
theorem allOnCriticalLine_dirichletData_entireCompletion_iff {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    AllOnCriticalLine (dirichletData χ hχ).entireCompletion univ univ ↔ DirichletGRH χ := by
  rw [← allOnCriticalLine_completedLFunction_iff hχ]
  simp only [allOnCriticalLine_iff, zero_lt_divisor_dirichletData_entireCompletion_iff,
    hχ.zero_lt_divisor_completedLFunction_iff]

end TauCeti.LFunctions
