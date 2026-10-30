/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.CompactSublevel
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The mod-two Morse boundary

This file defines the algebraic boundary obtained by counting isolated negative-gradient
trajectories between critical points of consecutive Morse index. A trajectory is represented by
its unique intersection with the middle level between its endpoints. Under compact-sublevel and
Morse--Smale hypotheses, this slice is finite, so its cardinality modulo two is well-defined.

The boundary of one critical point is a finitely supported sum: every endpoint with nonzero
coefficient is a critical point in the compact sublevel of the source. Extending this assignment
linearly gives an endomorphism of the free `ZMod 2`-module on the critical points. Proving that
this endomorphism squares to zero requires the compactification and gluing of index-two trajectory
spaces and is not asserted here.

## Main declarations

* `TauCeti.MorseCriticalPoint`: the type of nondegenerate critical points of a real-valued
  function.
* `TauCeti.morseTrajectorySlice`: the middle-level representatives of trajectories from `p` to
  `q`.
* `TauCeti.morseTrajectoryCount`: the cardinality modulo two of a finite trajectory slice.
* `TauCeti.morseBoundaryOnGenerator`: the finitely supported boundary of a critical point.
* `TauCeti.morseBoundary`: the linear extension to mod-two Morse chains.

## Reference

M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
Chapter 4 (the Morse complex).
-/

public section

open Set
open scoped Gradient NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {K : ℝ≥0}

/-- A nondegenerate critical point of a real-valued function. These are the generators of the
Morse chain module. -/
abbrev MorseCriticalPoint (f : E → ℝ) := {x : E // IsNondegenerateCriticalPoint f x}

namespace MorseCriticalPoint

omit [FiniteDimensional ℝ E] in
/-- The differential vanishes at a Morse critical point. -/
@[simp]
theorem fderiv_eq_zero (p : MorseCriticalPoint f) : fderiv ℝ f p = 0 :=
  p.property.fderiv_eq_zero

omit [FiniteDimensional ℝ E] in
/-- A Morse critical point is nondegenerate. -/
theorem isNondegenerate (p : MorseCriticalPoint f) :
    IsNondegenerateCriticalPoint f p :=
  p.property

end MorseCriticalPoint

omit [FiniteDimensional ℝ E] in
/-- Under compact sublevels, only finitely many critical points have critical value at most
`c`. -/
theorem finite_setOf_value_le_of_isCompact_sublevel (hfs : ContDiff ℝ 2 f)
    (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c}) (c : ℝ) :
    {q : MorseCriticalPoint f | f q ≤ c}.Finite := by
  have hcrit : {x ∈ {x | f x ≤ c} | fderiv ℝ f x = 0}.Finite :=
    (hM.mono (subset_univ _)).finite_setOfPred_fderiv_eq_zero (hcompact c)
      (hfs.continuous_fderiv (by norm_num)).continuousOn
  exact (hcrit.preimage Subtype.val_injective.injOn).subset fun q hq ↦
    ⟨hq, q.property.fderiv_eq_zero⟩

/-- Mod-two Morse chains are finitely supported functions on the critical points. -/
abbrev MorseChain (f : E → ℝ) := MorseCriticalPoint f →₀ ZMod 2

/-- The middle-level slice representing unparametrized negative-gradient trajectories from `p`
to `q`. Every nonconstant trajectory crosses this level exactly once. -/
noncomputable def morseTrajectorySlice (hf : LipschitzWith K (∇ f)) (p q : E) : Set E :=
  Flow.unstableSet (negativeGradientFlow f hf) p ∩
    Flow.stableSet (negativeGradientFlow f hf) q ∩
      {z | f z = (f p + f q) / 2}

/-- Membership in the middle-level trajectory slice. -/
@[simp]
theorem mem_morseTrajectorySlice {hf : LipschitzWith K (∇ f)} {p q z : E} :
    z ∈ morseTrajectorySlice hf p q ↔
      z ∈ Flow.unstableSet (negativeGradientFlow f hf) p ∧
        z ∈ Flow.stableSet (negativeGradientFlow f hf) q ∧
          f z = (f p + f q) / 2 :=
  by simp only [morseTrajectorySlice, mem_inter_iff, mem_ofPred_eq, and_assoc]

/-- The canonical middle-level trajectory slice is finite for critical points of consecutive
index under compact-sublevel and Morse--Smale hypotheses. -/
theorem finite_morseTrajectorySlice_of_isCompact_sublevel
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c}) {p q : E}
    (hp : IsNondegenerateCriticalPoint f p) (hq : IsNondegenerateCriticalPoint f q)
    (hind : morseIndex f p = morseIndex f q + 1) (hqp : f q < f p)
    (htr : IsMorseSmale f hf) :
    (morseTrajectorySlice hf p q).Finite := by
  apply finite_unstableSet_inter_stableSet_inter_level_of_isCompact_sublevel
    hfs hf hM hcompact hp hq hind (c := (f p + f q) / 2) (by constructor <;> linarith) htr

/-- The mod-two count of a finite middle-level trajectory slice. The finiteness witness is an
explicit argument so the definition cannot silently assign zero to an infinite slice. -/
noncomputable def morseTrajectoryCount (hf : LipschitzWith K (∇ f)) (p q : E)
    (hfinite : (morseTrajectorySlice hf p q).Finite) : ZMod 2 :=
  hfinite.toFinset.card

/-- The trajectory count is the natural-number cardinality of the slice, reduced modulo two. -/
theorem morseTrajectoryCount_eq_ncard (hf : LipschitzWith K (∇ f)) (p q : E)
    (hfinite : (morseTrajectorySlice hf p q).Finite) :
    morseTrajectoryCount hf p q hfinite = ((morseTrajectorySlice hf p q).ncard : ZMod 2) := by
  rw [morseTrajectoryCount, Set.ncard_eq_toFinset_card _ hfinite]

section Boundary

variable (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
  (hM : HasNondegenerateCriticalPointsOn f univ)
  (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c})
  (htr : IsMorseSmale f hf)

/-- The coefficient of `q` in the mod-two boundary of `p`. It is zero unless the Morse index
drops by one and the critical value strictly decreases; otherwise it counts the canonical
middle-level trajectory slice modulo two. -/
noncomputable def morseBoundaryCoeff (p q : MorseCriticalPoint f) : ZMod 2 :=
  if hind : morseIndex f p = morseIndex f q + 1 then
    if hqp : f q < f p then
      morseTrajectoryCount hf p q
        (finite_morseTrajectorySlice_of_isCompact_sublevel hfs hf hM hcompact
          p.isNondegenerate q.isNondegenerate hind hqp htr)
    else 0
  else 0

/-- When the endpoints have consecutive index and decreasing critical value, the boundary
coefficient is the parity of the middle-level trajectory slice. -/
theorem morseBoundaryCoeff_eq_trajectoryCount (p q : MorseCriticalPoint f)
    (hind : morseIndex f p = morseIndex f q + 1) (hqp : f q < f p) :
    morseBoundaryCoeff hfs hf hM hcompact htr p q =
      morseTrajectoryCount hf p q
        (finite_morseTrajectorySlice_of_isCompact_sublevel hfs hf hM hcompact
          p.isNondegenerate q.isNondegenerate hind hqp htr) := by
  simp only [morseBoundaryCoeff, dite_eq_left hind, dite_eq_left hqp]

/-- The boundary coefficient vanishes when the endpoint indices do not differ by one. -/
@[simp]
theorem morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (p q : MorseCriticalPoint f)
    (hind : morseIndex f p ≠ morseIndex f q + 1) :
    morseBoundaryCoeff hfs hf hM hcompact htr p q = 0 := by
  simp only [morseBoundaryCoeff, dite_eq_right hind]

/-- The boundary coefficient vanishes unless the critical value decreases. -/
@[simp]
theorem morseBoundaryCoeff_eq_zero_of_value_le (p q : MorseCriticalPoint f)
    (hqp : f p ≤ f q) :
    morseBoundaryCoeff hfs hf hM hcompact htr p q = 0 := by
  by_cases hind : morseIndex f p = morseIndex f q + 1
  · simp only [morseBoundaryCoeff, dite_eq_left hind, dite_eq_right (not_lt_of_ge hqp)]
  · exact morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one
      hfs hf hM hcompact htr p q hind

/-- A nonzero boundary coefficient can only join critical points whose indices differ by one. -/
theorem morseIndex_eq_add_one_of_morseBoundaryCoeff_ne_zero {p q : MorseCriticalPoint f}
    (hcoeff : morseBoundaryCoeff hfs hf hM hcompact htr p q ≠ 0) :
    morseIndex f p = morseIndex f q + 1 := by
  by_contra hind
  exact hcoeff (by simp only [morseBoundaryCoeff, dite_eq_right hind])

/-- A nonzero boundary coefficient strictly decreases the critical value. -/
theorem value_lt_of_morseBoundaryCoeff_ne_zero {p q : MorseCriticalPoint f}
    (hcoeff : morseBoundaryCoeff hfs hf hM hcompact htr p q ≠ 0) :
    f q < f p := by
  have hind := morseIndex_eq_add_one_of_morseBoundaryCoeff_ne_zero
    hfs hf hM hcompact htr hcoeff
  by_contra hqp
  exact hcoeff (by
    simp only [morseBoundaryCoeff, dite_eq_left hind, dite_eq_right hqp])

/-- Only finitely many critical points have a nonzero coefficient in the boundary of `p`. -/
private theorem finite_support_morseBoundaryCoeff (p : MorseCriticalPoint f) :
    (Function.support (morseBoundaryCoeff hfs hf hM hcompact htr p)).Finite :=
  (finite_setOf_value_le_of_isCompact_sublevel hfs hM hcompact (f p)).subset fun _ hq ↦
    (value_lt_of_morseBoundaryCoeff_ne_zero hfs hf hM hcompact htr hq).le

/-- The mod-two Morse boundary of one critical point, as a finitely supported sum of critical
points. -/
noncomputable def morseBoundaryOnGenerator (p : MorseCriticalPoint f) : MorseChain f :=
  Finsupp.ofSupportFinite (morseBoundaryCoeff hfs hf hM hcompact htr p)
    (finite_support_morseBoundaryCoeff hfs hf hM hcompact htr p)

/-- The coefficient of a generator in the boundary is its mod-two trajectory count. -/
@[simp]
theorem morseBoundaryOnGenerator_apply (p q : MorseCriticalPoint f) :
    morseBoundaryOnGenerator hfs hf hM hcompact htr p q =
      morseBoundaryCoeff hfs hf hM hcompact htr p q :=
  congrFun Finsupp.ofSupportFinite_coe q

/-- Every generator in the support of a boundary has Morse index one below the source. -/
theorem morseIndex_eq_add_one_of_mem_support_morseBoundaryOnGenerator
    {p q : MorseCriticalPoint f}
    (hq : q ∈ (morseBoundaryOnGenerator hfs hf hM hcompact htr p).support) :
    morseIndex f p = morseIndex f q + 1 :=
  morseIndex_eq_add_one_of_morseBoundaryCoeff_ne_zero hfs hf hM hcompact htr
    (Finsupp.mem_support_iff.mp hq)

/-- Every generator in the support of a boundary has smaller critical value than the source. -/
theorem value_lt_of_mem_support_morseBoundaryOnGenerator {p q : MorseCriticalPoint f}
    (hq : q ∈ (morseBoundaryOnGenerator hfs hf hM hcompact htr p).support) :
    f q < f p :=
  value_lt_of_morseBoundaryCoeff_ne_zero hfs hf hM hcompact htr
    (Finsupp.mem_support_iff.mp hq)

/-- The mod-two Morse boundary, obtained by linearly extending the trajectory count on critical
points. -/
noncomputable def morseBoundary : MorseChain f →ₗ[ZMod 2] MorseChain f :=
  Finsupp.linearCombination (ZMod 2)
    (morseBoundaryOnGenerator hfs hf hM hcompact htr)

/-- The Morse boundary sends a basis generator to its trajectory-counting boundary. -/
@[simp]
theorem morseBoundary_single (p : MorseCriticalPoint f) (a : ZMod 2) :
    morseBoundary hfs hf hM hcompact htr (Finsupp.single p a) =
      a • morseBoundaryOnGenerator hfs hf hM hcompact htr p := by
  simp [morseBoundary]

/-- The `q` coefficient of a Morse boundary is the finite sum of the input coefficients times
the trajectory counts from their generators to `q`. -/
theorem morseBoundary_apply (c : MorseChain f) (q : MorseCriticalPoint f) :
    morseBoundary hfs hf hM hcompact htr c q =
      c.sum fun p a ↦ a * morseBoundaryCoeff hfs hf hM hcompact htr p q := by
  simp [morseBoundary, Finsupp.linearCombination_apply]

end Boundary

end TauCeti

end
