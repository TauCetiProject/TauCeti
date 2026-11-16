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
import TauCeti.Analysis.Calculus.Morse.Stable

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

/-- A point of the middle-level slice between distinct endpoints forces the critical value to
drop strictly. -/
theorem value_lt_of_mem_morseTrajectorySlice (hfd : Differentiable ℝ f)
    {hf : LipschitzWith K (∇ f)} {p q z : E} (hpq : p ≠ q)
    (hz : z ∈ morseTrajectorySlice hf p q) :
    f q < f p := by
  rw [mem_morseTrajectorySlice] at hz
  exact (isNegativeGradient_negativeGradientFlow f hf).value_lt_of_mem_unstableSet_inter_stableSet
    (fun _ ↦ hfd.differentiableAt) hfd.continuous.continuousAt hfd.continuous.continuousAt hpq
    ⟨hz.1, hz.2.1⟩

/-- The middle-level slice between distinct endpoints is empty unless the critical value drops
strictly. -/
theorem morseTrajectorySlice_eq_empty_of_le (hfd : Differentiable ℝ f)
    {hf : LipschitzWith K (∇ f)} {p q : E} (hpq : p ≠ q) (hqp : f p ≤ f q) :
    morseTrajectorySlice hf p q = ∅ :=
  eq_empty_of_forall_notMem fun _ hz ↦
    (value_lt_of_mem_morseTrajectorySlice hfd hpq hz).not_ge hqp

/-- The canonical middle-level trajectory slice is finite for points of consecutive index under
compact-sublevel and Morse--Smale hypotheses. It is empty unless the critical value drops
(`morseTrajectorySlice_eq_empty_of_le`). -/
theorem finite_morseTrajectorySlice_of_isCompact_sublevel
    (hfs : ContDiff ℝ 2 f) (hf : LipschitzWith K (∇ f))
    (hM : HasNondegenerateCriticalPointsOn f univ)
    (hcompact : ∀ c : ℝ, IsCompact {z | f z ≤ c}) {p q : E}
    (hind : morseIndex f p = morseIndex f q + 1) (htr : IsMorseSmale f hf) :
    (morseTrajectorySlice hf p q).Finite := by
  by_cases hqp : f q < f p
  · exact finite_unstableSet_inter_stableSet_inter_level_of_isCompact_sublevel
      hfs hf hM hcompact hind (c := (f p + f q) / 2) (by constructor <;> linarith) htr
  · have hpq : p ≠ q := fun h ↦ by simp [h] at hind
    exact morseTrajectorySlice_eq_empty_of_le (hfs.differentiable (by norm_num)) hpq
      (not_lt.1 hqp) ▸ finite_empty

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
drops by one; otherwise it counts the canonical middle-level trajectory slice modulo two. That
slice is empty unless the critical value strictly decreases, so the coefficient vanishes in that
case too (`morseBoundaryCoeff_eq_zero_of_value_le`). -/
noncomputable def morseBoundaryCoeff (p q : MorseCriticalPoint f) : ZMod 2 :=
  if hind : morseIndex f p = morseIndex f q + 1 then
    morseTrajectoryCount hf p q
      (finite_morseTrajectorySlice_of_isCompact_sublevel hfs hf hM hcompact hind htr)
  else 0

/-- When the endpoints have consecutive index, the boundary coefficient is the parity of the
middle-level trajectory slice. -/
theorem morseBoundaryCoeff_eq_trajectoryCount (p q : MorseCriticalPoint f)
    (hind : morseIndex f p = morseIndex f q + 1) :
    morseBoundaryCoeff hfs hf hM hcompact htr p q =
      morseTrajectoryCount hf p q
        (finite_morseTrajectorySlice_of_isCompact_sublevel hfs hf hM hcompact hind htr) := by
  simp only [morseBoundaryCoeff, dite_eq_left hind]

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
  · have hpq : (p : E) ≠ q := fun h ↦ by simp [h] at hind
    rw [morseBoundaryCoeff_eq_trajectoryCount hfs hf hM hcompact htr p q hind,
      morseTrajectoryCount_eq_ncard, morseTrajectorySlice_eq_empty_of_le
        (hfs.differentiable (by norm_num)) hpq hqp, ncard_empty, Nat.cast_zero]
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
    f q < f p :=
  lt_of_not_ge fun hqp ↦
    hcoeff (morseBoundaryCoeff_eq_zero_of_value_le hfs hf hM hcompact htr p q hqp)

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
