/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.LinearFormExponent
public import TauCeti.NumberTheory.Height.Naive
-- Proof-only: Northcott finiteness for the naive height.
import TauCeti.NumberTheory.Height.Counting

/-!
# Approximation by algebraic numbers of bounded degree

For `n : ℕ` and `ξ : ℝ`, the exponent `algebraicApproximationExponent n ξ`, usually written
`w*ₙ(ξ)`, is the supremum of the real exponents `w` for which infinitely many complex algebraic
numbers `α` of degree at most `n` satisfy `0 < |ξ - α| ≤ H(α) ^ (-w - 1)`, where `H(α)` is the
naive height of `α`, the largest absolute value of a coefficient of its primitive integer minimal
polynomial. The supremum is taken in `ℝ≥0∞`, so negative exponents contribute `0`.

Where Mahler's exponent `wₙ(ξ)` measures how small nonzero values `P(ξ)` of integer polynomials
of degree at most `n` can be, Koksma's exponent `w*ₙ(ξ)` measures how closely `ξ` is approximated
by the roots of such polynomials.

## Main results

* `algebraicApproximation_infinite_iff_allow_eq`: allowing the exact approximation `α = ξ` does
  not change whether there are infinitely many approximations.
* `algebraicApproximationExponent_mono`: `w*ₙ(ξ)` is monotone in `n`, and
  `algebraicApproximationExponent_zero`: it vanishes for `n = 0`.
* `algebraicApproximationExponent_le_mahlerExponent`: `w*ₙ(ξ) ≤ wₙ(ξ)` for every real `ξ`, with
  no hypothesis on `ξ`: the conjugates of an algebraic `ξ` are only finitely many approximations.
* `algebraicApproximationExponent_one_add`: `w*₁(ξ) + 1 = μ(ξ)`, where `μ` is the irrationality
  exponent.

## References

* Y. Bugeaud, *Exponents of Diophantine approximation*, §2, Definition 2.1 and Theorem 2.5.
* J.-H. Evertse, *Diophantine Approximation* (2019), ch. 7, Theorem 7.8.
-/

public section

open Polynomial Filter
open scoped ENNReal

namespace TauCeti

/-- The complex algebraic numbers `α` of degree at most `n` with
`0 < |ξ - α| ≤ H(α) ^ (-w - 1)`, where `H(α)` is the naive height of `α`. -/
def algebraicApproximations (n : ℕ) (ξ w : ℝ) : Set ℂ :=
  {α | IsAlgebraic ℚ α ∧ (minpoly ℚ α).natDegree ≤ n ∧ 0 < ‖(ξ : ℂ) - α‖ ∧
    ‖(ξ : ℂ) - α‖ ≤ naiveHeight α ^ (-w - 1)}

/-- Membership in `algebraicApproximations n ξ w` unfolds to its four defining conditions. -/
@[simp]
theorem mem_algebraicApproximations {n : ℕ} {ξ w : ℝ} {α : ℂ} :
    α ∈ algebraicApproximations n ξ w ↔ IsAlgebraic ℚ α ∧ (minpoly ℚ α).natDegree ≤ n ∧
      0 < ‖(ξ : ℂ) - α‖ ∧ ‖(ξ : ℂ) - α‖ ≤ naiveHeight α ^ (-w - 1) :=
  Iff.rfl

/-- The sets of approximations shrink as the exponent grows. -/
theorem algebraicApproximations_antitone (n : ℕ) (ξ : ℝ) :
    Antitone (algebraicApproximations n ξ) := fun _ _ hww' _ hα ↦
  ⟨hα.1, hα.2.1, hα.2.2.1, hα.2.2.2.trans
    (Real.rpow_le_rpow_of_exponent_le (one_le_naiveHeight _) (by linarith))⟩

/-- The sets of approximations grow with the permitted degree. -/
theorem algebraicApproximations_mono (ξ w : ℝ) :
    Monotone (algebraicApproximations · ξ w) := fun _ _ hmn _ hα ↦
  ⟨hα.1, hα.2.1.trans hmn, hα.2.2⟩

/-- Allowing the exact approximation `α = ξ` changes the set of approximations by at most the
point `ξ`, so it does not change whether the set is infinite. -/
theorem algebraicApproximation_infinite_iff_allow_eq (n : ℕ) (ξ w : ℝ) :
    (algebraicApproximations n ξ w).Infinite ↔
      {α : ℂ | IsAlgebraic ℚ α ∧ (minpoly ℚ α).natDegree ≤ n ∧
        ‖(ξ : ℂ) - α‖ ≤ naiveHeight α ^ (-w - 1)}.Infinite := by
  constructor
  · refine fun h ↦ h.mono fun α hα ↦ ?_
    rw [mem_algebraicApproximations] at hα
    exact ⟨hα.1, hα.2.1, hα.2.2.2⟩
  · refine fun h ↦ (h.sdiff (Set.finite_singleton (ξ : ℂ))).mono fun α hα ↦ ?_
    obtain ⟨⟨halg, hdeg, hle⟩, hne⟩ := hα
    exact ⟨halg, hdeg, norm_pos_iff.2 (sub_ne_zero.2 fun h ↦ hne h.symm), hle⟩

/-- The exponent `w*ₙ(ξ)` of approximation of `ξ` by algebraic numbers of degree at most `n`: the
supremum, in `ℝ≥0∞`, of the real exponents `w` for which infinitely many complex algebraic numbers
`α` of degree at most `n` satisfy `0 < |ξ - α| ≤ H(α) ^ (-w - 1)`, where `H(α)` is the naive
height. Negative exponents contribute `0`. -/
noncomputable def algebraicApproximationExponent (n : ℕ) (ξ : ℝ) : ℝ≥0∞ :=
  ⨆ (w : ℝ) (_ : (algebraicApproximations n ξ w).Infinite), ENNReal.ofReal w

/-- The exponent `w*ₙ(ξ)` is the supremum of `ENNReal.ofReal w` over the exponents `w` with
infinitely many approximations. -/
theorem algebraicApproximationExponent_def (n : ℕ) (ξ : ℝ) :
    algebraicApproximationExponent n ξ =
      ⨆ (w : ℝ) (_ : (algebraicApproximations n ξ w).Infinite), ENNReal.ofReal w :=
  (rfl)

/-- An exponent with infinitely many approximations is at most `w*ₙ(ξ)`. -/
theorem le_algebraicApproximationExponent_of_infinite {n : ℕ} {ξ w : ℝ}
    (h : (algebraicApproximations n ξ w).Infinite) :
    ENNReal.ofReal w ≤ algebraicApproximationExponent n ξ :=
  le_iSup₂_of_le w h le_rfl

/-- The exponent `w*ₙ(ξ)` is bounded by `a` exactly when every exponent with infinitely many
approximations maps below `a`. -/
theorem algebraicApproximationExponent_le_iff {n : ℕ} {ξ : ℝ} {a : ℝ≥0∞} :
    algebraicApproximationExponent n ξ ≤ a ↔
      ∀ w : ℝ, (algebraicApproximations n ξ w).Infinite → ENNReal.ofReal w ≤ a := by
  simp [algebraicApproximationExponent]

/-- A real exponent strictly below `w*ₙ(ξ)` has infinitely many approximations. -/
theorem infinite_algebraicApproximations_of_lt {n : ℕ} {ξ w : ℝ}
    (h : ENNReal.ofReal w < algebraicApproximationExponent n ξ) :
    (algebraicApproximations n ξ w).Infinite := by
  rw [algebraicApproximationExponent, lt_iSup_iff] at h
  obtain ⟨w', hw'⟩ := h
  rw [lt_iSup_iff] at hw'
  obtain ⟨hinf, hlt⟩ := hw'
  exact hinf.mono
    (algebraicApproximations_antitone n ξ (ENNReal.ofReal_lt_ofReal_iff'.mp hlt).1.le)

/-- The exponent `w*ₙ(ξ)` is monotone in the degree `n`. -/
theorem algebraicApproximationExponent_mono (ξ : ℝ) :
    Monotone (algebraicApproximationExponent · ξ) := fun _ _ hmn ↦
  algebraicApproximationExponent_le_iff.2 fun w hw ↦
    le_algebraicApproximationExponent_of_infinite (hw.mono (algebraicApproximations_mono ξ w hmn))

/-- There are no algebraic numbers of degree `0`, so `w*₀(ξ) = 0`. -/
@[simp]
theorem algebraicApproximationExponent_zero (ξ : ℝ) : algebraicApproximationExponent 0 ξ = 0 := by
  refine le_antisymm (algebraicApproximationExponent_le_iff.2 fun w hw ↦ absurd ?_ hw) bot_le
  refine Set.finite_empty.subset fun α hα ↦ ?_
  exact absurd hα.2.1 (minpoly.natDegree_pos hα.1.isIntegral).not_ge

/-! ### Comparison with Mahler's exponent -/

/-- If infinitely many algebraic numbers of degree at most `n` approximate `ξ` with exponent `w`,
then for every `0 ≤ w' < w` infinitely many integer polynomials `P` of degree at most `n` satisfy
`0 < |P(ξ)| ≤ H(P) ^ (-w')`: the primitive minimal polynomials of all but finitely many of the
approximations. -/
private theorem infinite_linearFormApproximations_of_infinite {n : ℕ} {ξ w w' : ℝ}
    (hw' : 0 ≤ w') (hww' : w' < w) (h : (algebraicApproximations n ξ w).Infinite) :
    (linearFormApproximations (fun j : Fin n ↦ ξ ^ (j.val + 1)) w').Infinite := by
  set K : ℝ := (n + 1) * (2 + |ξ|) ^ n
  obtain ⟨R, hR⟩ := eventually_atTop.1 <|
    (tendsto_rpow_atTop (sub_pos.2 hww')).eventually_ge_atTop K
  -- Discard the conjugates of `ξ` and the finitely many approximations of height at most `R`.
  set S := algebraicApproximations n ξ w \ ((minpoly ℚ ξ).rootSet ℂ ∪
    {α : ℂ | IsAlgebraic ℚ α ∧ (minpoly ℚ α).natDegree ≤ n ∧ naiveHeight α ≤ R})
  have hS : S.Infinite :=
    h.sdiff (((minpoly ℚ ξ).rootSet_finite ℂ).union (finite_setOf_naiveHeight_le n R).1)
  -- Each polynomial has finitely many roots, so the primitive minimal polynomials of `S` form an
  -- infinite set.
  have hT : (primitiveMinpoly '' S).Infinite := fun hfin ↦
    hS <| (hfin.biUnion fun P _ ↦ P.rootSet_finite ℂ).subset fun α hα ↦
      Set.mem_biUnion (Set.mem_image_of_mem _ hα)
        (mem_rootSet.2 ⟨primitiveMinpoly_ne_zero α, aeval_primitiveMinpoly hα.1.1⟩)
  have hinj : Set.InjOn (coeffVec n) (primitiveMinpoly '' S) := (coeffVec_injOn n).mono <| by
    rintro _ ⟨α, hα, rfl⟩
    simpa using hα.1.2.1
  refine (hT.image hinj).mono ?_
  rintro _ ⟨_, ⟨α, ⟨⟨halg, hdeg, -, hle⟩, hα⟩, rfl⟩, rfl⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_le] at hα
  obtain ⟨hconj, hR'⟩ := hα
  set H := naiveHeight α
  have hH : R < H := hR' halg hdeg
  have hH₁ : 1 ≤ H := one_le_naiveHeight α
  have hH₀ : 0 < H := zero_lt_one.trans_le hH₁
  have hdegP : (primitiveMinpoly α).natDegree ≤ n := by rwa [natDegree_primitiveMinpoly]
  set x := coeffVec n (primitiveMinpoly α)
  have hL : (x.1 : ℝ) + ∑ j, (x.2 j : ℝ) * ξ ^ (j.val + 1) = aeval ξ (primitiveMinpoly α) :=
    coeffVec_linearForm hdegP ξ
  have hLℂ : ‖aeval (ξ : ℂ) (primitiveMinpoly α)‖ = |aeval ξ (primitiveMinpoly α)| := by
    simpa using congrArg norm (aeval_algebraMap_apply ℂ ξ (primitiveMinpoly α))
  -- `F_α(ξ) ≠ 0`, since otherwise `α` would be a conjugate of `ξ`.
  have hne : aeval ξ (primitiveMinpoly α) ≠ 0 := fun h₀ ↦ hconj <| by
    rw [← minpoly_eq_of_aeval_primitiveMinpoly_eq_zero halg h₀, mem_rootSet]
    exact ⟨minpoly.ne_zero halg.isIntegral, minpoly.aeval ℚ α⟩
  have hx₀ : x ≠ 0 := fun hx ↦ hne (by rw [← hL, hx]; simp)
  have hξα : ‖(ξ : ℂ) - α‖ ≤ 1 :=
    hle.trans (Real.rpow_le_one_of_one_le_of_nonpos hH₁ (by linarith))
  rw [mem_linearFormApproximations, hL]
  refine ⟨abs_pos.2 hne, ?_⟩
  have hK : ((minpoly ℚ α).natDegree + 1) * (2 + ‖(ξ : ℂ)‖) ^ (minpoly ℚ α).natDegree ≤ K := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [K]
    gcongr
    linarith [abs_nonneg ξ]
  calc |aeval ξ (primitiveMinpoly α)| ≤ K * H * ‖(ξ : ℂ) - α‖ := by
        rw [← hLℂ]
        refine (norm_aeval_primitiveMinpoly_le halg hξα).trans ?_
        gcongr
    _ ≤ K * H * H ^ (-w - 1) := by gcongr
    _ = K * H ^ (-w) := by
        rw [Real.rpow_sub_one hH₀.ne']
        field_simp
    _ ≤ H ^ (w - w') * H ^ (-w) := by
        gcongr
        exact hR H hH.le
    _ = H ^ (-w') := by
        rw [← Real.rpow_add hH₀]
        ring_nf
    _ ≤ ‖x‖ ^ (-w') :=
        Real.rpow_le_rpow_of_nonpos (norm_pos_iff.2 hx₀)
          ((norm_coeffVec_le n _).trans_eq (naiveHeight_def α).symm) (neg_nonpos.2 hw')

/-- **Approximation by algebraic numbers versus small polynomial values** (Bugeaud,
Theorem 2.5). For every real `ξ` and every `n`, Koksma's exponent is at most Mahler's exponent:
`w*ₙ(ξ) ≤ wₙ(ξ)`. -/
theorem algebraicApproximationExponent_le_mahlerExponent (n : ℕ) (ξ : ℝ) :
    algebraicApproximationExponent n ξ ≤ mahlerExponent n ξ := by
  refine algebraicApproximationExponent_le_iff.2 fun w hw ↦ le_of_forall_lt fun c hc ↦ ?_
  have hct : c ≠ ⊤ := hc.ne_top
  have hcw : c.toReal < w := (ENNReal.lt_ofReal_iff_toReal_lt hct).1 hc
  have hc₀ : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  calc c < ENNReal.ofReal ((c.toReal + w) / 2) :=
        (ENNReal.lt_ofReal_iff_toReal_lt hct).2 (by linarith)
    _ ≤ mahlerExponent n ξ := by
        rw [mahlerExponent_def]
        exact le_linearFormExponent_of_infinite
          (infinite_linearFormApproximations_of_infinite (by linarith) (by linarith) hw)

/-! ### Approximation by rational numbers -/

/-- If infinitely many rational numbers `s` satisfy `|ξ - s| < s.den ^ (-p)`, then for every
`0 < r < p` infinitely many rational numbers approximate `ξ` with `0 < |ξ - s| ≤ H(s) ^ (-r)`. -/
private theorem infinite_algebraicApproximations_one_of_infinite {ξ p r : ℝ} (hr : 0 < r)
    (hrp : r < p) (h : {s : ℚ | |ξ - s| < (s.den : ℝ) ^ (-p)}.Infinite) :
    (algebraicApproximations 1 ξ (r - 1)).Infinite := by
  set C : ℝ := (|ξ| + 1) ^ (-r)
  obtain ⟨N, hN⟩ := eventually_atTop.1 <|
    ((tendsto_rpow_neg_atTop (sub_pos.2 hrp)).comp tendsto_natCast_atTop_atTop).eventually
      (ge_mem_nhds (by positivity : 0 < C))
  -- Discard the exact approximation and the finitely many fractions with denominator at most `N`.
  have hB := ((Metric.isBounded_ball (x := ξ) (r := 1)).finite_setOf_rat_den_le N).union
    ((Set.subsingleton_singleton (a := ξ)).preimage Rat.cast_injective).finite
  refine ((h.sdiff hB).image (Rat.cast_injective (α := ℂ)).injOn).mono ?_
  rintro _ ⟨s, ⟨hs, hsB⟩, rfl⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, not_or,
    not_and, Metric.mem_ball, Real.dist_eq] at hs hsB
  obtain ⟨hden, hne⟩ := hsB
  have hd₁ : (1 : ℝ) ≤ s.den := by exact_mod_cast s.pos
  have hd₀ : (0 : ℝ) < s.den := zero_lt_one.trans_le hd₁
  have hsξ : |(s : ℝ) - ξ| < 1 := by
    rw [abs_sub_comm]
    exact hs.trans_le (Real.rpow_le_one_of_one_le_of_nonpos hd₁ (by linarith))
  have hdN : N ≤ s.den := (not_le.1 fun h ↦ hden h hsξ).le
  -- The naive height of `s` is at most `(|ξ| + 1) s.den`.
  have hH : naiveHeight (s : ℂ) ≤ (|ξ| + 1) * s.den := by
    rw [naiveHeight_ratCast]
    refine max_le ?_ (le_mul_of_one_le_left hd₀.le (by linarith [abs_nonneg ξ]))
    have hnum : (s.num.natAbs : ℝ) = |(s : ℝ)| * s.den := by
      have h₁ : (s.num : ℝ) = (s : ℝ) * s.den := by exact_mod_cast (Rat.mul_den_eq_num s).symm
      rw [Nat.cast_natAbs, Int.cast_abs, h₁, abs_mul, abs_of_pos hd₀]
    rw [hnum]
    gcongr
    have := abs_sub_abs_le_abs_sub (s : ℝ) ξ
    linarith
  have hH₀ : 0 < naiveHeight (s : ℂ) := zero_lt_one.trans_le (one_le_naiveHeight _)
  have hnorm : ‖(ξ : ℂ) - (s : ℂ)‖ = |ξ - s| := by
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨isAlgebraic_ratCast ℚ s, ?_, ?_, ?_⟩
  · rw [← eq_ratCast (algebraMap ℚ ℂ), minpoly.eq_X_sub_C, natDegree_X_sub_C]
  · rw [hnorm]
    exact abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  rw [hnorm, show -(r - 1) - 1 = -r by ring]
  calc |ξ - s| ≤ (s.den : ℝ) ^ (-p) := hs.le
    _ = (s.den : ℝ) ^ (r - p) * (s.den : ℝ) ^ (-r) := by
        rw [← Real.rpow_add hd₀]
        ring_nf
    _ ≤ C * (s.den : ℝ) ^ (-r) := by
        gcongr
        simpa [neg_sub] using hN s.den hdN
    _ = ((|ξ| + 1) * s.den) ^ (-r) := by
        rw [Real.mul_rpow (by positivity) hd₀.le]
    _ ≤ naiveHeight (s : ℂ) ^ (-r) :=
        Real.rpow_le_rpow_of_nonpos hH₀ hH (neg_nonpos.2 hr.le)

/-- **Koksma's exponent in degree one** (Bugeaud, §2). For every real `ξ`, the exponent of
approximation by rational numbers measured with the naive height is the irrationality exponent
minus one: `w*₁(ξ) + 1 = μ(ξ)`. Both sides equal `1` for rational `ξ`. -/
theorem algebraicApproximationExponent_one_add (ξ : ℝ) :
    algebraicApproximationExponent 1 ξ + 1 = irrationalityExponent ξ := by
  refine le_antisymm ?_ ?_
  · rw [← mahlerExponent_one_add_one]
    gcongr
    exact algebraicApproximationExponent_le_mahlerExponent 1 ξ
  rw [irrationalityExponent_eq_iSup_infinite]
  refine iSup₂_le fun p hp ↦ ?_
  rcases le_or_gt p 1 with hp₁ | hp₁
  · exact (ENNReal.ofReal_le_ofReal hp₁).trans (by simp)
  -- Approximate `ENNReal.ofReal p` from below by exponents `r` with `1 < r < p`.
  refine le_of_forall_lt fun c hc ↦ ?_
  have hct : c ≠ ⊤ := hc.ne_top
  have hcp : c.toReal < p := (ENNReal.lt_ofReal_iff_toReal_lt hct).1 hc
  obtain ⟨r, hr_def⟩ : ∃ r, r = (max c.toReal 1 + p) / 2 := ⟨_, rfl⟩
  have hmax : max c.toReal 1 < p := max_lt hcp hp₁
  have hr : 1 < r := by linarith [le_max_right c.toReal 1]
  calc c < ENNReal.ofReal r :=
        (ENNReal.lt_ofReal_iff_toReal_lt hct).2 (by linarith [le_max_left c.toReal 1])
    _ = ENNReal.ofReal (r - 1) + 1 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one, sub_add_cancel]
    _ ≤ algebraicApproximationExponent 1 ξ + 1 := by
        gcongr
        exact le_algebraicApproximationExponent_of_infinite
          (infinite_algebraicApproximations_one_of_infinite (by linarith) (by linarith) hp)

end TauCeti
