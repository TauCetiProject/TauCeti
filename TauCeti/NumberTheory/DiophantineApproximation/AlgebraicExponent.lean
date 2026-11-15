/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.LinearFormExponent
public import TauCeti.NumberTheory.Height.Naive
-- Proof-only: Northcott finiteness, Möbius identities and field invariance, and Mahler's exponent
-- at rationals.
import TauCeti.Algebra.Field.LinearFractional
import TauCeti.FieldTheory.IntermediateField.Adjoin.Mobius
import TauCeti.NumberTheory.DiophantineApproximation.MahlerExponent
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

Like `irrationalityExponent` and `mahlerExponent n`, Koksma's exponent `w*ₙ` is invariant under
rational Möbius transformations `ξ ↦ (a ξ + b) / (c ξ + d)` of nonzero determinant `a d - b c`:
nonsingular rational Möbius transformations preserve degree over `ℚ`, distort distances near `ξ`
by a bounded factor away from the pole, and change the naive height by at most a constant factor
(`TauCeti.naiveHeight_mul_add_div_mul_add_le`).

## Main results

* `algebraicApproximation_infinite_iff_allow_eq`: allowing the exact approximation `α = ξ` does
  not change whether there are infinitely many approximations.
* `algebraicApproximationExponent_mono`: `w*ₙ(ξ)` is monotone in `n`, and
  `algebraicApproximationExponent_zero`: it vanishes for `n = 0`.
* `algebraicApproximationExponent_le_mahlerExponent`: `w*ₙ(ξ) ≤ wₙ(ξ)` for every real `ξ`, with
  no hypothesis on `ξ`: the conjugates of an algebraic `ξ` are only finitely many approximations.
* `algebraicApproximationExponent_one_add`: `w*₁(ξ) + 1 = μ(ξ)`, where `μ` is the irrationality
  exponent.
* `algebraicApproximationExponent_ratCast`: rational numbers have Koksma exponent `0` in every
  degree.
* `algebraicApproximationExponent_mul_add_div_mul_add`: `w*ₙ` is invariant under rational Möbius
  transformations of nonzero determinant; in particular under adding or multiplying by a nonzero
  rational number, negation, and inversion (`algebraicApproximationExponent_add_ratCast`,
  `algebraicApproximationExponent_ratCast_mul`, `algebraicApproximationExponent_neg`,
  `algebraicApproximationExponent_inv`).

## References

* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Chapter 3.
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

/-- For `w' ≥ 0`, the estimate for a single approximation: if `α` is algebraic of degree at most
`n`, is not a conjugate of `ξ`, and approximates `ξ` with exponent `w`, where
`(n + 1) (2 + |ξ|) ^ n ≤ H(α) ^ (w - w')`, then the coefficient vector of its primitive minimal
polynomial is a `w'`-approximation of the linear form in `ξ, ξ², …, ξⁿ`. -/
private theorem coeffVec_primitiveMinpoly_mem_linearFormApproximations {n : ℕ} {ξ w w' : ℝ}
    {α : ℂ} (hw' : 0 ≤ w') (halg : IsAlgebraic ℚ α)
    (hdeg : (minpoly ℚ α).natDegree ≤ n)
    (hle : ‖(ξ : ℂ) - α‖ ≤ naiveHeight α ^ (-w - 1)) (hconj : α ∉ (minpoly ℚ ξ).rootSet ℂ)
    (hR : (n + 1) * (2 + |ξ|) ^ n ≤ naiveHeight α ^ (w - w')) :
    coeffVec n (primitiveMinpoly α) ∈
      linearFormApproximations (fun j : Fin n ↦ ξ ^ (j.val + 1)) w' := by
  set K : ℝ := (n + 1) * (2 + |ξ|) ^ n
  set H := naiveHeight α
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
    rw [← minpoly_eq_of_aeval_primitiveMinpoly_eq_zero h₀, mem_rootSet]
    exact ⟨minpoly.ne_zero halg.isIntegral, minpoly.aeval ℚ α⟩
  have hx₀ : x ≠ 0 := fun hx ↦ hne (by rw [← hL, hx]; simp)
  rw [mem_linearFormApproximations, hL]
  refine ⟨abs_pos.2 hne, ?_⟩
  have hK : ((minpoly ℚ α).natDegree + 1) * (2 + ‖(ξ : ℂ)‖) ^ (minpoly ℚ α).natDegree ≤ K := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [K]
    gcongr
    linarith [abs_nonneg ξ]
  calc |aeval ξ (primitiveMinpoly α)| ≤ K * H * ‖(ξ : ℂ) - α‖ := by
        rw [← hLℂ]
        refine (norm_aeval_primitiveMinpoly_le halg).trans ?_
        gcongr
    _ ≤ K * H * H ^ (-w - 1) := by gcongr
    _ = K * H ^ (-w) := by
        rw [Real.rpow_sub_one hH₀.ne']
        field_simp
    _ ≤ H ^ (w - w') * H ^ (-w) := by
        gcongr
    _ = H ^ (-w') := by
        rw [← Real.rpow_add hH₀]
        ring_nf
    _ ≤ ‖x‖ ^ (-w') :=
        Real.rpow_le_rpow_of_nonpos (norm_pos_iff.2 hx₀)
          ((norm_coeffVec_le n _).trans_eq (naiveHeight_def α).symm) (neg_nonpos.2 hw')

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
  exact coeffVec_primitiveMinpoly_mem_linearFormApproximations hw' halg hdeg hle hconj
    (hR _ (hR' halg hdeg).le)

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

/-- Rational numbers have Koksma exponent `0` in every degree. -/
@[simp]
theorem algebraicApproximationExponent_ratCast (n : ℕ) (q : ℚ) :
    algebraicApproximationExponent n q = 0 :=
  le_antisymm ((algebraicApproximationExponent_le_mahlerExponent n q).trans
    (mahlerExponent_ratCast n q).le) bot_le

/-! ### Invariance under rational Möbius transformations -/

section Mobius

/-- Metric and left-inverse estimates for a complex approximant `α` close to `ξ` under an integer
Möbius transformation of nonzero determinant `a * d - b * c` away from its pole `c ξ + d = 0`. -/
private theorem mobius_sub_and_inv {ξ : ℝ} {a b c d : ℤ} (hdet : a * d - b * c ≠ 0)
    (hξ : (c : ℝ) * ξ + d ≠ 0) {α : ℂ} (hpos : 0 < ‖(ξ : ℂ) - α‖)
    (hclose : ‖(ξ : ℂ) - α‖ ≤ |(c : ℝ) * ξ + d| / (2 * (|(c : ℝ)| + 1))) :
    let ξ' : ℝ := ((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d);
    let β : ℂ := ((a : ℂ) * α + b) / ((c : ℂ) * α + d);
    ((d : ℂ) * β - b) / (-(c : ℂ) * β + a) = α ∧
      0 < ‖(ξ' : ℂ) - β‖ ∧
      ‖(ξ' : ℂ) - β‖ ≤
        (2 * |((a * d - b * c : ℤ) : ℝ)| / |(c : ℝ) * ξ + d| ^ 2) * ‖(ξ : ℂ) - α‖ := by
  intro ξ' β
  set Dξ : ℝ := |(c : ℝ) * ξ + d|
  have hDξ : 0 < Dξ := abs_pos.2 hξ
  have hnorm_ξ : ‖(c : ℂ) * (ξ : ℂ) + d‖ = Dξ := by
    rw [← Complex.ofReal_intCast c, ← Complex.ofReal_intCast d, ← Complex.ofReal_mul,
      ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  have hξ_den : (c : ℂ) * (ξ : ℂ) + d ≠ 0 := norm_pos_iff.mp (hnorm_ξ ▸ hDξ)
  have hden_lb : Dξ / 2 ≤ ‖(c : ℂ) * α + d‖ := by
    have hsub : (c : ℂ) * α + d = ((c : ℂ) * (ξ : ℂ) + d) - (c : ℂ) * ((ξ : ℂ) - α) := by ring
    have htri := norm_sub_norm_le ((c : ℂ) * (ξ : ℂ) + d) ((c : ℂ) * ((ξ : ℂ) - α))
    rw [← hsub, hnorm_ξ, norm_mul, Complex.norm_intCast] at htri
    have hc_le : |(c : ℝ)| * ‖(ξ : ℂ) - α‖ ≤ Dξ / 2 := calc
      |(c : ℝ)| * ‖(ξ : ℂ) - α‖
          ≤ (|(c : ℝ)| + 1) * (Dξ / (2 * (|(c : ℝ)| + 1))) :=
            mul_le_mul (by linarith) hclose (norm_nonneg _) (by positivity)
      _ = Dξ / 2 := by
            have : |(c : ℝ)| + 1 ≠ 0 := by positivity
            field_simp
    linarith
  have hα_den : (c : ℂ) * α + d ≠ 0 := norm_pos_iff.mp (by linarith)
  have hdetC : (a : ℂ) * d - b * c ≠ 0 := by exact_mod_cast hdet
  have hinv : ((d : ℂ) * β - b) / (-(c : ℂ) * β + a) = α := moebius_inv_moebius hdetC hα_den
  have hξ'ℂ : (ξ' : ℂ) = ((a : ℂ) * (ξ : ℂ) + b) / ((c : ℂ) * (ξ : ℂ) + d) := by simp [ξ']
  have hnorm_diff : ‖(ξ' : ℂ) - β‖ =
      |((a * d - b * c : ℤ) : ℝ)| * ‖(ξ : ℂ) - α‖ / (Dξ * ‖(c : ℂ) * α + d‖) := by
    rw [hξ'ℂ, moebius_sub_moebius hα_den hξ_den, ← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub,
      norm_div, norm_mul, norm_mul, hnorm_ξ, Complex.norm_intCast]
  have : 0 < |((a * d - b * c : ℤ) : ℝ)| := abs_pos.2 (Int.cast_ne_zero.mpr hdet)
  refine ⟨hinv, by rw [hnorm_diff]; positivity, ?_⟩
  rw [hnorm_diff]
  calc |((a * d - b * c : ℤ) : ℝ)| * ‖(ξ : ℂ) - α‖ / (Dξ * ‖(c : ℂ) * α + d‖)
      ≤ |((a * d - b * c : ℤ) : ℝ)| * ‖(ξ : ℂ) - α‖ / (Dξ ^ 2 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    _ = (2 * |((a * d - b * c : ℤ) : ℝ)| / Dξ ^ 2) * ‖(ξ : ℂ) - α‖ := by ring

/-- Single-approximant transfer: for `0 < w' < w`, an approximant
`α ∈ algebraicApproximations n ξ w` whose naive height exceeds both
`(|c ξ + d| / (2 (|c| + 1)))⁻¹` and the constant-absorption threshold maps into
`algebraicApproximations n ξ' w'`. -/
private theorem mobius_mem_algebraicApproximations {n : ℕ} {ξ w w' : ℝ} {a b c d : ℤ}
    (hw' : 0 < w') (hww' : w' < w) (hdet : a * d - b * c ≠ 0) (hξ : (c : ℝ) * ξ + d ≠ 0)
    {α : ℂ} (hα : α ∈ algebraicApproximations n ξ w)
    (hH_close : (|(c : ℝ) * ξ + d| / (2 * (|(c : ℝ)| + 1)))⁻¹ ≤ naiveHeight α)
    (hH_abs : (2 * |((a * d - b * c : ℤ) : ℝ)| / |(c : ℝ) * ξ + d| ^ 2) *
      (max 1 ((2 * (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| + |(d : ℝ)|)) ^ n)) ^ (w' + 1) ≤
      naiveHeight α ^ (w - w')) :
    (((a : ℂ) * α + b) / ((c : ℂ) * α + d)) ∈
      algebraicApproximations n (((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)) w' ∧
      ((d : ℂ) * (((a : ℂ) * α + b) / ((c : ℂ) * α + d)) - b) /
        (-(c : ℂ) * (((a : ℂ) * α + b) / ((c : ℂ) * α + d)) + a) = α := by
  obtain ⟨halg, hdeg, hpos, hle⟩ := hα
  set H := naiveHeight α
  have hH₁ : 1 ≤ H := one_le_naiveHeight α
  have hH₀ : 0 < H := zero_lt_one.trans_le hH₁
  have hδ₀ : 0 < |(c : ℝ) * ξ + d| / (2 * (|(c : ℝ)| + 1)) := by
    have := abs_pos.2 hξ; positivity
  have hclose : ‖(ξ : ℂ) - α‖ ≤ |(c : ℝ) * ξ + d| / (2 * (|(c : ℝ)| + 1)) := calc
    ‖(ξ : ℂ) - α‖ ≤ H ^ (-w - 1) := hle
    _ ≤ H ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hH₁ (by linarith)
    _ = H⁻¹ := Real.rpow_neg_one H
    _ ≤ |(c : ℝ) * ξ + d| / (2 * (|(c : ℝ)| + 1)) := inv_le_of_inv_le₀ hδ₀ hH_close
  obtain ⟨hinv, hβ_pos, hβ_le⟩ := mobius_sub_and_inv hdet hξ hpos hclose
  set β : ℂ := ((a : ℂ) * α + b) / ((c : ℂ) * α + d)
  set K₁ : ℝ := 2 * |((a * d - b * c : ℤ) : ℝ)| / |(c : ℝ) * ξ + d| ^ 2
  set M : ℝ := 2 * (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| + |(d : ℝ)|)
  set K₂ : ℝ := max 1 (M ^ n)
  have hK₂ : 0 < K₂ := zero_lt_one.trans_le (le_max_left _ _)
  have hdetQ : (a : ℚ) * d - b * c ≠ 0 := by exact_mod_cast hdet
  have hβ_alg : IsAlgebraic ℚ β := by
    simpa [β] using (isAlgebraic_mul_add_div_mul_add_iff (K := ℚ) α hdetQ).mpr halg
  have hβ_deg : (minpoly ℚ β).natDegree ≤ n := by
    have hdeg_eq : (minpoly ℚ β).natDegree = (minpoly ℚ α).natDegree := by
      simpa [β] using TauCeti.minpoly.natDegree_mul_add_div_mul_add (K := ℚ) α hdetQ
    exact hdeg_eq.trans_le hdeg
  have hHβ : naiveHeight β ≤ K₂ * H := by
    refine (naiveHeight_mul_add_div_mul_add_le α hdet).trans (mul_le_mul_of_nonneg_right ?_ hH₀.le)
    rcases le_or_gt M 1 with hM | hM
    · exact (pow_le_one₀ (by positivity) hM).trans (le_max_left _ _)
    · exact (pow_le_pow_right₀ hM.le hdeg).trans (le_max_right _ _)
  refine ⟨⟨hβ_alg, hβ_deg, hβ_pos, ?_⟩, hinv⟩
  have hK₁ : 0 ≤ K₁ := by
    have := abs_pos.2 hξ; positivity
  have hexp : w - w' + (-w - 1) = -w' - 1 := by ring
  calc ‖((((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d) : ℝ) : ℂ) - β‖
      ≤ K₁ * H ^ (-w - 1) := hβ_le.trans (mul_le_mul_of_nonneg_left hle hK₁)
    _ = K₁ * K₂ ^ (w' + 1) * K₂ ^ (-w' - 1) * H ^ (-w - 1) := by
        rw [mul_assoc K₁, ← Real.rpow_add hK₂]
        ring_nf
        simp
    _ ≤ H ^ (w - w') * K₂ ^ (-w' - 1) * H ^ (-w - 1) := by gcongr
    _ = (K₂ * H) ^ (-w' - 1) := by
        rw [mul_right_comm, ← Real.rpow_add hH₀, hexp, mul_comm, Real.mul_rpow hK₂.le hH₀.le]
    _ ≤ naiveHeight β ^ (-w' - 1) :=
        Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le (one_le_naiveHeight β)) hHβ
          (by linarith)

/-- Infinitely many `w`-approximations of `ξ` yield infinitely many `w'`-approximations of
`(a ξ + b) / (c ξ + d)` for every `0 < w' < w`. -/
private theorem infinite_algebraicApproximations_of_mobius_int {n : ℕ} {ξ w w' : ℝ}
    {a b c d : ℤ} (hw' : 0 < w') (hww' : w' < w) (hdet : a * d - b * c ≠ 0)
    (hξ : (c : ℝ) * ξ + d ≠ 0) (hinf : (algebraicApproximations n ξ w).Infinite) :
    (algebraicApproximations n (((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)) w').Infinite := by
  set K₁ : ℝ := 2 * |((a * d - b * c : ℤ) : ℝ)| / |(c : ℝ) * ξ + d| ^ 2
  set K₂ : ℝ := max 1 ((2 * (|(a : ℝ)| + |(b : ℝ)| + |(c : ℝ)| + |(d : ℝ)|)) ^ n)
  set δ₀ : ℝ := |(c : ℝ) * ξ + d| / (2 * (|(c : ℝ)| + 1))
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 <|
    (tendsto_rpow_atTop (sub_pos.2 hww')).eventually_ge_atTop (K₁ * K₂ ^ (w' + 1))
  set R : ℝ := max δ₀⁻¹ R₁
  set S := algebraicApproximations n ξ w \
    {α : ℂ | IsAlgebraic ℚ α ∧ (minpoly ℚ α).natDegree ≤ n ∧ naiveHeight α ≤ R}
  have hS : S.Infinite := hinf.sdiff (finite_setOf_naiveHeight_le n R).1
  set f : ℂ → ℂ := fun α ↦ ((a : ℂ) * α + b) / ((c : ℂ) * α + d)
  have hmem : ∀ α ∈ S, f α ∈ algebraicApproximations n
      (((a : ℝ) * ξ + b) / ((c : ℝ) * ξ + d)) w' ∧
      ((d : ℂ) * f α - b) / (-(c : ℂ) * f α + a) = α := by
    rintro α ⟨hα, hnot⟩
    simp only [Set.mem_ofPred_eq, not_and, not_le] at hnot
    have hHR : R < naiveHeight α := hnot hα.1 hα.2.1
    exact mobius_mem_algebraicApproximations hw' hww' hdet hξ hα
      ((le_max_left _ _).trans hHR.le) (hR₁ _ ((le_max_right _ _).trans hHR.le))
  have hinj : Set.InjOn f S := fun α₁ h₁ α₂ h₂ heq ↦ by
    rw [← (hmem α₁ h₁).2, ← (hmem α₂ h₂).2, heq]
  refine (hS.image hinj).mono fun _ h ↦ ?_
  obtain ⟨α, hα, rfl⟩ := h
  exact (hmem α hα).1

/-- One-sided Koksma-exponent inequality under an integer Möbius transformation away from its
pole. -/
private theorem algebraicApproximationExponent_le_mul_add_div_mul_add_of_int (n : ℕ) {ξ : ℝ}
    {a b c d : ℤ} (hdet : a * d - b * c ≠ 0) (hξ : (c : ℝ) * ξ + d ≠ 0) :
    algebraicApproximationExponent n ξ ≤
      algebraicApproximationExponent n ((a * ξ + b) / (c * ξ + d)) := by
  refine algebraicApproximationExponent_le_iff.2 fun w hw ↦ ?_
  rcases le_or_gt w 0 with hw₀ | hw₀
  · simp [ENNReal.ofReal_eq_zero.2 hw₀]
  refine le_of_forall_lt fun t ht ↦ ?_
  have htt : t ≠ ⊤ := ht.ne_top
  have htw : t.toReal < w := (ENNReal.lt_ofReal_iff_toReal_lt htt).1 ht
  have ht₀ : 0 ≤ t.toReal := ENNReal.toReal_nonneg
  calc t < ENNReal.ofReal ((t.toReal + w) / 2) :=
        (ENNReal.lt_ofReal_iff_toReal_lt htt).2 (by linarith)
    _ ≤ algebraicApproximationExponent n ((a * ξ + b) / (c * ξ + d)) :=
        le_algebraicApproximationExponent_of_infinite
          (infinite_algebraicApproximations_of_mobius_int (by linarith) (by linarith) hdet hξ hw)

/-- Koksma's exponent is invariant under a Möbius transformation with integer coefficients and
nonzero determinant away from its pole. -/
private theorem algebraicApproximationExponent_mul_add_div_mul_add_of_int (n : ℕ) {ξ : ℝ}
    {a b c d : ℤ} (hdet : a * d - b * c ≠ 0) (hξ : (c : ℝ) * ξ + d ≠ 0) :
    algebraicApproximationExponent n ((a * ξ + b) / (c * ξ + d)) =
      algebraicApproximationExponent n ξ := by
  refine le_antisymm ?_ (algebraicApproximationExponent_le_mul_add_div_mul_add_of_int n hdet hξ)
  set η : ℝ := (a * ξ + b) / (c * ξ + d)
  have hdetR : (a : ℝ) * d - b * c ≠ 0 := by exact_mod_cast hdet
  have hη : ((-c : ℤ) : ℝ) * η + a ≠ 0 := by
    simpa using neg_mul_moebius_add_ne_zero hdetR hξ
  have hinv : ((d : ℝ) * η + ((-b : ℤ) : ℝ)) / (((-c : ℤ) : ℝ) * η + a) = ξ := by
    simpa [sub_eq_add_neg] using moebius_inv_moebius hdetR hξ
  have hdet' : d * a - (-b) * (-c) ≠ 0 := fun h0 ↦ hdet (by linear_combination h0)
  have := algebraicApproximationExponent_le_mul_add_div_mul_add_of_int n (ξ := η) hdet' hη
  rwa [hinv] at this

/-- **Möbius invariance of Koksma's exponent.** For rational `a, b, c, d` with `a d - b c ≠ 0`,
`w*ₙ((a ξ + b) / (c ξ + d)) = w*ₙ(ξ)`. At the pole `ξ = -d / c`, where Lean's convention
`x / 0 = 0` applies, both sides vanish because both points are rational. -/
theorem algebraicApproximationExponent_mul_add_div_mul_add (n : ℕ) (ξ : ℝ) {a b c d : ℚ}
    (h : a * d - b * c ≠ 0) :
    algebraicApproximationExponent n ((a * ξ + b) / (c * ξ + d)) =
      algebraicApproximationExponent n ξ := by
  by_cases hξ : (c : ℝ) * ξ + d = 0
  · -- At the pole `ξ = -d / c`, both `ξ` and its image `0` are rational.
    have hc : c ≠ 0 := by
      rintro rfl
      have hd : d = 0 := by exact_mod_cast (by simpa using hξ : (d : ℝ) = 0)
      simp [hd] at h
    have hxq : ξ = ((-d / c : ℚ) : ℝ) := by
      have hc' : (c : ℝ) ≠ 0 := Rat.cast_ne_zero.2 hc
      push_cast
      field_simp
      linarith
    rw [hξ, div_zero, hxq, ← Rat.cast_zero, algebraicApproximationExponent_ratCast,
      algebraicApproximationExponent_ratCast]
  -- Scale `(a, b, c, d)` by the product `m` of their denominators to obtain integer coefficients.
  have hscale (q : ℚ) (k : ℕ) : ((q.num * (k : ℤ) : ℤ) : ℝ) = ((q.den * k : ℕ) : ℝ) * q := by
    have hQ : ((q.num * (k : ℤ) : ℤ) : ℚ) = (q.den * k : ℕ) * q := by
      push_cast
      linear_combination (k : ℚ) * (Rat.mul_den_eq_num q).symm
    exact_mod_cast hQ
  set m : ℕ := a.den * b.den * c.den * d.den
  have hm : (m : ℝ) ≠ 0 := by positivity
  let a' : ℤ := a.num * ((b.den * c.den * d.den : ℕ) : ℤ)
  let b' : ℤ := b.num * ((a.den * c.den * d.den : ℕ) : ℤ)
  let c' : ℤ := c.num * ((a.den * b.den * d.den : ℕ) : ℤ)
  let d' : ℤ := d.num * ((a.den * b.den * c.den : ℕ) : ℤ)
  have ha' : (a' : ℝ) = m * a := by rw [hscale]; push_cast [m]; ring
  have hb' : (b' : ℝ) = m * b := by rw [hscale]; push_cast [m]; ring
  have hc' : (c' : ℝ) = m * c := by rw [hscale]; push_cast [m]; ring
  have hd' : (d' : ℝ) = m * d := by rw [hscale]; push_cast [m]; ring
  have hdet : a' * d' - b' * c' ≠ 0 := fun h0 ↦ by
    have hR : ((a * d - b * c : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.2 h
    push_cast at hR
    have h0R : (a' : ℝ) * d' - b' * c' = 0 := by exact_mod_cast h0
    rw [ha', hb', hc', hd'] at h0R
    exact mul_ne_zero (pow_ne_zero 2 hm) hR (by linear_combination h0R)
  have hden : (c' : ℝ) * ξ + d' = m * (c * ξ + d) := by rw [hc', hd']; ring
  have hnum : (a' : ℝ) * ξ + b' = m * (a * ξ + b) := by rw [ha', hb']; ring
  have key : ((a : ℝ) * ξ + b) / (c * ξ + d) = (a' * ξ + b') / (c' * ξ + d') := by
    rw [hden, hnum, mul_div_mul_left _ _ hm]
  rw [key]
  exact algebraicApproximationExponent_mul_add_div_mul_add_of_int n hdet
    (by rw [hden]; exact mul_ne_zero hm hξ)

/-- Adding a rational number does not change Koksma's exponent. -/
@[simp]
theorem algebraicApproximationExponent_add_ratCast (n : ℕ) (ξ : ℝ) (q : ℚ) :
    algebraicApproximationExponent n (ξ + q) = algebraicApproximationExponent n ξ := by
  simpa using algebraicApproximationExponent_mul_add_div_mul_add n ξ
    (a := 1) (b := q) (c := 0) (d := 1) (by simp)

/-- Multiplying by a nonzero rational number does not change Koksma's exponent. -/
@[simp]
theorem algebraicApproximationExponent_ratCast_mul (n : ℕ) (q : ℚ) (ξ : ℝ) (hq : q ≠ 0) :
    algebraicApproximationExponent n (q * ξ) = algebraicApproximationExponent n ξ := by
  simpa using algebraicApproximationExponent_mul_add_div_mul_add n ξ
    (a := q) (b := 0) (c := 0) (d := 1) (by simpa)

/-- Negation does not change Koksma's exponent. -/
@[simp]
theorem algebraicApproximationExponent_neg (n : ℕ) (ξ : ℝ) :
    algebraicApproximationExponent n (-ξ) = algebraicApproximationExponent n ξ := by
  simpa using algebraicApproximationExponent_ratCast_mul n (-1) ξ (by norm_num)

/-- Inversion does not change Koksma's exponent. -/
@[simp]
theorem algebraicApproximationExponent_inv (n : ℕ) (ξ : ℝ) :
    algebraicApproximationExponent n ξ⁻¹ = algebraicApproximationExponent n ξ := by
  simpa using algebraicApproximationExponent_mul_add_div_mul_add n ξ
    (a := 0) (b := 1) (c := 1) (d := 0) (by simp)

end Mobius

/-! ### Boundary examples -/

/- Neither `mahlerExponent 1` nor `algebraicApproximationExponent 1` equals
`irrationalityExponent`: at `0` both degree-`1` exponents vanish while `irrationalityExponent 0 = 1`
(`w₁(ξ) + 1 = w*₁(ξ) + 1 = μ(ξ)`). -/
example : mahlerExponent 1 (0 : ℝ) ≠ irrationalityExponent 0 ∧
    algebraicApproximationExponent 1 (0 : ℝ) ≠ irrationalityExponent 0 := by
  have hμ : irrationalityExponent 0 = 1 := by
    rw [← algebraicApproximationExponent_one_add, ← Rat.cast_zero,
      algebraicApproximationExponent_ratCast, zero_add]
  rw [hμ, ← Rat.cast_zero, mahlerExponent_ratCast, algebraicApproximationExponent_ratCast]
  exact ⟨zero_ne_one, zero_ne_one⟩

/- The nonzero-determinant hypothesis `a * d - b * c ≠ 0` in
`algebraicApproximationExponent_mul_add_div_mul_add` cannot be dropped: the singular matrix
`a = b = c = 0, d = 1` maps `√2` (with `w*₁(√2) ≥ 1`) to `0` (with `w*₁(0) = 0`). -/
example : ∃ (a b c d : ℚ) (ξ : ℝ),
    algebraicApproximationExponent 1 ((a * ξ + b) / (c * ξ + d)) ≠
      algebraicApproximationExponent 1 ξ := by
  refine ⟨0, 0, 0, 1, √2, ?_⟩
  have h2 : (2 : ℝ≥0∞) ≤ algebraicApproximationExponent 1 √2 + 1 := by
    rw [algebraicApproximationExponent_one_add]
    exact (two_le_irrationalityExponent_iff √2).2 irrational_sqrt_two
  intro heq
  have hzero : (((0 : ℚ) : ℝ) * √2 + (0 : ℚ)) / (((0 : ℚ) : ℝ) * √2 + (1 : ℚ)) =
      ((0 : ℚ) : ℝ) := by norm_num
  rw [hzero, algebraicApproximationExponent_ratCast] at heq
  rw [← heq, zero_add] at h2
  exact absurd h2 (by norm_num)

end TauCeti
