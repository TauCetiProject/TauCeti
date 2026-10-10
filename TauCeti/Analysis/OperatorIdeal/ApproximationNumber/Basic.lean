/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/
module

public import TauCeti.LinearAlgebra.Dimension.RankComp
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Dimension.LinearMap
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Approximation numbers of bounded operators

The **zero-based** approximation number of a continuous linear map `T` at index
`n` is the operator-norm distance from `T` to continuous linear maps of rank
**at most** `n`.  This file develops its elementary order and ideal API over an
arbitrary nontrivially normed field, with independent source and target
universes.

The declarations here deliberately stop before Hilbert-space-specific results:
adjoint invariance, finite-dimensional singular-value identification, and
infinite-dimensional min--max lower bounds live in sibling modules.

## The index convention

The operator-ideal literature is split.  Pietsch's `s`-numbers are one-based,
`sₙ(T) = dist(T, {rank < n})` with `s₁(T) = ‖T‖`; here `aₙ(T)` is zero-based,
`aₙ(T) = dist(T, {rank ≤ n})` with `a₀(T) = ‖T‖`, so `sₙ = a_{n-1}`.  Only one
of the two is developed — carrying both would duplicate the whole API for an
index shift — and the zero-based one is chosen because every downstream
statement is off-by-one free in it:

* the additive ideal inequality is `a_{m+n}(S + T) ≤ aₘ(S) + aₙ(T)`
  (`ContinuousLinearMap.approximationNumber_add_le`), against the one-based
  `s_{m+n-1}`;
* the singular-value identification is `aₙ(T) = σₙ(T)`
  (`ContinuousLinearMap.approximationNumber_eq_singularValues`), a genuine
  identity of indices, because Mathlib's `LinearMap.singularValues` is itself
  zero-indexed; one-based numbering would put an `n - 1` — truncated
  subtraction — into the flagship theorem of the development;
* `a₀(T) = ‖T‖` needs no convention at `n = 0`, whereas the one-based `s₀` has
  to be defined by fiat.

The convention is stated in the first sentence of the definition's docstring
and is recorded as decision 1 of
`TauCetiRoadmap/OperatorTheory/OperatorIdeals/README.md` (Part A generality bar).

## Main declarations

* `ContinuousLinearMap.approximationNumber`: the `n`th zero-based approximation
  number, valued in `ℝ`.
* `ContinuousLinearMap.approximationNumber_le_norm_sub` and
  `ContinuousLinearMap.le_approximationNumber_iff`: the characteristic upper and
  lower bounds.  Together they replace unfolding the definition; the defining
  infimum itself is available as
  `ContinuousLinearMap.approximationNumber_eq_iInf`, which is deliberately not a
  `simp` lemma.
* `ContinuousLinearMap.approximationNumber_index_zero`: the **zeroth**
  approximation number is the operator norm.  The index, not the operator, is
  what is zero here; `ContinuousLinearMap.approximationNumber_zero` is the
  companion statement about the zero operator, matching Mathlib's
  `LinearMap.singularValues_zero`.
* `ContinuousLinearMap.approximationNumber_antitone`: approximation numbers
  decrease with the allowed rank.
* `ContinuousLinearMap.approximationNumber_add_le`,
  `approximationNumber_comp_le_norm_mul`, `approximationNumber_comp_le_mul_norm`,
  `approximationNumber_comp_comp_le`: the additive and two-sided ideal
  inequalities.
* `ContinuousLinearMap.approximationNumber_comp_eq_of_leftInverse`: enlarging the
  codomain along a contraction with a contractive left inverse changes nothing.
* `ContinuousLinearMap.approximationNumber_smul`: absolute homogeneity.

## Namespace note

These declarations extend the existing Mathlib namespace `ContinuousLinearMap`
rather than living under `TauCeti`, so that dot notation
(`T.approximationNumber`) resolves and the names match the eventual Mathlib
upstreaming target (adapted from Mathlib PR #32126). Lean field projection binds
`T.approximationNumber` only to the literal `ContinuousLinearMap.approximationNumber`
and does not consult the enclosing `TauCeti` namespace. This is a deliberate API
choice, flagged for Tau Ceti maintainer review.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/Normed/Operator/ApproximationNumber.lean`
  at Davis--Kahan commit `fc38eb48b9b49f2e1d87fe0c7022dc5e262820a7`.
* Original declarations: `ContinuousLinearMap.approximationNumber` and the order
  and ideal API in the same namespace, plus two pieces of plumbing that have
  since moved out so that this module carries approximation-number API and
  nothing else: the universe helper `Cardinal.le_natCast_of_lift_le` (now the iff
  `Cardinal.lift_le_natCast` in `ForTauCeti/SetTheory/Cardinal/Lift.lean`) and
  the rank-of-composition bounds `rank_comp_left_le_of_rank_le` and
  `rank_comp_right_le_rank` (now `ContinuousLinearMap.rank_comp_le_natCast_right`
  and `ContinuousLinearMap.rank_comp_le_left` in
  `ForTauCeti/LinearAlgebra/Dimension/RankComp.lean`, generalized to
  `LinearMap`).
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss,
  Arnav Mehta, Rawad Kansoh; Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* The Davis--Kahan file was itself adapted from Mathlib PR #32126.
* Extraction class: **copied**, converted to the Tau Ceti module system, then
  renamed conclusion-outward per the signature-polish backlog
  No mathematical change; see Appendix A of that document for the name index.
* Spectra influence: **none** — this module has no Spectra dependency and never
  did; it imports only Mathlib.
-/

public section

noncomputable section

universe u v w x y

namespace ContinuousLinearMap

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} {F : Type w}
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

private instance approximationNumberIndexNonempty (n : ℕ) :
    Nonempty {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)} :=
  ⟨⟨0, by simp [LinearMap.rank_zero]⟩⟩

/-- The defining family of approximation errors is bounded below by `0`.
Scaffolding for the conditionally-complete-lattice infimum API on `ℝ`. -/
private theorem bddBelow_norm_sub_range (T : E →L[𝕜] F) (n : ℕ) :
    BddBelow (Set.range fun R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)} =>
      ‖T - R.1‖) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨R, rfl⟩
  exact norm_nonneg _

/-- The **zero-based** approximation number `aₙ(T)`: the operator-norm distance
from `T` to the continuous linear maps of rank **at most** `n`.

The indexing is zero-based, so `a₀(T) = ‖T‖`
(`ContinuousLinearMap.approximationNumber_index_zero`).  This differs from the
one-based convention `sₙ(T) = dist(T, {rank < n})` common in the operator-ideal
literature (Pietsch), for which `s₁(T) = ‖T‖`; the translation is
`sₙ = a_{n-1}`.  The zero-based form is the one used throughout this
development: see the module docstring for why. -/
noncomputable def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ :=
  ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖

/-- The defining infimum.  Stated for proofs that genuinely need the
construction; it is deliberately not a `simp` lemma, since a `ciInf` over a
subtype is not a useful normal form for a norm-like quantity.  Prefer
`ContinuousLinearMap.approximationNumber_le_norm_sub` and
`ContinuousLinearMap.le_approximationNumber_iff`. -/
theorem approximationNumber_eq_iInf (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n =
      ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖ := (rfl)
/-- Every admissible approximation of rank at most `n` bounds `aₙ(T)` above. -/
theorem approximationNumber_le_norm_sub (T : E →L[𝕜] F) {n : ℕ}
    {R : E →L[𝕜] F} (hR : R.rank ≤ (n : Cardinal)) :
    T.approximationNumber n ≤ ‖T - R‖ :=
  ciInf_le (T.bddBelow_norm_sub_range n) ⟨R, hR⟩

/-- Characteristic lower-bound property: `x` bounds `aₙ(T)` from below exactly
when it bounds every admissible approximation error. -/
theorem le_approximationNumber_iff (T : E →L[𝕜] F) {n : ℕ} {x : ℝ} :
    x ≤ T.approximationNumber n ↔
      ∀ R : E →L[𝕜] F, R.rank ≤ (n : Cardinal) → x ≤ ‖T - R‖ := by
  refine ⟨fun h R hR => h.trans (T.approximationNumber_le_norm_sub hR), fun h => ?_⟩
  apply le_ciInf
  rintro ⟨R, hR⟩
  exact h R hR

/-- A best approximation of rank at most `n` computes `aₙ(T)`: if no admissible
`S` does better than `R`, then the infimum is attained at `R`.

Existence of such an `R` is not automatic — the defining infimum need not be
attained — which is why this is stated with the minimality hypothesis rather
than as an unconditional `∃`. -/
theorem approximationNumber_eq_norm_sub_of_forall_le (T : E →L[𝕜] F) {n : ℕ}
    {R : E →L[𝕜] F} (hR : R.rank ≤ (n : Cardinal))
    (hbest : ∀ S : E →L[𝕜] F, S.rank ≤ (n : Cardinal) →
      ‖T - R‖ ≤ ‖T - S‖) :
    T.approximationNumber n = ‖T - R‖ := by
  apply le_antisymm
  · exact T.approximationNumber_le_norm_sub hR
  · exact T.le_approximationNumber_iff.mpr hbest

/-- The **zeroth** approximation number is the operator norm: allowing rank-`0`
approximants allows only `0`.  This is the statement that fixes the zero-based
convention; see the module docstring.  Not to be confused with
`ContinuousLinearMap.approximationNumber_zero`, which is about the zero
*operator*. -/
@[simp]
theorem approximationNumber_index_zero (T : E →L[𝕜] F) :
    T.approximationNumber 0 = ‖T‖ := by
  suffices h : T.approximationNumber 0 = ‖T - 0‖ by simpa using h
  apply T.approximationNumber_eq_norm_sub_of_forall_le
  · simp [LinearMap.rank_zero]
  · intro R hR
    apply le_of_eq
    congr
    symm
    simpa [LinearMap.range_eq_bot, ← ContinuousLinearMap.toLinearMap_zero,
      ContinuousLinearMap.coe_inj] using hR

/-- Approximation numbers decrease with the allowed rank. -/
theorem approximationNumber_antitone (T : E →L[𝕜] F) :
    Antitone T.approximationNumber := by
  intro n m hnm
  refine T.le_approximationNumber_iff.mpr ?_
  intro R hR
  exact T.approximationNumber_le_norm_sub
    (hR.trans (by exact_mod_cast hnm))

/-- Every approximation number is bounded by the operator norm. -/
theorem approximationNumber_le_norm (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n ≤ ‖T‖ := by
  calc
    T.approximationNumber n ≤ T.approximationNumber 0 :=
      T.approximationNumber_antitone (Nat.zero_le n)
    _ = ‖T‖ := T.approximationNumber_index_zero

/-- Approximation numbers are nonnegative.  (With the real-valued codomain
this is a theorem rather than a triviality; it is the price of matching the
Mathlib convention for norm-like quantities.) -/
theorem approximationNumber_nonneg (T : E →L[𝕜] F) (n : ℕ) :
    0 ≤ T.approximationNumber n :=
  le_ciInf fun _ => norm_nonneg _

/-- The zero operator has every approximation number equal to zero.  Named for
the operator, as in Mathlib's `LinearMap.singularValues_zero`; the companion
`ContinuousLinearMap.approximationNumber_index_zero` is the one about index
`0`. -/
@[simp]
theorem approximationNumber_zero (n : ℕ) :
    (0 : E →L[𝕜] F).approximationNumber n = 0 := by
  apply le_antisymm
  · simpa using
      (approximationNumber_le_norm_sub (0 : E →L[𝕜] F) (n := n) (R := 0)
        (by simp [LinearMap.rank_zero]))
  · exact approximationNumber_nonneg _ n

/-- **The rank cutoff.**  An operator of rank at most `n` is its own best
approximation of rank at most `n`, so `aₙ(T) = 0`.

This is the first of the four statements roadmap topic T09 §A4 asks for.  It holds
over any normed pair — no inner product, no completeness, no finite dimension —
because `R := T` is admissible in the defining infimum.  The converse for a finite-dimensional
source over a complete field is proved in
`ApproximationNumber.Rank` as `approximationNumber_eq_zero_iff_rank_le`;
it does not require an inner product. -/
theorem approximationNumber_eq_zero_of_rank_le (T : E →L[𝕜] F) {n : ℕ}
    (hT : T.rank ≤ (n : Cardinal)) :
    T.approximationNumber n = 0 := by
  refine le_antisymm ?_ (T.approximationNumber_nonneg n)
  simpa using T.approximationNumber_le_norm_sub hT

/-- Every approximation number at or past the rank vanishes: the cutoff
`ContinuousLinearMap.approximationNumber_eq_zero_of_rank_le` in the form a
consumer with a *finite* rank bound uses. -/
theorem approximationNumber_eq_zero_of_rank_le_of_le (T : E →L[𝕜] F) {r n : ℕ}
    (hT : T.rank ≤ (r : Cardinal)) (hrn : r ≤ n) :
    T.approximationNumber n = 0 :=
  T.approximationNumber_eq_zero_of_rank_le
    (hT.trans (Nat.cast_le.mpr hrn))

/-- Near-minimizers exist: the defining infimum is approached to within any
`ε > 0` by an admissible approximant.  This is the workhorse behind every
inequality below, each of which builds an approximant for the left-hand side out
of near-minimizers for the right. -/
theorem exists_rank_le_norm_sub_lt_approximationNumber_add (T : E →L[𝕜] F)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : E →L[𝕜] F,
      R.rank ≤ (n : Cardinal) ∧
        ‖T - R‖ < T.approximationNumber n + ε := by
  have hlt : T.approximationNumber n < T.approximationNumber n + ε := by
    exact lt_add_of_pos_right _ hε
  rw [T.approximationNumber_eq_iInf] at hlt
  obtain ⟨⟨R, hR⟩, hdist⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨R, hR, hdist⟩

/-- Approximation numbers are `1`-Lipschitz in the ambient operator norm.  The
index-shifted `ContinuousLinearMap.approximationNumber_add_le` is the sharper
statement; this is its `n = 0` specialization in the second summand, kept
separate because perturbation arguments want the norm on the right. -/
theorem approximationNumber_add_le_add_norm (T S : E →L[𝕜] F) (n : ℕ) :
    (T + S).approximationNumber n ≤ T.approximationNumber n + ‖S‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have happ := T.exists_rank_le_norm_sub_lt_approximationNumber_add n hε
  obtain ⟨R, hRrank, hRdist⟩ := happ
  exact le_of_lt <| calc
    (T + S).approximationNumber n ≤ ‖(T + S) - R‖ :=
      (T + S).approximationNumber_le_norm_sub hRrank
    _ = ‖(T - R) + S‖ := by rw [add_sub_right_comm]
    _ ≤ ‖T - R‖ + ‖S‖ := norm_add_le _ _
    _ < (T.approximationNumber n + ε) + ‖S‖ := by
      simpa [add_comm] using add_lt_add_left hRdist ‖S‖
    _ = T.approximationNumber n + ‖S‖ + ε := by
      ac_rfl

/-- **Each approximation number is `1`-Lipschitz in the operator norm:**
`|aₙ(T) − aₙ(S)| ≤ ‖T − S‖`.

This is the reverse-triangle form of `approximationNumber_add_le_add_norm`, and
it is the perturbation statement downstream arguments actually want: it says the
whole `s`-sequence moves no faster than the operator does.  In finite dimensions
it specializes to Weyl's inequality for singular values, via
`approximationNumber_eq_singularValues`. -/
theorem abs_approximationNumber_sub_approximationNumber_le (T S : E →L[𝕜] F) (n : ℕ) :
    |T.approximationNumber n - S.approximationNumber n| ≤ ‖T - S‖ := by
  have key : ∀ A B : E →L[𝕜] F,
      A.approximationNumber n - B.approximationNumber n ≤ ‖A - B‖ := by
    intro A B
    have h := B.approximationNumber_add_le_add_norm (A - B) n
    have hAB : B + (A - B) = A := by abel
    rw [hAB] at h
    linarith
  rw [abs_sub_le_iff]
  exact ⟨key T S, by simpa only [norm_sub_rev] using key S T⟩

/-- The additive ideal inequality: `a_{m+n}(T + S) ≤ aₘ(T) + aₙ(S)`, because two
approximants of ranks at most `m` and `n` add to one of rank at most `m + n`.
The index shift is exact in the zero-based convention — one-based `s`-numbers
would carry an `m + n - 1` here. -/
theorem approximationNumber_add_le
    (T S : E →L[𝕜] F) (m n : ℕ) :
    (T + S).approximationNumber (m + n) ≤
      T.approximationNumber m + S.approximationNumber n := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  obtain ⟨R, hRrank, hRdist⟩ :=
    T.exists_rank_le_norm_sub_lt_approximationNumber_add m hhalf
  obtain ⟨Q, hQrank, hQdist⟩ :=
    S.exists_rank_le_norm_sub_lt_approximationNumber_add n hhalf
  have hsumRank : (R + Q).rank ≤ ((m + n : ℕ) : Cardinal) := by
    calc
      (R + Q).rank ≤ R.rank + Q.rank := LinearMap.rank_add_le _ _
      _ ≤ (m : Cardinal) + (n : Cardinal) := add_le_add hRrank hQrank
      _ = ((m + n : ℕ) : Cardinal) := by norm_cast
  exact le_of_lt <| calc
    (T + S).approximationNumber (m + n) ≤ ‖(T + S) - (R + Q)‖ :=
      (T + S).approximationNumber_le_norm_sub hsumRank
    _ = ‖(T - R) + (S - Q)‖ := by rw [add_sub_add_comm]
    _ ≤ ‖T - R‖ + ‖S - Q‖ := norm_add_le _ _
    _ < (T.approximationNumber m + ε / 2) +
        (S.approximationNumber n + ε / 2) := add_lt_add hRdist hQdist
    _ = T.approximationNumber m + S.approximationNumber n + ε := by
      ring

/-- **Composition multiplicativity across indices**: `a_{m+n}(S ∘ T) ≤ aₘ(S) · aₙ(T)`.

The name carries `add` deliberately.  `approximationNumber_comp_comp_le` is the *two-sided ideal*
bound `aₙ(L ∘ T ∘ R) ≤ ‖L‖ · aₙ(T) · ‖R‖`, a different theorem at a fixed index; this one splits
the index, which is what makes the approximation numbers behave like a multiplicative scale and is
the input to the Schatten Hölder inequalities.

The approximant is `R₁ ∘ T + (S - R₁) ∘ R₂`, whose rank is at most `m + n` because each summand is
bounded by the rank of *its own* finite-rank factor — the left one by `R₁`, the right one by `R₂`.
The residual then factors as `(S - R₁) ∘ (T - R₂)`, so the two approximation errors multiply. -/
theorem approximationNumber_comp_add_le_mul
    {G : Type x} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (S : F →L[𝕜] G) (T : E →L[𝕜] F) (m n : ℕ) :
    (S ∘L T).approximationNumber (m + n) ≤
      S.approximationNumber m * T.approximationNumber n := by
  apply le_of_forall_pos_le_add
  intro ε hε
  set a := S.approximationNumber m with ha
  set b := T.approximationNumber n with hb
  have ha0 : 0 ≤ a := S.approximationNumber_nonneg m
  have hb0 : 0 ≤ b := T.approximationNumber_nonneg n
  -- a tolerance small enough that `(a + δ)(b + δ) ≤ a * b + ε`
  set δ := min 1 (ε / (a + b + 1)) with hδ
  have hden : 0 < a + b + 1 := by positivity
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (a + b + 1) ≤ ε := by
    have := min_le_right (1 : ℝ) (ε / (a + b + 1))
    calc δ * (a + b + 1) ≤ (ε / (a + b + 1)) * (a + b + 1) :=
          mul_le_mul_of_nonneg_right this hden.le
      _ = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨R₁, hR₁rank, hR₁dist⟩ :=
    S.exists_rank_le_norm_sub_lt_approximationNumber_add m hδ0
  obtain ⟨R₂, hR₂rank, hR₂dist⟩ :=
    T.exists_rank_le_norm_sub_lt_approximationNumber_add n hδ0
  set Q : E →L[𝕜] G := R₁ ∘L T + (S - R₁) ∘L R₂ with hQ
  have hQrank : Q.rank ≤ ((m + n : ℕ) : Cardinal) := by
    calc
      Q.rank ≤ (R₁ ∘L T).rank + ((S - R₁) ∘L R₂).rank := LinearMap.rank_add_le _ _
      _ ≤ (m : Cardinal) + (n : Cardinal) :=
          add_le_add ((ContinuousLinearMap.rank_comp_le_left T R₁).trans hR₁rank)
            (ContinuousLinearMap.rank_comp_le_natCast_right R₂ (S - R₁) hR₂rank)
      _ = ((m + n : ℕ) : Cardinal) := by norm_cast
  have hres : (S ∘L T) - Q = (S - R₁) ∘L (T - R₂) := by
    ext x
    simp only [hQ, sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel
  exact le_of_lt <| calc
    (S ∘L T).approximationNumber (m + n) ≤ ‖(S ∘L T) - Q‖ :=
      (S ∘L T).approximationNumber_le_norm_sub hQrank
    _ = ‖(S - R₁) ∘L (T - R₂)‖ := by rw [hres]
    _ ≤ ‖S - R₁‖ * ‖T - R₂‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ < (a + δ) * (b + δ) := by
        refine mul_lt_mul'' hR₁dist hR₂dist (norm_nonneg _) (norm_nonneg _)
    _ ≤ a * b + ε := by nlinarith [hδε, hδ0.le, hδ1, ha0, hb0]

/-- Right ideal inequality for approximation numbers. -/
theorem approximationNumber_comp_le_mul_norm
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (T : E →L[𝕜] F) (A : G →L[𝕜] E) (n : ℕ) :
    (T ∘L A).approximationNumber n ≤
      T.approximationNumber n * ‖A‖ := by
  by_cases hA : ‖A‖ = 0
  · calc
      (T ∘L A).approximationNumber n ≤ ‖T ∘L A‖ :=
        (T ∘L A).approximationNumber_le_norm n
      _ ≤ ‖T‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = T.approximationNumber n * ‖A‖ := by simp [hA]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hεA : 0 < ε / ‖A‖ := div_pos hε (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA))
    obtain ⟨R, hRrank, hRdist⟩ :=
      T.exists_rank_le_norm_sub_lt_approximationNumber_add n hεA
    have hcompRank : (R ∘L A).rank ≤ (n : Cardinal) :=
      (ContinuousLinearMap.rank_comp_le_left A R).trans hRrank
    exact le_of_lt <| calc
      (T ∘L A).approximationNumber n ≤ ‖(T ∘L A) - (R ∘L A)‖ :=
        (T ∘L A).approximationNumber_le_norm_sub hcompRank
      _ = ‖(T - R) ∘L A‖ := by rw [ContinuousLinearMap.sub_comp]
      _ ≤ ‖T - R‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ < (T.approximationNumber n + ε / ‖A‖) * ‖A‖ :=
        mul_lt_mul_of_pos_right hRdist (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA))
      _ = T.approximationNumber n * ‖A‖ + ε := by
        rw [add_mul, div_mul_cancel₀ ε hA]

/-- Left ideal inequality for approximation numbers. -/
theorem approximationNumber_comp_le_norm_mul
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    (B : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T).approximationNumber n ≤
      ‖B‖ * T.approximationNumber n := by
  by_cases hB : ‖B‖ = 0
  · calc
      (B ∘L T).approximationNumber n ≤ ‖B ∘L T‖ :=
        (B ∘L T).approximationNumber_le_norm n
      _ ≤ ‖B‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖B‖ * T.approximationNumber n := by simp [hB]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hεB : 0 < ε / ‖B‖ := div_pos hε (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hB))
    obtain ⟨R, hRrank, hRdist⟩ :=
      T.exists_rank_le_norm_sub_lt_approximationNumber_add n hεB
    have hcompRank : (B ∘L R).rank ≤ (n : Cardinal) :=
      ContinuousLinearMap.rank_comp_le_natCast_right R B hRrank
    exact le_of_lt <| calc
      (B ∘L T).approximationNumber n ≤ ‖(B ∘L T) - (B ∘L R)‖ :=
        (B ∘L T).approximationNumber_le_norm_sub hcompRank
      _ = ‖B ∘L (T - R)‖ := by rw [ContinuousLinearMap.comp_sub]
      _ ≤ ‖B‖ * ‖T - R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ < ‖B‖ * (T.approximationNumber n + ε / ‖B‖) :=
        mul_lt_mul_of_pos_left hRdist (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hB))
      _ = ‖B‖ * T.approximationNumber n + ε := by
        rw [mul_add, mul_div_cancel₀ ε hB]

/-- Two-sided ideal inequality for approximation numbers. -/
theorem approximationNumber_comp_comp_le
    {G : Type x} {H : Type y}
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E)
    (n : ℕ) :
    (L ∘L T ∘L R).approximationNumber n ≤
      ‖L‖ * T.approximationNumber n * ‖R‖ := by
  calc
    (L ∘L T ∘L R).approximationNumber n
        ≤ (L ∘L T).approximationNumber n * ‖R‖ :=
      (L ∘L T).approximationNumber_comp_le_mul_norm R n
    _ ≤ (‖L‖ * T.approximationNumber n) * ‖R‖ := by
      gcongr
      exact approximationNumber_comp_le_norm_mul L T n

/-- **Approximation numbers do not see an enlargement of the codomain.**

`ι` embeds `F` into `G` with `‖ι‖ ≤ 1`, and `π` is a left inverse with `‖π‖ ≤ 1`; the
model is the inclusion of `F` as one summand of an `ℓ²` direct sum together with the
projection back onto it.  Postcomposing with `ι` then leaves every approximation number
where it was, because both ideal inequalities apply and `π ∘ ι = id` closes the loop.
(The two hypotheses force `ι` to be isometric: `‖y‖ = ‖π (ι y)‖ ≤ ‖ι y‖ ≤ ‖y‖`.)

Nothing here needs an inner product, completeness, or a bound on any dimension.  Its use
is to move an operator into a codomain with room for as many orthonormal vectors as an
argument needs, without changing the quantity being computed. -/
theorem approximationNumber_comp_eq_of_leftInverse
    {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
    {ι : F →L[𝕜] G} {π : G →L[𝕜] F} (hπι : Function.LeftInverse π ι)
    (hι : ‖ι‖ ≤ 1) (hπ : ‖π‖ ≤ 1) (T : E →L[𝕜] F) (n : ℕ) :
    (ι ∘L T).approximationNumber n = T.approximationNumber n := by
  have hcomp : π ∘L (ι ∘L T) = T := by
    ext x
    exact hπι (T x)
  refine le_antisymm ?_ ?_
  · calc (ι ∘L T).approximationNumber n
        ≤ ‖ι‖ * T.approximationNumber n := approximationNumber_comp_le_norm_mul ι T n
      _ ≤ 1 * T.approximationNumber n :=
        mul_le_mul_of_nonneg_right hι (T.approximationNumber_nonneg n)
      _ = T.approximationNumber n := one_mul _
  · calc T.approximationNumber n
        = (π ∘L (ι ∘L T)).approximationNumber n := by rw [hcomp]
      _ ≤ ‖π‖ * (ι ∘L T).approximationNumber n :=
        approximationNumber_comp_le_norm_mul π (ι ∘L T) n
      _ ≤ 1 * (ι ∘L T).approximationNumber n :=
        mul_le_mul_of_nonneg_right hπ ((ι ∘L T).approximationNumber_nonneg n)
      _ = (ι ∘L T).approximationNumber n := one_mul _

/-- Rank of scalar multiples is no larger than the original rank. -/
private theorem rank_smul_le_rank (c : 𝕜) (R : E →L[𝕜] F) :
    (c • R).rank ≤ R.rank := by
  refine Submodule.rank_mono ?_
  rintro y ⟨x, rfl⟩
  exact ⟨c • x, by simp⟩

/-- Approximation numbers are absolutely homogeneous. -/
@[simp]
theorem approximationNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    (c • T).approximationNumber n = ‖c‖ * T.approximationNumber n := by
  have upper (d : 𝕜) (S : E →L[𝕜] F) :
      (d • S).approximationNumber n ≤ ‖d‖ * S.approximationNumber n := by
    by_cases hd : d = 0
    · subst d
      have hz : (0 : E →L[𝕜] F).approximationNumber n = 0 :=
        approximationNumber_zero n
      simpa only [zero_smul, norm_zero, zero_mul] using hz.le
    · apply le_of_forall_pos_le_add
      intro ε hε
      have hdn : ‖d‖ ≠ 0 := by simpa using hd
      have hεd : 0 < ε / ‖d‖ := div_pos hε (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hdn))
      obtain ⟨R, hRrank, hRdist⟩ :=
        S.exists_rank_le_norm_sub_lt_approximationNumber_add n hεd
      exact le_of_lt <| calc
        (d • S).approximationNumber n ≤ ‖d • S - d • R‖ :=
          (d • S).approximationNumber_le_norm_sub ((rank_smul_le_rank d R).trans hRrank)
        _ = ‖d‖ * ‖S - R‖ := by
          rw [← smul_sub, norm_smul]
        _ < ‖d‖ * (S.approximationNumber n + ε / ‖d‖) :=
          mul_lt_mul_of_pos_left hRdist (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hdn))
        _ = ‖d‖ * S.approximationNumber n + ε := by
          rw [mul_add, mul_div_cancel₀ ε hdn]
  by_cases hc : c = 0
  · subst c
    have hz : (0 : E →L[𝕜] F).approximationNumber n = 0 :=
      approximationNumber_zero n
    simpa only [zero_smul, norm_zero, zero_mul] using hz
  apply le_antisymm
  · exact upper c T
  · have hupper := upper c⁻¹ (c • T)
    have hcinv : c⁻¹ • (c • T) = T := by
      rw [← mul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hcinv, norm_inv] at hupper
    have hnorm_ne : ‖c‖ ≠ 0 := by simpa using hc
    calc
      ‖c‖ * T.approximationNumber n
          ≤ ‖c‖ * (‖c‖⁻¹ * (c • T).approximationNumber n) := by
        gcongr
      _ = (c • T).approximationNumber n := by
        rw [← mul_assoc, mul_inv_cancel₀ hnorm_ne, one_mul]

end ContinuousLinearMap

end

end
