/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import TauCeti.Analysis.Normed.Operator.Basic
public import TauCeti.Analysis.Normed.Operator.SNumbers.Basic
-- Private: finite-dimensional volume bounds, total-boundedness characterizations of compactness,
-- and metric covering/separation helpers are used only inside proofs.
import TauCeti.Analysis.Normed.Module.CoveringNumber
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import TauCeti.Topology.MetricSpace.CoveringNumbers

/-!
# Entropy numbers of bounded operators

For a bounded linear map `T : E →L[𝕜] F` between seminormed spaces, the `n`-th (dyadic) entropy
number `eₙ(T)` is the infimum of all radii `ε ≥ 0` for which the image `T(B_E)` of the closed unit
ball can be covered by at most `2 ^ n` closed `ε`-balls in `F`. Indexing starts at zero, so
`e₀(T)` measures the smallest single closed ball in `F` containing `T(B_E)`.

Over `ℝ` or `ℂ`, in Pietsch's terminology (*Operator Ideals*, Chapter 12), entropy numbers are
*pseudo-s-numbers*: they satisfy the norm, monotonicity, perturbation, and two-sided ideal laws
together with the mixed-index additive and multiplicative inequalities
`e_{m+n}(S + T) ≤ eₘ(S) + eₙ(T)` and `e_{m+n}(B ∘L S) ≤ eₘ(B) * eₙ(S)`,
and they detect compactness (`IsCompactOperator T ↔ eₙ(T) → 0` when `F` is complete), yet they
fail the finite-rank vanishing axiom because `eₙ(T) > 0` for every nonzero operator into a normed
space (with the quantitative bound `‖T‖₊ / 2 ^ n ≤ eₙ(T)`).

The hypotheses track the exact scalar-field and norm geometry each law needs:
* Over any `NontriviallyNormedField 𝕜`, we establish the covering-number characterizations,
  monotonicity, `eₙ(T) ≤ ‖T‖₊`, additivity `e_{m+n}(S + T) ≤ eₘ(S) + eₙ(T)`, the perturbation and
  `1`-Lipschitz bounds, postcomposition `eₙ(B ∘L T) ≤ ‖B‖₊ * eₙ(T)`, scalar homogeneity, the
  metric separation lower bounds, `eₙ(T) = 0 ↔ ‖T‖₊ = 0` (hence `eₙ(T) > 0` for `T ≠ 0` and
  `¬ IsSNumberSequence entropy` when the target is a `NormedAddCommGroup`), and the
  characterization of total boundedness and compactness.
* Over a `DenselyNormedField 𝕜`, rescaling balls into the unit ball yields multiplicativity
  `e_{m+n}(B ∘L S) ≤ eₘ(B) * eₙ(S)`, precomposition `eₙ(T ∘L A) ≤ eₙ(T) * ‖A‖₊`, and the
  two-sided ideal inequality `eₙ(B ∘L T ∘L A) ≤ ‖B‖₊ * eₙ(T) * ‖A‖₊`. Over a non-densely normed
  field such as `ℚ₂`, precomposition can fail on normed spaces equipped with a rescaled module norm
  (such as `(3 / 2) |·|₂` on `ℚ₂`) because unit balls ignore scalar gaps in the value group.
* Over `RCLike 𝕜`, symmetry and convexity of real segments give `‖T‖₊ / 2 ^ n ≤ eₙ(T)` and hence
  `e₀(T) = ‖T‖₊` on seminormed spaces. On a `NormedAddCommGroup` (so nonzero vectors have positive
  norm; a space with the zero seminorm has `e₀(id) = 0`), comparing Haar volumes in finite
  dimension and applying Riesz's lemma in infinite dimension give the lower bound `1 / 2 ≤ eₙ(id_X)`
  for every index `n` strictly below `Module.rank 𝕜 X`.

## Main declarations

* `ContinuousLinearMap.entropyNumber`: the dyadic entropy numbers `eₙ(T)`.
* `ContinuousLinearMap.entropyNumber_eq_iInf_externalCoveringNumber`: `eₙ(T)` as the infimum of
  radii `ε` with `Metric.externalCoveringNumber ε (T '' closedBall 0 1) ≤ 2 ^ n`.
* `ContinuousLinearMap.antitone_entropyNumber`, `ContinuousLinearMap.entropyNumber_le_nnnorm`,
  `ContinuousLinearMap.entropyNumber_zero`: monotonicity, operator-norm bound, and `e₀(T) = ‖T‖₊`.
* `ContinuousLinearMap.entropyNumber_add_index_le`: `e_{m+n}(S + T) ≤ eₘ(S) + eₙ(T)`.
* `ContinuousLinearMap.entropyNumber_comp_add_le_mul`: `e_{m+n}(B ∘L S) ≤ eₘ(B) * eₙ(S)`.
* `ContinuousLinearMap.entropyNumber_comp_comp_le`: `eₙ(B ∘L T ∘L A) ≤ ‖B‖₊ * eₙ(T) * ‖A‖₊`.
* `ContinuousLinearMap.tendsto_entropyNumber_atTop_nhds_zero_iff_totallyBounded`,
  `ContinuousLinearMap.isCompactOperator_iff_tendsto_entropyNumber`: total boundedness and
  compactness via `eₙ(T) → 0`.
* `ContinuousLinearMap.div_two_le_entropyNumber_of_subset_image`,
  `ContinuousLinearMap.div_two_le_entropyNumber_of_pairwise_le_dist`,
  `ContinuousLinearMap.div_two_le_entropyNumber_of_le_dist`: separation lower bounds `δ / 2 ≤ eₙ(T)`
  from more than `2 ^ n` separated points.
* `ContinuousLinearMap.nnnorm_div_two_pow_le_entropyNumber`,
  `ContinuousLinearMap.entropyNumber_pos`: `‖T‖₊ / 2 ^ n ≤ eₙ(T)` and strict positivity on nonzero
  operators.
* `ContinuousLinearMap.one_half_le_entropyNumber_id`: `1 / 2 ≤ eₙ(id_X)` for `n < Module.rank 𝕜 X`.
* `TauCeti.SNumbers.entropy`, `TauCeti.SNumbers.not_isSNumberSequence_entropy`: the family
  wrapper and proof that entropy numbers fail Pietsch's s-number axioms.

## References

* A. Pietsch, *Operator Ideals*, North-Holland Mathematical Library 20, North-Holland (1980),
  Chapter 12.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), §2.11.
* B. Carl and I. Stephani, *Entropy, Compactness and the Approximation of Operators*, Cambridge
  Tracts in Mathematics 98, Cambridge University Press (1990), Chapters 1–2.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/Entropy.lean` and `SNumbers/EntropyBounds.lean`: an earlier Lean formalization of
  entropy numbers and their lower bounds.
-/

public section

open Filter Metric Set
open scoped NNReal Topology

namespace ContinuousLinearMap

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

section Seminormed

variable {E F G H : Type*}
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-! ### Definition and covering characterizations -/

/-- The `n`-th (dyadic) entropy number `eₙ(T)` of a bounded linear map `T`: the infimum of all
radii `ε ≥ 0` for which the image of the closed unit ball under `T` is covered by at most `2 ^ n`
closed `ε`-balls in `F`. Indexing starts at zero, so `e₀(T)` uses a single ball. -/
noncomputable def entropyNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0 :=
  ⨅ ε : {ε : ℝ≥0 // ∃ N : Finset F, N.card ≤ 2 ^ n ∧
      (T : E → F) '' closedBall 0 1 ⊆ ⋃ y ∈ (N : Set F), closedBall y ε},
    ε.val

/-- Defining infimum formula for the `n`-th entropy number. -/
theorem entropyNumber_def (T : E →L[𝕜] F) (n : ℕ) :
    T.entropyNumber n =
      ⨅ ε : {ε : ℝ≥0 // ∃ N : Finset F, N.card ≤ 2 ^ n ∧
          (T : E → F) '' closedBall 0 1 ⊆ ⋃ y ∈ (N : Set F), closedBall y ε},
        ε.val := (rfl)

private instance (T : E →L[𝕜] F) (n : ℕ) :
    Nonempty {ε : ℝ≥0 // ∃ N : Finset F, N.card ≤ 2 ^ n ∧
      (T : E → F) '' closedBall 0 1 ⊆ ⋃ y ∈ (N : Set F), closedBall y ε} :=
  ⟨⟨‖T‖₊, {0}, by simpa using Nat.one_le_two_pow,
    by simpa using (T.lipschitzWith.mapsTo_closedBall 0 1).image_subset⟩⟩

/-- Any covering of `T '' closedBall 0 1` by at most `2 ^ n` closed `ε`-balls bounds `eₙ(T)`. -/
theorem entropyNumber_le_of_subset_biUnion (T : E →L[𝕜] F) {n : ℕ} {ε : ℝ≥0} {N : Finset F}
    (hcard : N.card ≤ 2 ^ n)
    (hcov : (T : E → F) '' closedBall 0 1 ⊆ ⋃ y ∈ (N : Set F), closedBall y ε) :
    T.entropyNumber n ≤ ε := by
  rw [entropyNumber_def]
  exact ciInf_le (f := fun x : {ε : ℝ≥0 // ∃ N : Finset F, N.card ≤ 2 ^ n ∧
      (T : E → F) '' closedBall 0 1 ⊆ ⋃ y ∈ (N : Set F), closedBall y ε} ↦ x.val)
    (OrderBot.bddBelow _) ⟨ε, N, hcard, hcov⟩

/-- Any `ε`-cover of `T '' closedBall 0 1` of cardinality at most `2 ^ n` bounds `eₙ(T)`. -/
theorem entropyNumber_le_of_isCover (T : E →L[𝕜] F) {n : ℕ} {ε : ℝ≥0} {N : Finset F}
    (hcard : N.card ≤ 2 ^ n) (hcov : IsCover ε ((T : E → F) '' closedBall 0 1) N) :
    T.entropyNumber n ≤ ε :=
  T.entropyNumber_le_of_subset_biUnion hcard hcov.subset_iUnion_closedBall

/-- Bounding the external covering number of `T '' closedBall 0 1` by `2 ^ n` bounds `eₙ(T)`. -/
theorem entropyNumber_le_of_externalCoveringNumber_le (T : E →L[𝕜] F) {n : ℕ} {ε : ℝ≥0}
    (h : externalCoveringNumber ε ((T : E → F) '' closedBall 0 1) ≤ 2 ^ n) :
    T.entropyNumber n ≤ ε := by
  rw [← Nat.cast_ofNat, ← Nat.cast_pow] at h
  obtain ⟨N, hcard, hcov⟩ := externalCoveringNumber_le_natCast_iff.mp h
  exact T.entropyNumber_le_of_isCover hcard hcov

/-- Lower-bound characterization of `eₙ(T)` in terms of unions of closed balls. -/
theorem le_entropyNumber_iff {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    c ≤ T.entropyNumber n ↔
      ∀ (ε : ℝ≥0) (N : Finset F), N.card ≤ 2 ^ n →
        (T : E → F) '' closedBall 0 1 ⊆ ⋃ y ∈ (N : Set F), closedBall y ε → c ≤ ε := by
  rw [entropyNumber_def, le_ciInf_iff (OrderBot.bddBelow _), Subtype.forall]
  exact ⟨fun h ε N hcard hcov ↦ h ε ⟨N, hcard, hcov⟩, fun h ε ⟨N, hcard, hcov⟩ ↦ h ε N hcard hcov⟩

/-- Lower-bound characterization of `eₙ(T)` in terms of `Metric.IsCover`. -/
theorem le_entropyNumber_iff_isCover {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0} :
    c ≤ T.entropyNumber n ↔
      ∀ (ε : ℝ≥0) (N : Finset F), N.card ≤ 2 ^ n →
        IsCover ε ((T : E → F) '' closedBall 0 1) N → c ≤ ε := by
  simp_rw [le_entropyNumber_iff, isCover_iff_subset_iUnion_closedBall]

/-- `eₙ(T)` is the greatest lower bound of admissible covering radii. -/
theorem isGLB_entropyNumber (T : E →L[𝕜] F) (n : ℕ) :
    IsGLB {ε : ℝ≥0 | ∃ N : Finset F, N.card ≤ 2 ^ n ∧
      IsCover ε ((T : E → F) '' closedBall 0 1) N} (T.entropyNumber n) := by
  refine ⟨?_, fun c hc ↦ le_entropyNumber_iff_isCover.mpr fun ε N hcard hcov ↦ hc ⟨N, hcard, hcov⟩⟩
  rintro ε ⟨N, hcard, hcov⟩
  exact T.entropyNumber_le_of_isCover hcard hcov

/-- Any radius strictly above `eₙ(T)` admits a cover of `T '' closedBall 0 1` by at most `2 ^ n`
points. -/
theorem exists_isCover_of_entropyNumber_lt {T : E →L[𝕜] F} {n : ℕ} {c : ℝ≥0}
    (h : T.entropyNumber n < c) :
    ∃ N : Finset F, N.card ≤ 2 ^ n ∧ IsCover c ((T : E → F) '' closedBall 0 1) N := by
  rw [entropyNumber_def] at h
  obtain ⟨⟨ε, N, hcard, hcov⟩, hlt⟩ := exists_lt_of_ciInf_lt h
  exact ⟨N, hcard, (IsCover.of_subset_iUnion_closedBall hcov).mono_radius hlt.le⟩

/-- `eₙ(T)` is the infimum of all radii at which `T '' closedBall 0 1` has external covering number
at most `2 ^ n`. -/
theorem entropyNumber_eq_iInf_externalCoveringNumber (T : E →L[𝕜] F) (n : ℕ) :
    T.entropyNumber n =
      ⨅ ε : {ε : ℝ≥0 // externalCoveringNumber ε ((T : E → F) '' closedBall 0 1) ≤ 2 ^ n},
        ε.val := by
  have hcov_le {ε : ℝ≥0} {N : Finset F} (hcard : N.card ≤ 2 ^ n)
      (hcov : IsCover ε ((T : E → F) '' closedBall 0 1) N) :
      externalCoveringNumber ε ((T : E → F) '' closedBall 0 1) ≤ 2 ^ n := by
    rw [← Nat.cast_ofNat, ← Nat.cast_pow]
    exact externalCoveringNumber_le_natCast_iff.mpr ⟨N, hcard, hcov⟩
  obtain ⟨N₀, hcard₀, hcov₀⟩ :=
    exists_isCover_of_entropyNumber_lt (lt_add_one (T.entropyNumber n))
  have : Nonempty {ε : ℝ≥0 // externalCoveringNumber ε ((T : E → F) '' closedBall 0 1) ≤ 2 ^ n} :=
    ⟨⟨_, hcov_le hcard₀ hcov₀⟩⟩
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun ε ↦ T.entropyNumber_le_of_externalCoveringNumber_le ε.property
  · refine le_entropyNumber_iff_isCover.mpr fun ε N hcard hcov ↦ ?_
    exact ciInf_le (f := fun x : {ε : ℝ≥0 //
        externalCoveringNumber ε ((T : E → F) '' closedBall 0 1) ≤ 2 ^ n} ↦ x.val)
      (OrderBot.bddBelow _) ⟨ε, hcov_le hcard hcov⟩

/-! ### Monotonicity, norm bound, additivity, and Lipschitz continuity -/

/-- Every entropy number is bounded above by the operator norm. -/
theorem entropyNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) : T.entropyNumber n ≤ ‖T‖₊ :=
  T.entropyNumber_le_of_subset_biUnion (N := {0}) (by simpa using Nat.one_le_two_pow)
    (by simpa using (T.lipschitzWith.mapsTo_closedBall 0 1).image_subset)

/-- Entropy numbers form an antitone sequence. -/
theorem antitone_entropyNumber (T : E →L[𝕜] F) : Antitone T.entropyNumber :=
  fun _ _ hmn ↦ le_entropyNumber_iff_isCover.mpr fun _ _ hcard hcov ↦
    T.entropyNumber_le_of_isCover (hcard.trans (Nat.pow_le_pow_right (by positivity) hmn)) hcov

/-- Successive entropy numbers decrease: `e_{n+1}(T) ≤ eₙ(T)`. -/
theorem entropyNumber_succ_le (T : E →L[𝕜] F) (n : ℕ) :
    T.entropyNumber (n + 1) ≤ T.entropyNumber n :=
  T.antitone_entropyNumber n.le_succ

/-- The range of `T.entropyNumber` is bounded above. -/
theorem bddAbove_range_entropyNumber (T : E →L[𝕜] F) : BddAbove (range T.entropyNumber) :=
  ⟨‖T‖₊, forall_mem_range.mpr T.entropyNumber_le_nnnorm⟩

/-- An operator of vanishing seminorm has vanishing entropy numbers. -/
theorem entropyNumber_eq_zero_of_nnnorm_eq_zero {T : E →L[𝕜] F} (hT : ‖T‖₊ = 0) (n : ℕ) :
    T.entropyNumber n = 0 :=
  le_antisymm ((T.entropyNumber_le_nnnorm n).trans_eq hT) bot_le

/-- All entropy numbers of the zero operator vanish. -/
@[simp]
theorem zero_entropyNumber (n : ℕ) : (0 : E →L[𝕜] F).entropyNumber n = 0 :=
  entropyNumber_eq_zero_of_nnnorm_eq_zero nnNorm_zero n

/-- **Mixed-index additive inequality.** `e_{m+n}(S + T) ≤ eₘ(S) + eₙ(T)`. -/
theorem entropyNumber_add_index_le (S T : E →L[𝕜] F) (m n : ℕ) :
    (S + T).entropyNumber (m + n) ≤ S.entropyNumber m + T.entropyNumber n := by
  classical
  -- Cover `S(B_E)` and `T(B_E)` separately, then take pairwise sums of centers.
  rw [entropyNumber_def S, entropyNumber_def T]
  refine NNReal.le_iInf_add_iInf fun ε₁ ε₂ ↦ ?_
  obtain ⟨N₁, hN₁, hcov₁⟩ := ε₁.property
  obtain ⟨N₂, hN₂, hcov₂⟩ := ε₂.property
  refine (S + T).entropyNumber_le_of_subset_biUnion
    (N := Finset.image₂ (· + ·) N₁ N₂) ?_ ?_
  · exact (Finset.card_image₂_le _ _ _).trans
      ((Nat.mul_le_mul hN₁ hN₂).trans_eq (pow_add 2 m n).symm)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y₁, hy₁, hx₁⟩ := mem_iUnion₂.mp (hcov₁ ⟨x, hx, rfl⟩)
    obtain ⟨y₂, hy₂, hx₂⟩ := mem_iUnion₂.mp (hcov₂ ⟨x, hx, rfl⟩)
    refine mem_iUnion₂.mpr ⟨y₁ + y₂, Finset.mem_coe.mpr (Finset.mem_image₂_of_mem hy₁ hy₂), ?_⟩
    rw [mem_closedBall, add_apply, NNReal.coe_add]
    exact (dist_add_add_le (S x) (T x) y₁ y₂).trans
      (add_le_add (mem_closedBall.mp hx₁) (mem_closedBall.mp hx₂))

/-- **Perturbation inequality.** `eₙ(S + T) ≤ eₙ(S) + ‖T‖₊`. -/
theorem entropyNumber_add_le (S T : E →L[𝕜] F) (n : ℕ) :
    (S + T).entropyNumber n ≤ S.entropyNumber n + ‖T‖₊ :=
  calc (S + T).entropyNumber n
      = (S + T).entropyNumber (n + 0) := rfl
    _ ≤ S.entropyNumber n + T.entropyNumber 0 := S.entropyNumber_add_index_le T n 0
    _ ≤ S.entropyNumber n + ‖T‖₊ := by gcongr; exact T.entropyNumber_le_nnnorm 0

/-- At each index, entropy numbers satisfy `|eₙ(S) - eₙ(T)| ≤ ‖S - T‖`. -/
theorem abs_entropyNumber_sub_entropyNumber_le (S T : E →L[𝕜] F) (n : ℕ) :
    |(S.entropyNumber n : ℝ) - T.entropyNumber n| ≤ ‖S - T‖ := by
  have key (A B : E →L[𝕜] F) : (A.entropyNumber n : ℝ) ≤ B.entropyNumber n + ‖A - B‖ := by
    have h := B.entropyNumber_add_le (A - B) n
    rw [add_sub_cancel] at h
    exact_mod_cast h
  rw [abs_sub_le_iff]
  exact ⟨sub_le_iff_le_add'.mpr (key S T), sub_le_iff_le_add'.mpr (norm_sub_rev T S ▸ key T S)⟩

/-- At each fixed index, `T ↦ eₙ(T)` is `1`-Lipschitz in the operator norm. -/
theorem lipschitzWith_entropyNumber (n : ℕ) :
    LipschitzWith 1 fun T : E →L[𝕜] F ↦ T.entropyNumber n :=
  LipschitzWith.of_dist_le_mul fun S T ↦ by
    simpa [NNReal.dist_eq, dist_eq_norm] using abs_entropyNumber_sub_entropyNumber_le S T n

/-- At each fixed index, `T ↦ eₙ(T)` is continuous in the operator norm topology. -/
@[fun_prop]
theorem continuous_entropyNumber (n : ℕ) : Continuous fun T : E →L[𝕜] F ↦ T.entropyNumber n :=
  (lipschitzWith_entropyNumber n).continuous

/-! ### Postcomposition, contractions, and scalar homogeneity -/

/-- Postcomposition scales entropy numbers by at most the operator norm. -/
theorem entropyNumber_comp_le_left (B : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T).entropyNumber n ≤ ‖B‖₊ * T.entropyNumber n := by
  classical
  rw [entropyNumber_def T, NNReal.mul_iInf]
  refine le_ciInf fun ε ↦ ?_
  obtain ⟨N, hcard, hcov⟩ := ε.property
  have hcovB : IsCover (‖B‖₊ * ε.val) ((B ∘L T : E → G) '' closedBall 0 1) (N.image B) := by
    simpa [Finset.coe_image, coe_comp, image_comp] using
      (IsCover.of_subset_iUnion_closedBall hcov).image_lipschitz B.lipschitzWith
  exact (B ∘L T).entropyNumber_le_of_isCover (Finset.card_image_le.trans hcard) hcovB

/-- Precomposition with a contraction does not increase entropy numbers. -/
theorem entropyNumber_comp_le_of_norm_le_one (T : F →L[𝕜] G) {A : E →L[𝕜] F}
    (hA : ‖A‖ ≤ 1) (n : ℕ) :
    (T ∘L A).entropyNumber n ≤ T.entropyNumber n := by
  refine le_entropyNumber_iff_isCover.mpr fun ε N hcard hcov ↦ ?_
  refine (T ∘L A).entropyNumber_le_of_isCover hcard (hcov.anti ?_)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨A x, mem_closedBall_zero_iff.mpr ?_, rfl⟩
  calc ‖A x‖ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
    _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg x)
    _ ≤ 1 := by simpa using mem_closedBall_zero_iff.mp hx

/-- Two-sided compression by contractions does not increase entropy numbers. -/
theorem entropyNumber_comp_comp_le_of_norm_le_one {B : G →L[𝕜] H} {A : E →L[𝕜] F}
    (hB : ‖B‖ ≤ 1) (hA : ‖A‖ ≤ 1) (T : F →L[𝕜] G) (n : ℕ) :
    (B ∘L T ∘L A).entropyNumber n ≤ T.entropyNumber n := by
  have hB' : ‖B‖₊ ≤ 1 := mod_cast hB
  calc (B ∘L T ∘L A).entropyNumber n
      ≤ ‖B‖₊ * (T ∘L A).entropyNumber n := B.entropyNumber_comp_le_left (T ∘L A) n
    _ ≤ 1 * T.entropyNumber n := by gcongr; exact T.entropyNumber_comp_le_of_norm_le_one hA n
    _ = T.entropyNumber n := one_mul _

/-- Scalar homogeneity of entropy numbers: `eₙ(c • T) = ‖c‖₊ * eₙ(T)`. -/
@[simp]
theorem entropyNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    (c • T).entropyNumber n = ‖c‖₊ * T.entropyNumber n := by
  have hle (a : 𝕜) (S : E →L[𝕜] F) : (a • S).entropyNumber n ≤ ‖a‖₊ * S.entropyNumber n := by
    have hid : ‖ContinuousLinearMap.id 𝕜 F‖₊ ≤ 1 := mod_cast norm_id_le
    have hcomp : a • S = (a • ContinuousLinearMap.id 𝕜 F) ∘L S := by ext; simp
    calc (a • S).entropyNumber n
        = ((a • ContinuousLinearMap.id 𝕜 F) ∘L S).entropyNumber n := by rw [hcomp]
      _ ≤ ‖a • ContinuousLinearMap.id 𝕜 F‖₊ * S.entropyNumber n :=
          (a • ContinuousLinearMap.id 𝕜 F).entropyNumber_comp_le_left S n
      _ ≤ (‖a‖₊ * ‖ContinuousLinearMap.id 𝕜 F‖₊) * S.entropyNumber n := by
          gcongr; exact nnNorm_smul_le _ _
      _ ≤ ‖a‖₊ * S.entropyNumber n := by gcongr; exact mul_le_of_le_one_right' hid
  refine (hle c T).antisymm ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  calc ‖c‖₊ * T.entropyNumber n
      = ‖c‖₊ * (c⁻¹ • c • T).entropyNumber n := by rw [inv_smul_smul₀ hc]
    _ ≤ ‖c‖₊ * (‖c⁻¹‖₊ * (c • T).entropyNumber n) := by gcongr; exact hle _ _
    _ = (c • T).entropyNumber n := by simp [hc]

/-- Negation preserves entropy numbers. -/
@[simp]
theorem entropyNumber_neg (T : E →L[𝕜] F) (n : ℕ) : (-T).entropyNumber n = T.entropyNumber n := by
  simpa using T.entropyNumber_smul (-1) n

/-! ### Separation lower bounds -/

/-- **Separation lower bound on `T(B_E)`.** If `T '' closedBall 0 1` contains a finite set of
strictly more than `2 ^ n` points at mutual distance at least `δ`, then `δ / 2 ≤ eₙ(T)`. -/
theorem div_two_le_entropyNumber_of_subset_image {T : E →L[𝕜] F} {n : ℕ} {s : Finset F} {δ : ℝ}
    (hs : (s : Set F) ⊆ (T : E → F) '' closedBall 0 1)
    (hsep : (s : Set F).Pairwise (δ ≤ dist · ·)) (hcard : 2 ^ n < s.card) :
    δ / 2 ≤ T.entropyNumber n := by
  rcases le_or_gt δ 0 with hδ | hδ
  · exact (div_nonpos_of_nonpos_of_nonneg hδ zero_le_two).trans (T.entropyNumber n).coe_nonneg
  have hnn : (⟨δ / 2, by positivity⟩ : ℝ≥0) ≤ T.entropyNumber n :=
    le_entropyNumber_iff_isCover.mpr fun ε N hN hcov ↦ by
      exact_mod_cast hcov.div_two_le_of_card_lt hs hsep (hN.trans_lt hcard)
  exact_mod_cast hnn

/-- **Indexed separation lower bound.** If `f : ι → E` maps a finite index type of cardinality
strictly greater than `2 ^ n` into `closedBall 0 1` and the images `T (f i)` lie at mutual distance
at least `δ`, then `δ / 2 ≤ eₙ(T)`. -/
theorem div_two_le_entropyNumber_of_pairwise_le_dist {ι : Type*} [Fintype ι] {T : E →L[𝕜] F}
    {n : ℕ} {f : ι → E} {δ : ℝ} (hf : ∀ i, f i ∈ closedBall 0 1)
    (hsep : Pairwise fun i j ↦ δ ≤ dist (T (f i)) (T (f j))) (hcard : 2 ^ n < Fintype.card ι) :
    δ / 2 ≤ T.entropyNumber n := by
  classical
  rcases le_or_gt δ 0 with hδ | hδ
  · exact (div_nonpos_of_nonpos_of_nonneg hδ zero_le_two).trans (T.entropyNumber n).coe_nonneg
  have hinj : Function.Injective (T ∘ f) := fun i j hij ↦ by
    by_contra hne
    have hle : δ ≤ dist (T (f i)) (T (f j)) := hsep hne
    have hij' : T (f i) = T (f j) := hij
    simp [hij', hδ.not_ge] at hle
  refine div_two_le_entropyNumber_of_subset_image (s := Finset.univ.image (T ∘ f)) ?_ ?_ ?_
  · rw [Finset.coe_image, Finset.coe_univ, image_univ]
    rintro _ ⟨i, rfl⟩
    exact ⟨f i, hf i, rfl⟩
  · rw [Finset.coe_image]
    rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩ hne
    exact hsep (ne_of_apply_ne (T ∘ f) hne)
  · rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- **Separation lower bound via preimages.** If `s ⊆ closedBall 0 1` has strictly more than
`2 ^ n` points whose images under `T` lie at mutual distance at least `δ`, then `δ / 2 ≤ eₙ(T)`. -/
theorem div_two_le_entropyNumber_of_le_dist {T : E →L[𝕜] F} {n : ℕ} {s : Finset E} {δ : ℝ}
    (hs : (s : Set E) ⊆ closedBall 0 1)
    (hsep : (s : Set E).Pairwise fun x y ↦ δ ≤ dist (T x) (T y)) (hcard : 2 ^ n < s.card) :
    δ / 2 ≤ T.entropyNumber n :=
  div_two_le_entropyNumber_of_pairwise_le_dist (ι := s) (f := Subtype.val) (fun x ↦ hs x.property)
    (fun _ _ hne ↦ hsep (Subtype.prop _) (Subtype.prop _) (Subtype.coe_ne_coe.mpr hne))
    (by simpa only [Fintype.card_coe] using hcard)

/-! ### Vanishing and positivity -/

/-- Sampling `(a ^ k) • u` for `0 ≤ k ≤ 2 ^ n` bounds `eₙ(T)` below on any unit-ball vector `u` and
contractive scalar `a`. -/
private theorem pow_mul_one_sub_mul_div_two_le_entropyNumber {T : E →L[𝕜] F} {u : E}
    (hu : u ∈ closedBall 0 1) {a : 𝕜} (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖a‖ ^ (2 ^ n) * (1 - ‖a‖) * ‖T u‖ / 2 ≤ T.entropyNumber n := by
  let f : Fin (2 ^ n + 1) → E := fun k ↦ (a ^ (k : ℕ)) • u
  let δ : ℝ := ‖a‖ ^ (2 ^ n) * (1 - ‖a‖) * ‖T u‖
  have hsep_lt : ∀ {i j : Fin (2 ^ n + 1)}, (i : ℕ) < j → δ ≤ dist (T (f i)) (T (f j)) := by
    intro i j hij
    set m : ℕ := (j : ℕ) - (i : ℕ)
    have hj_eq : (j : ℕ) = (i : ℕ) + m := (Nat.add_sub_of_le hij.le).symm
    have hsub : T (f i) - T (f j) = (a ^ (i : ℕ) * (1 - a ^ m)) • T u := by
      simp only [f, map_smul, ← sub_smul, hj_eq, pow_add, mul_sub, mul_one]
    have hpow_i : ‖a‖ ^ (2 ^ n) ≤ ‖a‖ ^ (i : ℕ) :=
      pow_le_pow_of_le_one (norm_nonneg a) ha (Nat.lt_succ_iff.mp i.isLt)
    have h1_sub : 1 - ‖a‖ ≤ ‖(1 : 𝕜) - a ^ m‖ := by
      have hpow_m : ‖a ^ m‖ ≤ ‖a‖ := by
        simpa [norm_pow] using pow_le_pow_of_le_one (norm_nonneg a) ha (Nat.sub_pos_of_lt hij)
      have htri := norm_sub_norm_le (1 : 𝕜) (a ^ m)
      rw [norm_one] at htri
      linarith
    rw [dist_eq_norm, hsub, norm_smul, norm_mul, norm_pow]
    dsimp only [δ]
    have : 0 ≤ 1 - ‖a‖ := sub_nonneg.mpr ha
    gcongr
  refine div_two_le_entropyNumber_of_pairwise_le_dist (T := T) (n := n) (f := f)
    (fun k ↦ ?_) (fun i j hij ↦ ?_) (by simp)
  · rw [mem_closedBall_zero_iff, norm_smul, norm_pow]
    calc ‖a‖ ^ (k : ℕ) * ‖u‖
        ≤ 1 * 1 := by
          gcongr
          · exact pow_le_one₀ (norm_nonneg a) ha
          · exact mem_closedBall_zero_iff.mp hu
      _ = 1 := one_mul 1
  · dsimp only
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact hsep_lt hlt
    · rw [dist_comm]; exact hsep_lt hgt

/-- The `n`-th entropy number vanishes if and only if `‖T‖₊ = 0`. -/
theorem entropyNumber_eq_zero_iff_nnnorm_eq_zero {T : E →L[𝕜] F} {n : ℕ} :
    T.entropyNumber n = 0 ↔ ‖T‖₊ = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h ↦ entropyNumber_eq_zero_of_nnnorm_eq_zero h n⟩
  rw [← NNReal.coe_eq_zero, coe_nnNorm]
  obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt_one 𝕜
  refine le_antisymm (T.opNorm_le_bound le_rfl fun x ↦ ?_) (norm_nonneg T)
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 ‖x‖
  have hc_pos : 0 < ‖c‖ := (norm_nonneg x).trans_lt hc
  have hu : c⁻¹ • x ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
    exact (inv_mul_le_iff₀ hc_pos).mpr (by simpa using hc.le)
  have hle := pow_mul_one_sub_mul_div_two_le_entropyNumber (T := T) hu ha1.le n
  rw [h0, NNReal.coe_zero, map_smul, norm_smul, norm_inv] at hle
  have hpos : 0 < ‖a‖ ^ (2 ^ n) * (1 - ‖a‖) * ‖c‖⁻¹ / 2 := by
    have : 0 < 1 - ‖a‖ := sub_pos.mpr ha1
    positivity
  have hTx : ‖T x‖ ≤ 0 := nonpos_of_mul_nonpos_right (by linarith) hpos
  simpa using hTx

/-! ### Total boundedness and compactness -/

/-- Entropy numbers tend to zero if and only if `T '' closedBall 0 1` is totally bounded. -/
theorem tendsto_entropyNumber_atTop_nhds_zero_iff_totallyBounded (T : E →L[𝕜] F) :
    Tendsto T.entropyNumber atTop (𝓝 0) ↔
      TotallyBounded ((T : E → F) '' closedBall 0 1) := by
  constructor
  · intro h
    rw [Metric.totallyBounded_iff]
    intro ε hε
    set δ : ℝ≥0 := ⟨ε / 2, by positivity⟩
    have hδ : 0 < δ := by exact_mod_cast half_pos hε
    obtain ⟨n, hn⟩ := (h.eventually (Iio_mem_nhds hδ)).exists
    obtain ⟨N, -, hcov⟩ := exists_isCover_of_entropyNumber_lt hn
    refine ⟨N, N.finite_toSet, hcov.subset_iUnion_closedBall.trans ?_⟩
    exact iUnion₂_mono fun y _ ↦ closedBall_subset_ball (half_lt_self hε)
  · intro h
    exact T.antitone_entropyNumber.tendsto_atTop_nhds_zero_of_isCover h (C := 1)
      fun _ _ hN ↦ by simpa using T.entropyNumber_le_of_isCover Nat.lt_two_pow_self.le hN

/-- Every compact operator has entropy numbers tending to zero. -/
theorem _root_.IsCompactOperator.tendsto_entropyNumber {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    Tendsto T.entropyNumber atTop (𝓝 0) :=
  T.tendsto_entropyNumber_atTop_nhds_zero_iff_totallyBounded.mpr
    (hT.totallyBounded_image_closedBall 1)

/-- For a complete codomain, `T` is compact if and only if its entropy numbers tend to zero. -/
theorem isCompactOperator_iff_tendsto_entropyNumber [CompleteSpace F] (T : E →L[𝕜] F) :
    IsCompactOperator T ↔ Tendsto T.entropyNumber atTop (𝓝 0) :=
  (isCompactOperator_iff_totallyBounded_image_closedBall T.toLinearMap one_pos).trans
    T.tendsto_entropyNumber_atTop_nhds_zero_iff_totallyBounded.symm

end Seminormed

section NormedCodomain

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- With a normed codomain, `eₙ(T) = 0` if and only if `T = 0`. -/
@[simp]
theorem entropyNumber_eq_zero_iff {T : E →L[𝕜] F} {n : ℕ} :
    T.entropyNumber n = 0 ↔ T = 0 :=
  entropyNumber_eq_zero_iff_nnnorm_eq_zero.trans T.opNNNorm_eq_zero_iff

/-- **Failure of the rank axiom.** Every nonzero operator into a normed space has strictly
positive entropy numbers at all indices. -/
theorem entropyNumber_pos {T : E →L[𝕜] F} (hT : T ≠ 0) (n : ℕ) : 0 < T.entropyNumber n :=
  pos_iff_ne_zero.mpr (entropyNumber_eq_zero_iff.not.mpr hT)

end NormedCodomain

end NontriviallyNormedField

/-! ### Multiplicativity and the two-sided ideal inequality -/

section DenselyNormedField

variable {𝕜 E F G H : Type*} [DenselyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- **Mixed-index multiplicative inequality.** Over a densely normed field,
`e_{m+n}(B ∘L S) ≤ eₘ(B) * eₙ(S)`. -/
theorem entropyNumber_comp_add_le_mul (B : F →L[𝕜] G) (S : E →L[𝕜] F) (m n : ℕ) :
    (B ∘L S).entropyNumber (m + n) ≤ B.entropyNumber m * S.entropyNumber n := by
  classical
  rw [entropyNumber_def B, NNReal.iInf_mul]
  refine le_ciInf fun ε₁ ↦ ?_
  rw [entropyNumber_def S, NNReal.mul_iInf]
  refine le_ciInf fun ε₂ ↦ ?_
  obtain ⟨N₁, hN₁, hcov₁⟩ := ε₁.property
  obtain ⟨N₂, hN₂, hcov₂⟩ := ε₂.property
  -- For any `r > ε₂`, pick a scalar `c` with `ε₂ < ‖c‖₊ < r` to rescale `ε₂`-balls into `B_F`.
  have key : ∀ r : ℝ≥0, ε₂.val < r → (B ∘L S).entropyNumber (m + n) ≤ ε₁.val * r := by
    intro r hr
    obtain ⟨c, hc₁, hc₂⟩ := NormedField.exists_lt_nnNorm_lt 𝕜 hr
    have hc0 : c ≠ 0 := nnNorm_pos.mp (zero_le.trans_lt hc₁)
    have hcov : (B ∘L S : E → G) '' closedBall 0 1 ⊆
        ⋃ w ∈ (Finset.image₂ (fun z y ↦ B y + c • z) N₁ N₂ : Set G),
          closedBall w ↑(ε₁.val * ‖c‖₊) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcov₂ ⟨x, hx, rfl⟩)
      -- Rescale `S x - y` by `c⁻¹` so it lands inside the closed unit ball of `F`.
      set u : F := c⁻¹ • (S x - y)
      have hu : u ∈ closedBall (0 : F) 1 := by
        rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
        have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
        have hnorm : ‖S x - y‖ ≤ ‖c‖ := by
          refine (dist_eq_norm (S x) y ▸ mem_closedBall.mp hxy).trans ?_
          exact_mod_cast hc₁.le
        exact (inv_mul_le_iff₀ hcpos).mpr (by simpa using hnorm)
      obtain ⟨z, hz, huz⟩ := mem_iUnion₂.mp (hcov₁ ⟨u, hu, rfl⟩)
      refine mem_iUnion₂.mpr
        ⟨B y + c • z, Finset.mem_coe.mpr (Finset.mem_image₂_of_mem hz hy), ?_⟩
      have hdecomp : B (S x) - (B y + c • z) = c • (B u - z) := by
        have hSu : S x = y + c • u := by simp [u, smul_inv_smul₀ hc0]
        rw [hSu, map_add, map_smul, add_sub_add_left_eq_sub, ← smul_sub]
      rw [mem_closedBall, dist_eq_norm, comp_apply, hdecomp, norm_smul, NNReal.coe_mul,
        coe_nnNorm, mul_comm (ε₁.val : ℝ)]
      exact mul_le_mul_of_nonneg_left
        (dist_eq_norm (B u) z ▸ mem_closedBall.mp huz) (norm_nonneg c)
    have hcard : (Finset.image₂ (fun z y ↦ B y + c • z) N₁ N₂).card ≤ 2 ^ (m + n) :=
      (Finset.card_image₂_le _ _ _).trans
        ((Nat.mul_le_mul hN₁ hN₂).trans_eq (pow_add 2 m n).symm)
    exact ((B ∘L S).entropyNumber_le_of_subset_biUnion hcard hcov).trans
      (mul_le_mul_right hc₂.le ε₁.val)
  rcases eq_or_ne ε₁.val 0 with hε₁ | hε₁
  · simpa [hε₁] using key (ε₂.val + 1) (lt_add_one _)
  · refine le_of_forall_pos_le_add fun η hη ↦ ?_
    have hpos : 0 < η / ε₁.val := div_pos hη (pos_iff_ne_zero.mpr hε₁)
    calc (B ∘L S).entropyNumber (m + n)
        ≤ ε₁.val * (ε₂.val + η / ε₁.val) := key _ (lt_add_of_pos_right _ hpos)
      _ = ε₁.val * ε₂.val + η := by rw [mul_add, mul_div_cancel₀ _ hε₁]

/-- Precomposition scales entropy numbers by at most the operator norm over a densely normed
field. -/
theorem entropyNumber_comp_le_right (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (T ∘L A).entropyNumber n ≤ T.entropyNumber n * ‖A‖₊ :=
  calc (T ∘L A).entropyNumber n
      = (T ∘L A).entropyNumber (n + 0) := rfl
    _ ≤ T.entropyNumber n * A.entropyNumber 0 := T.entropyNumber_comp_add_le_mul A n 0
    _ ≤ T.entropyNumber n * ‖A‖₊ := by gcongr; exact A.entropyNumber_le_nnnorm 0

/-- **Two-sided ideal inequality** for entropy numbers over a densely normed field. -/
theorem entropyNumber_comp_comp_le (B : G →L[𝕜] H) (T : F →L[𝕜] G) (A : E →L[𝕜] F) (n : ℕ) :
    (B ∘L T ∘L A).entropyNumber n ≤ ‖B‖₊ * T.entropyNumber n * ‖A‖₊ := by
  refine (B.entropyNumber_comp_le_left (T ∘L A) n).trans ?_
  rw [mul_assoc]
  gcongr
  exact T.entropyNumber_comp_le_right A n

/-- In an infinite-dimensional normed space over a complete densely normed field, every entropy
number of the identity map is at least `1 / 2`. -/
theorem one_half_le_entropyNumber_id_of_not_finiteDimensional [CompleteSpace 𝕜]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] (hX : ¬ FiniteDimensional 𝕜 X) (n : ℕ) :
    (1 / 2 : ℝ≥0) ≤ (ContinuousLinearMap.id 𝕜 X).entropyNumber n := by
  by_contra! hlt
  set e : ℝ := ((ContinuousLinearMap.id 𝕜 X).entropyNumber n : ℝ)
  have he0 : 0 ≤ e := NNReal.coe_nonneg _
  have he : e < 1 / 2 := by exact_mod_cast hlt
  have hpe : 0 < 1 / 2 + e := by linarith
  have h1 : (1 : ℝ) < (1 / 2 + e)⁻¹ := (one_lt_inv₀ hpe).mpr (by linarith)
  obtain ⟨c, hc1, hc2⟩ := NormedField.exists_lt_norm_lt 𝕜 zero_le_one h1
  obtain ⟨d, hcd, hd⟩ := NormedField.exists_lt_norm_lt 𝕜 (zero_le_one.trans hc1.le) hc2
  have hd0 : d ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans (hc1.trans hcd))
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  -- Riesz's lemma gives an infinite `1`-separated sequence inside `closedBall 0 ‖d‖`.
  obtain ⟨f, hf_norm, hf_sep⟩ := exists_seq_norm_le_one_le_norm_sub' hc1 hcd hX
  have hbound : ‖d‖⁻¹ / 2 ≤ e := by
    refine div_two_le_entropyNumber_of_pairwise_le_dist (T := ContinuousLinearMap.id 𝕜 X)
      (f := fun k : Fin (2 ^ n + 1) ↦ d⁻¹ • f k) (fun k ↦ ?_) (fun i j hij ↦ ?_) (by simp)
    · rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
      exact (inv_mul_le_iff₀ hdpos).mpr (by simpa using hf_norm k)
    · simp only [id_apply, dist_eq_norm, ← smul_sub, norm_smul, norm_inv]
      exact le_mul_of_one_le_right (inv_nonneg.mpr hdpos.le) (hf_sep (Fin.val_ne_of_ne hij))
  have hlt_inv : 1 / 2 + e < ‖d‖⁻¹ := (lt_inv_comm₀ hpe hdpos).mpr hd
  linarith

end DenselyNormedField

/-! ### Segment lower bound, zeroth term, and the identity lower bound over `ℝ` and `ℂ` -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

section Seminormed

variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Segment lower bound.** Over `ℝ` or `ℂ`, `‖T‖₊ / 2 ^ n ≤ eₙ(T)`. -/
theorem nnnorm_div_two_pow_le_entropyNumber (T : E →L[𝕜] F) (n : ℕ) :
    ‖T‖₊ / 2 ^ n ≤ T.entropyNumber n := by
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [div_le_iff₀ (by positivity)]
  refine T.opNorm_le_of_unit_norm (by positivity) fun u hu_norm ↦ ?_
  -- Sample `2 ^ n + 1` equally spaced points along the segment `[-u, u]`.
  let f : Fin (2 ^ n + 1) → E := fun k ↦ ((-1 + 2 * (k : ℝ) / 2 ^ n : ℝ) : 𝕜) • u
  have hbound : (2 * ‖T u‖ / 2 ^ n) / 2 ≤ T.entropyNumber n := by
    refine div_two_le_entropyNumber_of_pairwise_le_dist (T := T) (n := n) (f := f)
      (fun k ↦ ?_) (fun i j hij ↦ ?_) (by simp)
    · rw [mem_closedBall_zero_iff, norm_smul, RCLike.norm_ofReal, hu_norm, mul_one, abs_le]
      have hk : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
      have hdiv0 : (0 : ℝ) ≤ 2 * (k : ℝ) / 2 ^ n := by positivity
      have hdiv2 : 2 * (k : ℝ) / 2 ^ n ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
      constructor <;> linarith
    · dsimp only
      have hsub : T (f i) - T (f j) = ((2 * ((i : ℝ) - (j : ℝ)) / 2 ^ n : ℝ) : 𝕜) • T u := by
        simp only [f, map_smul, ← sub_smul]
        congr 1; push_cast; ring
      have h1 : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
        have hne : ((i : ℕ) : ℤ) - (j : ℕ) ≠ 0 :=
          sub_ne_zero.mpr (Int.ofNat_inj.not.mpr (Fin.val_ne_of_ne hij))
        exact_mod_cast Int.one_le_abs hne
      rw [dist_eq_norm, hsub, norm_smul, RCLike.norm_ofReal, abs_div, abs_mul,
        abs_of_pos zero_lt_two, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
      calc 2 * ‖T u‖ / 2 ^ n
          = (2 * 1 / 2 ^ n) * ‖T u‖ := by ring
        _ ≤ (2 * |(i : ℝ) - (j : ℝ)| / 2 ^ n) * ‖T u‖ := by gcongr
  have hdiv : ‖T u‖ / 2 ^ n ≤ T.entropyNumber n := (le_of_eq (by ring)).trans hbound
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ n)).mp hdiv

/-- Over `ℝ` or `ℂ`, the zeroth entropy number equals the operator norm. -/
@[simp]
theorem entropyNumber_zero (T : E →L[𝕜] F) : T.entropyNumber 0 = ‖T‖₊ :=
  (T.entropyNumber_le_nnnorm 0).antisymm (by simpa using T.nnnorm_div_two_pow_le_entropyNumber 0)

/-- Over `ℝ` or `ℂ`, the supremum of all entropy numbers is the operator norm. -/
@[simp]
theorem iSup_entropyNumber (T : E →L[𝕜] F) : ⨆ n, T.entropyNumber n = ‖T‖₊ :=
  (ciSup_le T.entropyNumber_le_nnnorm).antisymm
    (T.entropyNumber_zero ▸ le_ciSup T.bddAbove_range_entropyNumber 0)

end Seminormed

section Normed

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Identity lower bound.** Over `ℝ` or `ℂ`, `1 / 2 ≤ eₙ(id_X)` for every index `n` strictly
below the dimension of `X`. -/
theorem one_half_le_entropyNumber_id {n : ℕ} (hn : (n : Cardinal) < Module.rank 𝕜 X) :
    (1 / 2 : ℝ≥0) ≤ (ContinuousLinearMap.id 𝕜 X).entropyNumber n := by
  by_cases hfin : FiniteDimensional 𝕜 X
  · -- Finite dimension: compare Haar volumes of `closedBall 0 1` and at most `2 ^ n` `ε`-balls.
    have : NormedSpace ℝ X := .restrictScalars ℝ 𝕜 X
    have : FiniteDimensional ℝ X := FiniteDimensional.trans ℝ 𝕜 X
    have hn_fin : n < Module.finrank 𝕜 X := by
      rwa [← Module.finrank_eq_rank 𝕜 X, Nat.cast_lt] at hn
    have hD : n + 1 ≤ Module.finrank ℝ X := by
      have hk : 1 ≤ Module.finrank ℝ 𝕜 := Module.finrank_pos
      calc n + 1 ≤ Module.finrank 𝕜 X := hn_fin
        _ = 1 * Module.finrank 𝕜 X := (one_mul _).symm
        _ ≤ Module.finrank ℝ 𝕜 * Module.finrank 𝕜 X := Nat.mul_le_mul_right _ hk
        _ = Module.finrank ℝ X := Module.finrank_mul_finrank ℝ 𝕜 X
    refine le_entropyNumber_iff_isCover.mpr fun ε N hN hcov ↦ ?_
    have hcov' : IsCover ε (closedBall (0 : X) (1 : ℝ≥0)) N := by simpa using hcov
    have hvol := TauCeti.pow_finrank_le_card_mul_pow_of_isCover_closedBall hcov'
    by_contra! hlt
    have hlt' : (ε : ℝ) < 1 / 2 := by exact_mod_cast hlt
    have hupper : (N.card : ℝ) * (ε : ℝ) ^ Module.finrank ℝ X ≤ 1 / 2 :=
      calc (N.card : ℝ) * (ε : ℝ) ^ Module.finrank ℝ X
          ≤ 2 ^ n * (1 / 2 : ℝ) ^ Module.finrank ℝ X := by
            gcongr
            exact_mod_cast hN
        _ ≤ 2 ^ n * (1 / 2 : ℝ) ^ (n + 1) :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one (by positivity) (by norm_num) hD) (by positivity)
        _ = 1 / 2 := by rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
    rw [NNReal.coe_one, one_pow] at hvol
    linarith
  · exact one_half_le_entropyNumber_id_of_not_finiteDimensional hfin n

end Normed

end RCLike

end ContinuousLinearMap

/-! ### Family wrapper in `TauCeti.SNumbers` -/

universe u

namespace TauCeti.SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

/-- The family of dyadic entropy numbers on bounded operators between normed spaces. Over `ℝ` or
`ℂ` (`RCLike 𝕜`) they form a pseudo-s-number family (with the two-sided ideal inequality holding
more generally over any `DenselyNormedField 𝕜`), whereas over any nontrivially normed field they
fail the finite-rank vanishing axiom (`not_isSNumberSequence_entropy`). -/
noncomputable def entropy : SNumberFamily 𝕜 :=
  fun T ↦ T.entropyNumber

/-- Evaluation of the entropy family is `ContinuousLinearMap.entropyNumber`. -/
@[simp]
theorem entropy_apply {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (T : X →L[𝕜] Y) (n : ℕ) : entropy T n = T.entropyNumber n := (rfl)

/-- Entropy numbers do not form an s-number sequence, because they fail the finite-rank vanishing
axiom. -/
theorem not_isSNumberSequence_entropy :
    ¬ IsSNumberSequence (entropy (𝕜 := 𝕜)) := by
  intro hs
  -- Witness: `id_{Fin 1 → 𝕜}` has rank `1` yet `e₁(id_{Fin 1 → 𝕜}) > 0`.
  let I := ContinuousLinearMap.id 𝕜 (Fin 1 → 𝕜)
  have hrank : I.rank ≤ (1 : ℕ) := by
    simpa [I] using (LinearMap.rank_le_domain I.toLinearMap).trans_eq (rank_fin_fun 1)
  have hzero : I.entropyNumber 1 = 0 := hs.eq_zero_of_rank_le hrank
  have hne : I ≠ 0 := fun h ↦ by
    have h1 := congrFun (ContinuousLinearMap.ext_iff.mp h (fun _ : Fin 1 ↦ (1 : 𝕜))) (0 : Fin 1)
    simp [I] at h1
  exact (I.entropyNumber_pos hne 1).ne' hzero

end TauCeti.SNumbers
