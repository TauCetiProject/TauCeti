/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5, qwen3.8-27b-dbirks-hyperqwen-huge
-/
/-
Adapted from: Spectra (https://github.com/adambornemann-glitch/Spectra),
  `Spectra/ProjValMeasure/Basic.lean` at commit
  `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`.
Copyright (c) 2026 Spectra Formalization Project.
Authors: Adam Bornemann
Released under the Apache 2.0 license.
-/
module

public import TauCeti.Analysis.InnerProductSpace.OperatorIdentities
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.Sum
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.MeasureTheory.Measure.DisjointUnion
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Projection-valued measures

A projection-valued measure on the measurable sets of an arbitrary measurable
space `X`, acting on a complex Hilbert space `H`.

The finite diagonal scalar measures are provided by the DKPS donor's `diag`
field. Their measure-theoretic countable additivity supplies strong
countable additivity of the projections.
Idempotence, self-adjointness, positivity, and finite additivity are proved
from the structure's laws.

## Main declarations

* `ProjValMeasure X H`: the structure — a map `proj` from measurable sets to
  operators, the diagonal measures `diag : H → Measure X`, the weld
  `inner_proj`, the normalization `proj_univ : P(X) = 1`, and the
  multiplicativity law `proj_inter`.
* `proj_idem`, `isSelfAdjoint_proj`, `isPositive_proj`, `proj_mul_eq_left_of_subset`,
  `proj_range_mono`, `proj_union`, `proj_compl`, `norm_proj_apply_le`:
  the classical PVM laws, recovered from the structure.
* `hasSum_proj_of_pairwise_disjoint`: unconditional strong countable additivity
  (`HasSum`) on a pairwise-disjoint measurable family; `tendsto_sum_proj_of_pairwise_disjoint`
  gives convergence of the natural-order partial sums.
* `diag`, `diag_real_univ`, `diag_univ`: the finite diagonal scalar
  measures carried by the structure, and their real/extended-real total masses.
* `ext_of_diag`, `ext`, `ext_iff_diag`, `ext_iff`: extensionality from either
  data field.

## References

* Adam Bornemann, *Spectra*, `Spectra/ProjValMeasure/Basic.lean`,
  https://github.com/adambornemann-glitch/Spectra
  (commit `8dbaaf6728d1342ae16acf79fd7eef7c59b37e63`).
* AIQ-Kitware, *DKPS formalization*,
  `ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean`,
  https://github.com/AIQ-Kitware/aiq-dkps-formalization.

-/

public section

open MeasureTheory Filter Function
open scoped InnerProduct InnerProductSpace ENNReal Topology

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The structure -/

/-- A **projection-valued measure** on the measurable sets of `X`, acting on a
complex Hilbert space `H`.

The diagonal scalar measures `diag ξ` are supplied as finite measures,
related to the projections by `inner_proj`. This follows the donor's carrier
representation, in which the diagonal measures are uniquely determined by
`proj`. Idempotence, self-adjointness,
positivity, finite additivity, contraction, and strong countable additivity
follow from these laws. -/
structure ProjValMeasure (X : Type*) [MeasurableSpace X] (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The projection assigned to each measurable set. -/
  proj : ∀ B : Set X, MeasurableSet B → (H →L[ℂ] H)
  /-- The diagonal scalar measures, carried as data. -/
  diag : H → Measure X
  /-- Each diagonal measure is finite (its mass is `‖ξ‖ ^ 2`, by `diag_univ_toReal`). -/
  diag_finite : ∀ ξ : H, IsFiniteMeasure (diag ξ)
  /-- The weld: diagonal matrix elements of the projections are the diagonal measures. -/
  inner_proj : ∀ (B : Set X) (hB : MeasurableSet B) (ξ : H),
    ⟪ξ, proj B hB ξ⟫_ℂ = (((diag ξ) B).toReal : ℂ)
  /-- The whole space carries the identity. -/
  proj_univ : proj Set.univ MeasurableSet.univ = ContinuousLinearMap.id ℂ H
  /-- Multiplicativity: intersection of sets is composition of projections. -/
  proj_inter : ∀ (B₁ B₂ : Set X) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂),
    proj B₁ hB₁ * proj B₂ hB₂ = proj (B₁ ∩ B₂) (hB₁.inter hB₂)

attribute [simp] ProjValMeasure.proj_univ

namespace ProjValMeasure

/-! ## The classical axioms, recovered as theorems -/

/-- Each scalar diagonal measure is finite, as witnessed by the `diag_finite`
field. Its total mass is computed by `diag_univ`. -/
instance instIsFiniteMeasureDiag (P : ProjValMeasure X H) (ξ : H) :
    IsFiniteMeasure (P.diag ξ) :=
  P.diag_finite ξ

/-- The diagonal identity with the projection in the first inner-product slot. -/
lemma inner_proj_apply_left (P : ProjValMeasure X H) (B : Set X)
    (hB : MeasurableSet B) (ξ : H) :
    ⟪P.proj B hB ξ, ξ⟫_ℂ = (((P.diag ξ) B).toReal : ℂ) := by
  rw [← inner_conj_symm (P.proj B hB ξ) ξ, P.inner_proj, Complex.conj_ofReal]

/-- The projections do not depend on the measurability witness — proof
irrelevance: only the set matters. -/
lemma proj_congr (P : ProjValMeasure X H) {B₁ B₂ : Set X} (h : B₁ = B₂)
    (h₁ : MeasurableSet B₁) (h₂ : MeasurableSet B₂) :
    P.proj B₁ h₁ = P.proj B₂ h₂ := by
  subst h; rfl

/-- The projection of the empty measurable set is zero. -/
@[simp]
lemma proj_empty (P : ProjValMeasure X H) : P.proj ∅ MeasurableSet.empty = 0 := by
  apply ContinuousLinearMap.eq_of_diagonal
  intro ξ
  simp [P.inner_proj]

/-- Every measurable-set projection is idempotent. -/
@[simp]
lemma proj_idem (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B) :
    P.proj B hB * P.proj B hB = P.proj B hB := by
  rw [P.proj_inter B B hB hB]
  exact P.proj_congr (Set.inter_self B) (hB.inter hB) hB

/-- Every measurable-set projection is self-adjoint. -/
lemma isSelfAdjoint_proj (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B) :
    IsSelfAdjoint (P.proj B hB) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply ContinuousLinearMap.eq_of_diagonal
  intro ξ
  rw [ContinuousLinearMap.adjoint_inner_right, P.inner_proj_apply_left,
    P.inner_proj]

/-- Applying a measurable-set projection twice is the same as applying it once. -/
@[simp]
lemma proj_apply_proj (P : ProjValMeasure X H) (B : Set X)
    (hB : MeasurableSet B) (v : H) :
    P.proj B hB (P.proj B hB v) = P.proj B hB v := by
  calc
    P.proj B hB (P.proj B hB v) =
        (P.proj B hB * P.proj B hB) v :=
      (mul_apply_eq_comp (P.proj B hB) (P.proj B hB) v).symm
    _ = P.proj B hB v := by rw [P.proj_idem B hB]

/-- A measurable projection has the same matrix element when applied in both arguments. -/
lemma inner_proj_eq_inner_proj_proj (P : ProjValMeasure X H)
    (B : Set X) (hB : MeasurableSet B) (ψ ξ : H) :
    ⟪ψ, P.proj B hB ξ⟫_ℂ =
      ⟪P.proj B hB ψ, P.proj B hB ξ⟫_ℂ := by
  let T := P.proj B hB
  have hsym := (P.isSelfAdjoint_proj B hB).isSymmetric
  calc
    ⟪ψ, T ξ⟫_ℂ = ⟪T ψ, ξ⟫_ℂ := (hsym ψ ξ).symm
    _ = ⟪T (T ψ), ξ⟫_ℂ := by rw [P.proj_apply_proj]
    _ = ⟪T ψ, T ξ⟫_ℂ := hsym (T ψ) ξ

/-- Each measurable-set value of a PVM is an orthogonal (`star`) projection. -/
theorem isStarProjection_proj (P : ProjValMeasure X H) (B : Set X)
    (hB : MeasurableSet B) : IsStarProjection (P.proj B hB) := by
  exact (isStarProjection_iff' (p := P.proj B hB)).2
    ⟨P.proj_idem B hB, (P.isSelfAdjoint_proj B hB).star_eq⟩

/-- For each measurable set `B`, the operator `P(B)` is positive. -/
theorem isPositive_proj (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B) :
    (P.proj B hB).IsPositive :=
  .of_isStarProjection (P.isStarProjection_proj B hB)

/-- Measurable-set projections commute, because intersection is symmetric. -/
theorem proj_mul_comm (P : ProjValMeasure X H) (B C : Set X)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    P.proj B hB * P.proj C hC = P.proj C hC * P.proj B hB := by
  calc
    P.proj B hB * P.proj C hC = P.proj (B ∩ C) (hB.inter hC) :=
      P.proj_inter B C hB hC
    _ = P.proj (C ∩ B) (hC.inter hB) :=
      P.proj_congr (Set.inter_comm B C) (hB.inter hC) (hC.inter hB)
    _ = P.proj C hC * P.proj B hB := (P.proj_inter C B hC hB).symm

/-- Projections of disjoint measurable sets have zero product. -/
@[simp]
theorem proj_mul_eq_zero_of_disjoint (P : ProjValMeasure X H)
    {B C : Set X} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hd : Disjoint B C) : P.proj B hB * P.proj C hC = 0 := by
  rw [P.proj_inter B C hB hC,
    P.proj_congr (Disjoint.inter_eq hd) (hB.inter hC) MeasurableSet.empty,
    P.proj_empty]

/-- For measurable `B ⊆ C`, the projection product `P(B) * P(C)` is `P(B)`. -/
theorem proj_mul_eq_left_of_subset (P : ProjValMeasure X H) {B C : Set X} (hBC : B ⊆ C)
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    P.proj B hB * P.proj C hC = P.proj B hB := by
  rw [P.proj_inter B C hB hC]
  exact P.proj_congr (Set.inter_eq_left.mpr hBC) (hB.inter hC) hB

/-- Right absorption: if `B ⊆ C`, then `P(C) * P(B) = P(B)`. -/
theorem proj_mul_eq_right_of_subset (P : ProjValMeasure X H) {B C : Set X}
    (hBC : B ⊆ C) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    P.proj C hC * P.proj B hB = P.proj B hB := by
  rw [P.proj_mul_comm C B hC hB]
  exact P.proj_mul_eq_left_of_subset hBC hB hC

/-- If measurable `B ⊆ C`, then the range of `P(B)` is contained in the
range of `P(C)`. -/
theorem proj_range_mono (P : ProjValMeasure X H) {B C : Set X}
    (hBC : B ⊆ C) (hB : MeasurableSet B) (hC : MeasurableSet C) :
    (P.proj B hB).range ≤ (P.proj C hC).range := by
  rw [← P.proj_mul_eq_right_of_subset hBC hB hC]
  exact LinearMap.range_comp_le_range _ _

/-- For disjoint measurable sets, the projection of their union is the sum of
their projections. -/
lemma proj_union (P : ProjValMeasure X H) {B₁ B₂ : Set X}
    (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (hd : Disjoint B₁ B₂) :
    P.proj (B₁ ∪ B₂) (hB₁.union hB₂) = P.proj B₁ hB₁ + P.proj B₂ hB₂ := by
  have hdiag (ξ : H) :
      ⟪ξ, P.proj (B₁ ∪ B₂) (hB₁.union hB₂) ξ⟫_ℂ =
        ⟪ξ, (P.proj B₁ hB₁ + P.proj B₂ hB₂) ξ⟫_ℂ := by
    simp only [add_apply, inner_add_right, P.inner_proj, measure_union hd hB₂,
      ENNReal.toReal_add (measure_ne_top (μ := P.diag ξ) (s := B₁))
        (measure_ne_top (μ := P.diag ξ) (s := B₂))]
    push_cast
    ring
  exact ContinuousLinearMap.eq_of_diagonal _ _ hdiag

/-- **Complementation**: the projection of a complement is the complementary
projection. -/
@[simp]
lemma proj_compl (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B) :
    P.proj Bᶜ hB.compl = ContinuousLinearMap.id ℂ H - P.proj B hB := by
  have hsum := P.proj_union hB hB.compl disjoint_compl_right
  rw [P.proj_congr (Set.union_compl_self B) (hB.union hB.compl) MeasurableSet.univ,
    P.proj_univ] at hsum
  linear_combination (norm := module) -hsum

/-- The squared norm of the projection of `ξ` equals its diagonal measure
on the measurable set, interpreted as a real number. -/
lemma norm_sq_proj_apply (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B)
    (ξ : H) :
    ‖P.proj B hB ξ‖ ^ 2 = ((P.diag ξ) B).toReal := by
  have h1 : ⟪P.proj B hB ξ, P.proj B hB ξ⟫_ℂ = ⟪ξ, P.proj B hB ξ⟫_ℂ :=
    (P.inner_proj_eq_inner_proj_proj B hB ξ ξ).symm
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), h1, P.inner_proj, RCLike.re_eq_complex_re,
    Complex.ofReal_re]

/-- Total mass of the diagonal scalar measure, as a real number. -/
lemma diag_univ_toReal (P : ProjValMeasure X H) (ξ : H) :
    ((P.diag ξ) Set.univ).toReal = ‖ξ‖ ^ 2 := by
  -- The projection of the whole space is the identity, so its norm identity
  -- already computes the mass, without any complex-real coercion argument.
  simpa [P.proj_univ] using
    (P.norm_sq_proj_apply Set.univ MeasurableSet.univ ξ).symm

/-- The total mass of the diagonal measure as a real number. -/
@[simp]
theorem diag_real_univ (P : ProjValMeasure X H) (ξ : H) :
    (P.diag ξ).real Set.univ = ‖ξ‖ ^ 2 := by
  simpa only [measureReal_def] using P.diag_univ_toReal ξ

/-- The total mass of the diagonal measure in `ℝ≥0∞`. -/
@[simp]
theorem diag_univ (P : ProjValMeasure X H) (ξ : H) :
    P.diag ξ Set.univ = ‖ξ‖ₑ ^ 2 := by
  calc
    P.diag ξ Set.univ =
        ENNReal.ofReal ((P.diag ξ Set.univ).toReal) :=
      (ENNReal.ofReal_toReal
        (measure_ne_top (μ := P.diag ξ) (s := Set.univ))).symm
    _ = ENNReal.ofReal (‖ξ‖ ^ 2) :=
      congrArg ENNReal.ofReal (P.diag_univ_toReal ξ)
    _ = ‖ξ‖ₑ ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg ξ), ofReal_norm]

/-- For every measurable set `B`, `P(B)` is a contraction on vectors. -/
lemma norm_proj_apply_le (P : ProjValMeasure X H) (B : Set X) (hB : MeasurableSet B)
    (ξ : H) :
    ‖P.proj B hB ξ‖ ≤ ‖ξ‖ := by
  simpa using (P.proj B hB).le_of_opNorm_le (P.isStarProjection_proj B hB).norm_le ξ

/-! ## Strong countable additivity

For a pairwise-disjoint measurable family `(B_k)` with measurable union `B`,
write `S n = ∑_{k < n} P(B_k)`.  The diagonal measures are genuine measures,
so `μ(B) = ∑' μ(B_k)` for every `ξ`; the squared distance
`‖(S n) ξ - P(B) ξ‖²` then equals `μ(B) - ∑_{k < n} μ(B_k)` — the mass of
`B` not yet covered — and that tends to `0`.  This is strong countable
additivity: the partial sums converge strongly to `P(B)`. -/

private def partialSum (P : ProjValMeasure X H) (f : ℕ → Set X)
    (hf : ∀ n, MeasurableSet (f n)) (n : ℕ) : H →L[ℂ] H :=
  ∑ k < n, P.proj (f k) (hf k)

private theorem partialSum_zero (P : ProjValMeasure X H) (f : ℕ → Set X)
    (hf : ∀ n, MeasurableSet (f n)) : partialSum P f hf 0 = 0 :=
  Finset.sum_empty

private theorem partialSum_succ (P : ProjValMeasure X H) (f : ℕ → Set X)
    (hf : ∀ n, MeasurableSet (f n)) (n : ℕ) :
    partialSum P f hf (n + 1) = partialSum P f hf n + P.proj (f n) (hf n) := by
  simp [partialSum]

private theorem partialSum_idem (P : ProjValMeasure X H) {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (hdisj : Pairwise (Disjoint on f)) (n : ℕ) :
    partialSum P f hf n * partialSum P f hf n = partialSum P f hf n := by
  induction n with
  | zero => simp [partialSum_zero]
  | succ n ih =>
    rw [partialSum_succ, mul_add, add_mul, add_mul]
    -- the cross terms vanish: the sets are pairwise disjoint
    have hzero : partialSum P f hf n * P.proj (f n) (hf n) = 0 := by
      rw [partialSum, Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro k hk
      have hlt : k < n := by simpa using hk
      exact P.proj_mul_eq_zero_of_disjoint (hf k) (hf n) (hdisj (ne_of_lt hlt))
    have hzero' : P.proj (f n) (hf n) * partialSum P f hf n = 0 := by
      rw [partialSum, Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro k hk
      have hlt : k < n := by simpa using hk
      exact P.proj_mul_eq_zero_of_disjoint (hf n) (hf k) (hdisj (by omega))
    -- the only surviving term is `P_n P_n`, which is `P_n` again:
    have hsq : P.proj (f n) (hf n) * P.proj (f n) (hf n) = P.proj (f n) (hf n) :=
      P.proj_idem (f n) (hf n)
    rw [hzero, hzero', add_zero, zero_add, ih, hsq]

private theorem partialSum_selfAdjoint (P : ProjValMeasure X H) {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (n : ℕ) :
    IsSelfAdjoint (partialSum P f hf n) := by
  induction n with
  | zero => simp [partialSum_zero, IsSelfAdjoint.zero]
  | succ n ih =>
    rw [partialSum_succ]
    exact IsSelfAdjoint.add ih
      (P.isSelfAdjoint_proj (f n) (hf n))

private theorem partialSum_mul_univ (P : ProjValMeasure X H) {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (n : ℕ) :
    partialSum P f hf n * P.proj (⋃ k, f k) (MeasurableSet.iUnion hf) =
      partialSum P f hf n := by
  induction n with
  | zero => simp [partialSum_zero, zero_mul]
  | succ n ih =>
    rw [partialSum_succ, add_mul]
    rw [ih, P.proj_mul_eq_left_of_subset (Set.subset_iUnion f n)
      (hf n) (MeasurableSet.iUnion hf)]


/-- The diagonal-measure mass `∑_{k < n} μ_ξ(B_k)` of the first `n` sets equals the squared norm of
`(∑_{k < n} P(B_k)) ξ`. -/
private theorem norm_sq_partialSum (P : ProjValMeasure X H) {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (hdisj : Pairwise (Disjoint on f)) (ξ : H) (n : ℕ) :
    ‖partialSum P f hf n ξ‖ ^ 2 = (∑ k ∈ Finset.range n, P.diag ξ (f k)).toReal := by
  have hfin : ∀ k ∈ Finset.range n, P.diag ξ (f k) ≠ ⊤ :=
    fun k _ => measure_ne_top (μ := P.diag ξ) (s := f k)
  have hdiagCore : ⟪ξ, partialSum P f hf n ξ⟫_ℂ =
      (((∑ k ∈ Finset.range n, P.diag ξ (f k)).toReal : ℝ) : ℂ) := by
    rw [ENNReal.toReal_sum hfin]
    push_cast
    simp only [partialSum, Nat.Iio_eq_range, sum_apply, inner_sum]
    exact Finset.sum_congr rfl fun k _ => P.inner_proj (f k) (hf k) ξ
  have hself : ⟪partialSum P f hf n ξ, partialSum P f hf n ξ⟫_ℂ =
      (((∑ k ∈ Finset.range n, P.diag ξ (f k)).toReal : ℝ) : ℂ) := by
    calc
      ⟪partialSum P f hf n ξ, partialSum P f hf n ξ⟫_ℂ
          = ⟪ξ, partialSum P f hf n (partialSum P f hf n ξ)⟫_ℂ :=
        (partialSum_selfAdjoint P hf n).isSymmetric ξ _
      _ = ⟪ξ, partialSum P f hf n ξ⟫_ℂ := by
        rw [← mul_apply_eq_comp, partialSum_idem P hf hdisj n]
      _ = _ := hdiagCore
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hself]
  simp

/-- The squared distance from `(∑_{k < n} P(B_k)) ξ` to `P(⋃ B_k) ξ` is the mass of the union not
yet covered by the first `n` sets. -/
private theorem norm_sq_partialSum_sub (P : ProjValMeasure X H) {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (hdisj : Pairwise (Disjoint on f)) (ξ : H) (n : ℕ) :
    ‖partialSum P f hf n ξ - P.proj (⋃ k, f k) (MeasurableSet.iUnion hf) ξ‖ ^ 2 =
      (P.diag ξ (⋃ k, f k) - ∑ k ∈ Finset.range n, P.diag ξ (f k)).toReal := by
  have hUle := sum_measure_le_measure_iUnion (μ := P.diag ξ) (fun k => (hf k).nullMeasurableSet)
    hdisj.aedisjoint (Finset.range n)
  rw [ContinuousLinearMap.norm_sub_sq_of_selfAdjoint_idempotent_absorption _ _
    (partialSum_selfAdjoint P hf n) (partialSum_idem P hf hdisj n) (partialSum_mul_univ P hf n) ξ,
    P.norm_sq_proj_apply, norm_sq_partialSum P hf hdisj ξ n,
    ENNReal.toReal_sub_of_le hUle (measure_ne_top (μ := P.diag ξ) (s := ⋃ k, f k))]

/-- For pairwise disjoint measurable sets, the finite sums of their projections,
applied to any vector, converge to the projection of their union applied to that vector. -/
theorem tendsto_sum_proj_of_pairwise_disjoint {P : ProjValMeasure X H} {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (hdisj : Pairwise (Disjoint on f)) (ξ : H) :
    Tendsto (fun n => (∑ k < n, P.proj (f k) (hf k) : H →L[ℂ] H) ξ) Filter.atTop
        (𝓝 (P.proj (⋃ k, f k) (MeasurableSet.iUnion hf) ξ)) := by
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  -- The uncovered mass of the union tends to zero, by countable additivity of `P.diag ξ`.
  have hmass := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (tendsto_measure_iUnion_sub_sum_range (μ := P.diag ξ) (fun k => (hf k).nullMeasurableSet)
      hdisj.aedisjoint (measure_ne_top _ _))
  have hsq := (hmass.sqrt : Tendsto _ _ (𝓝 (Real.sqrt (ENNReal.toReal 0))))
  rw [ENNReal.toReal_zero, Real.sqrt_zero] at hsq
  refine hsq.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [← norm_sq_partialSum_sub P hf hdisj ξ n, Real.sqrt_sq (norm_nonneg _), partialSum]

/-- **Unconditional** strong countable additivity: disjoint measurable-set
projections form a summable family of vectors, and their sum is the projection
of the union. This is the `HasSum` interface needed by the spectral integral. -/
theorem hasSum_proj_of_pairwise_disjoint {P : ProjValMeasure X H} {f : ℕ → Set X}
    (hf : ∀ n, MeasurableSet (f n)) (hdisj : Pairwise (Disjoint on f)) (ξ : H) :
    HasSum (fun n => P.proj (f n) (hf n) ξ)
      (P.proj (⋃ n, f n) (MeasurableSet.iUnion hf) ξ) := by
  let V : ℕ → Submodule ℂ H := fun n => (P.proj (f n) (hf n)).range
  let v : ∀ n, V n := fun n => ⟨P.proj (f n) (hf n) ξ, ⟨ξ, rfl⟩⟩
  have hV : OrthogonalFamily ℂ (fun n => V n) (fun n => (V n).subtypeₗᵢ) := by
    intro i j hij u w
    obtain ⟨x, hx⟩ := u.property
    obtain ⟨y, hy⟩ := w.property
    -- The range's subtype isometry has the ambient inner product by definition.
    change ⟪(u : H), (w : H)⟫_ℂ = 0
    rw [← hx, ← hy]
    calc
      ⟪P.proj (f i) (hf i) x, P.proj (f j) (hf j) y⟫_ℂ =
          ⟪x, P.proj (f i) (hf i) (P.proj (f j) (hf j) y)⟫_ℂ :=
        (P.isSelfAdjoint_proj (f i) (hf i)).isSymmetric _ _
      _ = 0 := by
        rw [← mul_apply_eq_comp,
          P.proj_mul_eq_zero_of_disjoint (hf i) (hf j) (hdisj hij), zero_apply,
          inner_zero_right]
  have hmass : (∑' n, (P.diag ξ) (f n)) ≠ ∞ := by
    rw [← measure_iUnion₀ hdisj.aedisjoint (fun n => (hf n).nullMeasurableSet)]
    exact measure_ne_top (μ := P.diag ξ) (s := ⋃ n, f n)
  have hnorms : Summable (fun n => ‖v n‖ ^ 2) := by
    have heq : (fun n => ‖v n‖ ^ 2) =
        (fun n => ((P.diag ξ) (f n)).toReal) := by
      funext n
      -- The norm on the range subtype is the ambient Hilbert-space norm.
      change ‖P.proj (f n) (hf n) ξ‖ ^ 2 = ((P.diag ξ) (f n)).toReal
      exact P.norm_sq_proj_apply (f n) (hf n) ξ
    rw [heq]
    exact ENNReal.summable_toReal hmass
  have hvsum : Summable (fun n => (V n).subtypeₗᵢ (v n)) :=
    (hV.summable_iff_norm_sq_summable v).2 hnorms
  have hsum : Summable (fun n => P.proj (f n) (hf n) ξ) := by
    simpa [V, v] using hvsum
  exact (hsum.hasSum_iff_tendsto_nat).2 (by
    simpa only [Nat.Iio_eq_range, sum_apply] using
      P.tendsto_sum_proj_of_pairwise_disjoint hf hdisj ξ)

/-! ## Extensionality

A `ProjValMeasure` is determined by either its projection field or its
finite diagonal scalar measures. The identity `inner_proj` relates these
fields; finite measure values are recovered from their real embeddings. -/

/-- Two PVMs with the same data fields are equal; the remaining fields are
propositions. -/
private lemma ext_fields {P Q : ProjValMeasure X H} (hproj : P.proj = Q.proj)
    (hdiag : P.diag = Q.diag) : P = Q := by
  obtain ⟨p, d, _, _, _, _⟩ := P
  obtain ⟨q, e, _, _, _, _⟩ := Q
  obtain rfl : p = q := hproj
  obtain rfl : d = e := hdiag
  rfl

/-- Two projection-valued measures with the same diagonal scalar measures
are equal. -/
theorem ext_of_diag {P Q : ProjValMeasure X H}
    (h : ∀ ξ : H, P.diag ξ = Q.diag ξ) : P = Q := by
  refine ext_fields ?_ (funext h)
  funext B hB
  apply ContinuousLinearMap.eq_of_diagonal
  intro ξ
  rw [P.inner_proj, Q.inner_proj, h ξ]

/-- Two projection-valued measures agreeing on all measurable-set projections
are equal. -/
@[ext]
theorem ext {P Q : ProjValMeasure X H}
    (h : ∀ (B : Set X) (hB : MeasurableSet B), P.proj B hB = Q.proj B hB) :
    P = Q := by
  refine ext_of_diag fun ξ => Measure.ext fun B hB => ?_
  have hr : (((P.diag ξ) B).toReal : ℂ) = (((Q.diag ξ) B).toReal : ℂ) := by
    rw [← P.inner_proj B hB ξ, ← Q.inner_proj B hB ξ, h B hB]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ := P.diag ξ) (s := B))
      (measure_ne_top (μ := Q.diag ξ) (s := B))).mp
    (by exact_mod_cast hr)

/-- Equality of projection-valued measures is equivalent to equality of all
diagonal scalar measures. -/
theorem ext_iff_diag {P Q : ProjValMeasure X H} :
    P = Q ↔ ∀ ξ : H, P.diag ξ = Q.diag ξ :=
  ⟨fun h ξ => by rw [h], ext_of_diag⟩

-- `@[ext]` on `ext` already generates `ProjValMeasure.ext_iff`.

end ProjValMeasure

end TauCeti
