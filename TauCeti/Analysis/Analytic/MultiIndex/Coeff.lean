/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Algebra.MvPolynomial.Funext

/-!
# Multi-index coefficients of formal multilinear series

A formal multilinear series `p` on `ι → 𝕜`, for a finite type `ι`, has degree-`k` terms
`p k (fun _ ↦ z)` which are homogeneous polynomials of degree `k` in the coordinates `z i`. This
file defines their coefficients, indexed by multi-indices `α : ι → ℕ`:
`p.mvCoeff α` is the sum of `p (∑ i, α i)` over the tuples of standard basis vectors in which each
basis vector `Pi.single i 1` occurs exactly `α i` times. Every ordering of the basis vectors is
counted, so no symmetry of the multilinear maps `p k` is needed. The name avoids Mathlib's
one-variable `FormalMultilinearSeries.coeff`.

These are the coefficients through which a power series in several variables is handled
coordinate by coordinate, as in transcendence proofs by auxiliary functions in several variables.

## Main definitions and results

* `FormalMultilinearSeries.mvCoeff`: the multi-index coefficient of a formal multilinear series.
* `FormalMultilinearSeries.apply_eq_sum_mvCoeff`: the degree-`k` term is
  `∑ α ∈ univ.piAntidiag k, (∏ i, z i ^ α i) • p.mvCoeff α`.
* `FormalMultilinearSeries.sum_norm_mvCoeff_le`: the coefficients of total degree `k` have norms
  summing to at most `(card ι) ^ k * ‖p k‖`.
* `FormalMultilinearSeries.summable_norm_prod_pow_smul_mvCoeff`: the multi-index series converges
  absolutely wherever the operator-norm bounds `(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` are summable.
* `HasFPowerSeriesOnBall.hasSum_mvCoeff`: a function with a power series is the sum of its
  multi-index series wherever the operator-norm bounds `(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` are
  summable.
* `HasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero`: the identity theorem in coefficient
  form, so that the coefficients only depend on the function
  (`HasFPowerSeriesAt.mvCoeff_eq_of_eventuallyEq`).
* `TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum` and
  `TauCeti.exists_hasFPowerSeriesOnBall_tsum`: conversely, a normally convergent multi-index series
  has a power series on the polydisc whose multi-index coefficients are the given ones.
* `TauCeti.eq_zero_of_hasSum_prod_pow_smul_eq_zero` and
  `TauCeti.eq_zero_of_tsum_prod_pow_smul_eventuallyEq_zero`: a normally convergent multi-index
  series vanishing near the origin has all coefficients zero.

## References

Multi-index coefficients of formal multilinear series, under the name `coeff`, are also part of
Michail Karatarakis's formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`,
commit `1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/MultiIndex.lean`, Apache 2.0).
-/

public section

open Filter Finset Topology
open scoped ENNReal NNReal

namespace FormalMultilinearSeries

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Classical in
/-- The **multi-index coefficient** of a formal multilinear series `p` on `ι → 𝕜` at `α : ι → ℕ`:
the sum of `p (∑ i, α i)` over all tuples of standard basis vectors in which `Pi.single i 1`
occurs exactly `α i` times. It is the coefficient of `∏ i, z i ^ α i` in the homogeneous term
`p (∑ i, α i) (fun _ ↦ z)` (`FormalMultilinearSeries.apply_eq_sum_mvCoeff`). -/
noncomputable def mvCoeff (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) : F :=
  ∑ a ∈ univ.filter (fun a : Fin (∑ i, α i) → ι ↦ ∀ i, Fintype.card {j // a j = i} = α i),
    p (∑ i, α i) (fun j ↦ Pi.single (a j) 1)

/-- The multi-index coefficient as a sum over tuples of basis vectors, at any degree `k` equal
to the total degree `∑ i, α i`. -/
theorem mvCoeff_eq_sum [DecidableEq ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    {α : ι → ℕ} {k : ℕ} (hk : ∑ i, α i = k) :
    p.mvCoeff α = ∑ a ∈ univ.filter (fun a : Fin k → ι ↦ ∀ i, Fintype.card {j // a j = i} = α i),
      p k (fun j ↦ Pi.single (a j) 1) := by
  subst hk
  unfold mvCoeff
  -- The definition uses classical decidability; `congr!` identifies it with `DecidableEq ι`.
  congr!

@[simp]
theorem mvCoeff_zero (α : ι → ℕ) : (0 : FormalMultilinearSeries 𝕜 (ι → 𝕜) F).mvCoeff α = 0 := by
  classical
  simp [mvCoeff_eq_sum _ rfl]

@[simp]
theorem mvCoeff_add (p q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) :
    (p + q).mvCoeff α = p.mvCoeff α + q.mvCoeff α := by
  classical
  simp [mvCoeff_eq_sum _ rfl, sum_add_distrib]

@[simp]
theorem mvCoeff_smul (c : 𝕜) (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) :
    (c • p).mvCoeff α = c • p.mvCoeff α := by
  classical
  simp [mvCoeff_eq_sum _ rfl, smul_sum]

@[simp]
theorem mvCoeff_neg (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) :
    (-p).mvCoeff α = -p.mvCoeff α := by
  classical
  simp [mvCoeff_eq_sum _ rfl]

@[simp]
theorem mvCoeff_sub (p q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) :
    (p - q).mvCoeff α = p.mvCoeff α - q.mvCoeff α := by
  classical
  simp [mvCoeff_eq_sum _ rfl, sum_sub_distrib]

/-- The coefficient of the zero multi-index is the constant term `p 0`, evaluated at the empty
tuple. -/
theorem mvCoeff_zero_eq_apply (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (v : Fin 0 → ι → 𝕜) : p.mvCoeff 0 = p 0 v := by
  classical
  rw [mvCoeff_eq_sum p (k := 0) (by simp)]
  simp [Subsingleton.elim _ v]

/-- The multi-index coefficient at `α` is the sum over the tuples `a : Fin k → ι` whose
coordinate counts are `α`, for `α` of total degree `k`. -/
private theorem mvCoeff_eq_sum_fiber [DecidableEq ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    {k : ℕ} {α : ι → ℕ} (hα : α ∈ univ.piAntidiag k) :
    p.mvCoeff α = ∑ a : Fin k → ι with (fun i ↦ Fintype.card {j // a j = i}) = α,
      p k (fun j ↦ Pi.single (a j) 1) := by
  simp_rw [mvCoeff_eq_sum p (mem_piAntidiag.1 hα).1, funext_iff]

/-- **The degree-`k` term in multi-index form**: `p k (fun _ ↦ z)` is the polynomial
`∑ α, (∏ i, z i ^ α i) • p.mvCoeff α` over the multi-indices of total degree `k`. -/
theorem apply_eq_sum_mvCoeff [DecidableEq ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (k : ℕ)
    (z : ι → 𝕜) :
    p k (fun _ ↦ z) = ∑ α ∈ univ.piAntidiag k, (∏ i, z i ^ α i) • p.mvCoeff α := by
  -- Expand every argument in the standard basis, then group the tuples by coordinate counts.
  have hcount (a : Fin k → ι) : (fun i ↦ Fintype.card {j // a j = i}) ∈ univ.piAntidiag k := by
    simpa [mem_piAntidiag] using Fintype.sum_fiberwise' a (fun _ ↦ (1 : ℕ))
  have hz : (fun _ : Fin k ↦ z) = fun _ ↦ ∑ i, z i • Pi.single i (1 : 𝕜) :=
    funext fun _ ↦ pi_eq_sum_univ' z
  rw [hz, (p k).map_sum, ← sum_fiberwise_of_maps_to (fun a _ ↦ hcount a)]
  refine sum_congr rfl fun α hα ↦ ?_
  rw [mvCoeff_eq_sum_fiber p hα, smul_sum]
  refine sum_congr rfl fun a ha ↦ ?_
  rw [(p k).map_smul_univ, ← (mem_filter.1 ha).2]
  congr 1
  simpa using (Fintype.prod_fiberwise' a z).symm

end NormedField

end FormalMultilinearSeries

namespace TauCeti

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `‖c α‖ * r ^ (∑ i, α i)` is summable over multi-indices `α`, then the multi-index series
`∑ α, (∏ i, y i ^ α i) • c α` converges absolutely on the closed polydisc `‖y‖ ≤ r`. -/
theorem summable_norm_prod_pow_smul {c : (ι → ℕ) → F} {r : ℝ}
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * r ^ (∑ i, α i))
    {y : ι → 𝕜} (hy : ‖y‖ ≤ r) :
    Summable fun α : ι → ℕ ↦ ‖(∏ i, y i ^ α i) • c α‖ := by
  refine hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun α ↦ ?_
  rw [norm_smul, norm_prod, mul_comm, ← prod_pow_eq_pow_sum]
  gcongr with i
  rw [norm_pow]
  gcongr
  exact (norm_le_pi_norm y i).trans hy

end NormedField

end TauCeti

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FormalMultilinearSeries

/-- The multi-index coefficients of total degree `k` have norms summing to at most
`(card ι) ^ k * ‖p k‖`. -/
theorem sum_norm_mvCoeff_le [DecidableEq ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (k : ℕ) : ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ ≤ Fintype.card ι ^ k * ‖p k‖ := by
  have hcount (a : Fin k → ι) : (fun i ↦ Fintype.card {j // a j = i}) ∈ univ.piAntidiag k := by
    simpa [mem_piAntidiag] using Fintype.sum_fiberwise' a (fun _ ↦ (1 : ℕ))
  have hterm (a : Fin k → ι) : ‖p k (fun j ↦ Pi.single (a j) (1 : 𝕜))‖ ≤ ‖p k‖ := by
    simpa [Pi.norm_single] using (p k).le_opNorm fun j ↦ Pi.single (a j) (1 : 𝕜)
  calc ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖
      ≤ ∑ α ∈ univ.piAntidiag k,
          ∑ a : Fin k → ι with (fun i ↦ Fintype.card {j // a j = i}) = α, ‖p k‖ := by
        refine sum_le_sum fun α hα ↦ ?_
        rw [mvCoeff_eq_sum_fiber p hα]
        exact (norm_sum_le _ _).trans (sum_le_sum fun a _ ↦ hterm a)
    _ = Fintype.card ι ^ k * ‖p k‖ := by
        rw [sum_fiberwise_of_maps_to (fun a _ ↦ hcount a)]
        simp

/-- **Normal convergence of the multi-index coefficients**: if the operator-norm bounds
`(card ι) ^ k * ‖p k‖ * r ^ k` are summable for `0 ≤ r`, then `‖p.mvCoeff α‖ * r ^ (∑ i, α i)` is
summable over all multi-indices `α`. -/
theorem summable_norm_mvCoeff_mul_pow (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {r : ℝ}
    (hr : 0 ≤ r) (h : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * r ^ k) :
    Summable fun α : ι → ℕ ↦ ‖p.mvCoeff α‖ * r ^ (∑ i, α i) := by
  classical
  -- The weighted coefficients of total degree `k` sum to at most the `k`-th weighted term.
  have hdeg (k : ℕ) : ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ (∑ i, α i) ≤
      (Fintype.card ι : ℝ) ^ k * ‖p k‖ * r ^ k := by
    calc ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * r ^ (∑ i, α i)
        = (∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖) * r ^ k := by
          rw [sum_mul]
          exact sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
      _ ≤ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * r ^ k := by
          gcongr
          exact_mod_cast p.sum_norm_mvCoeff_le k
  -- A finite sum splits by total degree, and each degree is bounded by its weighted term.
  refine summable_of_sum_le (c := ∑' k, (Fintype.card ι : ℝ) ^ k * ‖p k‖ * r ^ k)
    (fun _ ↦ by positivity) fun s ↦ ?_
  rw [← sum_fiberwise_of_maps_to (g := fun α ↦ ∑ i, α i) (t := s.image (fun α ↦ ∑ i, α i))
    (fun α hα ↦ mem_image_of_mem _ hα)]
  refine (sum_le_sum fun k _ ↦ ?_).trans (h.sum_le_tsum _ fun _ _ ↦ by positivity)
  refine (sum_le_sum_of_subset_of_nonneg (fun α hα ↦ ?_) fun _ _ _ ↦ by positivity).trans (hdeg k)
  exact mem_piAntidiag.2 ⟨(mem_filter.1 hα).2, by simp⟩

/-- **Absolute convergence of the multi-index series**: if the operator-norm bounds
`(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` are summable, then the multi-index series
`∑ α, (∏ i, z i ^ α i) • p.mvCoeff α` converges absolutely. -/
theorem summable_norm_prod_pow_smul_mvCoeff (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    {z : ι → 𝕜} (h : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k) :
    Summable fun α : ι → ℕ ↦ ‖(∏ i, z i ^ α i) • p.mvCoeff α‖ :=
  TauCeti.summable_norm_prod_pow_smul (p.summable_norm_mvCoeff_mul_pow (norm_nonneg z) h) le_rfl

end FormalMultilinearSeries

namespace HasFPowerSeriesOnBall

open FormalMultilinearSeries

/-- **An analytic function is the sum of its multi-index series**: if `f` has the power series
`p` on a ball about `x`, then `f (x + z)` is the sum of `(∏ i, z i ^ α i) • p.mvCoeff α` over all
multi-indices `α`, for `z` in the ball at which the operator-norm bounds
`(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` are summable. The sum is then absolutely convergent
(`FormalMultilinearSeries.summable_norm_prod_pow_smul_mvCoeff`). -/
theorem hasSum_mvCoeff {f : (ι → 𝕜) → F} {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F}
    {x : ι → 𝕜} {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p x r) {z : ι → 𝕜}
    (hz : z ∈ Metric.eball (0 : ι → 𝕜) r)
    (h : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k) :
    HasSum (fun α : ι → ℕ ↦ (∏ i, z i ^ α i) • p.mvCoeff α) (f (x + z)) := by
  classical
  -- The multi-indices of total degree `< K` exhaust all multi-indices as `K` grows, and a sum
  -- over them can be taken degree by degree.
  let S : ℕ → Finset (ι → ℕ) := fun K ↦ (range K).biUnion (univ.piAntidiag ·)
  have hS (s : Finset (ι → ℕ)) (K : ℕ) (hK : s.sup (fun α ↦ ∑ i, α i) < K) : s ⊆ S K :=
    fun α hα ↦ by
      simp only [S, mem_biUnion, mem_range, mem_piAntidiag]
      exact ⟨∑ i, α i, (le_sup (f := fun α ↦ ∑ i, α i) hα).trans_lt hK, by simp⟩
  have hdisj (K : ℕ) : (range K : Set ℕ).PairwiseDisjoint (univ.piAntidiag (ι := ι) ·) :=
    fun k _ l _ hkl ↦ disjoint_left.2 fun α hk hl ↦
      hkl ((mem_piAntidiag.1 hk).1.symm.trans (mem_piAntidiag.1 hl).1)
  refine hasSum_of_subseq_of_summable (p.summable_norm_prod_pow_smul_mvCoeff h) (s := S)
    (p := atTop) ?_ ?_
  · exact tendsto_atTop_atTop.2 fun s ↦ ⟨s.sup (fun α ↦ ∑ i, α i) + 1,
      fun K hK ↦ hS s K ((lt_add_one _).trans_le hK)⟩
  · simp_rw [S, sum_biUnion (hdisj _), ← apply_eq_sum_mvCoeff]
    exact (hf.hasSum hz).tendsto_sum_nat

end HasFPowerSeriesOnBall

namespace HasFPowerSeriesAt

open FormalMultilinearSeries

/-- **The identity theorem in coefficient form**: if `f` has the power series `p` at `x` and
vanishes near `x`, then every multi-index coefficient of `p` is zero. -/
theorem mvCoeff_eq_zero_of_eventuallyEq_zero {f : (ι → 𝕜) → F}
    {p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} (hf : HasFPowerSeriesAt f p x)
    (h0 : f =ᶠ[𝓝 x] 0) (α : ι → ℕ) : p.mvCoeff α = 0 := by
  classical
  have h := (hf.congr h0).apply_eq_zero (∑ i, α i)
  exact TauCeti.eq_zero_of_forall_sum_prod_pow_smul_eq_zero
    (fun z ↦ by rw [← apply_eq_sum_mvCoeff, h]) (mem_piAntidiag.2 ⟨rfl, by simp⟩)

/-- Power series of two functions that agree near `x` have the same multi-index coefficients. In
particular the multi-index coefficients of a power series of `f` at `x` depend only on `f`. -/
theorem mvCoeff_eq_of_eventuallyEq {f g : (ι → 𝕜) → F}
    {p q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {x : ι → 𝕜} (hf : HasFPowerSeriesAt f p x)
    (hg : HasFPowerSeriesAt g q x) (hfg : f =ᶠ[𝓝 x] g) (α : ι → ℕ) :
    p.mvCoeff α = q.mvCoeff α := by
  rw [← sub_eq_zero, ← mvCoeff_sub]
  exact (hf.sub hg).mvCoeff_eq_zero_of_eventuallyEq_zero
    (hfg.mono fun y hy ↦ by simp [hy]) α

end HasFPowerSeriesAt

end NontriviallyNormedField

namespace TauCeti

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous `k`-linear map on `ι → 𝕜` whose diagonal value at `z` is
`(∏ i, z i ^ α i) • v`, with operator norm at most `‖v‖`. -/
private noncomputable def monomialMultilinearMap (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] (α : ι → ℕ) (v : F) {k : ℕ} (hα : ∑ i, α i = k) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin k ↦ ι → 𝕜) F :=
  let e : (Σ i : ι, Fin (α i)) ≃ Fin k := Fintype.equivFinOfCardEq (by simp [hα])
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin k) v).compContinuousLinearMap
    fun j ↦ ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) (e.symm j).1

private theorem monomialMultilinearMap_apply (α : ι → ℕ) (v : F) {k : ℕ} (hα : ∑ i, α i = k)
    (z : ι → 𝕜) :
    monomialMultilinearMap 𝕜 α v hα (fun _ ↦ z) = (∏ i, z i ^ α i) • v := by
  classical
  dsimp only [monomialMultilinearMap]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply]
  congr 1
  let e : (Σ i : ι, Fin (α i)) ≃ Fin k := Fintype.equivFinOfCardEq (by simp [hα])
  simp only [ContinuousLinearMap.proj_apply]
  rw [e.symm.prod_comp (fun x : Σ i : ι, Fin (α i) ↦ z x.1), Fintype.prod_sigma]
  simp

private theorem norm_monomialMultilinearMap_le (α : ι → ℕ) (v : F) {k : ℕ} (hα : ∑ i, α i = k) :
    ‖monomialMultilinearMap 𝕜 α v hα‖ ≤ ‖v‖ := by
  dsimp only [monomialMultilinearMap]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [ContinuousMultilinearMap.norm_mkPiRing]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  calc ∏ j : Fin k, ‖ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) _‖
      ≤ ∏ _ : Fin k, (1 : ℝ) := by
        gcongr with j
        exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by
          simpa using norm_le_pi_norm z _
    _ = 1 := by simp

/-- **A normally convergent multi-index expansion yields a power series** on the polydisc, whose
multi-index coefficients are the given ones. No completeness of `F` is assumed because the
convergence of the series to `f (x + y)` is given directly by `hf`. -/
theorem exists_hasFPowerSeriesOnBall_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    {c : (ι → ℕ) → F} {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (hf : ∀ y : ι → 𝕜, ‖y‖ < r →
      HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y))) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall f p x r ∧ ∀ α, p.mvCoeff α = c α := by
  classical
  let p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F := fun k ↦
    ∑ α ∈ (univ.piAntidiag k).attach, monomialMultilinearMap 𝕜 α.1 (c α.1) (mem_piAntidiag.1 α.2).1
  have hp_apply (k : ℕ) (z : ι → 𝕜) :
      p k (fun _ ↦ z) = ∑ α ∈ univ.piAntidiag k, (∏ i, z i ^ α i) • c α := by
    simp only [p, sum_apply, monomialMultilinearMap_apply]
    exact sum_attach _ fun α ↦ (∏ i, z i ^ α i) • c α
  have hp_norm (k : ℕ) : ‖p k‖ ≤ ∑ α ∈ univ.piAntidiag k, ‖c α‖ := by
    calc ‖p k‖
        ≤ ∑ α ∈ (univ.piAntidiag k).attach,
            ‖monomialMultilinearMap 𝕜 α.1 (c α.1) (mem_piAntidiag.1 α.2).1‖ := norm_sum_le _ _
      _ ≤ ∑ α ∈ (univ.piAntidiag k).attach, ‖c α.1‖ :=
            sum_le_sum fun α _ ↦ norm_monomialMultilinearMap_le _ _ _
      _ = ∑ α ∈ univ.piAntidiag k, ‖c α‖ := sum_attach _ fun α ↦ ‖c α‖
  refine ⟨p, ⟨?_, ENNReal.coe_pos.2 hr, ?_⟩, ?_⟩
  · refine p.le_radius_of_bound (∑' α : ι → ℕ, ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) fun k ↦ ?_
    calc ‖p k‖ * (r : ℝ) ^ k
        ≤ (∑ α ∈ univ.piAntidiag k, ‖c α‖) * (r : ℝ) ^ k := by gcongr; exact hp_norm k
      _ = ∑ α ∈ univ.piAntidiag k, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
            rw [sum_mul]
            exact sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
      _ ≤ ∑' α : ι → ℕ, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) :=
            hsum.sum_le_tsum _ fun _ _ ↦ by positivity
  · intro y hy
    have hy' : ‖y‖ < r := by
      simpa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_coe_iff] using hy
    -- Group the multi-index `HasSum` by total degree `k = ∑ i, α i`.
    have hdisj (s : Finset ℕ) : (s : Set ℕ).PairwiseDisjoint (univ.piAntidiag (ι := ι) ·) :=
      fun k _ l _ hkl ↦ disjoint_left.2 fun α hk hl ↦
        hkl ((mem_piAntidiag.1 hk).1.symm.trans (mem_piAntidiag.1 hl).1)
    have hbiUnion :
        Tendsto (fun s : Finset ℕ ↦ s.biUnion (univ.piAntidiag (ι := ι) ·)) atTop atTop :=
      tendsto_atTop_atTop.2 fun t ↦ ⟨t.image fun α ↦ ∑ i, α i, fun s hs α hα ↦
        mem_biUnion.2 ⟨∑ i, α i, hs (mem_image_of_mem _ hα), mem_piAntidiag.2 ⟨rfl, by simp⟩⟩⟩
    have h := (hf y hy').comp hbiUnion
    simpa only [HasSum, SummationFilter.unconditional_filter, Function.comp_def,
      sum_biUnion (hdisj _), ← hp_apply] using h
  · intro α
    have hsub (z : ι → 𝕜) :
        ∑ β ∈ univ.piAntidiag (∑ i, α i), (∏ i, z i ^ β i) • (p.mvCoeff β - c β) = 0 := by
      simp_rw [smul_sub, sum_sub_distrib, ← p.apply_eq_sum_mvCoeff, ← hp_apply, sub_self]
    exact sub_eq_zero.1 <| eq_zero_of_forall_sum_prod_pow_smul_eq_zero hsub
      (mem_piAntidiag.2 ⟨rfl, by simp⟩)

/-- **A normally convergent multi-index series has a power series** on the polydisc about `0`,
whose multi-index coefficients are the given ones. -/
theorem exists_hasFPowerSeriesOnBall_tsum [CompleteSpace F] (c : (ι → ℕ) → F) {r : ℝ≥0}
    (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) p 0 r ∧
        ∀ α, p.mvCoeff α = c α :=
  exists_hasFPowerSeriesOnBall_of_hasSum hr hsum fun y hy ↦ by
    simpa using (summable_norm_prod_pow_smul hsum hy.le).of_norm.hasSum

/-- **The identity theorem for normally convergent multi-index series**: if
`∑ α, (∏ i, y i ^ α i) • c α` converges normally on the polydisc of radius `r > 0` and has sum `0`
on `‖y‖ < r`, then every coefficient `c α` vanishes. -/
theorem eq_zero_of_hasSum_prod_pow_smul_eq_zero {c : (ι → ℕ) → F} {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h0 : ∀ y : ι → 𝕜, ‖y‖ < r → HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) 0)
    (α : ι → ℕ) : c α = 0 := by
  obtain ⟨p, hp, hpc⟩ := exists_hasFPowerSeriesOnBall_of_hasSum (f := fun _ ↦ (0 : F))
    (x := 0) hr hsum fun y hy ↦ by simpa using h0 y hy
  rw [← hpc α]
  exact hp.hasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero EventuallyEq.rfl α

/-- **The identity theorem for a normally convergent `tsum`**: if
`z ↦ ∑' α, (∏ i, z i ^ α i) • c α` converges normally on the polydisc of radius `r > 0` and
vanishes near `0`, then every coefficient `c α` vanishes. -/
theorem eq_zero_of_tsum_prod_pow_smul_eventuallyEq_zero [CompleteSpace F] {c : (ι → ℕ) → F}
    {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h0 : (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) =ᶠ[𝓝 0] 0)
    (α : ι → ℕ) : c α = 0 := by
  obtain ⟨p, hp, hpc⟩ := exists_hasFPowerSeriesOnBall_tsum (𝕜 := 𝕜) c hr hsum
  rw [← hpc α]
  exact hp.hasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero h0 α

end NontriviallyNormedField

end TauCeti
