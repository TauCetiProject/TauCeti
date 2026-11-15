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
import Mathlib.Analysis.Normed.Group.InfiniteSum
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
* `FormalMultilinearSeries.summable_norm_mvCoeff_mul_pow` and
  `FormalMultilinearSeries.summable_norm_prod_pow_smul_mvCoeff`: the multi-index series converges
  normally and absolutely wherever `(card ι) ^ k * ‖p k‖ * ρ ^ k` is summable.
* `HasFPowerSeriesOnBall.hasSum_mvCoeff`: a function with a power series is the sum of its
  multi-index series wherever `(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` is summable.
* `TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum` and `TauCeti.exists_hasFPowerSeriesOnBall_tsum`:
  conversely, a normally convergent multi-index series on a polydisc comes from a formal
  multilinear series whose multi-index coefficients are the given ones.
* `HasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero` and
  `TauCeti.eq_zero_of_forall_mem_ball_tsum_prod_pow_smul_eq_zero`: the identity theorem in
  coefficient form, both for germs with a power series and for normally convergent multi-index
  series on a polydisc.

## References

Multi-index coefficients of formal multilinear series, under the name `coeff`, are also part of
Michail Karatarakis's formalization of Baker's theorem (`mkaratarakis/mathlib4`, branch `baker`,
commit `1d51891b5b`, `Mathlib/NumberTheory/Transcendental/Baker/MultiIndex.lean`, Apache 2.0).
-/

public section

open Filter Finset Topology
open scoped NNReal ENNReal

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

theorem mvCoeff_sum {κ : Type*} (s : Finset κ)
    (p : κ → FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) :
    (∑ j ∈ s, p j).mvCoeff α = ∑ j ∈ s, (p j).mvCoeff α := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert _ _ h ih => simp [sum_insert h, ih]

@[simp]
theorem _root_.ContinuousLinearMap.mvCoeff_compFormalMultilinearSeries
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (L : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) :
    (L.compFormalMultilinearSeries p).mvCoeff α = L (p.mvCoeff α) := by
  classical
  simp [mvCoeff_eq_sum _ rfl, map_sum]

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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FormalMultilinearSeries

open scoped Classical in
@[simp]
theorem mvCoeff_constFormalMultilinearSeries (c : F) (α : ι → ℕ) :
    (constFormalMultilinearSeries 𝕜 (ι → 𝕜) c).mvCoeff α = if α = 0 then c else 0 := by
  split_ifs with hα
  · subst hα
    simpa using mvCoeff_zero_eq_apply (constFormalMultilinearSeries 𝕜 (ι → 𝕜) c) 0
  · have hk : ∑ i, α i ≠ 0 :=
      mt sum_eq_zero_iff.1 fun h ↦ hα (funext fun i ↦ h i (mem_univ i))
    simp [mvCoeff_eq_sum _ rfl, constFormalMultilinearSeries_apply_of_ne_zero hk]

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
`(card ι) ^ k * ‖p k‖ * ρ ^ k` are summable for `ρ ≥ 0`, then `‖p.mvCoeff α‖ * ρ ^ (∑ i, α i)`
is summable over all multi-indices `α`. -/
theorem summable_norm_mvCoeff_mul_pow (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (h : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k) :
    Summable fun α : ι → ℕ ↦ ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) := by
  classical
  have hdeg (k : ℕ) : ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤
      (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k := calc
    _ = (∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖) * ρ ^ k := by
        rw [sum_mul]
        exact sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
    _ ≤ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k := by
        gcongr
        exact_mod_cast sum_norm_mvCoeff_le p k
  refine summable_of_sum_le (c := ∑' k, (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k)
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
    Summable fun α : ι → ℕ ↦ ‖(∏ i, z i ^ α i) • p.mvCoeff α‖ := by
  refine (p.summable_norm_mvCoeff_mul_pow (norm_nonneg z) h).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) fun α ↦ ?_
  rw [norm_smul, norm_prod, mul_comm, ← prod_pow_eq_pow_sum]
  gcongr with i
  rw [norm_pow]
  gcongr
  exact norm_le_pi_norm z i

/-- Composing a formal multilinear series on the right with a continuous linear map preserves
vanishing of all multi-index coefficients in any fixed total degree `k`. -/
theorem mvCoeff_compContinuousLinearMap_eq_zero {κ : Type*} [Fintype κ]
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (A : (κ → 𝕜) →L[𝕜] (ι → 𝕜)) {k : ℕ}
    (h : ∀ α : ι → ℕ, ∑ i, α i = k → p.mvCoeff α = 0) :
    ∀ β : κ → ℕ, ∑ j, β j = k → (p.compContinuousLinearMap A).mvCoeff β = 0 := by
  classical
  intro β hβ
  refine TauCeti.eq_zero_of_forall_sum_prod_pow_smul_eq_zero (fun z : κ → 𝕜 ↦ ?_)
    (mem_piAntidiag.2 ⟨hβ, by simp⟩)
  rw [← apply_eq_sum_mvCoeff, compContinuousLinearMap_apply, Function.comp_def,
    apply_eq_sum_mvCoeff]
  exact sum_eq_zero fun α hα ↦ by simp [h α (mem_piAntidiag.1 hα).1]

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

namespace TauCeti

/-- **A normally convergent multi-index expansion comes from a formal power series**: if
`‖c α‖ * r ^ (∑ i, α i)` is summable on a polydisc of radius `r > 0` and the multi-index series
sums to `f (x + y)` for every `‖y‖ < r`, then `f` has a formal multilinear series `p` on the ball
of radius `r` about `x` whose multi-index coefficients are `c`. Completeness of `F` is not needed
when the sum function `f` is already given. -/
theorem exists_hasFPowerSeriesOnBall_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (c : (ι → ℕ) → F) {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (hf : ∀ y : ι → 𝕜, ‖y‖ < r → HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y))) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall f p x r ∧ ∀ α, p.mvCoeff α = c α := by
  classical
  -- Realize each multi-index `α` of total degree `k` by one ordered monomial multilinear map.
  have htuple {k : ℕ} {α : ι → ℕ} (hα : α ∈ univ.piAntidiag k) :
      ∃ g : Fin k → ι, ∀ i, Fintype.card {j // g j = i} = α i := by
    let e : Fin k ≃ Σ i : ι, Fin (α i) :=
      Fintype.equivOfCardEq (by simp [(mem_piAntidiag.1 hα).1])
    refine ⟨fun j ↦ (e j).1, fun i ↦ ?_⟩
    let e_fib : {x : Σ i' : ι, Fin (α i') // x.1 = i} ≃ Fin (α i) :=
      { toFun := fun x ↦ x.1.2.cast (congrArg α x.2)
        invFun := fun m ↦ ⟨⟨i, m⟩, rfl⟩
        left_inv := fun ⟨⟨_, _⟩, rfl⟩ ↦ rfl
        right_inv := fun _ ↦ rfl }
    simpa using Fintype.card_congr ((Equiv.subtypeEquiv e fun _ ↦ Iff.rfl).trans e_fib)
  let mono (k : ℕ) (g : Fin k → ι) (v : F) :
      ContinuousMultilinearMap 𝕜 (fun _ : Fin k ↦ ι → 𝕜) F :=
    ((ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 k 𝕜).compContinuousLinearMap
      fun j ↦ ContinuousLinearMap.proj (g j)).smulRight v
  have hmono_apply (k : ℕ) (g : Fin k → ι) (v : F) (u : Fin k → ι → 𝕜) :
      mono k g v u = (∏ j : Fin k, u j (g j)) • v := by
    simp [mono, List.prod_ofFn]
  have hmono_norm (k : ℕ) (g : Fin k → ι) (v : F) : ‖mono k g v‖ ≤ ‖v‖ := by
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg v) fun u ↦ ?_
    rw [hmono_apply, norm_smul, norm_prod, mul_comm]
    gcongr with j
    exact norm_le_pi_norm (u j) (g j)
  have hmono_single (k : ℕ) (g a : Fin k → ι) (v : F) :
      mono k g v (fun j ↦ Pi.single (a j) 1) = if a = g then v else 0 := by
    rw [hmono_apply]
    split_ifs with h
    · subst h; simp
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
      rw [prod_eq_zero (mem_univ j) (Pi.single_eq_of_ne hj.symm 1), zero_smul]
  let p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F := fun k ↦
    ∑ α ∈ (univ.piAntidiag k).attach, mono k (htuple α.2).choose (c α.1)
  have hpc (β : ι → ℕ) : p.mvCoeff β = c β := by
    let k := ∑ i, β i
    have hβ : β ∈ univ.piAntidiag k := mem_piAntidiag.2 ⟨rfl, by simp⟩
    rw [FormalMultilinearSeries.mvCoeff_eq_sum p (k := k) rfl]
    simp only [p, sum_apply, hmono_single]
    rw [sum_comm]
    have hinner (α : {α // α ∈ univ.piAntidiag k}) :
        (∑ a ∈ univ.filter (fun a : Fin k → ι ↦ ∀ i, Fintype.card {j // a j = i} = β i),
          if a = (htuple α.2).choose then c α.1 else 0) =
        if α.1 = β then c α.1 else 0 := by
      have hg := (htuple α.2).choose_spec
      rw [sum_ite_eq']
      simp [hg, funext_iff]
    simp_rw [hinner]
    have hatt : ∑ α ∈ (univ.piAntidiag k).attach, (if α.1 = β then c α.1 else 0) =
        ∑ α ∈ univ.piAntidiag k, if α = β then c α else 0 :=
      sum_attach _ fun α ↦ if α = β then c α else 0
    rw [hatt, sum_ite_eq' _ _ (fun α ↦ c α)]
    simp [hβ]
  have hpnorm_le (k : ℕ) : ‖p k‖ ≤ ∑ α ∈ univ.piAntidiag k, ‖c α‖ :=
    (norm_sum_le _ _).trans <|
      (sum_le_sum fun α _ ↦ hmono_norm _ _ (c α.1)).trans_eq
        (sum_attach (univ.piAntidiag k) fun α ↦ ‖c α‖)
  have hpnorm : Summable fun k ↦ ‖p k‖ * (r : ℝ) ^ k := by
    refine summable_of_sum_le (c := ∑' α, ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
      (fun _ ↦ by positivity) fun t ↦ ?_
    have hdisj : (t : Set ℕ).PairwiseDisjoint (univ.piAntidiag (ι := ι) ·) :=
      fun _ _ _ _ hkl ↦ disjoint_left.2 fun _ hk hl ↦
        hkl ((mem_piAntidiag.1 hk).1.symm.trans (mem_piAntidiag.1 hl).1)
    calc ∑ k ∈ t, ‖p k‖ * (r : ℝ) ^ k
        ≤ ∑ k ∈ t, ∑ α ∈ univ.piAntidiag k, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
          refine sum_le_sum fun k _ ↦ ?_
          calc ‖p k‖ * (r : ℝ) ^ k
              ≤ (∑ α ∈ univ.piAntidiag k, ‖c α‖) * (r : ℝ) ^ k := by gcongr; exact hpnorm_le k
            _ = ∑ α ∈ univ.piAntidiag k, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
                rw [sum_mul]
                exact sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
      _ = ∑ α ∈ t.biUnion (univ.piAntidiag ·), ‖c α‖ * (r : ℝ) ^ (∑ i, α i) :=
          (sum_biUnion hdisj).symm
      _ ≤ ∑' α, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) :=
          hsum.sum_le_tsum _ fun _ _ ↦ by positivity
  refine ⟨p, ⟨p.le_radius_of_summable hpnorm, ENNReal.coe_pos.mpr hr, fun {y} hy ↦ ?_⟩, hpc⟩
  have hynorm : ‖y‖ < (r : ℝ) := by
    have h : ‖y‖₊ < r := by
      simpa only [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm, ENNReal.coe_lt_coe] using hy
    exact_mod_cast h
  have hpy_norm : Summable fun k ↦ ‖p k (fun _ ↦ y)‖ := by
    refine hpnorm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun k ↦ ?_
    calc ‖p k (fun _ ↦ y)‖
        ≤ ‖p k‖ * ∏ _ : Fin k, ‖y‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖p k‖ * ‖y‖ ^ k := by simp
      _ ≤ ‖p k‖ * (r : ℝ) ^ k := by gcongr
  rw [hasSum_iff_tendsto_nat_of_summable_norm hpy_norm]
  have hdeg (k : ℕ) : p k (fun _ ↦ y) = ∑ α ∈ univ.piAntidiag k, (∏ i, y i ^ α i) • c α := by
    simp_rw [p.apply_eq_sum_mvCoeff, hpc]
  have hdisj (K : ℕ) : (range K : Set ℕ).PairwiseDisjoint (univ.piAntidiag (ι := ι) ·) :=
    fun _ _ _ _ hkl ↦ disjoint_left.2 fun _ hk hl ↦
      hkl ((mem_piAntidiag.1 hk).1.symm.trans (mem_piAntidiag.1 hl).1)
  have hExhaust : Tendsto (fun K : ℕ ↦ (range K).biUnion (univ.piAntidiag (ι := ι) ·))
      atTop atTop := by
    refine tendsto_atTop_atTop.2 fun s ↦ ⟨s.sup (fun α ↦ ∑ i, α i) + 1, fun K hK α hα ↦ ?_⟩
    simp only [mem_biUnion, mem_range, mem_piAntidiag]
    exact ⟨∑ i, α i, (le_sup (f := fun α ↦ ∑ i, α i) hα).trans_lt ((lt_add_one _).trans_le hK),
      by simp⟩
  simp_rw [hdeg, ← sum_biUnion (hdisj _)]
  exact (hf y hynorm).comp hExhaust

/-- **A normally convergent multi-index series has a power series** on the polydisc, whose
multi-index coefficients are the given ones. -/
theorem exists_hasFPowerSeriesOnBall_tsum [CompleteSpace F] (c : (ι → ℕ) → F) {r : ℝ≥0}
    (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) p 0 r ∧
        ∀ α, p.mvCoeff α = c α := by
  refine exists_hasFPowerSeriesOnBall_of_hasSum c hr hsum fun y hy ↦ ?_
  rw [zero_add]
  refine (Summable.of_norm_bounded hsum fun α ↦ ?_).hasSum
  rw [norm_smul, norm_prod, mul_comm, ← prod_pow_eq_pow_sum]
  gcongr with i
  rw [norm_pow]
  gcongr
  exact (norm_le_pi_norm y i).trans hy.le

/-- **Identity theorem for normally convergent multi-index series**: if `‖c α‖ * r ^ (∑ i, α i)` is
summable for some `r > 0` and `z ↦ ∑' α, (∏ i, z i ^ α i) • c α` vanishes near `0`, then every
coefficient `c α` is zero. -/
theorem eq_zero_of_eventually_tsum_prod_pow_smul_eq_zero [CompleteSpace F]
    {c : (ι → ℕ) → F} {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h0 : (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) =ᶠ[𝓝 0] 0)
    (α : ι → ℕ) : c α = 0 := by
  obtain ⟨p, hp, hpc⟩ := exists_hasFPowerSeriesOnBall_tsum (𝕜 := 𝕜) c hr hsum
  rw [← hpc]
  exact hp.hasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero h0 α

/-- **Identity theorem on a polydisc**: if `‖c α‖ * r ^ (∑ i, α i)` is summable for some `r > 0`
and `∑' α, (∏ i, z i ^ α i) • c α = 0` for all `z` in the open polydisc `Metric.ball 0 r`, then
every coefficient `c α` is zero. -/
theorem eq_zero_of_forall_mem_ball_tsum_prod_pow_smul_eq_zero [CompleteSpace F]
    {c : (ι → ℕ) → F} {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h0 : ∀ z ∈ Metric.ball (0 : ι → 𝕜) r, ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α = 0)
    (α : ι → ℕ) : c α = 0 :=
  eq_zero_of_eventually_tsum_prod_pow_smul_eq_zero hr hsum
    (eventually_of_mem (Metric.ball_mem_nhds 0 hr) h0) α

end TauCeti
