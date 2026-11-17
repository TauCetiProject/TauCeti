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
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
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
  `FormalMultilinearSeries.summable_norm_prod_pow_smul_mvCoeff`: normal and absolute convergence of
  the multi-index series wherever `(card ι) ^ k * ‖p k‖ * ρ ^ k` is summable.
* `Summable.norm_prod_pow_smul_of_le`: normal convergence on a closed polydisc implies absolute
  convergence at every point of the polydisc.
* `HasFPowerSeriesOnBall.hasSum_mvCoeff`: a function with a power series is the sum of its
  multi-index series wherever the operator-norm bounds `(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` are
  summable.
* `HasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero`: the identity theorem in coefficient
  form, so that the coefficients only depend on the function
  (`HasFPowerSeriesAt.mvCoeff_eq_of_eventuallyEq`).
* `TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum` and `TauCeti.exists_hasFPowerSeriesOnBall_tsum`:
  a normally convergent multi-index series has a power series on the polydisc whose multi-index
  coefficients are the given ones.
* `TauCeti.eq_zero_of_forall_hasSum_prod_pow_smul_eq_zero` and
  `TauCeti.eq_zero_of_forall_tsum_prod_pow_smul_eq_zero`: uniqueness of coefficients for a normally
  convergent multi-index series vanishing on a polydisc.

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

/-- A normally convergent multi-index series on a closed polydisc of radius `r` is absolutely
summable at every point `y` with `‖y‖ ≤ r`. -/
theorem Summable.norm_prod_pow_smul_of_le {R : Type*} [NormedCommRing R] [NormOneClass R]
    {ι : Type*} [Fintype ι] {F : Type*} [SeminormedAddCommGroup F] [SMulZeroClass R F]
    [IsBoundedSMul R F] {c : (ι → ℕ) → F} {r : ℝ}
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * r ^ (∑ i, α i))
    {y : ι → R} (hy : ‖y‖ ≤ r) :
    Summable fun α : ι → ℕ ↦ ‖(∏ i, y i ^ α i) • c α‖ := by
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun α ↦ ?_) hsum
  calc ‖(∏ i, y i ^ α i) • c α‖
      ≤ ‖∏ i, y i ^ α i‖ * ‖c α‖ := norm_smul_le _ _
    _ = ‖c α‖ * ‖∏ i, y i ^ α i‖ := mul_comm _ _
    _ ≤ ‖c α‖ * ∏ i, ‖y i ^ α i‖ := by
        gcongr
        exact Finset.norm_prod_le _ _
    _ ≤ ‖c α‖ * r ^ (∑ i, α i) := by
        rw [← prod_pow_eq_pow_sum]
        gcongr with i
        exact (norm_pow_le (y i) (α i)).trans
          (pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm y i).trans hy) _)

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

/-- **Normal convergence of the multi-index series**: if `(card ι) ^ k * ‖p k‖ * ρ ^ k` is summable
for `ρ ≥ 0`, then the weighted norms `‖p.mvCoeff α‖ * ρ ^ (∑ i, α i)` are summable over all
multi-indices `α`. -/
theorem summable_norm_mvCoeff_mul_pow (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (h : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k) :
    Summable fun α : ι → ℕ ↦ ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) := by
  classical
  refine summable_of_sum_le (c := ∑' k, (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k)
    (fun _ ↦ by positivity) fun s ↦ ?_
  rw [← sum_fiberwise_of_maps_to (g := fun α ↦ ∑ i, α i) (t := s.image (fun α ↦ ∑ i, α i))
    (fun α hα ↦ mem_image_of_mem _ hα)]
  refine (sum_le_sum fun k _ ↦ ?_).trans (h.sum_le_tsum _ fun _ _ ↦ by positivity)
  have hsub : s.filter (fun α ↦ ∑ i, α i = k) ⊆ univ.piAntidiag k :=
    fun α hα ↦ mem_piAntidiag.2 ⟨(mem_filter.1 hα).2, by simp⟩
  calc ∑ α ∈ s.filter (fun α ↦ ∑ i, α i = k), ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i)
      ≤ ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
    _ = (∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖) * ρ ^ k := by
        rw [sum_mul]
        exact sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
    _ ≤ ((Fintype.card ι : ℝ) ^ k * ‖p k‖) * ρ ^ k := by
        gcongr
        exact_mod_cast sum_norm_mvCoeff_le p k

/-- **Absolute convergence of the multi-index series**: if the operator-norm bounds
`(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` are summable, then the multi-index series
`∑ α, (∏ i, z i ^ α i) • p.mvCoeff α` converges absolutely. -/
theorem summable_norm_prod_pow_smul_mvCoeff (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    {z : ι → 𝕜} (h : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k) :
    Summable fun α : ι → ℕ ↦ ‖(∏ i, z i ^ α i) • p.mvCoeff α‖ :=
  (p.summable_norm_mvCoeff_mul_pow (norm_nonneg z) h).norm_prod_pow_smul_of_le le_rfl

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

/-- A chosen tuple of coordinates of length `k` in which each `i : ι` appears `α i` times. -/
private noncomputable def canonicalTuple {k : ℕ} {α : ι → ℕ} (hk : ∑ i, α i = k) : Fin k → ι :=
  let e : (Σ i : ι, Fin (α i)) ≃ Fin k :=
    (Fintype.equivFin (Σ i : ι, Fin (α i))).trans (finCongr (by simp [hk]))
  fun j ↦ (e.symm j).1

private theorem card_canonicalTuple_eq [DecidableEq ι] {k : ℕ} {α : ι → ℕ}
    (hk : ∑ i, α i = k) (i : ι) :
    Fintype.card {j : Fin k // canonicalTuple hk j = i} = α i := by
  let e : (Σ i : ι, Fin (α i)) ≃ Fin k :=
    (Fintype.equivFin (Σ i : ι, Fin (α i))).trans (finCongr (by simp [hk]))
  let e₁ : {j : Fin k // (e.symm j).1 = i} ≃ {x : Σ i', Fin (α i') // x.1 = i} :=
    Equiv.subtypeEquiv e.symm fun _ ↦ Iff.rfl
  let e₂ : {x : Σ i', Fin (α i') // x.1 = i} ≃ Fin (α i) :=
    { toFun := fun ⟨⟨_, b⟩, h⟩ ↦ by subst h; exact b
      invFun := fun b ↦ ⟨⟨i, b⟩, rfl⟩
      left_inv := fun ⟨⟨_, _⟩, rfl⟩ ↦ rfl
      right_inv := fun _ ↦ rfl }
  simpa [canonicalTuple, e] using Fintype.card_congr (e₁.trans e₂)

/-- A continuous `k`-multilinear map on `ι → 𝕜` supported on the single basis tuple
`canonicalTuple hk`, where it takes the value `v`. -/
private noncomputable def monomialMap {k : ℕ} {α : ι → ℕ} (hk : ∑ i, α i = k) (v : F) :
    ContinuousMultilinearMap 𝕜 (fun _ : Fin k ↦ ι → 𝕜) F :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin k) v).compContinuousLinearMap
    fun j ↦ ContinuousLinearMap.proj (R := 𝕜) (canonicalTuple hk j)

private theorem norm_monomialMap_le {k : ℕ} {α : ι → ℕ} (hk : ∑ i, α i = k) (v : F) :
    ‖monomialMap (𝕜 := 𝕜) hk v‖ ≤ ‖v‖ := by
  have hproj (i : ι) : ‖ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by
      simpa using norm_le_pi_norm z i
  calc ‖monomialMap (𝕜 := 𝕜) hk v‖
      ≤ ‖ContinuousMultilinearMap.mkPiRing 𝕜 (Fin k) v‖ *
          ∏ j : Fin k, ‖ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜)
            (canonicalTuple hk j)‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖v‖ * ∏ _ : Fin k, (1 : ℝ) := by
        rw [ContinuousMultilinearMap.norm_mkPiRing]
        gcongr
        exact hproj _
    _ = ‖v‖ := by simp

private theorem monomialMap_apply_single [DecidableEq ι] {k : ℕ} {α : ι → ℕ}
    (hk : ∑ i, α i = k) (v : F) (b : Fin k → ι) :
    monomialMap (𝕜 := 𝕜) hk v (fun j ↦ Pi.single (b j) 1) =
      if b = canonicalTuple hk then v else 0 := by
  simp only [monomialMap, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.proj_apply, ContinuousMultilinearMap.mkPiRing_apply]
  split_ifs with h
  · subst h
    simp [Pi.single_eq_same]
  · obtain ⟨j, hj⟩ : ∃ j, b j ≠ canonicalTuple hk j := by
      contrapose! h
      exact funext h
    have hzero : ∏ l : Fin k, (Pi.single (b l) (1 : 𝕜) : ι → 𝕜) (canonicalTuple hk l) = 0 :=
      prod_eq_zero (mem_univ j) (Pi.single_eq_of_ne hj.symm _)
    simp [hzero]

/-- A formal multilinear series whose multi-index coefficients are the given family `c`. -/
private noncomputable def ofMvCoeff [DecidableEq ι] (c : (ι → ℕ) → F) :
    FormalMultilinearSeries 𝕜 (ι → 𝕜) F :=
  fun k ↦ ∑ α ∈ (univ.piAntidiag k).attach, monomialMap (mem_piAntidiag.1 α.2).1 (c α.1)

private theorem mvCoeff_ofMvCoeff [DecidableEq ι] (c : (ι → ℕ) → F) (β : ι → ℕ) :
    (ofMvCoeff (𝕜 := 𝕜) c).mvCoeff β = c β := by
  rw [FormalMultilinearSeries.mvCoeff_eq_sum _ rfl]
  simp only [ofMvCoeff, sum_apply, monomialMap_apply_single]
  rw [sum_comm]
  have hβ : β ∈ univ.piAntidiag (∑ i, β i) := mem_piAntidiag.2 ⟨rfl, by simp⟩
  rw [sum_eq_single ⟨β, hβ⟩]
  · rw [sum_ite_eq']
    simp [card_canonicalTuple_eq]
  · intro α _ hα
    rw [sum_ite_eq']
    have hnot : ¬ ∀ i, Fintype.card {j // canonicalTuple (mem_piAntidiag.1 α.2).1 j = i} = β i := by
      intro h
      apply hα
      ext i
      simpa [card_canonicalTuple_eq] using h i
    simp [hnot]
  · intro h
    exact absurd (mem_attach _ ⟨β, hβ⟩) h

private theorem norm_ofMvCoeff_le [DecidableEq ι] (c : (ι → ℕ) → F) (k : ℕ) :
    ‖ofMvCoeff (𝕜 := 𝕜) c k‖ ≤ ∑ α ∈ univ.piAntidiag k, ‖c α‖ := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ α ∈ (univ.piAntidiag k).attach,
        ‖monomialMap (𝕜 := 𝕜) (mem_piAntidiag.1 α.2).1 (c α.1)‖
      ≤ ∑ α ∈ (univ.piAntidiag k).attach, ‖c α.1‖ := sum_le_sum fun _ _ ↦ norm_monomialMap_le _ _
    _ = ∑ α ∈ univ.piAntidiag k, ‖c α‖ := sum_attach (univ.piAntidiag k) (fun α ↦ ‖c α‖)

private theorem le_radius_ofMvCoeff [DecidableEq ι] {c : (ι → ℕ) → F} {r : ℝ≥0}
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) :
    (r : ℝ≥0∞) ≤ (ofMvCoeff (𝕜 := 𝕜) c).radius := by
  refine (ofMvCoeff (𝕜 := 𝕜) c).le_radius_of_summable ?_
  refine summable_of_sum_le (c := ∑' α : ι → ℕ, ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (fun _ ↦ by positivity) fun s ↦ ?_
  have hdisj : (s : Set ℕ).PairwiseDisjoint (univ.piAntidiag (ι := ι) ·) :=
    fun k _ l _ hkl ↦ disjoint_left.2 fun α hk hl ↦
      hkl ((mem_piAntidiag.1 hk).1.symm.trans (mem_piAntidiag.1 hl).1)
  calc ∑ k ∈ s, ‖ofMvCoeff (𝕜 := 𝕜) c k‖ * (r : ℝ) ^ k
      ≤ ∑ k ∈ s, (∑ α ∈ univ.piAntidiag k, ‖c α‖) * (r : ℝ) ^ k :=
        sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right (norm_ofMvCoeff_le c k) (by positivity)
    _ = ∑ k ∈ s, ∑ α ∈ univ.piAntidiag k, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
        refine sum_congr rfl fun k _ ↦ ?_
        rw [sum_mul]
        exact sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
    _ = ∑ α ∈ s.biUnion (univ.piAntidiag ·), ‖c α‖ * (r : ℝ) ^ (∑ i, α i) :=
        (sum_biUnion hdisj).symm
    _ ≤ ∑' α : ι → ℕ, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) :=
        hsum.sum_le_tsum _ fun _ _ ↦ by positivity

/-- **A normally convergent multi-index series gives a power series on the polydisc**: if
`f (x + y)` is the sum of `(∏ i, y i ^ α i) • c α` on the open polydisc of radius `r > 0` and the
coefficient norms weighted by `r ^ (∑ i, α i)` are summable, then `f` has a formal power series on
that ball whose multi-index coefficients are `c`. No completeness assumption on `F` is needed. -/
theorem exists_hasFPowerSeriesOnBall_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    {c : (ι → ℕ) → F} {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (hf : ∀ y : ι → 𝕜, ‖y‖ < r →
      HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y))) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall f p x r ∧ ∀ α, p.mvCoeff α = c α := by
  classical
  let p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F := ofMvCoeff c
  have hpc : ∀ α, p.mvCoeff α = c α := mvCoeff_ofMvCoeff c
  refine ⟨p, ⟨le_radius_ofMvCoeff hsum, ENNReal.coe_pos.mpr hr, fun {y} hy ↦ ?_⟩, hpc⟩
  have hynorm : ‖y‖ < (r : ℝ) := by
    have h : ‖y‖₊ < r := by
      simpa only [mem_eball_zero_iff, eNorm_eq_nnNorm, ENNReal.coe_lt_coe] using hy
    exact_mod_cast h
  -- Group the multi-index sum by total degree via the fiber equivalence over `univ.piAntidiag`.
  let e : (Σ k : ℕ, univ.piAntidiag (ι := ι) k) ≃ (ι → ℕ) :=
    { toFun := fun x ↦ x.2.1
      invFun := fun α ↦ ⟨∑ i, α i, ⟨α, mem_piAntidiag.2 ⟨rfl, by simp⟩⟩⟩
      left_inv := fun ⟨k, ⟨α, hα⟩⟩ ↦ by
        have hk : ∑ i, α i = k := (mem_piAntidiag.1 hα).1
        subst hk
        rfl
      right_inv := fun _ ↦ rfl }
  have hsigma : HasSum (fun q : Σ k : ℕ, univ.piAntidiag (ι := ι) k ↦
      (∏ i, y i ^ q.2.1 i) • c q.2.1) (f (x + y)) :=
    e.hasSum_iff.mpr (hf y hynorm)
  have hgrouped := hsigma.sigma fun k ↦
    hasSum_fintype (L := .unconditional _) fun α : univ.piAntidiag (ι := ι) k ↦
      (∏ i, y i ^ α.1 i) • c α.1
  convert hgrouped using 1
  ext k
  rw [FormalMultilinearSeries.apply_eq_sum_mvCoeff, Finset.univ_eq_attach]
  simp only [hpc]
  exact (sum_attach (univ.piAntidiag k) fun α ↦ (∏ i, y i ^ α i) • c α).symm

/-- **A normally convergent multi-index `tsum` has a power series on the polydisc** whose
multi-index coefficients are the given ones. -/
theorem exists_hasFPowerSeriesOnBall_tsum [CompleteSpace F] (c : (ι → ℕ) → F) {r : ℝ≥0}
    (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) p 0 r ∧
        ∀ α, p.mvCoeff α = c α :=
  exists_hasFPowerSeriesOnBall_of_hasSum hr hsum fun y hy ↦ by
    simpa using (hsum.norm_prod_pow_smul_of_le hy.le).of_norm.hasSum

/-- **Uniqueness of coefficients for a normally convergent multi-index series**: if a normally
convergent multi-index series sums to `0` on an open polydisc of positive radius, then every
coefficient vanishes. -/
theorem eq_zero_of_forall_hasSum_prod_pow_smul_eq_zero {c : (ι → ℕ) → F} {r : ℝ≥0}
    (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h0 : ∀ y : ι → 𝕜, ‖y‖ < r → HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) 0)
    (α : ι → ℕ) : c α = 0 := by
  obtain ⟨p, hp, hpc⟩ := exists_hasFPowerSeriesOnBall_of_hasSum (f := 0) (x := 0) hr hsum h0
  rw [← hpc α]
  exact hp.hasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero .rfl α

/-- **Uniqueness of coefficients for a normally convergent multi-index `tsum`**: in a complete
space, if `∑' α, (∏ i, y i ^ α i) • c α = 0` on an open polydisc of positive radius, then every
coefficient vanishes. -/
theorem eq_zero_of_forall_tsum_prod_pow_smul_eq_zero [CompleteSpace F] {c : (ι → ℕ) → F}
    {r : ℝ≥0} (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h0 : ∀ y : ι → 𝕜, ‖y‖ < r → (∑' α : ι → ℕ, (∏ i, y i ^ α i) • c α) = 0)
    (α : ι → ℕ) : c α = 0 :=
  eq_zero_of_forall_hasSum_prod_pow_smul_eq_zero hr hsum (fun y hy ↦ by
    rw [← h0 y hy]
    exact (hsum.norm_prod_pow_smul_of_le hy.le).of_norm.hasSum) α

end TauCeti
