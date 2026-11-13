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
import TauCeti.GroupTheory.Perm.FiberSubgroup

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

* `FormalMultilinearSeries.mvCoeff`: the multi-index coefficient of a formal multilinear series,
  together with `ContinuousLinearMap.mvCoeff_compFormalMultilinearSeries` and
  `FormalMultilinearSeries.mvCoeff_constFormalMultilinearSeries`.
* `FormalMultilinearSeries.apply_eq_sum_mvCoeff`: the degree-`k` term is
  `∑ α ∈ univ.piAntidiag k, (∏ i, z i ^ α i) • p.mvCoeff α`.
* `FormalMultilinearSeries.sum_norm_mvCoeff_le`: the coefficients of total degree `k` have norms
  summing to at most `(card ι) ^ k * ‖p k‖`.
* `TauCeti.summable_norm_prod_pow_smul_of_le`,
  `FormalMultilinearSeries.summable_norm_mvCoeff_mul_pow`, and
  `FormalMultilinearSeries.summable_norm_prod_pow_smul_mvCoeff`: normal summability at radius `ρ`
  implies absolute summability on `‖y‖ ≤ ρ`, and the multi-index series converges
  normally and absolutely wherever the operator-norm bounds `(card ι) ^ k * ‖p k‖ * ρ ^ k` are
  summable.
* `HasFPowerSeriesOnBall.hasSum_mvCoeff`: a function with a power series is the sum of its
  multi-index series wherever the operator-norm bounds `(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` are
  summable.
* `TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum` and
  `TauCeti.exists_hasFPowerSeriesOnBall_tsum`: conversely, a normally convergent multi-index
  series has a formal multilinear power series on the polydisc whose multi-index coefficients are
  the given ones.
* `HasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero` and
  `TauCeti.eq_zero_of_tsum_prod_pow_smul_eventuallyEq_zero`: the identity theorem in coefficient
  form, so that the coefficients only depend on the function
  (`HasFPowerSeriesAt.mvCoeff_eq_of_eventuallyEq`).

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

/-- The coefficient of the zero multi-index is the constant term `p 0`, evaluated at the empty
tuple. -/
theorem mvCoeff_zero_eq_apply (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (v : Fin 0 → ι → 𝕜) : p.mvCoeff 0 = p 0 v := by
  classical
  rw [mvCoeff_eq_sum p (k := 0) (by simp)]
  simp [Subsingleton.elim _ v]

/-- Postcomposing a formal multilinear series with a continuous linear map applies that map to each
multi-index coefficient. -/
@[simp]
theorem _root_.ContinuousLinearMap.mvCoeff_compFormalMultilinearSeries
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (g : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) :
    (g.compFormalMultilinearSeries p).mvCoeff α = g (p.mvCoeff α) := by
  classical
  simp [mvCoeff_eq_sum _ rfl, map_sum]

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

/-- On the closed polydisc `‖y‖ ≤ ρ`, normal summability of a multi-index family `d` at radius `ρ`
implies absolute summability of `(∏ i, y i ^ β i) • d β`. -/
theorem TauCeti.summable_norm_prod_pow_smul_of_le {𝕜 : Type*} [NormedField 𝕜] {ι : Type*}
    [Fintype ι] {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {d : (ι → ℕ) → F} {ρ : ℝ} {y : ι → 𝕜}
    (hd : Summable fun β : ι → ℕ ↦ ‖d β‖ * ρ ^ (∑ i, β i)) (hy : ‖y‖ ≤ ρ) :
    Summable fun β : ι → ℕ ↦ ‖(∏ i, y i ^ β i) • d β‖ := by
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun β ↦ ?_) hd
  rw [norm_smul, norm_prod, mul_comm, ← prod_pow_eq_pow_sum]
  gcongr with i
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm y i).trans hy) _

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace FormalMultilinearSeries

/-- The multi-index coefficient of `constFormalMultilinearSeries 𝕜 (ι → 𝕜) c` is `c` at `0` and `0`
at every nonzero multi-index. -/
@[simp]
theorem mvCoeff_constFormalMultilinearSeries (c : F) (α : ι → ℕ) :
    (constFormalMultilinearSeries 𝕜 (ι → 𝕜) c).mvCoeff α = if α = 0 then c else 0 := by
  classical
  split_ifs with hα
  · subst hα
    simp [mvCoeff_zero_eq_apply (v := 0)]
  · have hsum : ∑ i, α i ≠ 0 := fun h0 ↦
      hα (funext fun i ↦ Finset.sum_eq_zero_iff.1 h0 i (mem_univ i))
    rw [mvCoeff_eq_sum _ rfl]
    simp [constFormalMultilinearSeries_apply_of_ne_zero hsum]

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

/-- **Normal convergence of the multi-index coefficients**: if `0 ≤ ρ` and the operator-norm bounds
`(card ι) ^ k * ‖p k‖ * ρ ^ k` are summable, then `‖p.mvCoeff α‖ * ρ ^ (∑ i, α i)` is summable
over all multi-indices `α`. -/
theorem summable_norm_mvCoeff_mul_pow (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (h : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k) :
    Summable fun α : ι → ℕ ↦ ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) := by
  classical
  have hdeg (k : ℕ) : ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) ≤
      (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k := by
    calc ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i)
        = (∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖) * ρ ^ k := by
          rw [sum_mul]
          exact sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
      _ ≤ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k := by
          gcongr
          exact_mod_cast sum_norm_mvCoeff_le p k
  -- A finite sum splits by total degree, and each degree is bounded by its weighted term.
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
    Summable fun α : ι → ℕ ↦ ‖(∏ i, z i ^ α i) • p.mvCoeff α‖ :=
  TauCeti.summable_norm_prod_pow_smul_of_le
    (p.summable_norm_mvCoeff_mul_pow (norm_nonneg z) h) le_rfl

omit [Fintype ι] in
/-- The continuous `k`-multilinear map `(m₁, …, mₖ) ↦ (∏ j, mⱼ (g j)) • v` realizing one ordered
monomial of degree `k`. -/
private noncomputable def monomialMultilinearMap {k : ℕ} (g : Fin k → ι) (v : F) :
    (ι → 𝕜) [×k]→L[𝕜] F :=
  (ContinuousMultilinearMap.mkPiRing 𝕜 (Fin k) v).compContinuousLinearMap
    fun j ↦ ContinuousLinearMap.proj (g j)

private theorem norm_monomialMultilinearMap_le {k : ℕ} (g : Fin k → ι) (v : F) :
    ‖monomialMultilinearMap (𝕜 := 𝕜) g v‖ ≤ ‖v‖ :=
  ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg v) fun m ↦ by
    simp only [monomialMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearMap.proj_apply, ContinuousMultilinearMap.mkPiRing_apply]
    rw [norm_smul, norm_prod, mul_comm]
    gcongr with j
    exact norm_le_pi_norm (m j) (g j)

omit [Fintype ι] in
private theorem monomialMultilinearMap_basis [DecidableEq ι] {k : ℕ} (g a : Fin k → ι) (v : F) :
    monomialMultilinearMap g v (fun j ↦ Pi.single (a j) (1 : 𝕜)) = if a = g then v else 0 := by
  simp only [monomialMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.proj_apply, ContinuousMultilinearMap.mkPiRing_apply]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.1 h
    rw [prod_eq_zero (mem_univ j), zero_smul]
    simp [hj.symm]

open Classical in
/-- Formal multilinear series realizing a prescribed family of multi-index coefficients `c` by
picking one coordinate ordering per multi-index in each total degree `k`. Kept private because
off-diagonal multilinear values depend on the chosen ordering; only `mvCoeff` and the diagonal
evaluation are canonical. -/
private noncomputable def ofMvCoeff (c : (ι → ℕ) → F) :
    FormalMultilinearSeries 𝕜 (ι → 𝕜) F := fun k ↦
  ∑ α ∈ univ.piAntidiag k,
    if hα : ∑ i, α i = k then
      monomialMultilinearMap
        (TauCeti.exists_forall_card_filter_eq (α := Fin k)
          (hα.trans (Fintype.card_fin k).symm)).choose (c α)
    else 0

open Classical in
private theorem norm_ofMvCoeff_le (c : (ι → ℕ) → F) (k : ℕ) :
    ‖ofMvCoeff (𝕜 := 𝕜) c k‖ ≤ ∑ α ∈ univ.piAntidiag k, ‖c α‖ := by
  unfold ofMvCoeff
  refine (norm_sum_le _ _).trans (sum_le_sum fun α hα ↦ ?_)
  rw [dite_eq_left_of_eq_true (eq_true (mem_piAntidiag.1 hα).1)]
  exact norm_monomialMultilinearMap_le _ _

open Classical in
private theorem mvCoeff_ofMvCoeff (c : (ι → ℕ) → F) (β : ι → ℕ) :
    (ofMvCoeff (𝕜 := 𝕜) c).mvCoeff β = c β := by
  set k := ∑ i, β i with hk_def
  let S := univ.filter fun a : Fin k → ι ↦ ∀ i, Fintype.card {j // a j = i} = β i
  rw [mvCoeff_eq_sum _ hk_def.symm]
  simp only [ofMvCoeff, _root_.sum_apply]
  rw [sum_comm]
  have hterm (α : ι → ℕ) (hα : α ∈ univ.piAntidiag k) :
      (∑ x ∈ S, (if h : ∑ i, α i = k then
        monomialMultilinearMap (𝕜 := 𝕜)
          (TauCeti.exists_forall_card_filter_eq (α := Fin k)
            (h.trans (Fintype.card_fin k).symm)).choose (c α)
      else 0) (fun j ↦ Pi.single (x j) (1 : 𝕜))) = if α = β then c α else 0 := by
    have hαk : ∑ i, α i = k := (mem_piAntidiag.1 hα).1
    have hcard : ∑ i, α i = Fintype.card (Fin k) := hαk.trans (Fintype.card_fin k).symm
    have hg := (TauCeti.exists_forall_card_filter_eq (α := Fin k) hcard).choose_spec
    simp_rw [dite_eq_left_of_eq_true (eq_true hαk), monomialMultilinearMap_basis]
    have hmem : (TauCeti.exists_forall_card_filter_eq (α := Fin k) hcard).choose ∈ S ↔ α = β := by
      simp [S, Fintype.card_subtype, hg, funext_iff]
    simp [hmem]
  rw [sum_congr rfl hterm]
  have hβ : β ∈ univ.piAntidiag k := mem_piAntidiag.2 ⟨hk_def.symm, by simp⟩
  simp [hβ]

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

open FormalMultilinearSeries

/-- **Power series from a normally convergent multi-index expansion**: if `c` is normally summable
at radius `r > 0` and `(∏ i, y i ^ α i) • c α` has sum `f (x + y)` on the open polydisc `‖y‖ < r`,
then `f` has a formal multilinear power series on the ball of radius `r` about `x` whose
multi-index coefficients are `c`. No completeness assumption on `F` is needed. -/
theorem exists_hasFPowerSeriesOnBall_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    {c : (ι → ℕ) → F} {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (hf : ∀ y : ι → 𝕜, ‖y‖ < r → HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y))) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall f p x r ∧ ∀ α, p.mvCoeff α = c α := by
  classical
  let p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F := ofMvCoeff c
  have hpc : ∀ α, p.mvCoeff α = c α := mvCoeff_ofMvCoeff c
  have hdisj (s : Set ℕ) : s.PairwiseDisjoint (univ.piAntidiag (ι := ι) ·) :=
    fun k _ l _ hkl ↦ disjoint_left.2 fun α hk hl ↦
      hkl ((mem_piAntidiag.1 hk).1.symm.trans (mem_piAntidiag.1 hl).1)
  -- Group the weighted coefficient norms by total degree to bound `p.radius` below by `r`.
  have hrad : (r : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_summable
    refine summable_of_sum_le (c := ∑' α, ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
      (fun _ ↦ by positivity) fun t ↦ ?_
    have ht : ∑ k ∈ t, ‖p k‖ * (r : ℝ) ^ k ≤
        ∑ k ∈ t, ∑ α ∈ univ.piAntidiag k, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
      refine sum_le_sum fun k _ ↦ ?_
      calc ‖p k‖ * (r : ℝ) ^ k
          ≤ (∑ α ∈ univ.piAntidiag k, ‖c α‖) * (r : ℝ) ^ k := by
            gcongr; exact norm_ofMvCoeff_le c k
        _ = ∑ α ∈ univ.piAntidiag k, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
            rw [sum_mul]
            exact sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
    rw [← sum_biUnion (hdisj t)] at ht
    exact ht.trans (hsum.sum_le_tsum _ fun _ _ ↦ by positivity)
  refine ⟨p, ⟨hrad, ENNReal.coe_pos.2 hr, fun {y} hy ↦ ?_⟩, hpc⟩
  have hynorm : ‖y‖ < (r : ℝ) := by
    have h : ‖y‖₊ < r := by
      simpa only [mem_eball_zero_iff, eNorm_eq_nnNorm, ENNReal.coe_lt_coe] using hy
    exact_mod_cast h
  -- Sum the given expansion fiberwise by total degree; each fiber is finite.
  let e : (Σ k : ℕ, {α // α ∈ univ.piAntidiag k}) ≃ (ι → ℕ) :=
    { toFun := fun x ↦ x.2.1
      invFun := fun α ↦ ⟨∑ i, α i, ⟨α, mem_piAntidiag.2 ⟨rfl, by simp⟩⟩⟩
      left_inv := by rintro ⟨_, α, hα⟩; obtain ⟨rfl, -⟩ := mem_piAntidiag.1 hα; rfl
      right_inv := fun _ ↦ rfl }
  refine (e.hasSum_iff.2 (hf y hynorm)).sigma fun k ↦ ?_
  rw [p.apply_eq_sum_mvCoeff k y]
  simp_rw [hpc, ← sum_coe_sort (univ.piAntidiag k)]
  exact hasSum_fintype _

/-- **A normally convergent multi-index series has a power series on the polydisc**, whose
multi-index coefficients are the given ones. -/
theorem exists_hasFPowerSeriesOnBall_tsum [CompleteSpace F] (c : (ι → ℕ) → F) {r : ℝ≥0}
    (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) p 0 r ∧
        ∀ α, p.mvCoeff α = c α := by
  refine exists_hasFPowerSeriesOnBall_of_hasSum hr hsum fun y hy ↦ ?_
  simpa only [zero_add] using (summable_norm_prod_pow_smul_of_le hsum hy.le).of_norm.hasSum

/-- **Uniqueness of normally convergent multi-index series**: if a multi-index series converges
normally on a polydisc of positive radius and vanishes near the origin (in particular if it
vanishes on the polydisc), then all its coefficients are zero. -/
theorem eq_zero_of_tsum_prod_pow_smul_eventuallyEq_zero [CompleteSpace F]
    {c : (ι → ℕ) → F} {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h0 : (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) =ᶠ[𝓝 0] 0)
    (α : ι → ℕ) : c α = 0 := by
  obtain ⟨p, hp, hpc⟩ := exists_hasFPowerSeriesOnBall_tsum (𝕜 := 𝕜) c hr hsum
  rw [← hpc α]
  exact hp.hasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero h0 α

end TauCeti
