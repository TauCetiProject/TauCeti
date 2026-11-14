/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fintype.EquivFin
import TauCeti.Algebra.MvPolynomial.Funext
import TauCeti.Analysis.Normed.Ring.InfiniteSum

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
* `FormalMultilinearSeries.prod_factorial_smul_mvCoeff`: `(∏ i, (α i)!) • p.mvCoeff α` equals the
  sum over permutations of `Fin (∑ i, α i)` appearing in the iterated Fréchet derivative.
* `FormalMultilinearSeries.sum_norm_mvCoeff_le`: the coefficients of total degree `k` have norms
  summing to at most `(card ι) ^ k * ‖p k‖`.
* `FormalMultilinearSeries.summable_norm_mvCoeff_mul_pow` and
  `FormalMultilinearSeries.summable_norm_prod_pow_smul_mvCoeff`: normal and absolute convergence
  of the multi-index series wherever `(card ι) ^ k * ‖p k‖ * ρ ^ k` is summable.
* `HasFPowerSeriesOnBall.hasSum_mvCoeff`: a function with a power series is the sum of its
  multi-index series wherever `(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` is summable.
* `TauCeti.summable_norm_prod_pow_smul` and
  `TauCeti.summable_norm_mul_pow_of_summable_prod_pow_smul`: absolute convergence on closed
  polydiscs and Abel's lemma for multi-index series.
* `TauCeti.exists_hasFPowerSeriesOnBall_of_hasSum`, `TauCeti.exists_hasFPowerSeriesOnBall_tsum`,
  and `TauCeti.exists_hasFPowerSeriesAt_of_eventually_hasSum`: conversely, a convergent
  multi-index series defines a formal multilinear series whose multi-index coefficients are the
  given ones.
* `HasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero`,
  `TauCeti.eq_zero_of_eventually_hasSum_prod_pow_smul_zero`, and
  `TauCeti.eq_zero_of_eventuallyEq_tsum_prod_pow_smul_zero`: the identity theorem in coefficient
  form for power series and for multi-index series.

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

/-- `mvCoeff p α` depends only on the homogeneous term of degree `∑ i, α i`. -/
theorem mvCoeff_congr {p q : FormalMultilinearSeries 𝕜 (ι → 𝕜) F} {α : ι → ℕ}
    (h : p (∑ i, α i) = q (∑ i, α i)) : p.mvCoeff α = q.mvCoeff α := by
  unfold mvCoeff
  simp_rw [h]

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

@[simp]
theorem mvCoeff_sum {κ : Type*} (s : Finset κ) (p : κ → FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (α : ι → ℕ) : (∑ x ∈ s, p x).mvCoeff α = ∑ x ∈ s, (p x).mvCoeff α := by
  classical
  induction s using Finset.induction_on <;> simp [*]

/-- The coefficient of the zero multi-index is the constant term `p 0`, evaluated at the empty
tuple. -/
theorem mvCoeff_zero_eq_apply (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (v : Fin 0 → ι → 𝕜) : p.mvCoeff 0 = p 0 v := by
  classical
  rw [mvCoeff_eq_sum p (k := 0) (by simp)]
  simp [Subsingleton.elim _ v]

/-- Over a singleton index type, `p.mvCoeff α` is `p (α default)` evaluated at the constant `1`
vector. -/
theorem mvCoeff_eq_apply_of_unique [Unique ι] (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    (α : ι → ℕ) : p.mvCoeff α = p (α default) (fun _ _ ↦ 1) := by
  classical
  rw [mvCoeff_eq_sum p (k := α default) (Fintype.sum_unique α)]
  have hcard (a : Fin (α default) → ι) (i : ι) : Fintype.card {j // a j = i} = α i := by
    rw [Unique.eq_default i,
      Fintype.card_congr (Equiv.subtypeUnivEquiv fun j ↦ Subsingleton.elim (a j) default),
      Fintype.card_fin]
  have huniq : univ.filter (fun a : Fin (α default) → ι ↦ ∀ i, Fintype.card {j // a j = i} = α i) =
      {fun _ ↦ default} := by
    ext a
    simp only [mem_filter, mem_univ, hcard a, implies_true, and_true, mem_singleton]
    exact iff_of_true trivial (Subsingleton.elim a _)
  have h1 : Pi.single (M := fun _ : ι ↦ 𝕜) default 1 = fun _ ↦ 1 := by
    ext i
    rw [Unique.eq_default i, Pi.single_eq_same]
  rw [huniq, sum_singleton]
  simp_rw [h1]

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

omit [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
/-- Bijection between permutations `σ` sending `a` to `v` (`v ∘ σ = a`) and families of fiberwise
bijections `{j // a j = i} ≃ {j // v j = i}`. -/
private def permCompEquiv {k : ℕ} (v a : Fin k → ι) :
    {σ : Equiv.Perm (Fin k) // v ∘ σ = a} ≃ ∀ i : ι, {j // a j = i} ≃ {j // v j = i} where
  toFun σ i :=
    { toFun := fun j ↦ ⟨σ.1 j.1, (congr_fun σ.2 j.1).trans j.2⟩
      invFun := fun j ↦ ⟨σ.1.symm j.1, by
        have h := congr_fun σ.2 (σ.1.symm j.1)
        simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
        exact h.symm.trans j.2⟩
      left_inv := fun j ↦ Subtype.ext (σ.1.symm_apply_apply j.1)
      right_inv := fun j ↦ Subtype.ext (σ.1.apply_symm_apply j.1) }
  invFun τ :=
    ⟨(Equiv.sigmaFiberEquiv a).symm.trans
        ((Equiv.sigmaCongrRight τ).trans (Equiv.sigmaFiberEquiv v)),
      funext fun j ↦ ((τ (a j)) ⟨j, rfl⟩).2⟩
  left_inv σ := by
    ext j
    simp [Equiv.sigmaFiberEquiv]
  right_inv τ := by
    ext i ⟨j, rfl⟩
    simp [Equiv.sigmaFiberEquiv]

omit [NormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
/-- The number of permutations `σ` of `Fin k` satisfying `v ∘ σ = a` is `∏ i, (α i)!` whenever both
`v` and `a` have fiber counts `α`. -/
private theorem card_perm_comp_eq [DecidableEq ι] {k : ℕ} {α : ι → ℕ} {v a : Fin k → ι}
    (hv : ∀ i, Fintype.card {j // v j = i} = α i)
    (ha : ∀ i, Fintype.card {j // a j = i} = α i) :
    (univ.filter fun σ : Equiv.Perm (Fin k) ↦ v ∘ σ = a).card = ∏ i, (α i).factorial := by
  rw [← Fintype.card_subtype, Fintype.card_congr (permCompEquiv v a), Fintype.card_pi]
  refine prod_congr rfl fun i _ ↦ ?_
  have ev := Fintype.equivFinOfCardEq (hv i)
  have ea := Fintype.equivFinOfCardEq (ha i)
  rw [Fintype.card_congr (Equiv.equivCongr ea ev), Fintype.card_perm, Fintype.card_fin]

/-- Multiplying `p.mvCoeff α` by `∏ i, (α i)!` gives the sum of `p (∑ i, α i)` over all
permutations of any tuple `v` of coordinate indices with counts `α`. -/
theorem prod_factorial_smul_mvCoeff [DecidableEq ι]
    (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) (v : Fin (∑ i, α i) → ι)
    (hv : ∀ i, (univ.filter fun j ↦ v j = i).card = α i) :
    (∏ i, (α i).factorial) • p.mvCoeff α =
      ∑ σ : Equiv.Perm (Fin (∑ i, α i)), p (∑ i, α i) (fun j ↦ Pi.single (v (σ j)) 1) := by
  have hv' (i : ι) : Fintype.card {j // v j = i} = α i := by
    simpa [Fintype.card_subtype] using hv i
  let S := univ.filter fun a : Fin (∑ i, α i) → ι ↦ ∀ i, Fintype.card {j // a j = i} = α i
  have hmaps : ∀ σ ∈ (univ : Finset (Equiv.Perm (Fin (∑ i, α i)))), v ∘ σ ∈ S := fun σ _ ↦ by
    simp only [S, mem_filter, mem_univ, true_and]
    intro i
    rw [← hv' i]
    exact Fintype.card_congr (Equiv.subtypeEquiv σ fun _ ↦ Iff.rfl)
  rw [← sum_fiberwise_of_maps_to hmaps, mvCoeff_eq_sum p rfl, smul_sum]
  refine sum_congr rfl fun a ha ↦ ?_
  have hcongr : ∑ σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (∑ i, α i)) ↦ v ∘ σ = a),
      p (∑ i, α i) (fun j ↦ Pi.single (v (σ j)) 1) =
      ∑ _σ ∈ univ.filter (fun σ : Equiv.Perm (Fin (∑ i, α i)) ↦ v ∘ σ = a),
        p (∑ i, α i) (fun j ↦ Pi.single (a j) 1) :=
    sum_congr rfl fun σ hσ ↦ by simp_rw [← funext_iff.1 (mem_filter.1 hσ).2, Function.comp_apply]
  rw [hcongr, sum_const, card_perm_comp_eq hv' (mem_filter.1 ha).2]

end NormedField

end FormalMultilinearSeries

namespace ContinuousLinearMap

/-- Applying a continuous linear map to a formal multilinear series applies it to each multi-index
coefficient. -/
@[simp]
theorem mvCoeff_compFormalMultilinearSeries {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Fintype ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (L : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) (α : ι → ℕ) :
    (L.compFormalMultilinearSeries p).mvCoeff α = L (p.mvCoeff α) := by
  classical
  simp [FormalMultilinearSeries.mvCoeff_eq_sum _ rfl]

end ContinuousLinearMap

section BiUnionPiAntidiag

variable {ι : Type*} [Fintype ι]

/-- The multi-indices of total degree `< K` form a pairwise disjoint union of `univ.piAntidiag k`
for `k ∈ range K`, and exhaust all multi-indices as `K → ∞`. -/
private theorem pairwiseDisjoint_range_piAntidiag [DecidableEq ι] (K : ℕ) :
    (range K : Set ℕ).PairwiseDisjoint (univ.piAntidiag (ι := ι) ·) :=
  fun _ _ _ _ hkl ↦ disjoint_left.2 fun _ hk hl ↦
    hkl ((mem_piAntidiag.1 hk).1.symm.trans (mem_piAntidiag.1 hl).1)

private theorem tendsto_biUnion_range_piAntidiag [DecidableEq ι] :
    Tendsto (fun K ↦ (range K).biUnion (univ.piAntidiag (ι := ι) ·)) atTop atTop :=
  tendsto_atTop_atTop.2 fun s ↦ ⟨s.sup (fun α ↦ ∑ i, α i) + 1, fun K hK α hα ↦ by
    simp only [mem_biUnion, mem_range, mem_piAntidiag]
    exact ⟨∑ i, α i, (le_sup (f := fun α ↦ ∑ i, α i) hα).trans_lt
      ((lt_add_one _).trans_le hK), rfl, by simp⟩⟩

end BiUnionPiAntidiag

namespace TauCeti

section NormedField

variable {𝕜 : Type*} [NormedField 𝕜] {ι : Type*} [Fintype ι]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `‖c α‖ * r ^ (∑ i, α i)` is summable and every coordinate of `z` satisfies `‖z i‖ ≤ r`,
then `(∏ i, z i ^ α i) • c α` is absolutely summable. -/
theorem summable_norm_prod_pow_smul {c : (ι → ℕ) → F} {r : ℝ}
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * r ^ (∑ i, α i)) {z : ι → 𝕜}
    (hz : ∀ i, ‖z i‖ ≤ r) :
    Summable fun α : ι → ℕ ↦ ‖(∏ i, z i ^ α i) • c α‖ := by
  refine hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun α ↦ ?_
  rw [norm_smul, mul_comm, norm_prod, ← prod_pow_eq_pow_sum]
  gcongr with i
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hz i) _

/-- **Abel's lemma for multi-index series**: if `(∏ i, w i ^ α i) • c α` is summable at a point `w`
whose coordinates all satisfy `|r| < ‖w i‖`, then `‖c α‖ * r ^ (∑ i, α i)` is summable. -/
theorem summable_norm_mul_pow_of_summable_prod_pow_smul {c : (ι → ℕ) → F} {w : ι → 𝕜}
    (hw : Summable fun α : ι → ℕ ↦ (∏ i, w i ^ α i) • c α) {r : ℝ}
    (hr : ∀ i, |r| < ‖w i‖) :
    Summable fun α : ι → ℕ ↦ ‖c α‖ * r ^ (∑ i, α i) := by
  have hw_pos (i : ι) : 0 < ‖w i‖ := (abs_nonneg r).trans_lt (hr i)
  have hgeom : Summable fun α : ι → ℕ ↦ ‖∏ i, (|r| / ‖w i‖) ^ α i‖ :=
    summable_norm_prod_of_summable_norm fun i ↦ by
      simpa [abs_of_nonneg (div_nonneg (abs_nonneg r) (hw_pos i).le)] using
        summable_geometric_of_lt_one (div_nonneg (abs_nonneg r) (hw_pos i).le)
          ((div_lt_one (hw_pos i)).2 (hr i))
  have hbdd : ∀ᶠ α : ι → ℕ in cofinite, ‖(∏ i, w i ^ α i) • c α‖ < 1 :=
    (tendsto_zero_iff_norm_tendsto_zero.1 hw.tendsto_cofinite_zero) (gt_mem_nhds zero_lt_one)
  refine Summable.of_norm_bounded_eventually hgeom (hbdd.mono fun α hα ↦ ?_)
  have hle : ‖c α‖ * ∏ i, ‖w i‖ ^ α i ≤ 1 := by
    simpa [norm_smul, norm_prod, mul_comm] using hα.le
  calc ‖‖c α‖ * r ^ (∑ i, α i)‖
      = (‖c α‖ * ∏ i, ‖w i‖ ^ α i) * ∏ i, (|r| / ‖w i‖) ^ α i := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _), abs_pow,
          ← prod_pow_eq_pow_sum, mul_assoc]
        congr 1
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun i _ ↦ ?_
        rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ (hw_pos i).ne')]
    _ ≤ 1 * ∏ i, (|r| / ‖w i‖) ^ α i := by gcongr
    _ ≤ ‖∏ i, (|r| / ‖w i‖) ^ α i‖ := by
        rw [one_mul]
        exact le_abs_self _

/-- A continuous `k`-multilinear map on `ι → 𝕜` whose diagonal value at `z` is
`(∏ i, z i ^ α i) • v`, for `α` of total degree `k`. -/
private noncomputable def monomialMultilinearMap {k : ℕ} {α : ι → ℕ} (hk : ∑ i, α i = k)
    (v : F) : ContinuousMultilinearMap 𝕜 (fun _ : Fin k ↦ ι → 𝕜) F :=
  let e : Fin k ≃ Σ i : ι, Fin (α i) := (Fintype.equivFinOfCardEq (by simp [hk])).symm
  ((ContinuousMultilinearMap.mkPiAlgebra 𝕜 (Fin k) 𝕜).compContinuousLinearMap
    (fun j ↦ ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) (e j).1)).smulRight v

private theorem monomialMultilinearMap_apply_diag {k : ℕ} {α : ι → ℕ} (hk : ∑ i, α i = k)
    (v : F) (z : ι → 𝕜) :
    monomialMultilinearMap (𝕜 := 𝕜) hk v (fun _ ↦ z) = (∏ i, z i ^ α i) • v := by
  let e : Fin k ≃ Σ i : ι, Fin (α i) := (Fintype.equivFinOfCardEq (by simp [hk])).symm
  simp only [monomialMultilinearMap, ContinuousMultilinearMap.smulRight_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.proj_apply]
  congr 1
  rw [e.prod_comp (fun x : Σ i : ι, Fin (α i) ↦ z x.1), Fintype.prod_sigma]
  simp

/-- Formal multilinear series built from a family of multi-index coefficients `c` by summing a
monomial multilinear map over `univ.piAntidiag k` in each degree `k`. -/
private noncomputable def ofMvCoeff [DecidableEq ι] (c : (ι → ℕ) → F) :
    FormalMultilinearSeries 𝕜 (ι → 𝕜) F :=
  fun k ↦ ∑ α ∈ (univ.piAntidiag k).attach,
    monomialMultilinearMap (mem_piAntidiag.1 α.2).1 (c α.1)

private theorem ofMvCoeff_apply_diag [DecidableEq ι] (c : (ι → ℕ) → F) (k : ℕ) (z : ι → 𝕜) :
    ofMvCoeff (𝕜 := 𝕜) c k (fun _ ↦ z) = ∑ α ∈ univ.piAntidiag k, (∏ i, z i ^ α i) • c α := by
  simp only [ofMvCoeff, sum_apply, monomialMultilinearMap_apply_diag]
  exact sum_attach (univ.piAntidiag k) fun α ↦ (∏ i, z i ^ α i) • c α

end NormedField

end TauCeti

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

/-- **Normal convergence of multi-index coefficients**: if `(card ι) ^ k * ‖p k‖ * ρ ^ k` is
summable, then `‖p.mvCoeff α‖ * ρ ^ (∑ i, α i)` is summable over all multi-indices `α`. -/
theorem summable_norm_mvCoeff_mul_pow (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F) {ρ : ℝ}
    (h : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ρ ^ k) :
    Summable fun α : ι → ℕ ↦ ‖p.mvCoeff α‖ * ρ ^ (∑ i, α i) := by
  classical
  have habs : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * |ρ| ^ k := by
    refine h.norm.congr fun k ↦ ?_
    simp
  rw [← summable_norm_iff]
  refine summable_of_sum_le (c := ∑' k, (Fintype.card ι : ℝ) ^ k * ‖p k‖ * |ρ| ^ k)
    (fun _ ↦ norm_nonneg _) fun s ↦ ?_
  rw [← sum_fiberwise_of_maps_to (g := fun α ↦ ∑ i, α i) (t := s.image (fun α ↦ ∑ i, α i))
    (fun α hα ↦ mem_image_of_mem _ hα)]
  refine (sum_le_sum fun k _ ↦ ?_).trans (habs.sum_le_tsum _ fun _ _ ↦ by positivity)
  calc ∑ α ∈ s with ∑ i, α i = k, ‖‖p.mvCoeff α‖ * ρ ^ (∑ i, α i)‖
      ≤ ∑ α ∈ univ.piAntidiag k, ‖p.mvCoeff α‖ * |ρ| ^ k := by
        refine (sum_le_sum_of_subset_of_nonneg
          (fun α hα ↦ mem_piAntidiag.2 ⟨(mem_filter.1 hα).2, by simp⟩)
          fun _ _ _ ↦ norm_nonneg _).trans (le_of_eq <| sum_congr rfl fun α hα ↦ ?_)
        simp [(mem_piAntidiag.1 hα).1]
    _ ≤ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * |ρ| ^ k := by
        rw [← sum_mul]
        gcongr
        exact_mod_cast sum_norm_mvCoeff_le p k

/-- **Absolute convergence of the multi-index series**: if the operator-norm bounds
`(card ι) ^ k * ‖p k‖ * ‖z‖ ^ k` are summable, then the multi-index series
`∑ α, (∏ i, z i ^ α i) • p.mvCoeff α` converges absolutely. -/
theorem summable_norm_prod_pow_smul_mvCoeff (p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F)
    {z : ι → 𝕜} (h : Summable fun k ↦ (Fintype.card ι : ℝ) ^ k * ‖p k‖ * ‖z‖ ^ k) :
    Summable fun α : ι → ℕ ↦ ‖(∏ i, z i ^ α i) • p.mvCoeff α‖ :=
  TauCeti.summable_norm_prod_pow_smul (p.summable_norm_mvCoeff_mul_pow h) (norm_le_pi_norm z)

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
  refine hasSum_of_subseq_of_summable (p.summable_norm_prod_pow_smul_mvCoeff h)
    tendsto_biUnion_range_piAntidiag ?_
  simp_rw [sum_biUnion (pairwiseDisjoint_range_piAntidiag _), ← apply_eq_sum_mvCoeff]
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

private theorem norm_monomialMultilinearMap_le {k : ℕ} {α : ι → ℕ} (hk : ∑ i, α i = k) (v : F) :
    ‖monomialMultilinearMap (𝕜 := 𝕜) hk v‖ ≤ ‖v‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg v) fun m ↦ ?_
  simp only [monomialMultilinearMap, ContinuousMultilinearMap.smulRight_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.proj_apply,
    norm_smul, norm_prod]
  rw [mul_comm]
  gcongr with j
  exact norm_le_pi_norm (m j) _

private theorem mvCoeff_ofMvCoeff [DecidableEq ι] (c : (ι → ℕ) → F) (α : ι → ℕ) :
    (ofMvCoeff (𝕜 := 𝕜) c).mvCoeff α = c α := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_sum_prod_pow_smul_eq_zero (K := 𝕜) (V := F)
    (s := univ.piAntidiag (∑ i, α i)) (c := fun β ↦ (ofMvCoeff (𝕜 := 𝕜) c).mvCoeff β - c β)
    (fun z ↦ ?_) (mem_piAntidiag.2 ⟨rfl, by simp⟩)
  simp_rw [smul_sub, sum_sub_distrib, ← apply_eq_sum_mvCoeff, ofMvCoeff_apply_diag, sub_self]

private theorem norm_ofMvCoeff_le [DecidableEq ι] (c : (ι → ℕ) → F) (k : ℕ) :
    ‖ofMvCoeff (𝕜 := 𝕜) c k‖ ≤ ∑ α ∈ univ.piAntidiag k, ‖c α‖ :=
  (norm_sum_le _ _).trans <| by
    rw [← sum_attach (univ.piAntidiag k)]
    exact sum_le_sum fun α _ ↦ norm_monomialMultilinearMap_le _ _

/-- **A normally convergent multi-index series has a power series on the polydisc**: if
`‖c α‖ * r ^ (∑ i, α i)` is summable for `0 < r` and `(∏ i, y i ^ α i) • c α` sums to `f (x + y)`
for every `y` of norm `< r`, then `f` has a formal multilinear series on `Metric.eball x r` whose
multi-index coefficients are `c`. No completeness assumption on `F` is needed. -/
theorem exists_hasFPowerSeriesOnBall_of_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (c : (ι → ℕ) → F) {r : ℝ≥0} (hr : 0 < r)
    (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h : ∀ y : ι → 𝕜, ‖y‖ < r → HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y))) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall f p x r ∧ ∀ α, p.mvCoeff α = c α := by
  classical
  let p := ofMvCoeff (𝕜 := 𝕜) c
  have hdeg : Summable fun k ↦ ‖p k‖ * (r : ℝ) ^ k := by
    refine summable_of_sum_le (c := ∑' α, ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
      (fun _ ↦ by positivity) fun s ↦ ?_
    calc ∑ k ∈ s, ‖p k‖ * (r : ℝ) ^ k
        ≤ ∑ k ∈ s, ∑ α ∈ univ.piAntidiag k, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
          refine sum_le_sum fun k _ ↦ ?_
          calc ‖p k‖ * (r : ℝ) ^ k
              ≤ (∑ α ∈ univ.piAntidiag k, ‖c α‖) * (r : ℝ) ^ k := by
                gcongr; exact norm_ofMvCoeff_le c k
            _ = ∑ α ∈ univ.piAntidiag k, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
                rw [sum_mul]
                exact sum_congr rfl fun α hα ↦ by rw [(mem_piAntidiag.1 hα).1]
      _ = ∑ α ∈ s.biUnion (univ.piAntidiag ·), ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := by
          rw [sum_biUnion]
          exact fun _ _ _ _ hkl ↦ disjoint_left.2 fun _ hk hl ↦
            hkl ((mem_piAntidiag.1 hk).1.symm.trans (mem_piAntidiag.1 hl).1)
      _ ≤ ∑' α, ‖c α‖ * (r : ℝ) ^ (∑ i, α i) := hsum.sum_le_tsum _ fun _ _ ↦ by positivity
  refine ⟨p, ⟨p.le_radius_of_summable hdeg, ENNReal.coe_pos.2 hr, fun {y} hy ↦ ?_⟩,
    mvCoeff_ofMvCoeff c⟩
  have hy_lt : ‖y‖ < (r : ℝ) := by
    have hnn : ‖y‖₊ < r := by
      simpa only [Metric.mem_eball, edist_zero_right, eNorm_eq_nnNorm, ENNReal.coe_lt_coe] using hy
    exact_mod_cast hnn
  have hpy_sum : Summable fun k ↦ ‖p k (fun _ ↦ y)‖ := by
    refine hdeg.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun k ↦ ?_
    calc ‖p k (fun _ ↦ y)‖ ≤ ‖p k‖ * ∏ _ : Fin k, ‖y‖ := (p k).le_opNorm _
      _ = ‖p k‖ * ‖y‖ ^ k := by simp only [prod_const, card_univ, Fintype.card_fin]
      _ ≤ ‖p k‖ * (r : ℝ) ^ k := by
        have := hy_lt.le
        gcongr
  rw [hasSum_iff_tendsto_nat_of_summable_norm hpy_sum]
  dsimp only [p]
  simp_rw [ofMvCoeff_apply_diag, ← sum_biUnion (pairwiseDisjoint_range_piAntidiag _)]
  exact (h y hy_lt).comp tendsto_biUnion_range_piAntidiag

/-- **A normally convergent multi-index series has a power series** on the polydisc about `0`,
whose multi-index coefficients are the given ones. -/
theorem exists_hasFPowerSeriesOnBall_tsum [CompleteSpace F] (c : (ι → ℕ) → F) {r : ℝ≥0}
    (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i)) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesOnBall (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) p 0 r ∧
        ∀ α, p.mvCoeff α = c α := by
  refine exists_hasFPowerSeriesOnBall_of_hasSum c hr hsum fun y hy ↦ ?_
  rw [zero_add]
  exact (Summable.of_norm <|
    summable_norm_prod_pow_smul hsum fun i ↦ (norm_le_pi_norm y i).trans hy.le).hasSum

/-- **A convergent local multi-index series defines a formal power series germ**: if
`(∏ i, y i ^ α i) • c α` sums to `f (x + y)` for all `y` in a neighbourhood of `0`, then `f` has a
formal multilinear series at `x` whose multi-index coefficients are `c`. -/
theorem exists_hasFPowerSeriesAt_of_eventually_hasSum {f : (ι → 𝕜) → F} {x : ι → 𝕜}
    (c : (ι → ℕ) → F)
    (h : ∀ᶠ y in 𝓝 (0 : ι → 𝕜), HasSum (fun α : ι → ℕ ↦ (∏ i, y i ^ α i) • c α) (f (x + y))) :
    ∃ p : FormalMultilinearSeries 𝕜 (ι → 𝕜) F,
      HasFPowerSeriesAt f p x ∧ ∀ α, p.mvCoeff α = c α := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 h
  obtain ⟨w, hw_pos, hwε⟩ := NormedField.exists_norm_lt 𝕜 hε
  have hw_sum : Summable fun β : ι → ℕ ↦ (∏ i, w ^ β i) • c β :=
    (hball (y := fun _ ↦ w)
      (by simpa [dist_zero_right] using (pi_norm_const_le w).trans_lt hwε)).summable
  let r : ℝ≥0 := ⟨‖w‖ / 2, by positivity⟩
  have hr_pos : 0 < r := Subtype.mk_lt_mk.2 (half_pos hw_pos)
  have hr_coe : (r : ℝ) = ‖w‖ / 2 := rfl
  have hsum : Summable fun β : ι → ℕ ↦ ‖c β‖ * (r : ℝ) ^ (∑ i, β i) :=
    summable_norm_mul_pow_of_summable_prod_pow_smul hw_sum fun _ ↦ by
      rw [hr_coe, abs_of_pos (half_pos hw_pos)]
      exact half_lt_self hw_pos
  obtain ⟨p, hp, hcoeff⟩ := exists_hasFPowerSeriesOnBall_of_hasSum c hr_pos hsum
    fun y hy ↦ hball (by simpa [dist_zero_right] using hy.trans ((half_lt_self hw_pos).trans hwε))
  exact ⟨p, hp.hasFPowerSeriesAt, hcoeff⟩

/-- **Identity theorem for convergent multi-index series**: if `(∏ i, z i ^ α i) • c α` sums to `0`
for all `z` in a neighbourhood of `0`, then every coefficient `c α` is `0`. -/
theorem eq_zero_of_eventually_hasSum_prod_pow_smul_zero {c : (ι → ℕ) → F}
    (h0 : ∀ᶠ z in 𝓝 (0 : ι → 𝕜), HasSum (fun α : ι → ℕ ↦ (∏ i, z i ^ α i) • c α) 0)
    (α : ι → ℕ) : c α = 0 := by
  obtain ⟨p, hp, hcoeff⟩ := exists_hasFPowerSeriesAt_of_eventually_hasSum (f := 0) (x := 0) c h0
  rw [← hcoeff α]
  exact hp.mvCoeff_eq_zero_of_eventuallyEq_zero .rfl α

/-- **Identity theorem for normally convergent `tsum` multi-index series**: if
`‖c α‖ * r ^ (∑ i, α i)` is summable for `0 < r` in a complete space and
`∑' α, (∏ i, z i ^ α i) • c α` vanishes near `0`, then every coefficient `c α` is `0`. -/
theorem eq_zero_of_eventuallyEq_tsum_prod_pow_smul_zero [CompleteSpace F] {c : (ι → ℕ) → F}
    {r : ℝ≥0} (hr : 0 < r) (hsum : Summable fun α : ι → ℕ ↦ ‖c α‖ * (r : ℝ) ^ (∑ i, α i))
    (h0 : (fun z : ι → 𝕜 ↦ ∑' α : ι → ℕ, (∏ i, z i ^ α i) • c α) =ᶠ[𝓝 0] 0) (α : ι → ℕ) :
    c α = 0 := by
  obtain ⟨p, hp, hcoeff⟩ := exists_hasFPowerSeriesOnBall_tsum (𝕜 := 𝕜) c hr hsum
  rw [← hcoeff α]
  exact hp.hasFPowerSeriesAt.mvCoeff_eq_zero_of_eventuallyEq_zero h0 α

end TauCeti
