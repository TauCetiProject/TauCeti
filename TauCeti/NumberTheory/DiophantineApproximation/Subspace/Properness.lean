/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Span
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Volume
import TauCeti.NumberTheory.Height.FundamentalInequality
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Eventual properness of negative-weight approximation domains

For independent systems of forms, an approximation domain of negative weight eventually
spans a proper subspace. This supplies the dimension restriction needed when studying the
exceptional subspaces of the parametric Subspace Theorem.

The argument uses determinants directly. The determinant of a full family of domain points
is integral outside the selected finite places. Its product of local absolute values is
therefore at least one, whereas the domain bounds make that product at most a fixed constant
times `Q ^ approxWeight S₀ c`. Negative weight makes the latter tend to zero. No successive
minima or Minkowski theorem is needed for this dimension restriction.

The conclusion is eventual, not valid at every positive level: at level one the coordinate
forms give the full span, for every exponent system, as checked in the span module.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006),
  Definition 7.5.11 and Lemma 7.5.12.
-/

public section

open Filter Module NumberField
open scoped Topology

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The archimedean determinant estimate for a family of points in a domain. -/
private theorem apply_det_le_of_mem_approxDomain
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    {x : ι → ι → K} (hx : ∀ k, x k ∈ approxDomain S₀ L c Q)
    (v : InfinitePlace K) (hL : LinearIndependent K (L v.1)) :
    v (Matrix.of x).det ≤
      ((v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹ *
        (Fintype.card ι : ℝ) ^ Fintype.card ι) * ∏ i, Q ^ c v.1 i := by
  classical
  have hdet : 0 < v (LinearMap.det (LinearMap.pi (L v.1))) :=
    InfinitePlace.pos_iff.mpr hL.det_pi_ne_zero
  rw [mul_assoc]
  apply (le_inv_mul_iff₀ hdet).2
  rw [mul_comm, ← map_mul, ← Matrix.det_of_apply_eq_det_mul_det_pi]
  calc
    v (Matrix.of (fun k i ↦ L v.1 i (x k))).det ≤
        ∏ i, ∑ k, v (L v.1 i (x k)) := Matrix.abv_det_le_prod_sum_abv' _ v.1
    _ ≤ ∏ i, (Fintype.card ι : ℝ) * Q ^ c v.1 i := by
      gcongr with i
      simpa using Finset.sum_le_sum (s := Finset.univ)
        (fun k _ ↦ (mem_approxDomain.mp (hx k)).1 v i)
    _ = (Fintype.card ι : ℝ) ^ Fintype.card ι * ∏ i, Q ^ c v.1 i := by
      simp [Finset.prod_mul_distrib]

open scoped Classical in
/-- The finite-place determinant estimate for a family of points in a domain. -/
private theorem apply_det_le_of_mem_approxDomain_finite
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    {c : AbsoluteValue K ℝ → ι → ℝ} {Q : ℝ}
    {x : ι → ι → K} (hx : ∀ k, x k ∈ approxDomain S₀ L c Q)
    {v : FinitePlace K} (hv : v ∈ S₀) (hL : LinearIndependent K (L v.1)) :
    v (Matrix.of x).det ≤
      (v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹ * ∏ i, Q ^ c v.1 i := by
  classical
  apply (le_inv_mul_iff₀ (FinitePlace.pos_iff.mpr hL.det_pi_ne_zero)).2
  rw [mul_comm, ← map_mul, ← Matrix.det_of_apply_eq_det_mul_det_pi]
  exact Matrix.abv_det_le_prod_of_le' _ v.add_le
    fun k i ↦ (mem_approxDomain.mp (hx k)).2.1 v hv i

open scoped Classical in
/-- The local determinant estimates combine with the weight identity into one uniform bound. -/
private theorem exists_pos_forall_prod_det_le
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1)) (c : AbsoluteValue K ℝ → ι → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 0 < Q → ∀ x : ι → ι → K,
      (∀ k, x k ∈ approxDomain S₀ L c Q) →
      (∏ v : InfinitePlace K, v (Matrix.of x).det ^ v.mult) *
        ∏ v ∈ S₀, v (Matrix.of x).det ≤ C * Q ^ approxWeight S₀ c := by
  classical
  let A : InfinitePlace K → ℝ := fun v ↦
    (v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹ *
      (Fintype.card ι : ℝ) ^ Fintype.card ι
  let B : FinitePlace K → ℝ := fun v ↦
    (v (LinearMap.det (LinearMap.pi (L v.1))))⁻¹
  have hN : 0 < (Fintype.card ι : ℝ) ^ Fintype.card ι := by
    by_cases h : Fintype.card ι = 0
    · simp [h]
    · exact pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)) _
  have hA (v : InfinitePlace K) : 0 < A v :=
    mul_pos (inv_pos.mpr (InfinitePlace.pos_iff.mpr (hLinf v).det_pi_ne_zero)) hN
  have hB (v : FinitePlace K) (hv : v ∈ S₀) : 0 < B v :=
    inv_pos.mpr (FinitePlace.pos_iff.mpr (hLfin v hv).det_pi_ne_zero)
  refine ⟨(∏ v, A v ^ v.mult) * ∏ v ∈ S₀, B v,
    mul_pos (Finset.prod_pos fun v _ ↦ pow_pos (hA v) _)
      (Finset.prod_pos hB), fun Q hQ x hx ↦ ?_⟩
  have hinf : (∏ v : InfinitePlace K, v (Matrix.of x).det ^ v.mult) ≤
      ∏ v : InfinitePlace K, (A v * ∏ i, Q ^ c v.1 i) ^ v.mult := by
    gcongr with v
    exact apply_det_le_of_mem_approxDomain hx v (hLinf v)
  have hfin : (∏ v ∈ S₀, v (Matrix.of x).det) ≤
      ∏ v ∈ S₀, B v * ∏ i, Q ^ c v.1 i := by
    gcongr with v hv
    exact apply_det_le_of_mem_approxDomain_finite hx hv (hLfin v hv)
  calc
    _ ≤ (∏ v : InfinitePlace K, (A v * ∏ i, Q ^ c v.1 i) ^ v.mult) *
        ∏ v ∈ S₀, B v * ∏ i, Q ^ c v.1 i := by
      exact mul_le_mul hinf hfin
        (Finset.prod_nonneg fun v _ ↦ apply_nonneg v _) (by positivity)
    _ = _ := by
      rw [rpow_approxWeight S₀ c hQ]
      simp only [mul_pow, Finset.prod_mul_distrib]
      ring

/-- **Negative-weight approximation domains eventually span a proper subspace.** The system
of forms is independent at all infinite places and the selected finite places. -/
theorem eventually_approxSpan_ne_top
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    {c : AbsoluteValue K ℝ → ι → ℝ} (hc : approxWeight S₀ c < 0) :
    ∀ᶠ Q : ℝ in atTop, approxSpan S₀ L c Q ≠ ⊤ := by
  classical
  obtain ⟨C, -, hC⟩ := exists_pos_forall_prod_det_le hLinf hLfin c
  have hlim : Tendsto (fun Q : ℝ ↦ C * Q ^ approxWeight S₀ c) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := C)).mul
      (tendsto_rpow_neg_atTop (neg_pos.mpr hc))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds one_pos)]
    with Q hQ hsmall
  intro htop
  obtain ⟨y, hy, hymem⟩ :=
    (Submodule.le_finrank_span_iff_exists_linearIndependent
      (s := approxDomain S₀ L c Q) (n := Fintype.card ι)).mp (by
        rw [← approxSpan_eq_span, htop, finrank_top,
          Module.finrank_fintype_fun_eq_card])
  let x : ι → ι → K := y ∘ Fintype.equivFin ι
  have hx : LinearIndependent K x := hy.comp _ (Fintype.equivFin ι).injective
  have hxmem (k : ι) : x k ∈ approxDomain S₀ L c Q := hymem _
  have hdet : (Matrix.of x).det ≠ 0 := by
    rw [← Pi.basisFun_det_apply]
    exact ((Module.Basis.is_basis_iff_det (Pi.basisFun K ι)).mp
      ⟨hx, hx.span_eq_top_of_card_eq_finrank' (Module.finrank_fintype_fun_eq_card K).symm⟩).ne_zero
  have hout (v : FinitePlace K) (hv : v ∉ S₀) : v (Matrix.of x).det ≤ 1 := by
    exact (Matrix.abv_det_le_prod_of_le' (Matrix.of x) v.add_le
      (b := fun _ ↦ (1 : ℝ)) fun k j ↦
        (mem_approxDomain.mp (hxmem k)).2.2 v hv j).trans_eq Finset.prod_const_one
  have hone := NumberField.one_le_prod_apply_of_forall_le_one S₀ hdet hout
  exact (not_lt_of_ge (hone.trans (hC Q hQ x hxmem))) hsmall

/-- For negative weight, the rank of an approximation domain is eventually strictly less
than the ambient dimension. This includes domains of rank zero. -/
theorem eventually_finrank_approxSpan_lt
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.1))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.1))
    {c : AbsoluteValue K ℝ → ι → ℝ} (hc : approxWeight S₀ c < 0) :
    ∀ᶠ Q : ℝ in atTop, finrank K (approxSpan S₀ L c Q) < Fintype.card ι := by
  filter_upwards [eventually_approxSpan_ne_top hLinf hLfin hc] with Q hQ
  simpa using Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hQ)

/- In one variable a negative-weight coordinate domain eventually has rank zero.
No positive lower bound on the rank is part of the properness assertion. -/
example : ∀ᶠ Q : ℝ in atTop,
    approxSpan (K := ℚ) ∅ (fun _ (i : Unit) ↦ LinearMap.proj i) (fun _ _ ↦ -1) Q = ⊥ := by
  have hL : LinearIndependent ℚ
      (fun i : Unit ↦ LinearMap.proj (R := ℚ) (φ := fun _ : Unit ↦ ℚ) i) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    simpa using LinearMap.congr_fun ha (fun _ ↦ (1 : ℚ))
  have hc : approxWeight (K := ℚ) ∅ (fun _ (_ : Unit) ↦ (-1 : ℝ)) < 0 := by
    rw [approxWeight_def]
    norm_num [← Finset.sum_neg_distrib, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  have h := eventually_finrank_approxSpan_lt
    (L := fun _ (i : Unit) ↦ LinearMap.proj (R := ℚ) i) (S₀ := ∅)
    (fun _ ↦ hL) (by simp) hc
  filter_upwards [h] with Q hQ
  apply Submodule.finrank_eq_zero.mp
  simpa only [Fintype.card_unit, Nat.lt_one_iff] using hQ

end TauCeti.NumberField
