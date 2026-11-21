/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Rank
public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.WedgeDomain

import TauCeti.LinearAlgebra.LinearIndependent.Unitriangular

/-!
# The successive minima of the wedge domain

Let `μ 0 ≤ ⋯ ≤ μ (N - 1)` be the successive minima over `K` of an approximation domain
`approxDomain S₀ L c Q` of `K^ι`, `N = card ι`, realized by linearly independent vectors `x l`.
For `k + p = N` with `0 < p`, Evertse's lemma corrects the `x l` triangularly to
vectors `y l` whose Plücker vectors `y J`, for the `p`-subsets `J` meeting `{0, …, k - 1}`, lie in
the wedge domain `S(Q)`, the approximation domain of the wedge forms `wedgeForms (L v) p` with
the exponents `wedgeExponent` (`TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeForms`).

This file proves Bombieri–Gubler's Lemma 7.5.31: if `ν` are the successive minima over `K` of
`S(Q)`, of which there are `M = N.choose p`, then all but the last are at most `1`, and the last is
at least `c₀ · μ k / μ (k - 1)`, with `c₀ > 0` independent of the exponents `c`, of the level `Q`
and of `k` (`TauCeti.NumberField.exists_successiveMinimum_wedge`). The first statement holds
because the `M - 1` Plücker vectors above lie in `S(Q)` and span a hyperplane, Lemma 7.5.33
(`TauCeti.finrank_wedgeSpan_add_one`). For the second, Minkowski's second theorem over `K` bounds
`∏ l, ν l ^ d`, with `d = [K : ℚ]`, below by a constant times `Q ^ (-w)`, where `w` is the weight of
`S(Q)`; since every minimum but the last is at most `1`, so is `ν (M - 1) ^ d`. The weight of `S(Q)`
is at most a constant times `(μ (k - 1) / μ k) ^ d` by Minkowski's second theorem for the original
domain (`TauCeti.NumberField.rpow_approxWeight_wedgeExponent_le`).

A large jump between consecutive minima exists whenever the domain has rank `R` with
`1 ≤ R < N` (Bombieri–Gubler (7.41)): some `k ∈ [R, N)` has
`(μ (k - 1) / μ k) ^ (N - R) ≤ μ (N - 1)⁻¹` (`TauCeti.NumberField.exists_div_pow_le_inv`), since
the ratios `μ (k - 1) / μ k` over `k ∈ [R, N)` multiply to `μ (R - 1) / μ (N - 1)` and
`μ (R - 1) ≤ 1`. For that `k`, the last minimum of `S(Q)` satisfies
`ν (M - 1) ^ (N - R) ≥ c₀ · μ (N - 1)` (`TauCeti.NumberField.exists_successiveMinimum_wedge_pow`).
When the weight of the original domain is negative, Minkowski's second theorem makes `μ (N - 1)`
grow with `Q`, so this bound pushes the last minimum of `S(Q)` above `1` for large `Q`; then `S(Q)`
has rank exactly `M - 1`.

## Main results

* `TauCeti.NumberField.exists_successiveMinimum_wedge`: Lemma 7.5.31, the successive minima of
  the wedge domain.
* `TauCeti.NumberField.exists_successiveMinimum_wedge_pow`: Lemma 7.5.31 combined with (7.41).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.30, (7.41) and Lemma 7.5.31.
* J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. 101
  (1996), 225–311.
-/

public section

open Finset Module NumberField NumberField.mixedEmbedding Set.powersetCard
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]

/-! ### The successive minima of the wedge domain -/

/-- **The last minimum of a domain controls its weight.** For forms independent at the infinite
places and at `S₀` there is `A > 0` such that for all exponents `c` and levels `0 < Q`, if every
successive minimum over `K` of `approxDomain S₀ L c Q` but the last is at most `1`, then the
`[K : ℚ]`-th power of the last is at least `A · Q ^ (-approxWeight S₀ c)`. -/
private theorem exists_pos_mul_rpow_le_successiveMinimum_pow {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) (hι : 0 < Fintype.card ι) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 0 < Q →
      (∀ l < Fintype.card ι - 1,
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ≤ 1) →
      A * Q ^ (-approxWeight S₀ c) ≤
        (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
          (Fintype.card ι - 1) ^ finrank ℚ K := by
  classical
  have := approxConst_pos hLinf hLfin
  have := zero_lt_one.trans_le (one_le_integralBasisHouse (K := K))
  refine ⟨_, by positivity, fun c Q hQ h₁ ↦
    (le_prod_successiveMinimum_approx hLinf hLfin c hQ).trans ?_⟩
  -- Split off the last factor; the others are at most `1`.
  let l₀ : Fin (Fintype.card ι) := ⟨Fintype.card ι - 1, by omega⟩
  rw [← mul_prod_erase _ _ (mem_univ l₀)]
  refine mul_le_of_le_one_right (pow_nonneg (Submodule.successiveMinimum_nonneg _ _ _) _)
    (prod_le_one₀ (fun _ _ ↦ pow_nonneg (Submodule.successiveMinimum_nonneg _ _ _) _)
      fun l hl ↦ pow_le_one₀ (Submodule.successiveMinimum_nonneg _ _ _) (h₁ l ?_))
  have hl' : l ≠ l₀ := ne_of_mem_erase hl
  have : (l : ℕ) ≠ Fintype.card ι - 1 := fun h ↦ hl' (Fin.ext h)
  omega

/-- For fixed forms, exterior degree `0 < p`, jump index `k` with `k + p = card ι` and constant
`C > 0`, there is `A > 0` such that `Q ^ approxWeight` of the wedge exponents is at most
`A · (μ (k - 1) / μ k) ^ [K : ℚ]` for all exponents `c`, levels `0 < Q ≠ 1` and bijections `σ`,
where `μ` are the successive minima over `K` of `approxDomain S₀ L c Q`. -/
private theorem exists_pos_rpow_approxWeight_wedgeExponent_le {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {k p : ℕ} (hp : 0 < p)
    (hkp : k + p = Fintype.card ι) {C : ℝ} (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 0 < Q → Q ≠ 1 →
      ∀ σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
      Q ^ approxWeight S₀ (wedgeExponent c p k σ
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) ≤
        A * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1) /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k) ^ finrank ℚ K := by
  have := approxConst_pos hLinf hLfin
  have : 0 < ∏ v ∈ S₀, (v.maximalIdeal.asIdeal.absNorm : ℝ) ^ Fintype.card ι :=
    prod_pos fun v _ ↦ pow_pos (by
      exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.maximalIdeal).pos) _
  exact ⟨_, by positivity, fun c Q hQ hQ₁ σ ↦
    rpow_approxWeight_wedgeExponent_le hLinf hLfin c hp hkp σ hC hQ hQ₁⟩

variable [LinearOrder ι]

/-- For fixed forms, exterior degree `p` and constant `C > 0`, the last successive minimum of the
wedge domain with jump index `k = card ι - p` is at least `c₀ · μ k / μ (k - 1)` whenever the
others are at most `1`, with `c₀ > 0` independent of the exponents, the level and the bijections.
-/
private theorem exists_pos_mul_div_le_successiveMinimum_wedge {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {C : ℝ} (hC : 0 < C) (p : ℕ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k : ℕ, 0 < p → k + p = Fintype.card ι →
      ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 0 < Q → Q ≠ 1 →
      ∀ σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
      (∀ l < (Fintype.card ι).choose p - 1,
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) →
      c₀ * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1)) ≤
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
          ((Fintype.card ι).choose p - 1) := by
  set N := Fintype.card ι
  set d := finrank ℚ K
  by_cases hpN : 0 < p ∧ p ≤ N
  swap
  · exact ⟨1, one_pos, fun k hp hkp ↦ absurd ⟨hp, by omega⟩ hpN⟩
  have hd : d ≠ 0 := finrank_pos.ne'
  have hMcard : Fintype.card (Set.powersetCard ι p) = N.choose p := fintypeCard p
  -- Minkowski's lower bound for the wedge domain, and the upper bound on its weight.
  obtain ⟨A₁, hA₁, h₁⟩ := exists_pos_mul_rpow_le_successiveMinimum_pow (S₀ := S₀)
    (L := fun v ↦ wedgeForms (L v) p) (fun v ↦ linearIndependent_wedgeForms (hLinf v) p)
    (fun v hv ↦ linearIndependent_wedgeForms (hLfin v hv) p)
    (by rw [hMcard]; exact Nat.choose_pos hpN.2)
  obtain ⟨A₂, hA₂, h₂⟩ :=
    exists_pos_rpow_approxWeight_wedgeExponent_le (k := N - p) hLinf hLfin hpN.1 (by omega) hC
  refine ⟨(A₁ / A₂) ^ (d⁻¹ : ℝ), Real.rpow_pos_of_pos (div_pos hA₁ hA₂) _,
    fun k _ hkp c Q hQ hQ₁ σ hν ↦ ?_⟩
  obtain rfl : k = N - p := by omega
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  set L' : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K) :=
    fun v ↦ wedgeForms (L v) p
  set c' := wedgeExponent c p (N - p) σ μ C Q
  set ν := (approxModule S₀ L' c' Q).successiveMinimum (approxBody L' c' Q)
  have hμ₀ : 0 < μ (N - p) := successiveMinimum_approx_pos hLinf hLfin c hQ (by omega)
  have hμ₁ : 0 < μ (N - p - 1) := successiveMinimum_approx_pos hLinf hLfin c hQ (by omega)
  have hr : 0 < μ (N - p) / μ (N - p - 1) := div_pos hμ₀ hμ₁
  have hQw : 0 < Q ^ approxWeight S₀ c' := Real.rpow_pos_of_pos hQ _
  have h₁' : A₁ * Q ^ (-approxWeight S₀ c') ≤ ν (N.choose p - 1) ^ d := by
    have h := h₁ c' hQ fun l hl ↦ hν l (by rwa [hMcard] at hl)
    rwa [hMcard] at h
  have h₂' : Q ^ approxWeight S₀ c' ≤ A₂ * (μ (N - p - 1) / μ (N - p)) ^ d := h₂ c hQ hQ₁ σ
  refine (pow_le_pow_iff_left₀ (mul_pos (Real.rpow_pos_of_pos (div_pos hA₁ hA₂) _) hr).le
    (Submodule.successiveMinimum_nonneg _ _ _) hd).1 ?_
  calc ((A₁ / A₂) ^ (d⁻¹ : ℝ) * (μ (N - p) / μ (N - p - 1))) ^ d
      = A₁ / (A₂ * (μ (N - p - 1) / μ (N - p)) ^ d) := by
        rw [mul_pow, Real.rpow_inv_natCast_pow (div_pos hA₁ hA₂).le hd, div_pow, div_pow]
        field_simp
    _ ≤ A₁ / Q ^ approxWeight S₀ c' := div_le_div_of_nonneg_left hA₁.le hQw h₂'
    _ = A₁ * Q ^ (-approxWeight S₀ c') := by rw [Real.rpow_neg hQ.le, div_eq_mul_inv]
    _ ≤ ν (N.choose p - 1) ^ d := h₁'

/-- The constant of `exists_pos_mul_div_le_successiveMinimum_wedge` can be chosen uniformly in the
exterior degree `p`. -/
private theorem exists_pos_forall_mul_div_le_successiveMinimum_wedge
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {C : ℝ} (hC : 0 < C) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k p : ℕ, 0 < p → k + p = Fintype.card ι →
      ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}, 0 < Q → Q ≠ 1 →
      ∀ σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
      (∀ l < (Fintype.card ι).choose p - 1,
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) →
      c₀ * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1)) ≤
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
          ((Fintype.card ι).choose p - 1) := by
  set N := Fintype.card ι
  have hc := exists_pos_mul_div_le_successiveMinimum_wedge hLinf hLfin hC
  choose c₀ hc₀ hc₀' using hc
  -- One constant for all exterior degrees `p ≤ N`; the bound is monotone in the constant.
  refine ⟨(range (N + 1)).inf' nonempty_range_add_one c₀, (lt_inf'_iff _).2 fun p _ ↦ hc₀ p,
    fun k p hp hkp c Q hQ hQ₁ σ hν ↦ le_trans ?_ (hc₀' p k hp hkp c hQ hQ₁ σ hν)⟩
  exact mul_le_mul_of_nonneg_right (inf'_le _ (mem_range.2 (by omega)))
    (div_pos (successiveMinimum_approx_pos hLinf hLfin c hQ (by omega))
      (successiveMinimum_approx_pos hLinf hLfin c hQ (by omega))).le

/-- **The successive minima of the wedge domain** (Bombieri–Gubler, Lemma 7.5.31). There is
`C > 0`, depending only on `K` and `ι`, with the following property. For forms `L` linearly
independent at the infinite places and at `S₀` there is `c₀ > 0` such that for all exponents `c`,
levels `0 < Q ≠ 1`, `k` and `0 < p` with `k + p = card ι`, and linearly independent vectors `x l` of
`approxModule S₀ L c Q` realizing its successive minima `μ` over `K`, there are triangular
corrections `y` of `x` and bijections `σ v` such that
* the Plücker vectors of the `p`-subfamilies of `y` meeting `{0, …, k - 1}` lie in the wedge
  domain `S(Q)`, the approximation domain of the wedge forms `wedgeForms (L v) p` with the
  exponents `wedgeExponent c p k σ μ C Q`;
* every successive minimum over `K` of `S(Q)` but the last, of index `(card ι).choose p - 1`, is
  at most `1`;
* the last is at least `c₀ · μ k / μ (k - 1)`. -/
theorem exists_successiveMinimum_wedge :
    ∃ C : ℝ, 0 < C ∧ ∀ {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)},
      (∀ v : InfinitePlace K, LinearIndependent K (L v.val)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.val)) →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ} {k p : ℕ}
        {x : Fin (Fintype.card ι) → ι → K}, 0 < Q → Q ≠ 1 → 0 < p →
        k + p = Fintype.card ι → LinearIndependent K x →
        (∀ l, x l ∈ approxModule S₀ L c Q) →
        (∀ l : Fin (Fintype.card ι), (fun j ↦ mixedEmbedding K (x l j)) ∈
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l • approxBody L c Q) →
        ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι),
          (∀ j, y j - x j ∈ Submodule.span K (x '' Set.Iio j)) ∧
          (∀ J : Set.powersetCard (Fin (Fintype.card ι)) p, (∃ j ∈ J, (j : ℕ) < k) →
            plucker (y ∘ ofFinEmbEquiv.symm J) ∈ approxDomain S₀ (fun v ↦ wedgeForms (L v) p)
              (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) ∧
          (∀ l < (Fintype.card ι).choose p - 1,
            (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) ∧
          c₀ * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k /
              (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1)) ≤
            (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
              ((Fintype.card ι).choose p - 1) := by
  obtain ⟨C, hC, hE⟩ := exists_plucker_mem_approxDomain_wedgeForms (K := K) (ι := ι)
  refine ⟨C, hC, fun {S₀ L} hLinf hLfin ↦ ?_⟩
  obtain ⟨c₀, hc₀, hlast⟩ := exists_pos_forall_mul_div_le_successiveMinimum_wedge hLinf hLfin hC
  set N := Fintype.card ι
  refine ⟨c₀, hc₀, fun c Q k p x hQ hQ₁ hp hkp hx hxΛ hxB ↦ ?_⟩
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  have hμ (l : ℕ) (hl : l < N) : 0 < μ l := successiveMinimum_approx_pos hLinf hLfin c hQ hl
  have hμm : MonotoneOn μ (Set.Iio N) := by
    let _ := discreteTopology_mixedImage_approxModule hLfin c Q
    let _ := isZLattice_mixedImage_approxModule hLfin c hQ.ne'
    obtain ⟨B, hcoe, hB, -⟩ := exists_convexBody_approxSpan (S₀ := S₀) hLinf c hQ
    simp only [μ, ← hcoe]
    exact Submodule.monotoneOn_successiveMinimum hB
  obtain ⟨y, σ, hspan, hmem⟩ := hE S₀ L c Q x μ hLinf hLfin hQ hQ₁ hx hμm hμ hxΛ
    fun v i l ↦ (mixedEmbedding_mem_smul_approxBody_iff (hμ l l.isLt)).1 (hxB l) v i
  set L' : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K) :=
    fun v ↦ wedgeForms (L v) p
  set c' := wedgeExponent c p k σ μ C Q
  have hL'inf (v : InfinitePlace K) : LinearIndependent K (L' v.val) :=
    linearIndependent_wedgeForms (hLinf v) p
  have hL'fin (v : FinitePlace K) (hv : v ∈ S₀) : LinearIndependent K (L' v.val) :=
    linearIndependent_wedgeForms (hLfin v hv) p
  have hMc : Fintype.card (Set.powersetCard ι p) = N.choose p := fintypeCard p
  -- The Plücker vectors meeting the first `k` indices span a hyperplane inside the span of `S(Q)`.
  have hrank : N.choose p - 1 ≤ finrank K (approxSpan S₀ L' c' Q) := by
    have hy := hx.of_sub_mem_span hspan
    have h₁ := finrank_wedgeSpan_add_one hy hkp
    have h₂ := Submodule.finrank_mono (wedgeSpan_le_iff.2 fun J hJ ↦
      mem_approxSpan_of_mem (hmem k p J hJ) : wedgeSpan k p y ≤ approxSpan S₀ L' c' Q)
    rw [hMc] at h₁
    omega
  have hν (l : ℕ) (hl : l < N.choose p - 1) :
      (approxModule S₀ L' c' Q).successiveMinimum (approxBody L' c' Q) l ≤ 1 :=
    (successiveMinimum_approx_le_one_iff hL'inf hL'fin c' hQ
      (by rw [hMc]; omega)).2 (by omega)
  exact ⟨y, σ, hspan, hmem k p, hν, hlast k p hp hkp c hQ hQ₁ σ hν⟩

/-- **The successive minima of the wedge domain after a large jump** (Bombieri–Gubler, (7.41) and
Lemma 7.5.31). There is `C > 0`, depending only on `K` and `ι`, with the following property. For
forms `L` linearly independent at the infinite places and at `S₀` there is `c₀ > 0` such that for
all exponents `c`, levels `0 < Q ≠ 1` and linearly independent vectors `x l` of
`approxModule S₀ L c Q` realizing its successive minima `μ` over `K`, if the rank
`R = finrank K (approxSpan S₀ L c Q)` satisfies `1 ≤ R < card ι`, then for some `k` with
`R ≤ k < card ι`, and `p = card ι - k`, there are triangular corrections `y` of `x` and bijections
`σ v` such that the Plücker vectors of the `p`-subfamilies of `y` meeting `{0, …, k - 1}` lie in
the wedge domain `S(Q)`, every successive minimum over `K` of `S(Q)` but the last is at most `1`,
and the last, raised to the power `card ι - R`, is at least `c₀ · μ (card ι - 1)`. -/
theorem exists_successiveMinimum_wedge_pow :
    ∃ C : ℝ, 0 < C ∧ ∀ {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)},
      (∀ v : InfinitePlace K, LinearIndependent K (L v.val)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.val)) →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) {Q : ℝ}
        {x : Fin (Fintype.card ι) → ι → K}, 0 < Q → Q ≠ 1 →
        0 < finrank K (approxSpan S₀ L c Q) →
        finrank K (approxSpan S₀ L c Q) < Fintype.card ι → LinearIndependent K x →
        (∀ l, x l ∈ approxModule S₀ L c Q) →
        (∀ l : Fin (Fintype.card ι), (fun j ↦ mixedEmbedding K (x l j)) ∈
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l • approxBody L c Q) →
        ∃ k, finrank K (approxSpan S₀ L c Q) ≤ k ∧ k < Fintype.card ι ∧
        ∃ (y : Fin (Fintype.card ι) → ι → K) (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι),
          (∀ j, y j - x j ∈ Submodule.span K (x '' Set.Iio j)) ∧
          (∀ J : Set.powersetCard (Fin (Fintype.card ι)) (Fintype.card ι - k),
            (∃ j ∈ J, (j : ℕ) < k) →
            plucker (y ∘ ofFinEmbEquiv.symm J) ∈
              approxDomain S₀ (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) ∧
          (∀ l < (Fintype.card ι).choose (Fintype.card ι - k) - 1,
            (approxModule S₀ (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) ∧
          c₀ * (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
              (Fintype.card ι - 1) ≤
            (approxModule S₀ (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) (Fintype.card ι - k))
                (wedgeExponent c (Fintype.card ι - k) k σ
                  ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
              ((Fintype.card ι).choose (Fintype.card ι - k) - 1) ^
              (Fintype.card ι - finrank K (approxSpan S₀ L c Q)) := by
  obtain ⟨C, hC, hW⟩ := exists_successiveMinimum_wedge (K := K) (ι := ι)
  refine ⟨C, hC, fun {S₀ L} hLinf hLfin ↦ ?_⟩
  obtain ⟨c₀, hc₀, h⟩ := hW hLinf hLfin
  set N := Fintype.card ι
  -- Shrinking `c₀` to at most `1` makes `c₀ ^ N` a constant for every exponent `N - R ≤ N`.
  refine ⟨min c₀ 1 ^ N, pow_pos (lt_min hc₀ one_pos) _,
    fun c Q x hQ hQ₁ hR hRN hx hxΛ hxB ↦ ?_⟩
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  set R := finrank K (approxSpan S₀ L c Q)
  have hbot : approxSpan S₀ L c Q ≠ ⊥ := fun h ↦ hR.ne' (Submodule.finrank_eq_zero.2 h)
  have htop : approxSpan S₀ L c Q ≠ ⊤ := fun h ↦ hRN.ne <| by
    rw [← Module.finrank_fintype_fun_eq_card K, ← finrank_top K (ι → K), ← h]
  obtain ⟨k, hk, hjump⟩ := exists_div_pow_le_inv hLinf hLfin c hQ hbot htop
  obtain ⟨hRk, hkN⟩ := Finset.mem_Ico.1 hk
  obtain ⟨y, σ, hspan, hmem, hν, hlast⟩ :=
    h c (k := k) (p := N - k) hQ hQ₁ (by omega) (by omega) hx hxΛ hxB
  refine ⟨k, hRk, hkN, y, σ, hspan, hmem, hν, ?_⟩
  have hμ (l : ℕ) (hl : l < N) : 0 < μ l := successiveMinimum_approx_pos hLinf hLfin c hQ hl
  have hr : 0 < μ k / μ (k - 1) := div_pos (hμ k hkN) (hμ (k - 1) (by omega))
  have hm : 0 < min c₀ 1 := lt_min hc₀ one_pos
  -- `μ (N - 1) ≤ (μ k / μ (k - 1)) ^ (N - R)` is the jump, inverted.
  have hjump' : μ (N - 1) ≤ (μ k / μ (k - 1)) ^ (N - R) := by
    have h := (le_inv_comm₀ (pow_pos (div_pos (hμ (k - 1) (by omega)) (hμ k hkN)) _)
      (hμ _ (by omega))).1 hjump
    rwa [← inv_pow, inv_div] at h
  calc min c₀ 1 ^ N * μ (N - 1)
      ≤ min c₀ 1 ^ (N - R) * (μ k / μ (k - 1)) ^ (N - R) :=
        mul_le_mul (pow_le_pow_of_le_one hm.le (min_le_right _ _) (by omega)) hjump'
          (hμ _ (by omega)).le (pow_nonneg hm.le _)
    _ = (min c₀ 1 * (μ k / μ (k - 1))) ^ (N - R) := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity)
        ((mul_le_mul_of_nonneg_right (min_le_left _ _) hr.le).trans hlast) _

end TauCeti.NumberField
