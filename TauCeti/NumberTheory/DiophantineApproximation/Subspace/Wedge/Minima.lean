/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Wedge.Domain

import Mathlib.Algebra.Order.Field.Pi
import TauCeti.LinearAlgebra.LinearIndependent.Unitriangular
import TauCeti.NumberTheory.DiophantineApproximation.Subspace.Rank

/-!
# The successive minima of a wedge domain

Let `μ` be the successive minima over `K` of an approximation domain
`approxDomain S₀ L c Q` of `K^ι`, `N = card ι`, with forms `L v` linearly independent at the
infinite places and at the places of `S₀` and a level `0 < Q ≠ 1`. Let `k + p = N` with `0 < p`
and `M = N.choose p`. Given bijections `σ v` between the indices of the minima and the forms, the
wedge domain `S(Q)` of `TauCeti.NumberField.wedgeExponent` is an approximation domain of the wedge
forms `wedgeForms (L v) p` in the Plücker space `Set.powersetCard ι p → K`, of dimension `M`.
Bombieri–Gubler's Lemma 7.5.31 says that, for suitable bijections `σ`, its successive minima `λ`
over `K` satisfy

```text
λ l ≤ 1  for l + 1 < M,      A · μ k / μ (k - 1) ≤ λ (M - 1),
```

with `A > 0` independent of the level `Q`, of the exponents `c` and of `p`: all minima but the
last are at most `1` and, for `0 < k`, a large jump between the consecutive minima `μ (k - 1)` and
`μ k` of the original domain makes the last minimum of the wedge domain large.

The upper bounds use the bijections `σ` produced, together with a basis `y` corrected from a
family realizing the minima `μ`, by
`TauCeti.NumberField.exists_plucker_mem_approxDomain_wedgeForms`: for them, the wedge domain
contains the Plücker vectors of the `p`-subfamilies of `y` that meet the first `k` indices. These
span `wedgeSpan k p y`, a hyperplane by Lemma 7.5.33 (`TauCeti.finrank_wedgeSpan_add_one`), so the
domain has rank at least `M - 1` and its first `M - 1` minima are at most `1`
(`TauCeti.NumberField.successiveMinimum_le_one_of_lt_finrank_approxSpan`). This uses nothing
about the forms or the exponents of the domain, and is stated for any approximation domain of
`⋀^p` containing those Plücker vectors
(`TauCeti.NumberField.successiveMinimum_le_one_of_forall_plucker_mem`).

The lower bound is Minkowski's second theorem twice. Its lower half for the wedge domain bounds
`∏ l, λ l ^ d` below by a constant times `Q ^ (-approxWeight)` of the wedge exponents, where
`d = [K : ℚ]`; its upper half for the original domain bounds that weight
(`TauCeti.NumberField.rpow_approxWeight_wedgeExponent_le`), leaving
`(μ k / μ (k - 1)) ^ d` up to a constant. These Minkowski estimates hold for every choice of the
bijections `σ v`, since the weight of the wedge exponents does not depend on them. If, for the
given `σ`, the first `M - 1` minima are at most `1`, the product is at most `λ (M - 1) ^ d`, and
taking `d`-th roots gives the bound
(`TauCeti.NumberField.exists_pos_forall_mul_div_le_successiveMinimum_wedge`). The constant there
depends on the degree `p`; as only the finitely many degrees `1 ≤ p ≤ card ι` occur, a common
positive lower bound of their constants serves for all of them.

## Main results

* `TauCeti.NumberField.successiveMinimum_le_one_of_forall_plucker_mem`: an approximation domain of
  `⋀^p` containing the Plücker vectors of the `p`-subfamilies of a basis meeting the first `k`
  indices has its first `M - 1` minima at most `1`.
* `TauCeti.NumberField.exists_pos_forall_mul_div_le_successiveMinimum_wedge`: for any
  bijections, if the first `M - 1` minima of the wedge domain of a fixed degree `p` are at most
  `1`, its last minimum is at least `A · μ k / μ (k - 1)`, with `A > 0` independent of `Q`, `c`
  and the bijections.
* `TauCeti.NumberField.exists_successiveMinimum_wedge`: Bombieri–Gubler's Lemma 7.5.31, the two
  bounds together for a wedge domain built from the successive minima and suitable bijections,
  with `A > 0` independent of `p`, `Q` and `c`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  7.5.30 and Lemma 7.5.31.
-/

public section

open Finset Module NumberField NumberField.mixedEmbedding Set.powersetCard
open scoped Pointwise

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **The first `M - 1` minima of a domain of `⋀^p` containing the wedges of a basis** (toward
Bombieri–Gubler, Lemma 7.5.31). Let `y` be a basis of `ι → K` and `k + p = card ι`. If an
approximation domain of `Set.powersetCard ι p → K` contains the Plücker vectors of the
`p`-subfamilies of `y` meeting the first `k` indices, then its `l`-th successive minimum over `K` is
at most `1` for every `l + 1 < (card ι).choose p`: those Plücker vectors span a hyperplane. -/
theorem successiveMinimum_le_one_of_forall_plucker_mem {p k : ℕ} {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → Set.powersetCard ι p → Dual K (Set.powersetCard ι p → K)}
    {c : AbsoluteValue K ℝ → Set.powersetCard ι p → ℝ} {Q : ℝ}
    (hkp : k + p = Fintype.card ι) {y : Fin (Fintype.card ι) → ι → K}
    (hy : LinearIndependent K y)
    (hyD : ∀ J : Set.powersetCard (Fin (Fintype.card ι)) p, (∃ j ∈ J, (j : ℕ) < k) →
      plucker (y ∘ ofFinEmbEquiv.symm J) ∈ approxDomain S₀ L c Q)
    {l : ℕ} (hl : l + 1 < (Fintype.card ι).choose p) :
    (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) l ≤ 1 := by
  -- The Plücker vectors span the hyperplane `wedgeSpan k p y` inside the span of the domain.
  have hW : wedgeSpan k p y ≤ approxSpan S₀ L c Q := by
    rw [approxSpan_eq_span]
    exact wedgeSpan_le_iff.2 fun J hJ ↦ Submodule.subset_span (hyD J hJ)
  have hrank := finrank_wedgeSpan_add_one hy hkp
  rw [Set.powersetCard.fintypeCard] at hrank
  exact successiveMinimum_le_one_of_lt_finrank_approxSpan
    (lt_of_lt_of_le (by omega) (Submodule.finrank_mono hW))

/-- **The product of the minima of the wedge domain is large after a large jump**: Minkowski's
second theorem for the wedge domain, with its weight bounded by Minkowski's second theorem for the
original domain. There is `A > 0` such that `A · (μ k / μ (k - 1)) ^ [K : ℚ]` is at most the
product of the `[K : ℚ]`-th powers of the successive minima of the wedge domain, for all exponents,
levels `0 < Q ≠ 1`, `k + p = card ι` and bijections. -/
private theorem exists_pos_forall_mul_div_pow_le_prod_successiveMinimum_wedge
    {S₀ : Finset (FinitePlace K)} {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {p : ℕ} (hp : 0 < p) {C : ℝ}
    (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) (k : ℕ)
      (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι), 0 < Q → Q ≠ 1 →
      k + p = Fintype.card ι →
      A * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1)) ^ finrank ℚ K ≤
        ∏ l : Fin (Fintype.card (Set.powersetCard ι p)),
          (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
              Q).successiveMinimum
            (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
              ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ^
            finrank ℚ K := by
  set N := Fintype.card ι
  set d := finrank ℚ K
  set M := Fintype.card (Set.powersetCard ι p)
  have hLinf' (v : InfinitePlace K) : LinearIndependent K (wedgeForms (L v.val) p) :=
    linearIndependent_wedgeForms (hLinf v) p
  have hLfin' (v : FinitePlace K) (hv : v ∈ S₀) : LinearIndependent K (wedgeForms (L v.val) p) :=
    linearIndependent_wedgeForms (hLfin v hv) p
  -- The constants of Minkowski's second theorem: the upper one `A₀` for the original domain and
  -- the lower one `A₁` for the wedge domain.
  set A₀ := approxUpperConst S₀ L
  have hA₀ : 0 < A₀ := approxUpperConst_pos hLinf hLfin
  set A₁ := approxLowerConst S₀ (fun v ↦ wedgeForms (L v) p)
  have hA₁ : 0 < A₁ := approxLowerConst_pos (L := fun v ↦ wedgeForms (L v) p) hLinf' hLfin'
  set D := A₀ ^ (N - 1).choose (p - 1) * C ^ (N.choose p * d)
  have hD : 0 < D := by positivity
  refine ⟨A₁ / D, div_pos hA₁ hD, fun c Q k σ hQ hQ₁ hkp ↦ ?_⟩
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)
  set e := wedgeExponent c p k σ μ C Q
  have hμ (l : ℕ) (hl : l < N) : 0 < μ l := successiveMinimum_approx_pos hLinf hLfin c hQ hl
  have hQw : 0 < Q ^ approxWeight S₀ e := Real.rpow_pos_of_pos hQ _
  -- `A₁ · Q ^ (-weight) ≤ ∏ l, λ l ^ d` for the wedge domain, and
  -- `Q ^ weight ≤ D · (μ (k - 1) / μ k) ^ d` for its weight.
  have hlow :=
    le_prod_successiveMinimum_approx (L := fun v ↦ wedgeForms (L v) p) hLinf' hLfin' e hQ
  have hup := rpow_approxWeight_wedgeExponent_le hLinf hLfin c hp hkp σ hC hQ hQ₁
  rw [Real.rpow_neg hQ.le, ← div_eq_mul_inv, div_le_iff₀ hQw] at hlow
  refine le_of_mul_le_mul_right (le_trans ?_ hlow) hQw
  calc A₁ / D * (μ k / μ (k - 1)) ^ d * Q ^ approxWeight S₀ e
      ≤ A₁ / D * (μ k / μ (k - 1)) ^ d * (D * (μ (k - 1) / μ k) ^ d) :=
        mul_le_mul_of_nonneg_left hup (mul_nonneg (div_pos hA₁ hD).le (pow_nonneg
          (div_nonneg (hμ k (by omega)).le (hμ (k - 1) (by omega)).le) _))
    _ = A₁ / D * D * (μ k / μ (k - 1) * (μ (k - 1) / μ k)) ^ d := by
        rw [mul_pow]
        ring
    _ = A₁ := by
        rw [div_mul_cancel₀ _ hD.ne', div_mul_div_cancel₀ (hμ (k - 1) (by omega)).ne',
          div_self (hμ k (by omega)).ne', one_pow, mul_one]

/-- **The last minimum of the wedge domain is large after a large jump** (Bombieri–Gubler,
Lemma 7.5.31), for a fixed degree `p`. Let the forms `L v` be linearly independent at the infinite
places and at `S₀`, let `0 < p` and `0 < C`. There is `A > 0`, depending on `p`, such that for
all exponents `c`, levels `0 < Q ≠ 1`, `k + p = card ι` and bijections `σ`, if `μ` are the
successive minima over `K` of `approxDomain S₀ L c Q` and the first `M - 1` successive minima
`λ` of the wedge domain `approxDomain S₀ (wedgeForms ∘ L) (wedgeExponent c p k σ μ C Q) Q` are at
most `1`, where `M = (card ι).choose p`, then `A · μ k / μ (k - 1) ≤ λ (M - 1)`. -/
theorem exists_pos_forall_mul_div_le_successiveMinimum_wedge {S₀ : Finset (FinitePlace K)}
    {L : AbsoluteValue K ℝ → ι → Dual K (ι → K)}
    (hLinf : ∀ v : InfinitePlace K, LinearIndependent K (L v.val))
    (hLfin : ∀ v ∈ S₀, LinearIndependent K (L v.val)) {p : ℕ} (hp : 0 < p) {C : ℝ}
    (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) (k : ℕ)
      (σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι), 0 < Q → Q ≠ 1 →
      k + p = Fintype.card ι →
      (∀ l, l + 1 < (Fintype.card ι).choose p →
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) →
      A * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k /
          (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1)) ≤
        (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
          ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
          (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
            ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
          ((Fintype.card ι).choose p - 1) := by
  obtain ⟨A, hA, hprod⟩ :=
    exists_pos_forall_mul_div_pow_le_prod_successiveMinimum_wedge hLinf hLfin hp hC
  have hd : finrank ℚ K ≠ 0 := finrank_pos.ne'
  refine ⟨A ^ ((finrank ℚ K)⁻¹ : ℝ), Real.rpow_pos_of_pos hA _,
    fun c Q k σ hQ hQ₁ hkp hle ↦ ?_⟩
  set ν := (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
    ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q).successiveMinimum
    (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
      ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
  set M := Fintype.card (Set.powersetCard ι p)
  have hM : M = (Fintype.card ι).choose p := Set.powersetCard.fintypeCard p
  have hM₀ : 0 < M := hM ▸ Nat.choose_pos (by omega)
  -- All minima of the wedge domain but the last are at most `1`, so the product of the `d`-th
  -- powers of the minima is at most the `d`-th power of the last one.
  have hprod_le : ∏ l : Fin M, ν l ^ finrank ℚ K ≤ ν (M - 1) ^ finrank ℚ K := by
    calc ∏ l : Fin M, ν l ^ finrank ℚ K
        ≤ ∏ l ∈ {(⟨M - 1, by omega⟩ : Fin M)}, ν l ^ finrank ℚ K :=
          prod_le_prod_of_subset_of_le_one₀ (subset_univ _)
            (fun _ _ ↦ pow_nonneg (Submodule.successiveMinimum_nonneg _ _ _) _)
            fun l _ hl ↦ pow_le_one₀ (Submodule.successiveMinimum_nonneg _ _ _) (hle _ (by
              have hne : (l : ℕ) ≠ M - 1 := fun h ↦ hl (mem_singleton.2 (Fin.ext h))
              omega))
      _ = ν (M - 1) ^ finrank ℚ K := prod_singleton _ _
  rw [← hM]
  refine (pow_le_pow_iff_left₀ (mul_nonneg (Real.rpow_pos_of_pos hA _).le
    (div_nonneg (Submodule.successiveMinimum_nonneg _ _ _)
      (Submodule.successiveMinimum_nonneg _ _ _))) (Submodule.successiveMinimum_nonneg _ _ _)
        hd).1 ?_
  rw [mul_pow, Real.rpow_inv_natCast_pow hA.le hd]
  exact (hprod c Q k σ hQ hQ₁ hkp).trans hprod_le

/-- **Bombieri–Gubler, Lemma 7.5.31: the successive minima of the wedge domain.** There is
`C > 0`, depending only on `K` and `ι`, with the following property. Let the forms `L v` be
linearly independent at the infinite places and at `S₀`. There is `A > 0` such that for all
`0 < p`, exponents `c`, levels `0 < Q ≠ 1` and `k + p = card ι`, with `μ` the successive minima over
`K` of `approxDomain S₀ L c Q`, some bijections `σ` make the successive minima `λ` of the wedge
domain `approxDomain S₀ (wedgeForms ∘ L) (wedgeExponent c p k σ μ C Q) Q` satisfy `λ l ≤ 1` for
`l + 1 < M` and `A · μ k / μ (k - 1) ≤ λ (M - 1)`, where `M = (card ι).choose p`. For fixed forms
`L` and places `S₀`, one `A > 0` works uniformly over the degrees `p`, the levels `Q` and the
exponents `c`. -/
theorem exists_successiveMinimum_wedge :
    ∃ C : ℝ, 0 < C ∧ ∀ (S₀ : Finset (FinitePlace K)) (L : AbsoluteValue K ℝ → ι → Dual K (ι → K)),
      (∀ v : InfinitePlace K, LinearIndependent K (L v.val)) →
      (∀ v ∈ S₀, LinearIndependent K (L v.val)) → ∃ A : ℝ, 0 < A ∧
      ∀ (p : ℕ) (c : AbsoluteValue K ℝ → ι → ℝ) (Q : ℝ) (k : ℕ), 0 < p → 0 < Q → Q ≠ 1 →
        k + p = Fintype.card ι → ∃ σ : AbsoluteValue K ℝ → Fin (Fintype.card ι) ≃ ι,
          (∀ l, l + 1 < (Fintype.card ι).choose p →
            (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
              ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q) l ≤ 1) ∧
          A * ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) k /
              (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) (k - 1)) ≤
            (approxModule S₀ (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
              ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q)
                Q).successiveMinimum
              (approxBody (fun v ↦ wedgeForms (L v) p) (wedgeExponent c p k σ
                ((approxModule S₀ L c Q).successiveMinimum (approxBody L c Q)) C Q) Q)
              ((Fintype.card ι).choose p - 1) := by
  obtain ⟨C, hC, hplucker⟩ := exists_plucker_mem_approxDomain_wedgeForms (K := K) (ι := ι)
  refine ⟨C, hC, fun S₀ L hLinf hLfin ↦ ?_⟩
  -- The constants for the finitely many degrees `1 ≤ p ≤ card ι` have a common positive lower
  -- bound `ε`.
  choose! A hA hlast using fun p (hp : 0 < p) ↦
    exists_pos_forall_mul_div_le_successiveMinimum_wedge hLinf hLfin hp hC
  obtain ⟨ε, hε, hεA⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : Icc 1 (Fintype.card ι) ↦ (0 : ℝ)) (y := fun p ↦ A p)
    fun p ↦ hA p (mem_Icc.1 p.property).1
  refine ⟨ε, hε, fun p c Q k hp hQ hQ₁ hkp ↦ ?_⟩
  have hεp : ε ≤ A p := by simpa using (hεA ⟨p, mem_Icc.2 ⟨hp, by omega⟩⟩).le
  set μ := (approxModule S₀ L c Q).successiveMinimum (approxBody L c Q) with hμ_def
  let _ := discreteTopology_mixedImage_approxModule hLfin c Q
  let _ := isZLattice_mixedImage_approxModule hLfin c hQ.ne'
  obtain ⟨B, hcoe, hB, -⟩ := exists_convexBody_approxSpan (S₀ := S₀) hLinf c hQ
  -- A family realizing the minima satisfies the hypotheses of the wedge-domain construction.
  obtain ⟨x, hx, hxB⟩ :=
    Submodule.exists_linearIndependent_mem_smul_successiveMinimum (Λ := approxModule S₀ L c Q) hB
  have hμ (l : ℕ) (hl : l < Fintype.card ι) : 0 < μ l :=
    successiveMinimum_approx_pos hLinf hLfin c hQ hl
  have hμm : MonotoneOn μ (Set.Iio (Fintype.card ι)) := by
    rw [hμ_def, ← hcoe]
    exact Submodule.monotoneOn_successiveMinimum hB
  have hxinf (v : InfinitePlace K) (i : ι) (l : Fin (Fintype.card ι)) :
      v (L v.val i (x l)) ≤ μ l * Q ^ c v.val i := by
    have h := (hxB l).2
    rw [hcoe, ← hμ_def] at h
    exact (mixedEmbedding_mem_smul_approxBody_iff (hμ l l.isLt)).1 h v i
  obtain ⟨y, σ, hspan, hmem⟩ := hplucker S₀ L c Q x μ hLinf hLfin hQ hQ₁ hx hμm hμ
    (fun l ↦ (hxB l).1) hxinf
  -- The corrected family is unitriangular over the independent family `x`.
  have hy : LinearIndependent K y := hx.of_sub_mem_span_image_Iio hspan
  set e := wedgeExponent c p k σ μ C Q
  have hle (l : ℕ) (hl : l + 1 < (Fintype.card ι).choose p) :
      (approxModule S₀ (fun v ↦ wedgeForms (L v) p) e Q).successiveMinimum
        (approxBody (fun v ↦ wedgeForms (L v) p) e Q) l ≤ 1 :=
    successiveMinimum_le_one_of_forall_plucker_mem (L := fun v ↦ wedgeForms (L v) p) (c := e) hkp
      hy (hmem k p) hl
  refine ⟨σ, hle, le_trans (mul_le_mul_of_nonneg_right hεp (div_nonneg
    (Submodule.successiveMinimum_nonneg _ _ _) (Submodule.successiveMinimum_nonneg _ _ _)))
    (hlast p hp c Q k σ hQ hQ₁ hkp hle)⟩

end TauCeti.NumberField
