/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import TauCeti.Analysis.Normed.Ring.InfiniteProd
public import TauCeti.Topology.Algebra.InfiniteSum.UniformOn

import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Uniform-tail convergence criteria for infinite products of functions

Mathlib's `Summable.hasProdUniformlyOn_one_add` proves uniform convergence of `∏' i, (1 + f i x)`
on a compact set `K` under a Weierstrass $M$-test bound `∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i`
with `Summable u`, assuming `ContinuousOn (f i) K` and `[NormOneClass R]`. That criterion does not
cover families whose pointwise absolute series `∑' i, ‖u i x‖` have uniformly vanishing tails on a
set `X` while `∑' i, sup_{x ∈ X} ‖u i x‖` diverges (for instance, `u n x = (n + 1)⁻¹` at `x = n`
and `0` elsewhere on `X = ℕ`).

This file establishes the general **uniform-tail product criterion** (Rainer, Theorem 14.3):

* `SummableUniformlyOn.uniformCauchySeqOn_prod_one_add`,
  `SummableUniformlyOn.hasProdUniformlyOn_one_add`, and
  `SummableUniformlyOn.multipliableUniformlyOn_one_add`: on an arbitrary set `X : Set α` (with no
  topology on `α`) and in any complete seminormed commutative ring `R` (with no condition on
  `‖1‖`), if each `u i` is bounded on `X` and `fun i x ↦ ‖u i x‖` is uniformly summable on `X`,
  then `∏' i, (1 + u i x)` converges uniformly on `X` along the unordered finite-subset filter.
* `TauCeti.hasProdUniformlyOn_nat_one_add_of_tail` and
  `TauCeti.tendstoUniformlyOn_prod_range_one_add_of_tail`: the sequential `ℕ`-indexed criteria
  under pointwise absolute summability and uniformly vanishing tails `∑' k, ‖u (N + k) x‖ < ε`.
* `SummableUniformlyOn.exists_finset_tprod_one_add_eq_prod_mul` and
  `SummableUniformlyOn.exists_finset_tprod_one_add_eq_prod_mul_ne_zero`: splitting off a finite
  head `I : Finset ι` leaves a uniformly convergent tail product close to `1` (hence nowhere zero
  when `‖1‖ = 1`) on `X`.
* `HasProdUniformlyOn.eq_zero_iff_exists_one_add_eq_zero`: in a complete normed commutative ring
  with multiplicative norm, the limit vanishes at `x ∈ X` if and only if some factor `1 + u i x`
  vanishes.
* `TauCeti.hasProdLocallyUniformlyOn_one_add_of_forall_isCompact`,
  `TauCeti.hasProdLocallyUniformlyOn_nat_one_add_of_tail`, and
  `TauCeti.tendstoLocallyUniformlyOn_prod_range_one_add_of_tail`: locally uniform convergence on
  open subsets of locally compact spaces, deriving factor boundedness on each compact set from
  continuity.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 14.3, pp. 35–36.
-/

public section

open Filter Function Set
open scoped Topology

namespace SummableUniformlyOn

section SeminormedCommRing

variable {ι α R : Type*} [SeminormedCommRing R] {u : ι → α → R} {X : Set α}

/-- If `fun i x ↦ ‖u i x‖` is uniformly summable on `X` and each `u i` is bounded on `X`, then all
finite partial products `∏ i ∈ s, (1 + u i x)` are uniformly bounded in norm on `X` by a single
positive constant `B`. -/
theorem exists_norm_prod_one_add_le
    (hsum : SummableUniformlyOn (fun i x ↦ ‖u i x‖) X)
    (hbd : ∀ i, Bornology.IsBounded (u i '' X)) :
    ∃ B > 0, ∀ (s : Finset ι), ∀ x ∈ X, ‖∏ i ∈ s, (1 + u i x)‖ ≤ B := by
  have hbdd : ∀ i, BddAbove ((fun x ↦ ‖u i x‖) '' X) := fun i ↦ by
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 (hbd i)
    exact ⟨M, by rintro _ ⟨x, hx, rfl⟩; exact hM (u i x) ⟨x, hx, rfl⟩⟩
  obtain ⟨C, -, -, hC⟩ := hsum.exists_tsum_le_of_nonneg (fun _ _ _ ↦ norm_nonneg _) hbdd
  refine ⟨Real.exp C + ‖(1 : R)‖,
    add_pos_of_pos_of_nonneg (Real.exp_pos C) (norm_nonneg _), fun s x hx ↦ ?_⟩
  have h1 : ‖∏ i ∈ s, (1 + u i x)‖ ≤ ‖∏ i ∈ s, (1 + u i x) - 1‖ + ‖(1 : R)‖ :=
    norm_le_norm_sub_add _ _
  have h2 : ‖∏ i ∈ s, (1 + u i x) - 1‖ ≤ Real.exp C - 1 :=
    (s.norm_prod_one_add_sub_one_le_prod_one_add_norm_sub_one (u · x)).trans <|
      sub_le_sub_right
        ((Real.prod_one_add_le_exp_sum s fun _ ↦ norm_nonneg _).trans
          (Real.exp_le_exp.2 (hC s x hx))) 1
  linarith [Real.exp_pos C]

/-- **Uniform Cauchy criterion for partial products under uniform norm summability.** On any set `X`
and in any seminormed commutative ring `R`, if `fun i x ↦ ‖u i x‖` is uniformly summable on `X` and
each `u i` is bounded on `X`, then the finite partial products `∏ i ∈ s, (1 + u i x)` form a
uniformly Cauchy net on `X`. -/
theorem uniformCauchySeqOn_prod_one_add
    (hsum : SummableUniformlyOn (fun i x ↦ ‖u i x‖) X)
    (hbd : ∀ i, Bornology.IsBounded (u i '' X)) :
    UniformCauchySeqOn (fun (s : Finset ι) x ↦ ∏ i ∈ s, (1 + u i x)) atTop X := by
  classical
  obtain ⟨B, hB_pos, hprod_le⟩ := hsum.exists_norm_prod_one_add_le hbd
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hδ_arg : 1 < 1 + ε / (3 * B) := lt_add_of_pos_right 1 (by positivity)
  have hδ : 0 < Real.log (1 + ε / (3 * B)) := Real.log_pos hδ_arg
  obtain ⟨I, hI⟩ := (TauCeti.summableUniformlyOn_of_nonneg_iff fun _ _ _ ↦ norm_nonneg _).1
    hsum _ hδ
  have hexp_δ : Real.exp (Real.log (1 + ε / (3 * B))) - 1 = ε / (3 * B) := by
    rw [Real.exp_log (zero_lt_one.trans hδ_arg), add_sub_cancel_left]
  have hstep : ∀ ⦃s : Finset ι⦄, I ⊆ s → ∀ x ∈ X,
      ‖(∏ i ∈ s, (1 + u i x)) - ∏ i ∈ I, (1 + u i x)‖ ≤ ε / 3 := fun s hIs x hx ↦ by
    have hdisj : Disjoint (s \ I) I := Finset.sdiff_disjoint
    have hexp : Real.exp (∑ i ∈ s \ I, ‖u i x‖) - 1 ≤ ε / (3 * B) := by
      rw [← hexp_δ]
      exact sub_le_sub_right (Real.exp_le_exp.2 (hI (s \ I) hdisj x hx).le) 1
    calc
      ‖(∏ i ∈ s, (1 + u i x)) - ∏ i ∈ I, (1 + u i x)‖
        ≤ ‖∏ i ∈ I, (1 + u i x)‖ * (Real.exp (∑ i ∈ s \ I, ‖u i x‖) - 1) :=
          Finset.norm_prod_one_add_sub_prod_one_add_le_exp hIs (u · x)
      _ ≤ B * (ε / (3 * B)) :=
          mul_le_mul (hprod_le I x hx) hexp
            (sub_nonneg.2 (Real.one_le_exp (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)))
            hB_pos.le
      _ = ε / 3 := by field_simp
  refine ⟨I, fun s₁ hs₁ s₂ hs₂ x hx ↦ ?_⟩
  calc
    dist (∏ i ∈ s₁, (1 + u i x)) (∏ i ∈ s₂, (1 + u i x))
      ≤ dist (∏ i ∈ s₁, (1 + u i x)) (∏ i ∈ I, (1 + u i x)) +
          dist (∏ i ∈ I, (1 + u i x)) (∏ i ∈ s₂, (1 + u i x)) := dist_triangle _ _ _
    _ = ‖(∏ i ∈ s₁, (1 + u i x)) - ∏ i ∈ I, (1 + u i x)‖ +
          ‖(∏ i ∈ s₂, (1 + u i x)) - ∏ i ∈ I, (1 + u i x)‖ := by
          rw [dist_eq_norm, dist_comm (∏ i ∈ I, _), dist_eq_norm]
    _ ≤ ε / 3 + ε / 3 := add_le_add (hstep hs₁ x hx) (hstep hs₂ x hx)
    _ < ε := by linarith

/-- **Uniform-tail product criterion (`HasProdUniformlyOn`).** On any set `X` and in any complete
seminormed commutative ring `R`, if `fun i x ↦ ‖u i x‖` is uniformly summable on `X` and each
`u i` is bounded on `X`, then `∏' i, (1 + u i x)` converges uniformly on `X`. -/
theorem hasProdUniformlyOn_one_add [CompleteSpace R]
    (hsum : SummableUniformlyOn (fun i x ↦ ‖u i x‖) X)
    (hbd : ∀ i, Bornology.IsBounded (u i '' X)) :
    HasProdUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) X := by
  classical
  have hUC := hsum.uniformCauchySeqOn_prod_one_add hbd
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  exact hUC.tendstoUniformlyOn_of_tendsto fun x hx ↦
    (multipliable_iff_cauchySeq_finset.2 (hUC.cauchySeq hx)).hasProd

/-- Under the hypotheses of `SummableUniformlyOn.hasProdUniformlyOn_one_add`, the family
`fun i x ↦ 1 + u i x` is uniformly multipliable on `X`. -/
theorem multipliableUniformlyOn_one_add [CompleteSpace R]
    (hsum : SummableUniformlyOn (fun i x ↦ ‖u i x‖) X)
    (hbd : ∀ i, Bornology.IsBounded (u i '' X)) :
    MultipliableUniformlyOn (fun i x ↦ 1 + u i x) X :=
  (hsum.hasProdUniformlyOn_one_add hbd).multipliableUniformlyOn

end SeminormedCommRing

section TailFactorization

/-- **Uniform tail factorization.** In a complete normed commutative ring `R`, if
`fun i x ↦ ‖u i x‖` is uniformly summable on `X` and each `u i` is bounded on `X`, then for every
`ε > 0` there is a finite index set `I` outside which `‖u i x‖ < ε` on `X`, the complement product
`G x = ∏' i : {i // i ∉ I}, (1 + u i x)` converges uniformly on `X` with
`‖G x - 1‖ ≤ exp ε - 1`, and `∏' i, (1 + u i x) = (∏ i ∈ I, (1 + u i x)) * G x` on `X`. -/
theorem exists_finset_tprod_one_add_eq_prod_mul {ι α R : Type*}
    [NormedCommRing R] [CompleteSpace R] {u : ι → α → R} {X : Set α}
    (hsum : SummableUniformlyOn (fun i x ↦ ‖u i x‖) X)
    (hbd : ∀ i, Bornology.IsBounded (u i '' X)) {ε : ℝ} (hε : 0 < ε) :
    ∃ I : Finset ι,
      (∀ i ∉ I, ∀ x ∈ X, ‖u i x‖ < ε) ∧
      HasProdUniformlyOn (fun (i : {i // i ∉ I}) x ↦ 1 + u i x)
        (fun x ↦ ∏' i : {i // i ∉ I}, (1 + u i x)) X ∧
      (∀ x ∈ X, ‖(∏' i : {i // i ∉ I}, (1 + u i x)) - 1‖ ≤ Real.exp ε - 1) ∧
      ∀ x ∈ X, ∏' i, (1 + u i x) =
        (∏ i ∈ I, (1 + u i x)) * ∏' i : {i // i ∉ I}, (1 + u i x) := by
  obtain ⟨hpt, htail⟩ := (TauCeti.summableUniformlyOn_iff_tsum_compl_of_nonneg
    fun _ _ _ ↦ norm_nonneg _).1 hsum
  obtain ⟨I, hI⟩ := htail ε hε
  have hsub_sum : SummableUniformlyOn (fun (i : {i // i ∉ I}) x ↦ ‖u i x‖) X :=
    hsum.subtype (· ∉ I)
  have htail_prod : HasProdUniformlyOn (fun (i : {i // i ∉ I}) x ↦ 1 + u i x)
      (fun x ↦ ∏' i : {i // i ∉ I}, (1 + u i x)) X :=
    hsub_sum.hasProdUniformlyOn_one_add fun i ↦ hbd i
  refine ⟨I, fun i hiI x hx ↦ ?_, htail_prod, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · let j : {k // k ∉ I} := ⟨i, hiI⟩
    have hj : ‖u i x‖ = ∑ k ∈ ({j} : Finset {k // k ∉ I}), ‖u k x‖ := by simp [j]
    have hsub_pt : Summable fun k : {k // k ∉ I} ↦ ‖u k x‖ := (hpt x hx).subtype (· ∉ I)
    rw [hj]
    exact (hsub_pt.sum_le_tsum {j} fun _ _ ↦ norm_nonneg _).trans_lt (hI x hx)
  · have hsub_pt : Summable fun k : {k // k ∉ I} ↦ ‖u k x‖ := (hpt x hx).subtype (· ∉ I)
    exact (TauCeti.norm_tprod_one_add_sub_one_le hsub_pt).trans <|
      sub_le_sub_right (Real.exp_le_exp.2 (hI x hx).le) 1
  · exact ((I.hasProd fun i ↦ 1 + u i x).mul_compl (htail_prod.hasProd hx)).tprod_eq

/-- **Nonvanishing tail factorization.** When `‖(1 : R)‖ = 1`, there is a finite index set `I`
outside which `‖u i x‖ < 1 / 2` and `1 + u i x ≠ 0` on `X`, and whose complement infinite product
is nowhere zero on `X`. -/
theorem exists_finset_tprod_one_add_eq_prod_mul_ne_zero {ι α R : Type*}
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R] {u : ι → α → R} {X : Set α}
    (hsum : SummableUniformlyOn (fun i x ↦ ‖u i x‖) X)
    (hbd : ∀ i, Bornology.IsBounded (u i '' X)) :
    ∃ I : Finset ι,
      (∀ i ∉ I, ∀ x ∈ X, ‖u i x‖ < 1 / 2) ∧
      (∀ i ∉ I, ∀ x ∈ X, 1 + u i x ≠ 0) ∧
      HasProdUniformlyOn (fun (i : {i // i ∉ I}) x ↦ 1 + u i x)
        (fun x ↦ ∏' i : {i // i ∉ I}, (1 + u i x)) X ∧
      (∀ x ∈ X, (∏' i : {i // i ∉ I}, (1 + u i x)) ≠ 0) ∧
      ∀ x ∈ X, ∏' i, (1 + u i x) =
        (∏ i ∈ I, (1 + u i x)) * ∏' i : {i // i ∉ I}, (1 + u i x) := by
  have hlog_pos : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  have hlog_le : Real.log (3 / 2) ≤ 1 / 2 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)]
  obtain ⟨I, hsmall, htail_prod, hdev, hfac⟩ :=
    hsum.exists_finset_tprod_one_add_eq_prod_mul hbd hlog_pos
  have hexp : Real.exp (Real.log (3 / 2)) - 1 = 1 / 2 := by
    rw [Real.exp_log (by norm_num)]
    norm_num
  refine ⟨I, fun i hi x hx ↦ (hsmall i hi x hx).trans_le hlog_le,
    fun i hi x hx h0 ↦ ?_, htail_prod, fun x hx h0 ↦ ?_, hfac⟩
  · have hlt : ‖u i x‖ < 1 / 2 := (hsmall i hi x hx).trans_le hlog_le
    have h1 : (1 : ℝ) ≤ ‖1 + u i x‖ + ‖u i x‖ := by
      simpa [norm_neg] using norm_add_le (1 + u i x) (-u i x)
    rw [h0, norm_zero, zero_add] at h1
    linarith
  · have hle := (hdev x hx).trans_eq hexp
    rw [h0, zero_sub, norm_neg, norm_one] at hle
    norm_num at hle

end TailFactorization

section Compact

/-- On a compact subset `K` of a topological space, continuity of each `u i` on `K` automatically
supplies boundedness, so uniform norm summability on `K` yields `HasProdUniformlyOn`. -/
theorem hasProdUniformlyOn_one_add_of_isCompact {ι α R : Type*} [TopologicalSpace α]
    [SeminormedCommRing R] [CompleteSpace R] {u : ι → α → R} {K : Set α}
    (hsum : SummableUniformlyOn (fun i x ↦ ‖u i x‖) K)
    (hK : IsCompact K) (hcts : ∀ i, ContinuousOn (u i) K) :
    HasProdUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) K :=
  hsum.hasProdUniformlyOn_one_add fun i ↦ (hK.image_of_continuousOn (hcts i)).isBounded

end Compact

end SummableUniformlyOn

namespace HasProdUniformlyOn

/-- In a complete normed commutative ring with multiplicative norm, the limit `P` of a uniformly
convergent product `∏' i, (1 + u i x)` on `X` vanishes at `x ∈ X` with `Summable (fun i ↦ ‖u i x‖)`
if and only if one of its factors `1 + u i x` vanishes. -/
theorem eq_zero_iff_exists_one_add_eq_zero {ι α R : Type*}
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R] [NormMulClass R]
    {u : ι → α → R} {P : α → R} {X : Set α}
    (hP : HasProdUniformlyOn (fun i x ↦ 1 + u i x) P X) {x : α} (hx : x ∈ X)
    (hsum : Summable fun i ↦ ‖u i x‖) :
    P x = 0 ↔ ∃ i, 1 + u i x = 0 := by
  rw [← hP.tprod_eqOn hx, TauCeti.tprod_one_add_eq_zero_iff hsum]

end HasProdUniformlyOn

namespace HasProdLocallyUniformlyOn

/-- In a complete normed commutative ring with multiplicative norm, the limit `P` of a locally
uniformly convergent product `∏' i, (1 + u i x)` on `Ω` vanishes at `x ∈ Ω` with
`Summable (fun i ↦ ‖u i x‖)` if and only if one of its factors `1 + u i x` vanishes. -/
theorem eq_zero_iff_exists_one_add_eq_zero {ι α R : Type*} [TopologicalSpace α]
    [NormedCommRing R] [NormOneClass R] [CompleteSpace R] [NormMulClass R]
    {u : ι → α → R} {P : α → R} {Ω : Set α}
    (hP : HasProdLocallyUniformlyOn (fun i x ↦ 1 + u i x) P Ω) {x : α} (hx : x ∈ Ω)
    (hsum : Summable fun i ↦ ‖u i x‖) :
    P x = 0 ↔ ∃ i, 1 + u i x = 0 := by
  rw [← hP.tprod_eqOn hx, TauCeti.tprod_one_add_eq_zero_iff hsum]

end HasProdLocallyUniformlyOn

namespace TauCeti

section ArbitrarySet

variable {ι α R : Type*} [SeminormedCommRing R] [CompleteSpace R] {u : ι → α → R} {X : Set α}

/-- **Unordered uniform-tail product criterion.** If each `u i` is bounded on `X` and finite sums
of `‖u i x‖` over index sets disjoint from a large finite set are uniformly small on `X`, then
`∏' i, (1 + u i x)` converges uniformly on `X`. -/
theorem hasProdUniformlyOn_one_add_of_tail
    (hbd : ∀ i, Bornology.IsBounded (u i '' X))
    (htail : ∀ ε > 0, ∃ I : Finset ι, ∀ J : Finset ι, Disjoint J I →
      ∀ x ∈ X, ∑ i ∈ J, ‖u i x‖ < ε) :
    HasProdUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) X :=
  ((summableUniformlyOn_of_nonneg_iff fun _ _ _ ↦ norm_nonneg _).2 htail).hasProdUniformlyOn_one_add
    hbd

/-- **Sequential uniform-tail product criterion (`HasProdUniformlyOn` over `ℕ`).** On an arbitrary
set `X` and in any complete seminormed commutative ring `R`, if each `u n` is bounded on `X`, each
series `∑' n, ‖u n x‖` converges on `X`, and the tails `∑' k, ‖u (N + k) x‖` vanish uniformly on
`X`, then `∏' n, (1 + u n x)` converges uniformly on `X` along the unordered finite-subset
filter. -/
theorem hasProdUniformlyOn_nat_one_add_of_tail {u : ℕ → α → R}
    (hbd : ∀ n, Bornology.IsBounded (u n '' X))
    (hsum : ∀ x ∈ X, Summable fun n ↦ ‖u n x‖)
    (htail : ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ X, (∑' k, ‖u (N + k) x‖) < ε) :
    HasProdUniformlyOn (fun n x ↦ 1 + u n x) (fun x ↦ ∏' n, (1 + u n x)) X :=
  ((summableUniformlyOn_nat_of_nonneg_iff fun _ _ _ ↦ norm_nonneg _).2
    ⟨hsum, htail⟩).hasProdUniformlyOn_one_add hbd

/-- **Sequential uniform-tail product criterion (`TendstoUniformlyOn` of partial products).** Under
the hypotheses of `TauCeti.hasProdUniformlyOn_nat_one_add_of_tail`, the sequential partial products
`∏ n ∈ Finset.range N, (1 + u n x)` converge uniformly on `X` to `∏' n, (1 + u n x)`. -/
theorem tendstoUniformlyOn_prod_range_one_add_of_tail {u : ℕ → α → R}
    (hbd : ∀ n, Bornology.IsBounded (u n '' X))
    (hsum : ∀ x ∈ X, Summable fun n ↦ ‖u n x‖)
    (htail : ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ X, (∑' k, ‖u (N + k) x‖) < ε) :
    TendstoUniformlyOn (fun N x ↦ ∏ n ∈ Finset.range N, (1 + u n x))
      (fun x ↦ ∏' n, (1 + u n x)) atTop X :=
  (hasProdUniformlyOn_nat_one_add_of_tail hbd hsum htail).tendstoUniformlyOn_finsetRange

end ArbitrarySet

section LocallyUniform

variable {ι α R : Type*} [TopologicalSpace α] [LocallyCompactSpace α]
  [SeminormedCommRing R] [CompleteSpace R]

/-- **Locally uniform product criterion on open sets.** If `Ω` is open in a locally compact space,
each `u i` is continuous on `Ω`, and `fun i x ↦ ‖u i x‖` is uniformly summable on every compact
subset of `Ω`, then `∏' i, (1 + u i x)` converges locally uniformly on `Ω`. -/
theorem hasProdLocallyUniformlyOn_one_add_of_forall_isCompact {u : ι → α → R} {Ω : Set α}
    (hcts : ∀ i, ContinuousOn (u i) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ K ⊆ Ω, IsCompact K → SummableUniformlyOn (fun i x ↦ ‖u i x‖) K) :
    HasProdLocallyUniformlyOn (fun i x ↦ 1 + u i x) (fun x ↦ ∏' i, (1 + u i x)) Ω :=
  hasProdLocallyUniformlyOn_of_forall_compact hΩ fun K hKΩ hK ↦
    (hsum K hKΩ hK).hasProdUniformlyOn_one_add_of_isCompact hK fun i ↦ (hcts i).mono hKΩ

/-- **Sequential locally uniform product criterion (`HasProdLocallyUniformlyOn` over `ℕ`).** If `Ω`
is open in a locally compact space, each `u n` is continuous on `Ω`, `∑' n, ‖u n x‖` converges on
`Ω`, and the tails `∑' k, ‖u (N + k) x‖` vanish uniformly on every compact subset of `Ω`, then
`∏' n, (1 + u n x)` converges locally uniformly on `Ω`. -/
theorem hasProdLocallyUniformlyOn_nat_one_add_of_tail {u : ℕ → α → R} {Ω : Set α}
    (hcts : ∀ n, ContinuousOn (u n) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ x ∈ Ω, Summable fun n ↦ ‖u n x‖)
    (htail : ∀ K ⊆ Ω, IsCompact K → ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ K, (∑' k, ‖u (N + k) x‖) < ε) :
    HasProdLocallyUniformlyOn (fun n x ↦ 1 + u n x) (fun x ↦ ∏' n, (1 + u n x)) Ω :=
  hasProdLocallyUniformlyOn_one_add_of_forall_isCompact hcts hΩ fun K hKΩ hK ↦
    (summableUniformlyOn_nat_of_nonneg_iff fun _ _ _ ↦ norm_nonneg _).2
      ⟨fun x hx ↦ hsum x (hKΩ hx), htail K hKΩ hK⟩

/-- **Sequential locally uniform product criterion (`TendstoLocallyUniformlyOn` of partial
products).** Under the hypotheses of `TauCeti.hasProdLocallyUniformlyOn_nat_one_add_of_tail`, the
sequential partial products `∏ n ∈ Finset.range N, (1 + u n x)` converge locally uniformly on `Ω`
to `∏' n, (1 + u n x)`. -/
theorem tendstoLocallyUniformlyOn_prod_range_one_add_of_tail {u : ℕ → α → R} {Ω : Set α}
    (hcts : ∀ n, ContinuousOn (u n) Ω) (hΩ : IsOpen Ω)
    (hsum : ∀ x ∈ Ω, Summable fun n ↦ ‖u n x‖)
    (htail : ∀ K ⊆ Ω, IsCompact K → ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ K, (∑' k, ‖u (N + k) x‖) < ε) :
    TendstoLocallyUniformlyOn (fun N x ↦ ∏ n ∈ Finset.range N, (1 + u n x))
      (fun x ↦ ∏' n, (1 + u n x)) atTop Ω :=
  (hasProdLocallyUniformlyOn_nat_one_add_of_tail hcts hΩ hsum htail)
    |>.tendstoLocallyUniformlyOn_finsetRange

end LocallyUniform

end TauCeti
