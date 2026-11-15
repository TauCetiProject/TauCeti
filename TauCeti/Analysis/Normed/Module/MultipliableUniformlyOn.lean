/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.Normed.Ring.InfiniteProd

/-!
# Uniform-tail convergence criterion for infinite products

Mathlib's `Summable.hasProdUniformlyOn_one_add` establishes uniform convergence of
`∏' i, (1 + f i x)` on a compact set `K` under a Weierstrass M-test majorant `‖f i x‖ ≤ u i` with
`Summable u`. That hypothesis requires `∑' i, ⨆ x ∈ K, ‖f i x‖ < ∞` and assumes both a topology on
the domain and compactness of `K`.

Uniform convergence of `∏' i, (1 + f i x)` on an arbitrary set `s` actually holds under a strictly
weaker uniform-tail condition (`SummableUniformlyOn.hasProdUniformlyOn_one_add`): it suffices that
each individual term `f i` is bounded on `s` and that the nonnegative norm series `∑' i, ‖f i x‖`
converges uniformly on `s` (`SummableUniformlyOn (fun i x ↦ ‖f i x‖) s`, equivalently pointwise
summability with uniformly vanishing tails), with no topology or compactness on the domain.

When the domain is a topological space and the terms `f i` are continuous on a compact set `K`,
each `f i` is automatically bounded on `K`, yielding uniform convergence on `K` and locally uniform
convergence on open subsets of locally compact spaces without any compact-sup-norm summability.
The diagonal harmonic family `f n x = (n + 1)⁻¹` for `x = n` (and `0` otherwise) on `ℕ` witnesses
that the uniform-tail hypothesis strictly extends the Weierstrass M-test: its uniform norm tail at
stage `N` is at most `(N + 1)⁻¹`, whereas `∑_n ⨆_x ‖f n x‖ = ∑_n (n + 1)⁻¹` diverges.

## Main declarations

* `TauCeti.summableUniformlyOn_iff_tail_tsum_lt`,
  `TauCeti.summableUniformlyOn_nat_iff_tail_tsum_lt`: for nonnegative functions,
  `SummableUniformlyOn` on `s` is equivalent to pointwise summability together with uniformly
  vanishing cofinite or sequential tails on `s`.
* `SummableUniformlyOn.exists_finset_forall_disjoint_norm_sum_lt`: uniform norm-vanishing of
  disjoint finite sub-sums in any seminormed additive commutative group.
* `SummableUniformlyOn.exists_finset_norm_tprod_compl_one_add_sub_one_lt`,
  `SummableUniformlyOn.exists_finset_tprod_compl_one_add_ne_zero`,
  `SummableUniformlyOn.finite_setOf_exists_mem_one_add_eq_zero`,
  `SummableUniformlyOn.tprod_one_add_eq_zero_iff`: a sufficiently far cofinite tail product is
  uniformly within `ε` of `1` on `s`, only finitely many factors vanish anywhere on `s`, and at each
  `x ∈ s` the infinite product vanishes if and only if one factor vanishes.
* `SummableUniformlyOn.hasProdUniformlyOn_one_add`: uniform-tail product criterion on an arbitrary
  set `s` without topological or compactness hypotheses (supplementing the empty-set and
  finite-support cases in `TauCeti.Topology.Algebra.InfiniteSum.UniformOn`).
* `TauCeti.hasProdUniformlyOn_nat_one_add_of_tail_lt`,
  `TauCeti.tendstoUniformlyOn_prod_range_one_add_of_tail_lt`: sequential `ℕ`-indexed unordered and
  partial-product convergence from uniformly vanishing sequential norm tails.
* `SummableUniformlyOn.hasProdUniformlyOn_one_add_of_isCompact`,
  `TauCeti.hasProdLocallyUniformlyOn_one_add_of_forall_isCompact`: continuous compact-set and
  locally-compact open-set versions needing no separate head-boundedness assumption.
* `TauCeti.exists_hasProdUniformly_one_add_and_not_summable_iSup_norm`: separation from the
  Weierstrass M-test on `ℕ`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 14.3.
-/

public section

open Filter Finset Function Metric Set Topology

namespace TauCeti

section NonnegTails

variable {α ι : Type*}

/-- For nonnegative real-valued functions on `s`, `SummableUniformlyOn u s` is equivalent to
pointwise summability on `s` together with uniformly vanishing cofinite tails on `s`. -/
theorem summableUniformlyOn_iff_tail_tsum_lt {u : ι → α → ℝ} {s : Set α}
    (hu₀ : ∀ i, ∀ x ∈ s, 0 ≤ u i x) :
    SummableUniformlyOn u s ↔
      (∀ x ∈ s, Summable (u · x)) ∧
        ∀ ε > 0, ∃ t : Finset ι, ∀ x ∈ s, ∑' i : {i // i ∉ t}, u i x < ε := by
  refine ⟨fun h ↦ ⟨fun x hx ↦ h.summable hx, fun ε hε ↦ ?_⟩, fun ⟨hsum, htail⟩ ↦ ?_⟩
  · obtain ⟨t, ht⟩ := eventually_atTop.mp <|
      Metric.tendstoUniformlyOn_iff.mp h.hasSumUniformlyOn.tendstoUniformlyOn ε hε
    refine ⟨t, fun x hx ↦ ?_⟩
    have hxt := ht t Finset.Subset.rfl x hx
    have hsplit := (h.summable hx).sum_add_tsum_subtype_compl t
    have hnn : 0 ≤ ∑' i : {i // i ∉ t}, u i x :=
      tsum_nonneg fun i ↦ hu₀ i x hx
    rw [Real.dist_eq, ← hsplit, add_sub_cancel_left, abs_of_nonneg hnn] at hxt
    exact hxt
  · refine (HasSumUniformlyOn.summableUniformlyOn (g := fun x ↦ ∑' i, u i x) ?_)
    rw [hasSumUniformlyOn_iff_tendstoUniformlyOn, Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨t₀, ht₀⟩ := htail ε hε
    refine eventually_atTop.mpr ⟨t₀, fun t hsub x hx ↦ ?_⟩
    have hsplit_t := (hsum x hx).sum_add_tsum_subtype_compl t
    have hsplit_t₀ := (hsum x hx).sum_add_tsum_subtype_compl t₀
    have hle : ∑ i ∈ t₀, u i x ≤ ∑ i ∈ t, u i x :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ ↦ hu₀ i x hx
    have hnn : 0 ≤ ∑' i : {i // i ∉ t}, u i x := tsum_nonneg fun i ↦ hu₀ i x hx
    rw [Real.dist_eq, ← hsplit_t, add_sub_cancel_left, abs_of_nonneg hnn]
    linarith [ht₀ x hx]

/-- For a sequence `u : ℕ → α → ℝ` of nonnegative functions on `s`, `SummableUniformlyOn u s` is
equivalent to pointwise summability on `s` together with uniformly vanishing sequential tails
`∑' k, u (k + N) x` on `s`. -/
theorem summableUniformlyOn_nat_iff_tail_tsum_lt {u : ℕ → α → ℝ} {s : Set α}
    (hu₀ : ∀ n, ∀ x ∈ s, 0 ≤ u n x) :
    SummableUniformlyOn u s ↔
      (∀ x ∈ s, Summable (u · x)) ∧
        ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ s, ∑' k, u (k + N) x < ε := by
  rw [summableUniformlyOn_iff_tail_tsum_lt hu₀]
  refine and_congr_right fun hsum ↦ ⟨fun htail ε hε ↦ ?_, fun htail ε hε ↦ ?_⟩
  · obtain ⟨t, ht⟩ := htail ε hε
    let N : ℕ := t.sup id + 1
    have htN : t ⊆ Finset.range N := fun n hn ↦
      Finset.mem_range.mpr (Nat.lt_succ_of_le (t.le_sup (f := id) hn))
    refine ⟨N, fun x hx ↦ ?_⟩
    have h1 := (hsum x hx).sum_add_tsum_subtype_compl t
    have h2 := (hsum x hx).sum_add_tsum_nat_add N
    have hle : ∑ n ∈ t, u n x ≤ ∑ n ∈ Finset.range N, u n x :=
      Finset.sum_le_sum_of_subset_of_nonneg htN fun n _ _ ↦ hu₀ n x hx
    linarith [ht x hx]
  · obtain ⟨N, hN⟩ := htail ε hε
    refine ⟨Finset.range N, fun x hx ↦ ?_⟩
    have h1 := (hsum x hx).sum_add_tsum_subtype_compl (Finset.range N)
    have h2 := (hsum x hx).sum_add_tsum_nat_add N
    linarith [hN x hx]

end NonnegTails

end TauCeti

namespace SummableUniformlyOn

section Vanishing

variable {α ι E : Type*} [SeminormedAddCommGroup E]

/-- If `u : ι → α → E` is uniformly summable on `s`, then for every `ε > 0` there is a finite set
`t` such that every finite sub-sum disjoint from `t` has norm uniformly below `ε` on `s`. -/
theorem exists_finset_forall_disjoint_norm_sum_lt {u : ι → α → E} {s : Set α}
    (hu : SummableUniformlyOn u s) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset ι, ∀ r : Finset ι, Disjoint r t → ∀ x ∈ s, ‖∑ i ∈ r, u i x‖ < ε := by
  simpa [Metric.mem_ball, dist_zero_right] using hu.vanishing (Metric.ball_mem_nhds 0 hε)

end Vanishing

section ArbitrarySet

variable {α ι R : Type*} [NormedCommRing R] [NormOneClass R]

/-- **Uniformly small cofinite tail product.** If `∑' i, ‖f i x‖` converges uniformly on `s`, then
for every `ε > 0` there is a finite set `t` outside which the restricted norm series still
converges uniformly on `s` and `‖(∏' i : {i // i ∉ t}, (1 + f i x)) - 1‖ < ε` for all `x ∈ s`.
Neither completeness of `R` nor boundedness of the finite head `t` is needed. -/
theorem exists_finset_norm_tprod_compl_one_add_sub_one_lt {f : ι → α → R} {s : Set α}
    (htail : SummableUniformlyOn (fun i x ↦ ‖f i x‖) s) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Finset ι,
      SummableUniformlyOn (fun (i : {i // i ∉ t}) x ↦ ‖f i x‖) s ∧
        ∀ x ∈ s, ‖(∏' i : {i // i ∉ t}, (1 + f i x)) - 1‖ < ε := by
  have hnn : ∀ i, ∀ x ∈ s, 0 ≤ ‖f i x‖ := fun _ _ _ ↦ norm_nonneg _
  let δ : ℝ := Real.log (1 + ε)
  have hδ : 0 < δ := Real.log_pos (by linarith)
  obtain ⟨_, htail'⟩ := (TauCeti.summableUniformlyOn_iff_tail_tsum_lt hnn).mp htail
  obtain ⟨t, ht⟩ := htail' δ hδ
  refine ⟨t, Summable.subtype htail (· ∉ t), fun x hx ↦ ?_⟩
  have hsum_x : Summable fun i : {i // i ∉ t} ↦ ‖f i x‖ := (htail.summable hx).subtype _
  calc ‖(∏' i : {i // i ∉ t}, (1 + f i x)) - 1‖
      ≤ Real.exp (∑' i : {i // i ∉ t}, ‖f i x‖) - 1 :=
        TauCeti.norm_tprod_one_add_sub_one_le hsum_x
    _ < Real.exp δ - 1 := sub_lt_sub_right (Real.exp_lt_exp.mpr (ht x hx)) 1
    _ = ε := by rw [Real.exp_log (by linarith), add_sub_cancel_left]

/-- **Nowhere-vanishing cofinite tail product and factors.** If `∑' i, ‖f i x‖` converges uniformly
on `s`, then outside a finite set `t` both every individual factor `1 + f i x` (`i ∉ t`) and the
complementary infinite product `∏' i : {i // i ∉ t}, (1 + f i x)` are nonzero at every point of
`s`. -/
theorem exists_finset_tprod_compl_one_add_ne_zero {f : ι → α → R} {s : Set α}
    (htail : SummableUniformlyOn (fun i x ↦ ‖f i x‖) s) :
    ∃ t : Finset ι,
      (∀ i ∉ t, ∀ x ∈ s, 1 + f i x ≠ 0) ∧
        ∀ x ∈ s, (∏' i : {i // i ∉ t}, (1 + f i x)) ≠ 0 := by
  have hnn : ∀ i, ∀ x ∈ s, 0 ≤ ‖f i x‖ := fun _ _ _ ↦ norm_nonneg _
  let δ : ℝ := min (Real.log 2) (1 / 2)
  have hδ : 0 < δ := lt_min (Real.log_pos one_lt_two) one_half_pos
  obtain ⟨hsum, htail'⟩ := (TauCeti.summableUniformlyOn_iff_tail_tsum_lt hnn).mp htail
  obtain ⟨t, ht⟩ := htail' δ hδ
  refine ⟨t, fun i hi x hx hzero ↦ ?_, fun x hx hzero ↦ ?_⟩
  · have hsub : Summable fun j : {j // j ∉ t} ↦ ‖f j x‖ := (hsum x hx).subtype _
    have hle : ‖f i x‖ ≤ ∑' j : {j // j ∉ t}, ‖f j x‖ :=
      hsub.le_tsum ⟨i, hi⟩ fun _ _ ↦ norm_nonneg _
    have hlt : ‖f i x‖ < 1 :=
      hle.trans_lt ((ht x hx).trans_le ((min_le_right _ _).trans (by norm_num)))
    have h1 : (1 : ℝ) ≤ ‖1 + f i x‖ + ‖f i x‖ := by
      simpa [add_sub_cancel_right] using norm_sub_le (1 + f i x) (f i x)
    rw [hzero, norm_zero, zero_add] at h1
    linarith
  · have hsub : Summable fun j : {j // j ∉ t} ↦ ‖f j x‖ := (hsum x hx).subtype _
    have hlt : ‖(∏' j : {j // j ∉ t}, (1 + f j x)) - 1‖ < 1 := by
      calc ‖(∏' j : {j // j ∉ t}, (1 + f j x)) - 1‖
          ≤ Real.exp (∑' j : {j // j ∉ t}, ‖f j x‖) - 1 :=
            TauCeti.norm_tprod_one_add_sub_one_le hsub
        _ < Real.exp δ - 1 := sub_lt_sub_right (Real.exp_lt_exp.mpr (ht x hx)) 1
        _ ≤ Real.exp (Real.log 2) - 1 :=
            sub_le_sub_right (Real.exp_le_exp.mpr (min_le_left _ _)) 1
        _ = 1 := by rw [Real.exp_log zero_lt_two]; norm_num
    rw [hzero, zero_sub, norm_neg, norm_one] at hlt
    exact lt_irrefl 1 hlt

/-- If `∑' i, ‖f i x‖` converges uniformly on `s`, then at most finitely many factors `1 + f i`
vanish anywhere on `s`. -/
theorem finite_setOf_exists_mem_one_add_eq_zero {f : ι → α → R} {s : Set α}
    (htail : SummableUniformlyOn (fun i x ↦ ‖f i x‖) s) :
    {i : ι | ∃ x ∈ s, 1 + f i x = 0}.Finite := by
  obtain ⟨t, hfac, _⟩ := htail.exists_finset_tprod_compl_one_add_ne_zero
  refine t.finite_toSet.subset fun i ⟨x, hx, hzero⟩ ↦ ?_
  by_contra hi
  exact hfac i hi x hx hzero

/-- In a complete normed commutative ring with multiplicative norm, if `∑' i, ‖f i x‖` converges
uniformly on `s`, then at every `x ∈ s` the product `∏' i, (1 + f i x)` vanishes if and only if one
of its factors vanishes. -/
theorem tprod_one_add_eq_zero_iff [CompleteSpace R] [NormMulClass R] {f : ι → α → R} {s : Set α}
    (htail : SummableUniformlyOn (fun i x ↦ ‖f i x‖) s) {x : α} (hx : x ∈ s) :
    (∏' i, (1 + f i x)) = 0 ↔ ∃ i, 1 + f i x = 0 :=
  TauCeti.tprod_one_add_eq_zero_iff (htail.summable hx)

/-- **Uniform-tail infinite-product criterion.** Let `s` be an arbitrary set (with no topology
assumed on `α`). If each `f i` is bounded on `s` and the norm series `∑' i, ‖f i x‖` converges
uniformly on `s`, then `∏' i, (1 + f i x)` converges uniformly on `s` along the unordered
finite-subset filter. -/
theorem hasProdUniformlyOn_one_add [CompleteSpace R] {f : ι → α → R} {s : Set α}
    (htail : SummableUniformlyOn (fun i x ↦ ‖f i x‖) s)
    (hbdd : ∀ i, ∃ M, ∀ x ∈ s, ‖f i x‖ ≤ M) :
    HasProdUniformlyOn (fun i x ↦ 1 + f i x) (fun x ↦ ∏' i, (1 + f i x)) s := by
  classical
  choose M hM using hbdd
  obtain ⟨t₀, ht₀⟩ := htail.exists_finset_forall_disjoint_norm_sum_lt zero_lt_one
  let C : ℝ := (∑ i ∈ t₀, max (M i) 0) + 1
  -- Every finite partial product on `s` has norm bounded by `exp C`.
  have hprod_le : ∀ b : Finset ι, ∀ x ∈ s, ‖∏ i ∈ b, (1 + f i x)‖ ≤ Real.exp C := by
    intro b x hx
    have hsub : b ⊆ t₀ ∪ (b \ t₀) := fun i hi ↦ by by_cases h : i ∈ t₀ <;> simp [hi, h]
    have hle₁ := (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ norm_nonneg _).trans_eq
      (Finset.sum_union disjoint_sdiff_self_right (f := fun i ↦ ‖f i x‖))
    have hhead : ∑ i ∈ t₀, ‖f i x‖ ≤ ∑ i ∈ t₀, max (M i) 0 :=
      Finset.sum_le_sum fun i _ ↦ (hM i x hx).trans (le_max_left _ _)
    have htail₀ : ∑ i ∈ b \ t₀, ‖f i x‖ < 1 :=
      (Real.le_norm_self _).trans_lt (ht₀ (b \ t₀) sdiff_disjoint x hx)
    exact (b.norm_prod_one_add_le_prod_one_add_norm fun i ↦ f i x).trans <|
      (Real.prod_one_add_le_exp_sum b fun _ ↦ norm_nonneg _).trans
        (Real.exp_le_exp.mpr (by linarith))
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn, Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let η : ℝ := Real.log (1 + ε / (2 * Real.exp C))
  have hη : 0 < η := Real.log_pos (by linarith [div_pos hε (mul_pos zero_lt_two (Real.exp_pos C))])
  obtain ⟨t₁, ht₁⟩ := htail.exists_finset_forall_disjoint_norm_sum_lt hη
  refine eventually_atTop.mpr ⟨t₁, fun b hb x hx ↦ ?_⟩
  have hmult : Multipliable fun i ↦ 1 + f i x :=
    multipliable_one_add_of_summable (htail.summable hx)
  -- Compare `∏ i ∈ b', (1 + f i x)` against `∏ i ∈ b, (1 + f i x)` for `b ⊆ b'`, then let `b' → ∞`.
  have hle : ‖(∏' i, (1 + f i x)) - ∏ i ∈ b, (1 + f i x)‖ ≤ ε / 2 := by
    refine le_of_tendsto ((hmult.hasProd.sub_const _).norm) <|
      eventually_atTop.mpr ⟨b, fun b' hbb' ↦ ?_⟩
    have hsplit : ∏ i ∈ b', (1 + f i x) - ∏ i ∈ b, (1 + f i x) =
        (∏ i ∈ b, (1 + f i x)) * (∏ i ∈ b' \ b, (1 + f i x) - 1) := by
      conv_lhs =>
        arg 1
        rw [← Finset.union_sdiff_of_subset hbb', Finset.prod_union sdiff_disjoint.symm]
      rw [mul_sub_one]
    have hdisj : ∑ i ∈ b' \ b, ‖f i x‖ ≤ η :=
      (Real.le_norm_self _).trans (ht₁ (b' \ b) (sdiff_disjoint.mono_right hb) x hx).le
    calc ‖∏ i ∈ b', (1 + f i x) - ∏ i ∈ b, (1 + f i x)‖
        ≤ ‖∏ i ∈ b, (1 + f i x)‖ * ‖∏ i ∈ b' \ b, (1 + f i x) - 1‖ := hsplit ▸ norm_mul_le _ _
      _ ≤ Real.exp C * (Real.exp (∑ i ∈ b' \ b, ‖f i x‖) - 1) :=
          mul_le_mul (hprod_le b x hx) ((b' \ b).norm_prod_one_add_sub_one_le _)
            (norm_nonneg _) (Real.exp_nonneg C)
      _ ≤ Real.exp C * (Real.exp η - 1) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_le_exp.mpr hdisj) 1)
            (Real.exp_nonneg C)
      _ = ε / 2 := by
          rw [Real.exp_log (by positivity), add_sub_cancel_left]
          have hexp : Real.exp C ≠ 0 := (Real.exp_pos C).ne'
          field_simp
  rw [dist_eq_norm]
  linarith

/-- Existential form of `SummableUniformlyOn.hasProdUniformlyOn_one_add`. -/
theorem multipliableUniformlyOn_one_add [CompleteSpace R] {f : ι → α → R} {s : Set α}
    (htail : SummableUniformlyOn (fun i x ↦ ‖f i x‖) s)
    (hbdd : ∀ i, ∃ M, ∀ x ∈ s, ‖f i x‖ ≤ M) :
    MultipliableUniformlyOn (fun i x ↦ 1 + f i x) s :=
  ⟨_, htail.hasProdUniformlyOn_one_add hbdd⟩

end ArbitrarySet

section TopologicalSpace

variable {α ι R : Type*} [TopologicalSpace α] [NormedCommRing R] [NormOneClass R] [CompleteSpace R]

/-- On a compact set `K`, continuous deviations `f i` whose norm series `∑' i, ‖f i x‖` converges
uniformly on `K` are automatically bounded termwise, so `∏' i, (1 + f i x)` converges uniformly on
`K` without any Weierstrass M-test majorant. -/
theorem hasProdUniformlyOn_one_add_of_isCompact {f : ι → α → R} {K : Set α}
    (hK : IsCompact K) (htail : SummableUniformlyOn (fun i x ↦ ‖f i x‖) K)
    (hcts : ∀ i, ContinuousOn (f i) K) :
    HasProdUniformlyOn (fun i x ↦ 1 + f i x) (fun x ↦ ∏' i, (1 + f i x)) K :=
  htail.hasProdUniformlyOn_one_add fun i ↦ hK.exists_bound_of_continuousOn (hcts i)

end TopologicalSpace

end SummableUniformlyOn

namespace TauCeti

section SequentialAndLocal

variable {α ι R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R]

/-- **Sequential uniform-tail infinite-product criterion (unordered limit).** If each `f n` is
bounded on `s`, each norm series `∑' n, ‖f n x‖` converges on `s`, and the sequential tails
`∑' k, ‖f (k + N) x‖` vanish uniformly on `s`, then `∏' n, (1 + f n x)` converges uniformly on `s`
along the unordered finite-subset filter. -/
theorem hasProdUniformlyOn_nat_one_add_of_tail_lt {f : ℕ → α → R} {s : Set α}
    (hbdd : ∀ n, ∃ M, ∀ x ∈ s, ‖f n x‖ ≤ M)
    (hsum : ∀ x ∈ s, Summable fun n ↦ ‖f n x‖)
    (htail : ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ s, ∑' k, ‖f (k + N) x‖ < ε) :
    HasProdUniformlyOn (fun n x ↦ 1 + f n x) (fun x ↦ ∏' n, (1 + f n x)) s :=
  ((summableUniformlyOn_nat_iff_tail_tsum_lt (fun _ _ _ ↦ norm_nonneg _)).mpr ⟨hsum, htail⟩)
    |>.hasProdUniformlyOn_one_add hbdd

/-- **Sequential uniform-tail infinite-product criterion (partial products).** Under the hypotheses
of `TauCeti.hasProdUniformlyOn_nat_one_add_of_tail_lt`, the sequential partial products
`∏ n ∈ Finset.range N, (1 + f n x)` converge uniformly on `s` to `∏' n, (1 + f n x)`. -/
theorem tendstoUniformlyOn_prod_range_one_add_of_tail_lt {f : ℕ → α → R} {s : Set α}
    (hbdd : ∀ n, ∃ M, ∀ x ∈ s, ‖f n x‖ ≤ M)
    (hsum : ∀ x ∈ s, Summable fun n ↦ ‖f n x‖)
    (htail : ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ s, ∑' k, ‖f (k + N) x‖ < ε) :
    TendstoUniformlyOn (fun N x ↦ ∏ n ∈ Finset.range N, (1 + f n x))
      (fun x ↦ ∏' n, (1 + f n x)) atTop s :=
  (hasProdUniformlyOn_nat_one_add_of_tail_lt hbdd hsum htail).tendstoUniformlyOn_finsetRange

/-- On an open subset `U` of a locally compact space, if each `f i` is continuous on `U` and
`∑' i, ‖f i x‖` converges uniformly on every compact subset of `U`, then `∏' i, (1 + f i x)`
converges locally uniformly on `U`. -/
theorem hasProdLocallyUniformlyOn_one_add_of_forall_isCompact [TopologicalSpace α]
    [LocallyCompactSpace α] {f : ι → α → R} {U : Set α} (hU : IsOpen U)
    (htail : ∀ K ⊆ U, IsCompact K → SummableUniformlyOn (fun i x ↦ ‖f i x‖) K)
    (hcts : ∀ i, ContinuousOn (f i) U) :
    HasProdLocallyUniformlyOn (fun i x ↦ 1 + f i x) (fun x ↦ ∏' i, (1 + f i x)) U :=
  hasProdLocallyUniformlyOn_of_forall_compact hU fun K hKU hK ↦
    (htail K hKU hK).hasProdUniformlyOn_one_add_of_isCompact hK fun i ↦ (hcts i).mono hKU

/-- Sequential-tail version of `TauCeti.hasProdLocallyUniformlyOn_one_add_of_forall_isCompact`
for `ℕ`-indexed families on open subsets of locally compact spaces. -/
theorem hasProdLocallyUniformlyOn_nat_one_add_of_tail_lt [TopologicalSpace α]
    [LocallyCompactSpace α] {f : ℕ → α → R} {U : Set α} (hU : IsOpen U)
    (hsum : ∀ x ∈ U, Summable fun n ↦ ‖f n x‖)
    (htail : ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ K, ∑' k, ‖f (k + N) x‖ < ε)
    (hcts : ∀ n, ContinuousOn (f n) U) :
    HasProdLocallyUniformlyOn (fun n x ↦ 1 + f n x) (fun x ↦ ∏' n, (1 + f n x)) U :=
  hasProdLocallyUniformlyOn_one_add_of_forall_isCompact hU
    (fun K hKU hK ↦ (summableUniformlyOn_nat_iff_tail_tsum_lt fun _ _ _ ↦ norm_nonneg _).mpr
      ⟨fun x hx ↦ hsum x (hKU hx), htail K hKU hK⟩) hcts

/-- Sequential partial-product version of
`TauCeti.hasProdLocallyUniformlyOn_nat_one_add_of_tail_lt`. -/
theorem tendstoLocallyUniformlyOn_prod_range_one_add_of_tail_lt [TopologicalSpace α]
    [LocallyCompactSpace α] {f : ℕ → α → R} {U : Set α} (hU : IsOpen U)
    (hsum : ∀ x ∈ U, Summable fun n ↦ ‖f n x‖)
    (htail : ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ N : ℕ, ∀ x ∈ K, ∑' k, ‖f (k + N) x‖ < ε)
    (hcts : ∀ n, ContinuousOn (f n) U) :
    TendstoLocallyUniformlyOn (fun N x ↦ ∏ n ∈ Finset.range N, (1 + f n x))
      (fun x ↦ ∏' n, (1 + f n x)) atTop U :=
  (hasProdLocallyUniformlyOn_nat_one_add_of_tail_lt hU hsum htail hcts)
    |>.tendstoLocallyUniformlyOn_finsetRange

end SequentialAndLocal

section SeparationExample

/-- **Separation from the Weierstrass M-test.** For any `RCLike` scalar field `𝕜` (such as `ℝ` or
`ℂ`), the diagonal harmonic family `f n x = ((n + 1 : ℕ) : 𝕜)⁻¹` for `x = n` and `0` otherwise on
`ℕ` satisfies `HasProdUniformly (fun n x ↦ 1 + f n x) (fun x ↦ ∏' n, (1 + f n x))` via uniform
norm tails, whereas the supremum-norm series `∑' n, ⨆ x : ℕ, ‖f n x‖` is the divergent harmonic
series. -/
theorem exists_hasProdUniformly_one_add_and_not_summable_iSup_norm (𝕜 : Type*) [RCLike 𝕜] :
    ∃ f : ℕ → ℕ → 𝕜,
      SummableUniformlyOn (fun n x ↦ ‖f n x‖) Set.univ ∧
        HasProdUniformly (fun n x ↦ 1 + f n x) (fun x ↦ ∏' n, (1 + f n x)) ∧
        ¬ Summable (fun n : ℕ ↦ ⨆ x : ℕ, ‖f n x‖) := by
  let f : ℕ → ℕ → 𝕜 := fun n x ↦ if x = n then ((n + 1 : ℕ) : 𝕜)⁻¹ else 0
  have hnorm (n x : ℕ) : ‖f n x‖ = if x = n then ((n + 1 : ℕ) : ℝ)⁻¹ else 0 := by
    by_cases h : x = n
    · simp only [f, h, ↓reduceIte, norm_inv, RCLike.norm_natCast]
    · simp only [f, h, ↓reduceIte, norm_zero]
  have hle_inv (n x : ℕ) : ‖f n x‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by
    rw [hnorm]
    split_ifs
    · exact le_rfl
    · positivity
  have htail_univ : SummableUniformlyOn (fun n x ↦ ‖f n x‖) (Set.univ : Set ℕ) := by
    rw [summableUniformlyOn_nat_iff_tail_tsum_lt (fun _ _ _ ↦ norm_nonneg _)]
    refine ⟨fun x _ ↦ summable_of_ne_finset_zero (s := {x}) fun n hn ↦ ?_, fun ε hε ↦ ?_⟩
    · simp only [Finset.mem_singleton] at hn
      simp [hnorm, Ne.symm hn]
    · obtain ⟨N, hN⟩ := exists_nat_gt ε⁻¹
      refine ⟨N, fun x _ ↦ ?_⟩
      by_cases hx : N ≤ x
      · have htsum : (∑' k, ‖f (k + N) x‖) = ((x + 1 : ℕ) : ℝ)⁻¹ := by
          rw [tsum_eq_single (x - N)]
          · simp [hnorm, Nat.sub_add_cancel hx]
          · intro k hk
            have hne : x ≠ k + N := fun h ↦ hk (by omega)
            simp [hnorm, hne]
        rw [htsum]
        have hle : ((x + 1 : ℕ) : ℝ)⁻¹ ≤ ((N + 1 : ℕ) : ℝ)⁻¹ :=
          inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hx 1)
        have hlt : ((N + 1 : ℕ) : ℝ)⁻¹ < ε := by
          rw [inv_lt_comm₀ (by positivity) hε]
          exact hN.trans (by exact_mod_cast Nat.lt_succ_self N)
        exact hle.trans_lt hlt
      · have hzero (k : ℕ) : ‖f (k + N) x‖ = 0 := by
          have hne : x ≠ k + N := by omega
          simp [hnorm, hne]
        simpa [hzero] using hε
  have hbdd : ∀ n, ∃ M, ∀ x ∈ (Set.univ : Set ℕ), ‖f n x‖ ≤ M :=
    fun n ↦ ⟨((n + 1 : ℕ) : ℝ)⁻¹, fun x _ ↦ hle_inv n x⟩
  have hprod : HasProdUniformly (fun n x ↦ 1 + f n x) (fun x ↦ ∏' n, (1 + f n x)) :=
    hasProdUniformlyOn_univ_iff.mp (htail_univ.hasProdUniformlyOn_one_add hbdd)
  have hiSup (n : ℕ) : (⨆ x : ℕ, ‖f n x‖) = ((n + 1 : ℕ) : ℝ)⁻¹ := by
    have hba : BddAbove (Set.range fun x : ℕ ↦ ‖f n x‖) :=
      ⟨((n + 1 : ℕ) : ℝ)⁻¹, by rintro _ ⟨x, rfl⟩; exact hle_inv n x⟩
    refine le_antisymm (ciSup_le (hle_inv n)) ?_
    simpa [hnorm] using le_ciSup hba n
  refine ⟨f, htail_univ, hprod, ?_⟩
  simp_rw [hiSup]
  intro hs
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp (by simpa using hs))

end SeparationExample

end TauCeti
