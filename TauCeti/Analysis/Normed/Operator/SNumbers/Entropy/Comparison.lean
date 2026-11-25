/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Entropy.Hilbert
public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.Analysis.Normed.Operator.SNumbers.Kolmogorov
public import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Data.Fin.Tuple.Basic

/-!
# s-numbers against entropy numbers

Over `ℝ` or `ℂ`, the entropy numbers of a bounded operator `T : E →L[𝕜] F` bound its Gelfand,
Kolmogorov, approximation and Hilbert numbers from above, up to an explicit factor:

* `cₙ(T) ≤ (n + 1) eₙ(T)` and `dₙ(T) ≤ (n + 1) eₙ(T)` on all seminormed spaces;
* `aₙ(T) ≤ 2 eₙ(T)` between inner product spaces;
* `hₙ(T) ≤ 2 eₙ(T)` on all seminormed spaces.

The first pair rests on *triangular families*. If `γ < dₙ(T)`, there are `x₀, …, xₙ` in the closed
unit ball such that each `T xⱼ` keeps distance more than `γ` from the span of the earlier images
`T xₖ`, `k < j`; if `γ < cₙ(T)`, there are moreover functionals `ρ₀, …, ρₙ` of norm at most one with
`|ρⱼ (T xⱼ)| > γ` and `ρᵢ (T xⱼ) = 0` for `i < j`. For any such family, the `2 ^ (n + 1)` sign
averages `(n + 1)⁻¹ ∑ₖ ±xₖ` lie in the unit ball and their images are `2γ / (n + 1)`-separated, so
no `2 ^ n` balls of radius below `γ / (n + 1)` cover `T(B_E)`.

The second pair is proved in `TauCeti.Analysis.Normed.Operator.SNumbers.Entropy.Hilbert`, which
this file re-exports: below `aₙ(T)`, the scalar factorization `B ∘L T ∘L A = c • id` through
contractions combines with the ideal inequality for entropy numbers and the lower bound
`1 / 2 ≤ eₙ(id)`. The Hilbert numbers inherit the bound from their compressions.

## Main declarations

* `ContinuousLinearMap.le_mul_entropyNumber_of_forall_le_norm_add`: a triangular family in the
  unit ball with gap `γ` gives `γ ≤ (n + 1) eₙ(T)`.
* `ContinuousLinearMap.exists_flag_of_lt_kolmogorovNumber`,
  `ContinuousLinearMap.exists_flag_of_lt_gelfandNumber`: triangular families below `dₙ(T)` and
  `cₙ(T)`.
* `ContinuousLinearMap.kolmogorovNumber_le_mul_entropyNumber`,
  `ContinuousLinearMap.gelfandNumber_le_mul_entropyNumber`: `dₙ(T), cₙ(T) ≤ (n + 1) eₙ(T)`.
* `ContinuousLinearMap.singularValue_le_two_mul_entropyNumber`: `aₙ(T) ≤ 2 eₙ(T)` between inner
  product spaces, and `ContinuousLinearMap.hilbertNumber_le_two_mul_entropyNumber`:
  `hₙ(T) ≤ 2 eₙ(T)`, from `Entropy.Hilbert`.

## References

* A. Pietsch, *Operator Ideals*, North-Holland Mathematical Library 20, North-Holland (1980),
  12.3.2 for the Gelfand and Kolmogorov bounds.
* B. Carl and I. Stephani, *Entropy, Compactness and the Approximation of Operators*, Cambridge
  Tracts in Mathematics 98, Cambridge University Press (1990), Chapter 2.
* M. Ullrich, Lean-SNumbers (Apache-2.0), <https://github.com/mario-ullrich/Lean-SNumbers>,
  `SNumbers/EntropyBounds.lean`: an earlier Lean formalization of these comparisons.
-/

public section

open Cardinal Metric Set
open scoped NNReal

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The separation step for sign averages of a triangular family: for two distinct sign vectors,
the coefficient at the last index where they differ has norm `2`, and the earlier terms lie in the
span of the earlier images. -/
private theorem two_mul_le_norm_sum_smul_sub {ι : Type*} [Fintype ι] [LinearOrder ι]
    {T : E →L[𝕜] F} {x : ι → E} {γ : ℝ}
    (hγ : ∀ j, ∀ w ∈ Submodule.span 𝕜 ((T ∘ x) '' Iio j), γ ≤ ‖T (x j) + w‖)
    {σ : Bool → 𝕜} (hσ : ∀ a b, a ≠ b → ‖σ a - σ b‖ = 2) {ε ε' : ι → Bool} (hne : ε ≠ ε') :
    2 * γ ≤ ‖∑ k, (σ (ε k) - σ (ε' k)) • T (x k)‖ := by
  classical
  -- The last index where the signs differ.
  obtain ⟨j, hj, hjmax⟩ : ∃ j, ε j ≠ ε' j ∧ ∀ k, ε k ≠ ε' k → k ≤ j := by
    have hD : (Finset.univ.filter fun k ↦ ε k ≠ ε' k).Nonempty := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
      exact ⟨k, by simpa using hk⟩
    exact ⟨_, (Finset.mem_filter.mp (Finset.max'_mem _ hD)).2,
      fun k hk ↦ Finset.le_max' _ k (by simpa using hk)⟩
  set S := Submodule.span 𝕜 ((T ∘ x) '' Iio j)
  let c : ι → 𝕜 := fun k ↦ σ (ε k) - σ (ε' k)
  set r := ∑ k ∈ Finset.univ.erase j, c k • T (x k)
  have hr : r ∈ S := Submodule.sum_mem _ fun k hk ↦ by
    by_cases hk' : ε k = ε' k
    · simp [c, hk']
    · exact S.smul_mem _ (Submodule.subset_span
        ⟨k, lt_of_le_of_ne (hjmax k hk') (Finset.ne_of_mem_erase hk), rfl⟩)
  have hcj : ‖c j‖ = 2 := hσ _ _ hj
  have hc0 : c j ≠ 0 := by rw [← norm_ne_zero_iff, hcj]; norm_num
  have hsum : ∑ k, c k • T (x k) = c j • (T (x j) + (c j)⁻¹ • r) := by
    rw [smul_add, smul_inv_smul₀ hc0]
    exact (Finset.add_sum_erase _ (fun k ↦ c k • T (x k)) (Finset.mem_univ j)).symm
  rw [hsum, norm_smul, hcj]
  gcongr
  exact hγ j _ (S.smul_mem _ hr)

/-- **Triangular families bound entropy numbers.** Let `x` be a family in the closed unit ball,
indexed by a finite linear order with `n + 1` elements, such that each `T (x j)` keeps norm at least
`γ` after adding any vector of the span of the earlier images `T (x k)`, `k < j`. Then
`γ ≤ (n + 1) eₙ(T)`. -/
theorem le_mul_entropyNumber_of_forall_le_norm_add {ι : Type*} [Fintype ι] [LinearOrder ι]
    {T : E →L[𝕜] F} {n : ℕ} (hι : Fintype.card ι = n + 1) {x : ι → E} (hx : ∀ i, ‖x i‖ ≤ 1)
    {γ : ℝ} (hγ : ∀ j, ∀ w ∈ Submodule.span 𝕜 ((T ∘ x) '' Iio j), γ ≤ ‖T (x j) + w‖) :
    γ ≤ (n + 1) * T.entropyNumber n := by
  -- The `2 ^ (n + 1)` sign averages `(n + 1)⁻¹ ∑ₖ ±xₖ`.
  let σ : Bool → 𝕜 := fun b ↦ if b then 1 else -1
  let f : (ι → Bool) → E := fun ε ↦ ((n + 1 : ℕ) : 𝕜)⁻¹ • ∑ k, σ (ε k) • x k
  have hσ : ∀ b, ‖σ b‖ = 1 := by intro b; cases b <;> simp [σ]
  have hσ₂ : ∀ a b, a ≠ b → ‖σ a - σ b‖ = 2 := by
    intro a b hab
    cases a <;> cases b <;> simp_all [σ] <;> norm_num
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hf : ∀ ε, f ε ∈ closedBall (0 : E) 1 := by
    intro ε
    have hsum : ‖∑ k, σ (ε k) • x k‖ ≤ n + 1 :=
      calc ‖∑ k, σ (ε k) • x k‖ ≤ ∑ _ : ι, (1 : ℝ) :=
            (norm_sum_le _ _).trans <| Finset.sum_le_sum fun k _ ↦ by
              simpa [norm_smul, hσ] using hx k
        _ = n + 1 := by simp [hι]
    simp only [f, mem_closedBall_zero_iff, norm_smul, norm_inv, RCLike.norm_natCast]
    rw [inv_mul_le_iff₀ (by positivity)]
    simpa using hsum
  have hsep : Pairwise fun ε ε' ↦ 2 * γ / (n + 1) ≤ dist (T (f ε)) (T (f ε')) := by
    intro ε ε' hne
    have hdiff : T (f ε) - T (f ε') =
        ((n + 1 : ℕ) : 𝕜)⁻¹ • ∑ k, (σ (ε k) - σ (ε' k)) • T (x k) := by
      simp only [f, map_smul, map_sum, ← smul_sub, ← Finset.sum_sub_distrib, sub_smul]
    simp only [dist_eq_norm, hdiff, norm_smul, norm_inv, RCLike.norm_natCast, div_eq_inv_mul]
    push_cast
    gcongr
    exact two_mul_le_norm_sum_smul_sub hγ hσ₂ hne
  have hcard : 2 ^ n < Fintype.card (ι → Bool) := by
    rw [Fintype.card_fun, Fintype.card_bool, hι]
    exact Nat.pow_lt_pow_right one_lt_two n.lt_succ_self
  have hbound := div_two_le_entropyNumber_of_pairwise_le_dist hf hsep hcard
  rw [mul_div_assoc, mul_div_cancel_left₀ _ two_ne_zero, div_le_iff₀ hn] at hbound
  linarith

/-- **Triangular families below Kolmogorov numbers.** If `γ < dₙ(T)`, there are vectors
`x 0, …, x n` in the closed unit ball such that each `T (x j)` keeps norm more than `γ` after adding
any vector of the span of the earlier images `T (x k)`, `k < j`. -/
theorem exists_flag_of_lt_kolmogorovNumber {T : E →L[𝕜] F} {n : ℕ} {γ : ℝ}
    (hγ : γ < T.kolmogorovNumber n) :
    ∃ x : Fin (n + 1) → E, (∀ j, ‖x j‖ ≤ 1) ∧
      ∀ j, ∀ w ∈ Submodule.span 𝕜 ((T ∘ x) '' Iio j), γ < ‖T (x j) + w‖ := by
  obtain ⟨x, hx⟩ := Fin.exists_tuple_forall_image_Iio (N := n + 1)
    (Q := fun s a ↦ ‖a‖ ≤ 1 ∧ ∀ w ∈ Submodule.span 𝕜 (T '' s), γ < ‖T a + w‖) fun m hm y ↦ by
      set V := Submodule.span 𝕜 (T '' range y)
      have hV : Module.rank 𝕜 V ≤ n := by
        refine (rank_span_le _).trans ?_
        rw [← range_comp]
        refine lift_le_nat_iff.mp (mk_range_le_lift.trans ?_)
        simpa using Nat.lt_succ_iff.mp hm
      have hlt : γ < ‖V.mkQL ∘L T‖ :=
        hγ.trans_le (by exact_mod_cast T.kolmogorovNumber_le hV)
      -- A unit vector on which `V.mkQL ∘L T` exceeds `γ`.
      obtain ⟨a, ha, hγa⟩ : ∃ a : E, ‖a‖ ≤ 1 ∧ γ < ‖V.mkQL (T a)‖ := by
        rcases lt_or_ge γ 0 with hγ0 | hγ0
        · exact ⟨0, by simp, by simpa using hγ0⟩
        by_contra! H
        exact hlt.not_ge ((V.mkQL ∘L T).opNorm_le_of_unit_norm hγ0 fun a ha ↦ H a ha.le)
      refine ⟨a, ha, fun w hw ↦ hγa.trans_le ?_⟩
      have hmk : V.mkQL (T a) = V.mkQL (T a + w) := by
        simp [(Submodule.Quotient.mk_eq_zero V).mpr hw]
      rw [hmk]
      exact Submodule.Quotient.norm_mk_le V _
  exact ⟨x, fun j ↦ (hx j).1, fun j ↦ by simpa only [image_comp] using (hx j).2⟩

/-- **Triangular families below Gelfand numbers.** If `γ < cₙ(T)`, there are vectors
`x 0, …, x n` in the closed unit ball and functionals `ρ 0, …, ρ n` on `F` of norm at most one
with `γ < ‖ρ j (T (x j))‖` and `ρ i (T (x j)) = 0` for `i < j`. -/
theorem exists_flag_of_lt_gelfandNumber {T : E →L[𝕜] F} {n : ℕ} {γ : ℝ}
    (hγ : γ < T.gelfandNumber n) :
    ∃ (x : Fin (n + 1) → E) (ρ : Fin (n + 1) → StrongDual 𝕜 F), (∀ j, ‖x j‖ ≤ 1) ∧
      (∀ j, ‖ρ j‖ ≤ 1) ∧ (∀ j, γ < ‖ρ j (T (x j))‖) ∧ ∀ i j, i < j → ρ i (T (x j)) = 0 := by
  obtain ⟨p, hp⟩ := Fin.exists_tuple_forall_image_Iio (α := E × StrongDual 𝕜 F) (N := n + 1)
    (Q := fun s a ↦ ‖a.1‖ ≤ 1 ∧ ‖a.2‖ ≤ 1 ∧ γ < ‖a.2 (T a.1)‖ ∧ ∀ q ∈ s, q.2 (T a.1) = 0)
    fun m hm y ↦ by
      -- The common kernel `M` of the functionals `(y i).2 ∘L T`, `i < m`, has codimension `≤ n`.
      let φ : E →L[𝕜] (Fin m → 𝕜) := ContinuousLinearMap.pi fun i ↦ (y i).2 ∘L T
      set M : Submodule 𝕜 E := LinearMap.ker (φ : E →ₗ[𝕜] Fin m → 𝕜)
      have hMc : IsClosed (M : Set E) := φ.isClosed_ker
      have hMr : Module.rank 𝕜 (E ⧸ M) ≤ n := by
        have hrange : Module.rank 𝕜 (LinearMap.range (φ : E →ₗ[𝕜] Fin m → 𝕜)) ≤ n :=
          (Submodule.rank_le _).trans <| by simpa using Nat.lt_succ_iff.mp hm
        exact lift_le_nat_iff.mp ((φ : E →ₗ[𝕜] Fin m → 𝕜).quotKerEquivRange.lift_rank_eq.trans_le
          (lift_le_nat_iff.mpr hrange))
      have hlt : γ < ‖T ∘L M.subtypeL‖ :=
        hγ.trans_le (by exact_mod_cast le_gelfandNumber_iff.mp le_rfl M hMc hMr)
      -- A unit vector of `M` on which `T` exceeds `γ`, normed by a Hahn–Banach functional.
      obtain ⟨a, ha, hγa⟩ : ∃ a : M, ‖a‖ ≤ 1 ∧ γ < ‖T a‖ := by
        rcases lt_or_ge γ 0 with hγ0 | hγ0
        · exact ⟨0, by simp, by simpa using hγ0⟩
        by_contra! H
        exact hlt.not_ge ((T ∘L M.subtypeL).opNorm_le_of_unit_norm hγ0 fun a ha ↦ H a ha.le)
      obtain ⟨g, hg, hga⟩ := exists_dual_vector'' 𝕜 (T a)
      refine ⟨(a, g), ha, hg, by simpa [hga] using hγa, ?_⟩
      rintro _ ⟨i, rfl⟩
      simpa [M, φ] using congrFun (LinearMap.mem_ker.mp a.property) i
  refine ⟨fun j ↦ (p j).1, fun j ↦ (p j).2, fun j ↦ (hp j).1, fun j ↦ (hp j).2.1,
    fun j ↦ (hp j).2.2.1, fun i j hij ↦ (hp j).2.2.2 (p i) ⟨i, hij, rfl⟩⟩

/-- **Kolmogorov numbers against entropy numbers.** `dₙ(T) ≤ (n + 1) eₙ(T)`. -/
theorem kolmogorovNumber_le_mul_entropyNumber (T : E →L[𝕜] F) (n : ℕ) :
    T.kolmogorovNumber n ≤ (n + 1) * T.entropyNumber n := by
  rw [← NNReal.coe_le_coe]
  refine le_of_forall_lt_imp_le_of_dense fun γ hγ ↦ ?_
  obtain ⟨x, hx, hγx⟩ := exists_flag_of_lt_kolmogorovNumber hγ
  exact_mod_cast le_mul_entropyNumber_of_forall_le_norm_add (Fintype.card_fin _) hx
    fun j w hw ↦ (hγx j w hw).le

/-- **Gelfand numbers against entropy numbers.** `cₙ(T) ≤ (n + 1) eₙ(T)`. -/
theorem gelfandNumber_le_mul_entropyNumber (T : E →L[𝕜] F) (n : ℕ) :
    T.gelfandNumber n ≤ (n + 1) * T.entropyNumber n := by
  rw [← NNReal.coe_le_coe]
  refine le_of_forall_lt_imp_le_of_dense fun γ hγ ↦ ?_
  obtain ⟨x, ρ, hx, hρ, hγx, horth⟩ := exists_flag_of_lt_gelfandNumber hγ
  -- Reversing the order makes the family triangular in the sense of
  -- `le_mul_entropyNumber_of_forall_le_norm_add`: `ρ j` kills every later image.
  push_cast
  refine le_mul_entropyNumber_of_forall_le_norm_add (ι := (Fin (n + 1))ᵒᵈ)
    (x := x ∘ OrderDual.ofDual) (by simp) (fun j ↦ hx _) fun j w hw ↦ ?_
  have hρw : ρ j w = 0 := by
    refine (Submodule.span_le (p := LinearMap.ker (ρ j : F →ₗ[𝕜] 𝕜))).mpr ?_ hw
    rintro _ ⟨k, hk, rfl⟩
    exact horth _ _ hk
  calc γ ≤ ‖ρ j (T (x j))‖ := (hγx j).le
    _ = ‖ρ j (T (x j) + w)‖ := by rw [map_add, hρw, add_zero]
    _ ≤ ‖T (x j) + w‖ := (ρ j).le_of_opNorm_le (hρ j) _ |>.trans_eq (one_mul _)

end ContinuousLinearMap
