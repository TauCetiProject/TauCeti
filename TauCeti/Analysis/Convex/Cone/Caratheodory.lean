/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.LinearAlgebra.LinearIndependent.Basic
import TauCeti.Analysis.Normed.Module.LinearIndependent

/-!
# Carathéodory's theorem for cones, bounded coefficients and relative openness

Let `g k`, for `k` in a finite type `κ`, be finitely many vectors. A nonnegative combination
`w = ∑ k, c k • g k` can be rewritten with nonnegative coefficients `c'`, vanishing wherever `c`
does, such that the vectors `g k` carrying nonzero coefficients are linearly independent
(`TauCeti.exists_nonneg_sum_smul_eq_and_linearIndepOn`). This is Carathéodory's theorem for
cones: if the vectors with nonzero coefficients satisfy a linear relation, subtracting a suitable
multiple of it kills one more coefficient while keeping all of them nonnegative.

Over `ℝ`, with the `g k` in a normed space, coordinates with respect to a linearly independent
family are bounded by a multiple of the norm (`LinearIndepOn.exists_norm_le_mul_norm_sum_smul`),
and there are finitely many subfamilies. Hence there is one constant `M` such that every
nonnegative combination `w` of the `g k` is a nonnegative combination with coefficients at most
`M ‖w‖` (`TauCeti.exists_forall_exists_nonneg_sum_smul_eq_and_le`).

This bound makes a linear map `L` on `ℝ^κ` relatively open on the closed nonnegative orthant
`O = Ici 0`: for `s ∈ O`, the image of every neighbourhood of `s` in `O` is a neighbourhood of
`L s` in the cone `L '' O` (`LinearMap.image_inter_Ici_mem_nhdsWithin`). Indeed, every `t ∈ L '' O`
differs from `L s` by the image of a vector `u - s` that is nonnegative in the coordinates where
`s` vanishes, and by the bound it is the image of such a vector of size `O(‖t - L s‖)`; adding it
to `s` stays in `O` once `t` is close to `L s`. The argument uses that the directions from `s`
into the orthant form a finitely generated cone.

## Main results

* `TauCeti.exists_nonneg_sum_smul_eq_and_linearIndepOn`: Carathéodory's theorem for cones.
* `TauCeti.exists_forall_exists_nonneg_sum_smul_eq_and_le`: nonnegative combinations with
  coefficients bounded by a multiple of the norm.
* `LinearMap.exists_forall_exists_map_eq_sub_and_norm_le`: from a point `s` of the orthant, every
  difference `L u - L s` with `u` in the orthant is the image of a vector of size `O(‖L u - L s‖)`
  pointing into the orthant at `s`.
* `LinearMap.image_inter_Ici_mem_nhdsWithin`: a linear map on `ℝ^κ` is relatively open from the
  nonnegative orthant onto its image.

## References

* A. Schrijver, *Theory of Linear and Integer Programming*, Wiley (1986), Section 7.7
  (Carathéodory's theorem for cones).
-/

public section

open Filter Function Set Topology

namespace TauCeti

variable {κ : Type*} [Fintype κ]

section Field

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

/-- One step of Carathéodory's reduction: if the vectors carrying nonzero coefficients of a
nonnegative combination are linearly dependent, there is another nonnegative combination with the
same value and strictly fewer nonzero coefficients, all among the original ones. -/
private theorem exists_nonneg_sum_smul_eq_card_lt (g : κ → E) {c : κ → 𝕜}
    (hc : 0 ≤ c) (hdep : ¬LinearIndepOn 𝕜 g (support c)) :
    ∃ c₁ : κ → 𝕜, 0 ≤ c₁ ∧ (∀ k, c k = 0 → c₁ k = 0) ∧
      ∑ k, c₁ k • g k = ∑ k, c k • g k ∧
      (Finset.univ.filter fun k ↦ c₁ k ≠ 0).card < (Finset.univ.filter fun k ↦ c k ≠ 0).card := by
  rw [Fintype.linearIndepOn_iff] at hdep
  push Not at hdep
  obtain ⟨a, has, hsum, k₀, hk₀⟩ := hdep
  -- Some relation among these vectors has a positive coefficient.
  obtain ⟨b, hbs, hbsum, hpos⟩ : ∃ b : κ → 𝕜, (∀ k ∉ support c, b k = 0) ∧
      ∑ k, b k • g k = 0 ∧ ∃ k, 0 < b k := by
    rcases hk₀.lt_or_gt with h | h
    · refine ⟨-a, fun k hk ↦ by simp [has k hk], ?_, k₀, by simpa using h⟩
      simp [neg_smul, Finset.sum_neg_distrib, hsum]
    · exact ⟨a, has, hsum, k₀, h⟩
  -- Subtract the largest multiple `τ b` keeping all coefficients nonnegative.
  obtain ⟨k₁, hk₁P, hk₁⟩ := (Finset.univ.filter fun k ↦ 0 < b k).exists_min_image
    (fun k ↦ c k / b k) (by obtain ⟨k, hk⟩ := hpos; exact ⟨k, by simpa using hk⟩)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk₁P hk₁
  set τ := c k₁ / b k₁ with hτ_def
  have hτ : 0 ≤ τ := div_nonneg (hc k₁) hk₁P.le
  have hck₁ : c k₁ ≠ 0 := fun h ↦ hk₁P.ne' (hbs k₁ (by simpa using h))
  refine ⟨c - τ • b, fun k ↦ ?_, fun k hk ↦ ?_, ?_, Finset.card_lt_card ?_⟩
  · simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_nonneg]
    rcases lt_or_ge 0 (b k) with hbk | hbk
    · exact (le_div_iff₀ hbk).1 (hk₁ k hbk)
    · exact (mul_nonpos_of_nonneg_of_nonpos hτ hbk).trans (hc k)
  · simp [hk, hbs k (by simpa using hk)]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, mul_smul,
      Finset.sum_sub_distrib, ← Finset.smul_sum, hbsum, smul_zero, sub_zero]
  · refine Finset.ssubset_iff_of_subset (fun k ↦ ?_) |>.2 ⟨k₁, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hk hck
      simp [hck, hbs k (by simpa using hck)] at hk
    · simpa using hck₁
    · simp [hτ_def, div_mul_cancel₀ _ hk₁P.ne']

/-- **Carathéodory's theorem for cones.** A nonnegative combination `∑ k, c k • g k` of finitely
many vectors is also a nonnegative combination `∑ k, c' k • g k` in which the vectors carrying
nonzero coefficients are linearly independent, with `c' k = 0` wherever `c k = 0`. -/
theorem exists_nonneg_sum_smul_eq_and_linearIndepOn (g : κ → E) {c : κ → 𝕜} (hc : 0 ≤ c) :
    ∃ c' : κ → 𝕜, 0 ≤ c' ∧ (∀ k, c k = 0 → c' k = 0) ∧
      ∑ k, c' k • g k = ∑ k, c k • g k ∧ LinearIndepOn 𝕜 g (support c') := by
  classical
  induction hn : (Finset.univ.filter fun k ↦ c k ≠ 0).card using Nat.strong_induction_on
    generalizing c with
  | _ n ih =>
  by_cases hli : LinearIndepOn 𝕜 g (support c)
  · exact ⟨c, hc, fun _ h ↦ h, rfl, hli⟩
  obtain ⟨c₁, hc₁, hzero₁, hsum₁, hlt⟩ := exists_nonneg_sum_smul_eq_card_lt g hc hli
  obtain ⟨c', hc', hzero', hsum', hli'⟩ := ih _ (hn ▸ hlt) hc₁ rfl
  exact ⟨c', hc', fun k hk ↦ hzero' k (hzero₁ k hk), hsum'.trans hsum₁, hli'⟩

end Field

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Bounded coefficients in a finitely generated cone.** For finitely many vectors `g k` in a
normed space there is a constant `M ≥ 0` such that every nonnegative combination
`w = ∑ k, c k • g k` is also a nonnegative combination `∑ k, c' k • g k` with every `c' k ≤ M ‖w‖`.
-/
theorem exists_forall_exists_nonneg_sum_smul_eq_and_le (g : κ → E) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c : κ → ℝ, 0 ≤ c → ∃ c' : κ → ℝ, 0 ≤ c' ∧
      ∑ k, c' k • g k = ∑ k, c k • g k ∧ ∀ k, c' k ≤ M * ‖∑ k, c k • g k‖ := by
  classical
  -- A bound for each linearly independent subfamily, and the junk value `0` for the others.
  have hbound (s : Set κ) : ∃ K : ℝ, 0 ≤ K ∧ (LinearIndepOn ℝ g s → ∀ a : κ → ℝ,
      (∀ k ∉ s, a k = 0) → ‖a‖ ≤ K * ‖∑ k, a k • g k‖) := by
    by_cases hs : LinearIndepOn ℝ g s
    · obtain ⟨K, hK0, hK⟩ := hs.exists_norm_le_mul_norm_sum_smul
      exact ⟨K, hK0, fun _ ↦ hK⟩
    · exact ⟨0, le_rfl, fun h ↦ absurd h hs⟩
  choose K hK0 hK using hbound
  refine ⟨∑ s : Set κ, K s, Finset.sum_nonneg fun s _ ↦ hK0 s, fun c hc ↦ ?_⟩
  obtain ⟨c', hc', -, hsum, hli⟩ := exists_nonneg_sum_smul_eq_and_linearIndepOn g hc
  refine ⟨c', hc', hsum, fun k ↦ ?_⟩
  calc c' k ≤ ‖c'‖ := (Real.le_norm_self _).trans (norm_le_pi_norm c' k)
    _ ≤ K (support c') * ‖∑ k, c' k • g k‖ :=
      hK _ hli c' fun k hk ↦ by simpa using hk
    _ ≤ (∑ s : Set κ, K s) * ‖∑ k, c k • g k‖ := by
      rw [hsum]
      exact mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun s _ ↦ hK0 s) (Finset.mem_univ _)) (norm_nonneg _)

end Normed

end TauCeti

namespace LinearMap

variable {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Bounded directions into the orthant.** For a linear map `L` on `ℝ^κ` and a point `s` of the
closed orthant, there is a constant `M ≥ 0` such that for every `u` in the orthant, `L u - L s` is
the image of a vector `d` with `‖d‖ ≤ M ‖L u - L s‖` that is nonnegative in every coordinate where
`s` vanishes. -/
theorem exists_forall_exists_map_eq_sub_and_norm_le [Fintype κ] (L : (κ → ℝ) →ₗ[ℝ] E)
    (s : κ → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : κ → ℝ, 0 ≤ u → ∃ d : κ → ℝ, L d = L u - L s ∧
      ‖d‖ ≤ M * ‖L u - L s‖ ∧ ∀ k, s k = 0 → 0 ≤ d k := by
  classical
  -- Generators of the directions from `s` into the orthant: `±` the coordinate vectors, with the
  -- negative ones dropped where `s` vanishes.
  let e : κ → E := fun k ↦ L (Pi.single k 1)
  let g : κ ⊕ κ → E := Sum.elim e fun k ↦ if s k = 0 then 0 else -e k
  have hL (x : κ → ℝ) : L x = ∑ k, x k • e k := by
    rw [L.pi_apply_eq_sum_univ x]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  obtain ⟨M, hM0, hM⟩ := TauCeti.exists_forall_exists_nonneg_sum_smul_eq_and_le g
  refine ⟨M, hM0, fun u hu ↦ ?_⟩
  -- Write `L u - L s = L (u - s)` as a nonnegative combination of the generators.
  set c : κ ⊕ κ → ℝ := Sum.elim (fun k ↦ max (u k - s k) 0) fun k ↦ max (s k - u k) 0
  have hc : 0 ≤ c := fun j ↦ by cases j <;> simp [c]
  have hcsum : ∑ j, c j • g j = L u - L s := by
    rw [← map_sub, hL, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : s k = 0
    · have hu' : 0 ≤ u k := hu k
      simp [c, g, hk, max_eq_left hu']
    · simp only [c, g, Sum.elim_inl, Sum.elim_inr, hk, ite_false, smul_neg, Pi.sub_apply]
      rw [← sub_eq_add_neg, ← sub_smul, ← neg_sub (u k) (s k), max_zero_sub_max_neg_zero_eq_self]
  obtain ⟨c', hc', hsum, hle⟩ := hM c hc
  rw [hcsum] at hsum hle
  -- The bounded coefficients give the vector `d`.
  refine ⟨fun k ↦ c' (Sum.inl k) - if s k = 0 then 0 else c' (Sum.inr k), ?_, ?_, fun k hk ↦ ?_⟩
  · rw [← hsum, hL, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : s k = 0 <;> simp [g, hk, sub_eq_add_neg, add_smul]
  · refine (pi_norm_le_iff_of_nonneg (mul_nonneg hM0 (norm_nonneg _))).2 fun k ↦ ?_
    rw [Real.norm_eq_abs, abs_le]
    have h1 := hle (Sum.inl k)
    have h2 := hle (Sum.inr k)
    have h3 : 0 ≤ c' (Sum.inl k) := hc' _
    have h4 : 0 ≤ c' (Sum.inr k) := hc' _
    by_cases hk : s k = 0 <;> simp only [hk, ite_true, ite_false] <;> constructor <;> linarith
  · simpa [hk] using hc' (Sum.inl k)

/-- **A linear map is relatively open on the nonnegative orthant.** For a linear map `L` on `ℝ^κ`
and a point `s` of the closed orthant `Ici 0`, the image of every neighbourhood of `s` in the
orthant is a neighbourhood of `L s` in the image cone `L '' Ici 0`. -/
theorem image_inter_Ici_mem_nhdsWithin [Finite κ] (L : (κ → ℝ) →ₗ[ℝ] E) {s : κ → ℝ}
    (hs : 0 ≤ s) {N : Set (κ → ℝ)} (hN : N ∈ 𝓝 s) : L '' (N ∩ Ici 0) ∈ 𝓝[L '' Ici 0] (L s) := by
  have := Fintype.ofFinite κ
  obtain ⟨M, -, hM⟩ := L.exists_forall_exists_map_eq_sub_and_norm_le s
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.1 hN
  -- Close to `L s`, the bound `M ‖t - L s‖` is below `ε` and below every positive `s k`.
  have hsmall : ∀ᶠ t in 𝓝 (L s), M * ‖t - L s‖ < ε ∧ ∀ k, s k ≠ 0 → M * ‖t - L s‖ < s k := by
    have ht : Tendsto (fun t ↦ M * ‖t - L s‖) (𝓝 (L s)) (𝓝 0) := by
      simpa using (tendsto_norm_sub_self (L s)).const_mul M
    refine (ht.eventually (gt_mem_nhds hε)).and (eventually_all.2 fun k ↦ ?_)
    by_cases hk : s k = 0
    · exact Eventually.of_forall fun _ h ↦ absurd hk h
    · exact (ht.eventually (gt_mem_nhds (lt_of_le_of_ne (hs k) (Ne.symm hk)))).mono
        fun _ h _ ↦ h
  rw [mem_nhdsWithin_iff_eventually]
  filter_upwards [hsmall] with t ⟨htε, hts⟩ ⟨u, hu, hut⟩
  -- Move from `s` by a small vector `d` with `L d = t - L s`.
  obtain ⟨d, hLd, hd, hd0⟩ := hM u hu
  rw [hut] at hLd hd
  refine ⟨s + d, ⟨hεN ?_, fun k ↦ ?_⟩, by rw [map_add, hLd, add_sub_cancel]⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hd.trans_lt htε
  · simp only [Pi.zero_apply, Pi.add_apply]
    by_cases hk : s k = 0
    · simpa [hk] using hd0 k hk
    · linarith [neg_abs_le (d k), (norm_le_pi_norm d k).trans hd, hts k hk, Real.norm_eq_abs (d k)]

end LinearMap
