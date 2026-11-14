/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Basic
import Mathlib.Analysis.Normed.Lp.lpHolder
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Annulus
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.MeasureTheory.Function.Holder

/-!
# Bony's paraproduct estimates on Besov spaces

Let `Δⱼ` be the inhomogeneous Littlewood–Paley blocks of a bump function `φ` and let
`S_m u = ∑_{k < m} Δₖ u` be the low-frequency cut-off (`TauCeti.BesovSpace.lowPass`). For a gap
`N : ℕ` satisfying `φ.rOut < 2 ^ N * φ.rIn`, the products `S_{j - N} u · Δⱼ v` and
`Δⱼ u · S_{j - N} v` have Fourier transforms supported in dyadic annuli of radii comparable to
`2 ^ j` (`TauCeti.BesovSpace.isVanishingOn_fourier_lowPass_smul_block`,
`TauCeti.BesovSpace.isVanishingOn_fourier_block_smul_lowPass`). Reconstructing Besov norms from
annular series (`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_annulus`) yields
Bahouri–Chemin–Danchin, Theorem 2.82:

* **Boundedness from `L^{p₁}` in the low-frequency factor.** For every `β ∈ ℝ`, `1 ≤ p₁, p₂, r ≤ ∞`
  with `1/r = 1/p₁ + 1/p₂`, and `1 ≤ q ≤ ∞`, the paraproduct `T_f v = ∑ⱼ S_{j - N} f · Δⱼ v` defines
  a bounded bilinear operator `L^{p₁} × B^β_{p₂,q} → B^β_{r,q}`
  (`TauCeti.BesovSpace.paraproductLpCLM`), with norm bounded independently of `p₁, p₂, r, q`. In
  particular, via `TauCeti.BesovSpace.toLpCLM`, any `u ∈ B^α_{p₁,q₁}` with `α > 0` acts boundedly on
  `B^β_{p₂,q}` for every `β ∈ ℝ`. The companion `TauCeti.BesovSpace.paraproductRightLpCLM` handles
  vector-valued low-frequency factors
  `T_g u = ∑ⱼ Δⱼ u · S_{j - N} g : B^α_{p₁,q} × L^{p₂} → B^α_{r,q}`.
* **Negative regularity in the low-frequency factor.** For `α < 0`, every `β ∈ ℝ`,
  `1/r = 1/p₁ + 1/p₂`, and `1/q = 1/q₁ + 1/q₂`, the paraproduct `T_u v = ∑ⱼ S_{j - N} u · Δⱼ v`
  maps `B^α_{p₁,q₁} × B^β_{p₂,q₂}` boundedly into `B^{α + β}_{r,q}`
  (`TauCeti.BesovSpace.paraproductNegCLM`), with norm bounded independently of the integrability
  and fine indices. Indeed the weighted low-pass norms `2^{α m} ‖S_m u‖_{p₁}` are bounded by a
  geometric prefix sum of the weighted block norms of `u`, hence lie in `ℓ^{q₁}`
  (`TauCeti.BesovSpace.exists_lp_lowPass_le_of_neg`), and sequence Hölder multiplication combines
  them with the `ℓ^{q₂}` weighted block norms of `v`. The companion
  `TauCeti.BesovSpace.paraproductRightNegCLM` treats `β < 0` in the right factor.

Specialising all exponents to `∞` gives the Hölder–Zygmund paraproduct bounds
`L^∞ × 𝒞^β → 𝒞^β` and `𝒞^α × 𝒞^β → 𝒞^{α + β}` (`α < 0`, every `β ∈ ℝ`).

## Main declarations

* `TauCeti.BesovSpace.lowPass_one_succ`, `TauCeti.BesovSpace.tendsto_lowPass`,
  `TauCeti.BesovSpace.exists_lp_lowPass_le_of_neg`: the low-frequency cut-offs of `1`, `Lᵖ`
  convergence of `S_m u` for `s > 0`, and the weighted `ℓ^q` majorant of `S_m u` for `s < 0`.
* `TauCeti.BesovSpace.mkContinuousOfHasSum₂`: bundles a bilinear series of `Lʳ` pieces whose sums in
  `𝓢'(E, F)` belong to `B^γ_{r,q}` as a continuous bilinear map.
* `TauCeti.BesovSpace.paraproductLpCLM` and `TauCeti.BesovSpace.paraproductRightLpCLM`: the
  paraproducts `L^{p₁} × B^β_{p₂,q} → B^β_{r,q}` and `B^α_{p₁,q} × L^{p₂} → B^α_{r,q}` for arbitrary
  real smoothness, together with their `HasSum` characterisations and uniform norm bounds.
* `TauCeti.BesovSpace.paraproductNegCLM` and `TauCeti.BesovSpace.paraproductRightNegCLM`: the
  paraproducts `B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^{α + β}_{r,q}` for `α < 0` (respectively `β < 0`),
  together with their `HasSum` characterisations, uniform norm bounds, and symmetry/compatibility
  identities.

## References

* J.-M. Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées
  partielles non linéaires*, Ann. Sci. École Norm. Sup. (4) 14 (1981), 209–246.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Theorem 2.82.
-/

public section

noncomputable section

open MeasureTheory Metric Filter Topology Distribution FourierTransform TemperedDistribution
open scoped ENNReal NNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

section LowPass

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- For every `m ≥ 1`, the low-frequency cut-off `S_m 1` of `1 ∈ B^s_{∞,q}` equals `1 ∈ L^∞`. -/
@[simp]
theorem lowPass_one_succ (m : ℕ) : (1 : BesovSpace ℂ φ s ∞ q).lowPass (m + 1) = 1 := by
  induction m with
  | zero => rw [lowPass_succ, lowPass_zero_right, block_one_zero, zero_add]
  | succ m ih => rw [lowPass_succ, ih, block_one_succ, add_zero]

/-- The low-frequency cut-off `S_m 1` of `1 ∈ B^s_{∞,q}` is `0` at `m = 0` and `1` for `m ≥ 1`. -/
theorem lowPass_one (m : ℕ) :
    (1 : BesovSpace ℂ φ s ∞ q).lowPass m = if m = 0 then 0 else 1 := by
  rcases m with _ | m <;> simp

/-- For `s > 0`, the low-frequency cut-offs `S_m u` converge in `Lᵖ` to `toLpCLM F φ p q hs u`. -/
theorem tendsto_lowPass [Fact (1 ≤ q)] (hs : 0 < s) (u : BesovSpace F φ s p q) :
    Tendsto u.lowPass atTop (𝓝 (toLpCLM F φ p q hs u)) :=
  (hasSum_block hs u).tendsto_sum_nat.congr fun m ↦ (u.lowPass_eq_sum m).symm

/-- For `s > 0`, the low-frequency cut-offs `S_m u` are bounded in `Lᵖ` uniformly in `m`. -/
theorem norm_lowPass_le_of_pos [Fact (1 ≤ q)] (hs : 0 < s) (u : BesovSpace F φ s p q) (m : ℕ) :
    ‖u.lowPass m‖ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * (1 - 2 ^ (-s))⁻¹ * ‖u‖ := by
  calc ‖u.lowPass m‖ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * ‖toLpCLM F φ p q hs u‖ :=
        u.norm_lowPass_le_of_toDistr_eq (coe_toLpCLM hs u).symm m
    _ ≤ (∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖) * ((1 - 2 ^ (-s))⁻¹ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_toLpCLM_apply_le hs u)
          (MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _)
    _ = _ := by ring

/-- **Weighted `ℓ^q` bound for the low-frequency cut-offs at negative regularity.** For `s < 0` and
`u ∈ B^s_{p,q}`, the sequence `2^{s m} ‖S_m u‖_p` is bounded pointwise by a nonnegative sequence
`a ∈ ℓ^q` of norm at most `(2^{-s} - 1)⁻¹ ‖u‖`. -/
theorem exists_lp_lowPass_le_of_neg [Fact (1 ≤ q)] (hs : s < 0) (u : BesovSpace F φ s p q) :
    ∃ a : lp (fun _ : ℕ ↦ ℝ) q, (∀ m, 0 ≤ a m) ∧
      (∀ m : ℕ, 2 ^ (s * m) * ‖u.lowPass m‖ ≤ a m) ∧ ‖a‖ ≤ (2 ^ (-s) - 1)⁻¹ * ‖u‖ := by
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set b : lp (fun _ : ℕ ↦ ℝ) q := ⟨fun k ↦ ‖u.weightedBlocks k‖, (lp.memℓp _).norm⟩
  have hb : ‖b‖ ≤ ‖u‖ := by
    rw [← norm_weightedBlocks]
    exact lp.norm_mono hq fun k ↦ (norm_norm _).le
  have hr0 : 0 ≤ (2 : ℝ) ^ s := by positivity
  have hr1 : (2 : ℝ) ^ s < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two hs
  obtain ⟨a, ha, han⟩ := lp.exists_forall_eq_sum_pow_smul_and_norm_le b hr0 hr1
  have hratio : (2 : ℝ) ^ s * (1 - 2 ^ s)⁻¹ = (2 ^ (-s) - 1)⁻¹ := by
    have hmul : (2 : ℝ) ^ (-s) * 2 ^ s = 1 := by rw [← Real.rpow_add two_pos]; simp
    refine eq_inv_of_mul_eq_one_left ?_
    calc (2 : ℝ) ^ s * (1 - 2 ^ s)⁻¹ * (2 ^ (-s) - 1)
        = (2 ^ s * 2 ^ (-s) - 2 ^ s) * (1 - 2 ^ s)⁻¹ := by ring
      _ = (1 - 2 ^ s) * (1 - 2 ^ s)⁻¹ := by rw [mul_comm ((2 : ℝ) ^ s), hmul]
      _ = 1 := mul_inv_cancel₀ (sub_pos.2 hr1).ne'
  refine ⟨a, fun m ↦ ?_, fun m ↦ ?_, ?_⟩
  · rw [ha m]
    exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (pow_nonneg hr0 _) (norm_nonneg _)
  · rw [ha m, lowPass_eq_sum]
    refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkm : k ≤ m := (Finset.mem_range.1 hk).le
    have hexp : (2 : ℝ) ^ (s * m) = (2 ^ s) ^ (m - k) * 2 ^ (s * k) := by
      rw [← Real.rpow_mul_natCast zero_le_two, ← Real.rpow_add two_pos, ← mul_add]
      congr 2
      exact_mod_cast (Nat.sub_add_cancel hkm).symm
    rw [smul_eq_mul, hexp, mul_assoc]
    exact le_of_eq (congrArg _ (u.norm_weightedBlocks_apply k).symm)
  · calc ‖a‖ ≤ 2 ^ s * (1 - 2 ^ s)⁻¹ * ‖b‖ := han
      _ ≤ 2 ^ s * (1 - 2 ^ s)⁻¹ * ‖u‖ := by gcongr
      _ = (2 ^ (-s) - 1)⁻¹ * ‖u‖ := by rw [hratio]

/-- Shifted version of `exists_lp_lowPass_le_of_neg` for `S_{j - N} u`: for `s < 0`, the sequence
`2^{s j} ‖S_{j - N} u‖_p` is bounded by an `ℓ^q` sequence of norm at most `(2^{-s} - 1)⁻¹ ‖u‖`. -/
private theorem exists_lp_lowPass_sub_le_of_neg [Fact (1 ≤ q)] (hs : s < 0) (N : ℕ)
    (u : BesovSpace F φ s p q) :
    ∃ a : lp (fun _ : ℕ ↦ ℝ) q,
      (∀ j : ℕ, 2 ^ (s * j) * ‖u.lowPass (j - N)‖ ≤ a j) ∧ ‖a‖ ≤ (2 ^ (-s) - 1)⁻¹ * ‖u‖ := by
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  obtain ⟨a₀, _, ha₀, ha₀_norm⟩ := exists_lp_lowPass_le_of_neg hs u
  have hinj : {j : ℕ | N ≤ j}.InjOn fun j ↦ j - N := fun _ hj _ hj' h ↦ tsub_inj_left hj hj' h
  set a : lp (fun _ : ℕ ↦ ℝ) q :=
    ⟨{j | N ≤ j}.indicator (a₀ ∘ fun j ↦ j - N), (lp.memℓp a₀).indicator_comp hinj⟩
  refine ⟨a, fun j ↦ ?_, (lp.norm_le_of_forall_eq_indicator_comp hq hinj fun _ ↦ rfl).trans
    ha₀_norm⟩
  by_cases hj : N ≤ j
  · have ha_eq : a j = a₀ (j - N) := Set.indicator_of_mem hj _
    have hexp : (2 : ℝ) ^ (s * j) = 2 ^ (s * N) * 2 ^ (s * (j - N : ℕ)) := by
      rw [← Real.rpow_add two_pos, ← mul_add]
      congr 2
      exact_mod_cast (Nat.add_sub_of_le hj).symm
    have hle1 : (2 : ℝ) ^ (s * N) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos one_le_two
        (mul_nonpos_of_nonpos_of_nonneg hs.le N.cast_nonneg)
    rw [ha_eq, hexp, mul_assoc]
    exact (mul_le_of_le_one_left (by positivity) hle1).trans (ha₀ (j - N))
  · have ha_eq : a j = 0 := Set.indicator_of_notMem hj _
    rw [ha_eq, Nat.sub_eq_zero_of_le (le_of_not_ge hj), lowPass_zero_right, norm_zero, mul_zero]

end LowPass

section Helpers

/-- Bundles a bilinear series of `Lʳ` pieces whose sums in `𝓢'(E, F)` belong to `B^γ_{r,q}` with a
bilinear norm bound as a continuous bilinear map into `B^γ_{r,q}`. -/
def mkContinuousOfHasSum₂ {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] {φ : ContDiffBump (0 : E)} {γ : ℝ} {r q : ℝ≥0∞}
    [Fact (1 ≤ r)] [Fact (1 ≤ q)] (term : ℕ → X → Y → Lp F r (volume : Measure E))
    (hadd₁ : ∀ j x₁ x₂ y, term j (x₁ + x₂) y = term j x₁ y + term j x₂ y)
    (hsmul₁ : ∀ j (c : ℂ) x y, term j (c • x) y = c • term j x y)
    (hadd₂ : ∀ j x y₁ y₂, term j x (y₁ + y₂) = term j x y₁ + term j x y₂)
    (hsmul₂ : ∀ j (c : ℂ) x y, term j x (c • y) = c • term j x y)
    {C : ℝ} (hC : ∀ x y, ∃ w : BesovSpace F φ γ r q,
      HasSum (fun j ↦ (term j x y : 𝓢'(E, F))) w.toDistr ∧ ‖w‖ ≤ C * ‖x‖ * ‖y‖) :
    X →L[ℂ] Y →L[ℂ] BesovSpace F φ γ r q :=
  (LinearMap.mk₂ ℂ (fun x y ↦ (hC x y).choose)
    (fun x₁ x₂ y ↦ ext <| (hC (x₁ + x₂) y).choose_spec.1.unique <| by
      simpa only [hadd₁, Lp.toTemperedDistribution_add, toDistr_add] using
        (hC x₁ y).choose_spec.1.add (hC x₂ y).choose_spec.1)
    (fun c x y ↦ ext <| (hC (c • x) y).choose_spec.1.unique <| by
      simpa only [hsmul₁, Lp.toTemperedDistribution_smul, toDistr_smul] using
        (hC x y).choose_spec.1.const_smul c)
    (fun x y₁ y₂ ↦ ext <| (hC x (y₁ + y₂)).choose_spec.1.unique <| by
      simpa only [hadd₂, Lp.toTemperedDistribution_add, toDistr_add] using
        (hC x y₁).choose_spec.1.add (hC x y₂).choose_spec.1)
    (fun c x y ↦ ext <| (hC x (c • y)).choose_spec.1.unique <| by
      simpa only [hsmul₂, Lp.toTemperedDistribution_smul, toDistr_smul] using
        (hC x y).choose_spec.1.const_smul c)).mkContinuous₂ C
    fun x y ↦ (hC x y).choose_spec.2

/-- Applying `mkContinuousOfHasSum₂` returns the chosen Besov limit `(hC x y).choose`. -/
@[simp]
theorem mkContinuousOfHasSum₂_apply {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] {φ : ContDiffBump (0 : E)}
    {γ : ℝ} {r q : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ q)]
    (term : ℕ → X → Y → Lp F r (volume : Measure E))
    (hadd₁ : ∀ j x₁ x₂ y, term j (x₁ + x₂) y = term j x₁ y + term j x₂ y)
    (hsmul₁ : ∀ j (c : ℂ) x y, term j (c • x) y = c • term j x y)
    (hadd₂ : ∀ j x y₁ y₂, term j x (y₁ + y₂) = term j x y₁ + term j x y₂)
    (hsmul₂ : ∀ j (c : ℂ) x y, term j x (c • y) = c • term j x y)
    {C : ℝ} (hC : ∀ x y, ∃ w : BesovSpace F φ γ r q,
      HasSum (fun j ↦ (term j x y : 𝓢'(E, F))) w.toDistr ∧ ‖w‖ ≤ C * ‖x‖ * ‖y‖)
    (x : X) (y : Y) :
    mkContinuousOfHasSum₂ term hadd₁ hsmul₁ hadd₂ hsmul₂ hC x y = (hC x y).choose :=
  (rfl)

/-- Operator-norm bound for `mkContinuousOfHasSum₂`. -/
theorem norm_mkContinuousOfHasSum₂_le {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y] {φ : ContDiffBump (0 : E)}
    {γ : ℝ} {r q : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ q)]
    (term : ℕ → X → Y → Lp F r (volume : Measure E))
    (hadd₁ : ∀ j x₁ x₂ y, term j (x₁ + x₂) y = term j x₁ y + term j x₂ y)
    (hsmul₁ : ∀ j (c : ℂ) x y, term j (c • x) y = c • term j x y)
    (hadd₂ : ∀ j x y₁ y₂, term j x (y₁ + y₂) = term j x y₁ + term j x y₂)
    (hsmul₂ : ∀ j (c : ℂ) x y, term j x (c • y) = c • term j x y)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ x y, ∃ w : BesovSpace F φ γ r q,
      HasSum (fun j ↦ (term j x y : 𝓢'(E, F))) w.toDistr ∧ ‖w‖ ≤ C * ‖x‖ * ‖y‖) :
    ‖mkContinuousOfHasSum₂ term hadd₁ hsmul₁ hadd₂ hsmul₂ hC‖ ≤ C :=
  LinearMap.mkContinuous₂_norm_le _ hC0 _

/-- Specialises `exists_hasSum_toDistr_and_norm_le_of_annulus` to the dyadic annuli supporting the
terms of Bony's paraproducts when `φ.rOut < 2 ^ N * φ.rIn`. -/
private theorem exists_hasSum_of_paraproduct_annulus {φ : ContDiffBump (0 : E)} {N : ℕ}
    (s : ℝ) (hN : φ.rOut < 2 ^ N * φ.rIn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r q : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ q)]
      (g : ℕ → Lp F r (volume : Measure E)) (w : lp (fun _ : ℕ ↦ ℝ) q),
      (∀ j : ℕ, IsVanishingOn (𝓕 (g j : 𝓢'(E, F)) : 𝓢'(E, F))
        (closedBall 0 (2 ^ j * (2 * φ.rOut)) \
          ball 0 (2 ^ j * ((φ.rIn - φ.rOut / 2 ^ N) / 2)))ᶜ) →
      (∀ j : ℕ, 2 ^ (s * j) * ‖g j‖ ≤ w j) →
      ∃ y : BesovSpace F φ s r q,
        HasSum (fun j ↦ (g j : 𝓢'(E, F))) y.toDistr ∧ ‖y‖ ≤ C * ‖w‖ := by
  have ha : 0 < (φ.rIn - φ.rOut / 2 ^ N) / 2 := by
    have hdiv : φ.rOut / 2 ^ N < φ.rIn := (div_lt_iff₀ (by positivity)).2 (by linarith)
    linarith
  obtain ⟨C, hC⟩ := exists_hasSum_toDistr_and_norm_le_of_annulus (F := F) φ s ha (2 * φ.rOut)
  refine ⟨max C 0, le_max_right _ _, fun {r q} _ _ g w hspec hw ↦ ?_⟩
  have hsub (j : ℕ) : ball (0 : E) (2 ^ j * ((φ.rIn - φ.rOut / 2 ^ N) / 2)) ⊆
      (closedBall 0 (2 ^ j * (2 * φ.rOut)) \
        ball 0 (2 ^ j * ((φ.rIn - φ.rOut / 2 ^ N) / 2)))ᶜ := fun _ hξ h ↦ h.2 hξ
  obtain ⟨y, hy, hyn⟩ := hC g w
    (fun j ↦ (hspec j).mono (Set.compl_subset_compl.2 Set.sdiff_subset))
    (fun j _ ↦ (hspec j).mono (hsub j)) hw
  exact ⟨y, hy, hyn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w))⟩

end Helpers

section ParaproductLp

variable {φ : ContDiffBump (0 : E)} {N : ℕ} {α β : ℝ} {p₁ p₂ r q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [Fact (1 ≤ q)] [p₁.HolderTriple p₂ r]

/-- Uniform existence and Besov bound for the paraproduct `T_f v = ∑ⱼ S_{j - N} f · Δⱼ v` with
`f ∈ L^{p₁}` and `v ∈ B^β_{p₂,q}`. -/
private theorem exists_paraproductLp (hN : φ.rOut < 2 ^ N * φ.rIn) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q)] [p₁.HolderTriple p₂ r]
      (f : Lp ℂ p₁ (volume : Measure E)) (v : BesovSpace F φ β p₂ q),
      ∃ y : BesovSpace F φ β r q,
        HasSum (fun j ↦ (((ofLpCLM ℂ φ p₁ f).lowPass (j - N) • v.block j :
          Lp F r (volume : Measure E)) : 𝓢'(E, F))) y.toDistr ∧
        ‖y‖ ≤ C * ‖f‖ * ‖v‖ := by
  obtain ⟨C₀, hC₀, hann⟩ := exists_hasSum_of_paraproduct_annulus (F := F) β hN
  set K₀ : ℝ := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  have : 0 ≤ K₀ := MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _
  refine ⟨C₀ * K₀, by positivity, fun {p₁ p₂ r q} _ _ _ _ _ f v ↦ ?_⟩
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set b : lp (fun _ : ℕ ↦ ℝ) q := ⟨fun j ↦ ‖v.weightedBlocks j‖, (lp.memℓp _).norm⟩
  -- Anonymous `lp` elements coerce through `Subtype.val` and have no simp lemma for evaluation.
  have hb_eq (j : ℕ) : b j = ‖v.weightedBlocks j‖ := rfl
  have hb : ‖b‖ ≤ ‖v‖ := by
    rw [← norm_weightedBlocks]
    exact lp.norm_mono hq fun j ↦ (norm_norm _).le
  obtain ⟨y, hy, hyn⟩ := hann (fun j ↦ (ofLpCLM ℂ φ p₁ f).lowPass (j - N) • v.block j)
    ((K₀ * ‖f‖) • b)
    (fun j ↦ isVanishingOn_fourier_lowPass_smul_block N j (ofLpCLM ℂ φ p₁ f) v) fun j ↦ by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hb_eq, v.norm_weightedBlocks_apply]
      calc 2 ^ (β * j) * ‖(ofLpCLM ℂ φ p₁ f).lowPass (j - N) • v.block j‖
          ≤ 2 ^ (β * j) * (‖(ofLpCLM ℂ φ p₁ f).lowPass (j - N)‖ * ‖v.block j‖) :=
            mul_le_mul_of_nonneg_left (Lp.norm_smul_le _ _) (by positivity)
        _ ≤ 2 ^ (β * j) * (K₀ * ‖f‖ * ‖v.block j‖) := by
            gcongr
            exact (ofLpCLM ℂ φ p₁ f).norm_lowPass_le_of_toDistr_eq (toDistr_ofLpCLM f) (j - N)
        _ = K₀ * ‖f‖ * (2 ^ (β * j) * ‖v.block j‖) := by ring
  refine ⟨y, hy, hyn.trans ?_⟩
  calc C₀ * ‖(K₀ * ‖f‖) • b‖ = C₀ * (K₀ * ‖f‖ * ‖b‖) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
    _ ≤ C₀ * (K₀ * ‖f‖ * ‖v‖) := by gcongr
    _ = C₀ * K₀ * ‖f‖ * ‖v‖ := by ring

variable (r) in
/-- **Bony's paraproduct with an `L^{p₁}` low-frequency factor** (Bahouri–Chemin–Danchin,
Theorem 2.82). For `φ.rOut < 2 ^ N * φ.rIn` and any real smoothness `β`, the series
`T_f v = ∑ⱼ S_{j - N} f · Δⱼ v` defines a continuous bilinear map
`L^{p₁} × B^β_{p₂,q} → B^β_{r,q}` whenever `1/r = 1/p₁ + 1/p₂`, with operator norm bounded
independently of `p₁, p₂, r, q`. -/
def paraproductLpCLM (hN : φ.rOut < 2 ^ N * φ.rIn) :
    Lp ℂ p₁ (volume : Measure E) →L[ℂ] BesovSpace F φ β p₂ q →L[ℂ] BesovSpace F φ β r q :=
  mkContinuousOfHasSum₂ (fun j f v ↦ (ofLpCLM ℂ φ p₁ f).lowPass (j - N) • v.block j)
    (fun _ _ _ _ ↦ by simp [Lp.smul_add])
    (fun _ _ _ _ ↦ by simp [Lp.smul_assoc])
    (fun _ _ _ _ ↦ by simp [block_add, Lp.add_smul])
    (fun _ _ _ _ ↦ by simp [block_smul, ← Lp.smul_comm])
    (fun f v ↦ (exists_paraproductLp (F := F) hN β).choose_spec.2 f v)

/-- The tempered distribution of `paraproductLpCLM r hN f v` is the sum of the series
`∑ⱼ S_{j - N} f · Δⱼ v`. -/
theorem hasSum_paraproductLpCLM (hN : φ.rOut < 2 ^ N * φ.rIn)
    (f : Lp ℂ p₁ (volume : Measure E)) (v : BesovSpace F φ β p₂ q) :
    HasSum (fun j ↦ (((ofLpCLM ℂ φ p₁ f).lowPass (j - N) • v.block j :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) (paraproductLpCLM r hN f v).toDistr :=
  ((exists_paraproductLp (F := F) hN β).choose_spec.2 f v).choose_spec.1

/-- When `f ∈ L^{p₁}` represents `u ∈ B^α_{p₁,q₁}`, `paraproductLpCLM r hN f v` sums
`S_{j - N} u · Δⱼ v`. -/
theorem hasSum_paraproductLpCLM_of_toDistr_eq {q₁ : ℝ≥0∞} (hN : φ.rOut < 2 ^ N * φ.rIn)
    {u : BesovSpace ℂ φ α p₁ q₁} {f : Lp ℂ p₁ (volume : Measure E)} (huf : u.toDistr = f)
    (v : BesovSpace F φ β p₂ q) :
    HasSum (fun j ↦ ((u.lowPass (j - N) • v.block j :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) (paraproductLpCLM r hN f v).toDistr := by
  simpa only [lowPass_eq_of_toDistr_eq (huf.trans (toDistr_ofLpCLM f).symm)] using
    hasSum_paraproductLpCLM (r := r) hN f v

/-- **Uniform operator norm bound for `paraproductLpCLM`.** The operator norm of
`paraproductLpCLM` is bounded by a constant depending only on `E`, `F`, `φ`, `N` and `β`,
independently of `p₁, p₂, r, q`. -/
theorem exists_norm_paraproductLpCLM_le (hN : φ.rOut < 2 ^ N * φ.rIn) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q)] [p₁.HolderTriple p₂ r],
      ‖paraproductLpCLM (F := F) (β := β) (p₁ := p₁) (p₂ := p₂) (q := q) r hN‖ ≤ C :=
  ⟨_, (exists_paraproductLp (F := F) hN β).choose_spec.1,
    fun {_ _ _ _} _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _
      (exists_paraproductLp (F := F) hN β).choose_spec.1 _⟩

/-- Uniform existence and Besov bound for the right paraproduct `T_g u = ∑ⱼ Δⱼ u · S_{j - N} g`
with `u ∈ B^α_{p₁,q}` and `g ∈ L^{p₂}`. -/
private theorem exists_paraproductRightLp (hN : φ.rOut < 2 ^ N * φ.rIn) (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q)] [p₁.HolderTriple p₂ r]
      (u : BesovSpace ℂ φ α p₁ q) (g : Lp F p₂ (volume : Measure E)),
      ∃ y : BesovSpace F φ α r q,
        HasSum (fun j ↦ ((u.block j • (ofLpCLM F φ p₂ g).lowPass (j - N) :
          Lp F r (volume : Measure E)) : 𝓢'(E, F))) y.toDistr ∧
        ‖y‖ ≤ C * ‖u‖ * ‖g‖ := by
  obtain ⟨C₀, hC₀, hann⟩ := exists_hasSum_of_paraproduct_annulus (F := F) α hN
  set K₀ : ℝ := ∫ x, ‖𝓕⁻ (fun ξ ↦ (φ ξ : ℂ)) x‖
  have : 0 ≤ K₀ := MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _
  refine ⟨C₀ * K₀, by positivity, fun {p₁ p₂ r q} _ _ _ _ _ u g ↦ ?_⟩
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set a : lp (fun _ : ℕ ↦ ℝ) q := ⟨fun j ↦ ‖u.weightedBlocks j‖, (lp.memℓp _).norm⟩
  -- Anonymous `lp` elements coerce through `Subtype.val` and have no simp lemma for evaluation.
  have ha_eq (j : ℕ) : a j = ‖u.weightedBlocks j‖ := rfl
  have ha : ‖a‖ ≤ ‖u‖ := by
    rw [← norm_weightedBlocks]
    exact lp.norm_mono hq fun j ↦ (norm_norm _).le
  obtain ⟨y, hy, hyn⟩ := hann (fun j ↦ u.block j • (ofLpCLM F φ p₂ g).lowPass (j - N))
    ((K₀ * ‖g‖) • a)
    (fun j ↦ isVanishingOn_fourier_block_smul_lowPass N j u (ofLpCLM F φ p₂ g)) fun j ↦ by
      rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ha_eq, u.norm_weightedBlocks_apply]
      calc 2 ^ (α * j) * ‖u.block j • (ofLpCLM F φ p₂ g).lowPass (j - N)‖
          ≤ 2 ^ (α * j) * (‖u.block j‖ * ‖(ofLpCLM F φ p₂ g).lowPass (j - N)‖) :=
            mul_le_mul_of_nonneg_left (Lp.norm_smul_le _ _) (by positivity)
        _ ≤ 2 ^ (α * j) * (‖u.block j‖ * (K₀ * ‖g‖)) := by
            gcongr
            exact (ofLpCLM F φ p₂ g).norm_lowPass_le_of_toDistr_eq (toDistr_ofLpCLM g) (j - N)
        _ = K₀ * ‖g‖ * (2 ^ (α * j) * ‖u.block j‖) := by ring
  refine ⟨y, hy, hyn.trans ?_⟩
  calc C₀ * ‖(K₀ * ‖g‖) • a‖ = C₀ * (K₀ * ‖g‖ * ‖a‖) := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_assoc]
    _ ≤ C₀ * (K₀ * ‖g‖ * ‖u‖) := by gcongr
    _ = C₀ * K₀ * ‖u‖ * ‖g‖ := by ring

variable (r) in
/-- **Bony's right paraproduct with an `L^{p₂}` low-frequency factor** (Bahouri–Chemin–Danchin,
Theorem 2.82). For `φ.rOut < 2 ^ N * φ.rIn` and any real smoothness `α`, the series
`T_g u = ∑ⱼ Δⱼ u · S_{j - N} g` defines a continuous bilinear map
`B^α_{p₁,q} × L^{p₂} → B^α_{r,q}` whenever `1/r = 1/p₁ + 1/p₂`, with operator norm bounded
independently of `p₁, p₂, r, q`. -/
def paraproductRightLpCLM (hN : φ.rOut < 2 ^ N * φ.rIn) :
    BesovSpace ℂ φ α p₁ q →L[ℂ] Lp F p₂ (volume : Measure E) →L[ℂ] BesovSpace F φ α r q :=
  mkContinuousOfHasSum₂ (fun j u g ↦ u.block j • (ofLpCLM F φ p₂ g).lowPass (j - N))
    (fun _ _ _ _ ↦ by simp [block_add, Lp.smul_add])
    (fun _ _ _ _ ↦ by simp [block_smul, Lp.smul_assoc])
    (fun _ _ _ _ ↦ by simp [Lp.add_smul])
    (fun _ _ _ _ ↦ by simp [← Lp.smul_comm])
    (fun u g ↦ (exists_paraproductRightLp (F := F) hN α).choose_spec.2 u g)

/-- The tempered distribution of `paraproductRightLpCLM r hN u g` is the sum of the series
`∑ⱼ Δⱼ u · S_{j - N} g`. -/
theorem hasSum_paraproductRightLpCLM (hN : φ.rOut < 2 ^ N * φ.rIn)
    (u : BesovSpace ℂ φ α p₁ q) (g : Lp F p₂ (volume : Measure E)) :
    HasSum (fun j ↦ ((u.block j • (ofLpCLM F φ p₂ g).lowPass (j - N) :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) (paraproductRightLpCLM r hN u g).toDistr :=
  ((exists_paraproductRightLp (F := F) hN α).choose_spec.2 u g).choose_spec.1

/-- When `g ∈ L^{p₂}` represents `v ∈ B^β_{p₂,q₂}`, `paraproductRightLpCLM r hN u g` sums
`Δⱼ u · S_{j - N} v`. -/
theorem hasSum_paraproductRightLpCLM_of_toDistr_eq {q₂ : ℝ≥0∞} (hN : φ.rOut < 2 ^ N * φ.rIn)
    (u : BesovSpace ℂ φ α p₁ q) {v : BesovSpace F φ β p₂ q₂} {g : Lp F p₂ (volume : Measure E)}
    (hvg : v.toDistr = g) :
    HasSum (fun j ↦ ((u.block j • v.lowPass (j - N) :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) (paraproductRightLpCLM r hN u g).toDistr := by
  simpa only [lowPass_eq_of_toDistr_eq (hvg.trans (toDistr_ofLpCLM g).symm)] using
    hasSum_paraproductRightLpCLM (r := r) hN u g

/-- **Uniform operator norm bound for `paraproductRightLpCLM`.** -/
theorem exists_norm_paraproductRightLpCLM_le (hN : φ.rOut < 2 ^ N * φ.rIn) (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q : ℝ≥0∞} [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)]
      [Fact (1 ≤ q)] [p₁.HolderTriple p₂ r],
      ‖paraproductRightLpCLM (F := F) (α := α) (p₁ := p₁) (p₂ := p₂) (q := q) r hN‖ ≤ C :=
  ⟨_, (exists_paraproductRightLp (F := F) hN α).choose_spec.1,
    fun {_ _ _ _} _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _
      (exists_paraproductRightLp (F := F) hN α).choose_spec.1 _⟩

/-- For scalar-valued factors (`F = ℂ`), the right paraproduct `T_g u` coincides with the left
paraproduct `T_g u` defined by `paraproductLpCLM`. -/
theorem paraproductRightLpCLM_eq_paraproductLpCLM (hN : φ.rOut < 2 ^ N * φ.rIn)
    (u : BesovSpace ℂ φ α p₁ q) (g : Lp ℂ p₂ (volume : Measure E)) :
    paraproductRightLpCLM r hN u g = paraproductLpCLM r hN g u :=
  ext <| (hasSum_paraproductRightLpCLM (r := r) hN u g).unique <|
    (hasSum_paraproductLpCLM (r := r) hN g u).congr_fun fun _ ↦
      congrArg _ (Lp.lpSMul_comm _ _)

end ParaproductLp

section ParaproductNeg

variable {φ : ContDiffBump (0 : E)} {N : ℕ} {α β : ℝ} {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
  [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q]

/-- Uniform existence and Besov bound for `T_u v = ∑ⱼ S_{j - N} u · Δⱼ v` when `α < 0`. -/
private theorem exists_paraproductNeg (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q]
      (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂),
      ∃ y : BesovSpace F φ (α + β) r q,
        HasSum (fun j ↦ ((u.lowPass (j - N) • v.block j :
          Lp F r (volume : Measure E)) : 𝓢'(E, F))) y.toDistr ∧
        ‖y‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C₀, hC₀, hann⟩ := exists_hasSum_of_paraproduct_annulus (F := F) (α + β) hN
  have hden : 0 ≤ ((2 : ℝ) ^ (-α) - 1)⁻¹ :=
    inv_nonneg.2 (sub_nonneg.2 (Real.one_lt_rpow one_lt_two (neg_pos.2 hα)).le)
  refine ⟨C₀ * (2 ^ (-α) - 1)⁻¹, by positivity,
    fun {p₁ p₂ r q₁ q₂ q} _ _ _ _ _ _ _ _ u v ↦ ?_⟩
  obtain ⟨a, ha, han⟩ := exists_lp_lowPass_sub_le_of_neg hα N u
  have hq₂ : q₂ ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set b : lp (fun _ : ℕ ↦ ℝ) q₂ := ⟨fun j ↦ ‖v.weightedBlocks j‖, (lp.memℓp _).norm⟩
  -- Anonymous `lp` elements coerce through `Subtype.val` and have no simp lemma for evaluation.
  have hb_eq (j : ℕ) : b j = ‖v.weightedBlocks j‖ := rfl
  have hb : ‖b‖ ≤ ‖v‖ := by
    rw [← norm_weightedBlocks]
    exact lp.norm_mono hq₂ fun j ↦ (norm_norm _).le
  have hB : ∀ _ : ℕ, ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ (1 : ℝ≥0) := fun _ ↦ by simp
  set B := lp.holderL (p := q₁) (q := q₂) q (fun _ ↦ ContinuousLinearMap.mul ℝ ℝ) hB
  set w : lp (fun _ : ℕ ↦ ℝ) q := B a b
  have hw (j : ℕ) : w j = a j * b j := rfl
  have hwn : ‖w‖ ≤ ‖a‖ * ‖b‖ := by
    simpa [w] using
      B.le_of_opNorm₂_le_of_le (lp.norm_holderL_le (p := q₁) (q := q₂) q _ hB) le_rfl le_rfl
  obtain ⟨y, hy, hyn⟩ := hann (fun j ↦ u.lowPass (j - N) • v.block j) w
    (fun j ↦ isVanishingOn_fourier_lowPass_smul_block N j u v) fun j ↦ by
      rw [hw j, hb_eq, v.norm_weightedBlocks_apply]
      calc 2 ^ ((α + β) * j) * ‖u.lowPass (j - N) • v.block j‖
          ≤ 2 ^ ((α + β) * j) * (‖u.lowPass (j - N)‖ * ‖v.block j‖) :=
            mul_le_mul_of_nonneg_left (Lp.norm_smul_le _ _) (by positivity)
        _ = (2 ^ (α * j) * ‖u.lowPass (j - N)‖) * (2 ^ (β * j) * ‖v.block j‖) := by
            rw [add_mul, Real.rpow_add two_pos]; ring
        _ ≤ a j * (2 ^ (β * j) * ‖v.block j‖) :=
            mul_le_mul_of_nonneg_right (ha j) (by positivity)
  refine ⟨y, hy, hyn.trans ?_⟩
  calc C₀ * ‖w‖ ≤ C₀ * (‖a‖ * ‖b‖) := by gcongr
    _ ≤ C₀ * (((2 ^ (-α) - 1)⁻¹ * ‖u‖) * ‖v‖) := by gcongr
    _ = C₀ * (2 ^ (-α) - 1)⁻¹ * ‖u‖ * ‖v‖ := by ring

variable (r q) in
/-- **Bony's paraproduct at negative regularity** (Bahouri–Chemin–Danchin, Theorem 2.82). For
`φ.rOut < 2 ^ N * φ.rIn`, `α < 0`, any `β ∈ ℝ`, `1/r = 1/p₁ + 1/p₂`, and `1/q = 1/q₁ + 1/q₂`,
the series `T_u v = ∑ⱼ S_{j - N} u · Δⱼ v` defines a continuous bilinear map
`B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^{α + β}_{r,q}`, with operator norm bounded independently of
`p₁, p₂, r, q₁, q₂, q`. -/
def paraproductNegCLM (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0) :
    BesovSpace ℂ φ α p₁ q₁ →L[ℂ] BesovSpace F φ β p₂ q₂ →L[ℂ] BesovSpace F φ (α + β) r q :=
  mkContinuousOfHasSum₂ (fun j u v ↦ u.lowPass (j - N) • v.block j)
    (fun _ _ _ _ ↦ by simp [Lp.smul_add])
    (fun _ _ _ _ ↦ by simp [Lp.smul_assoc])
    (fun _ _ _ _ ↦ by simp [block_add, Lp.add_smul])
    (fun _ _ _ _ ↦ by simp [block_smul, ← Lp.smul_comm])
    (fun u v ↦ (exists_paraproductNeg (F := F) hN hα β).choose_spec.2 u v)

/-- The tempered distribution of `paraproductNegCLM r q hN hα u v` is the sum of the series
`∑ⱼ S_{j - N} u · Δⱼ v`. -/
theorem hasSum_paraproductNegCLM (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    HasSum (fun j ↦ ((u.lowPass (j - N) • v.block j :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) (paraproductNegCLM r q hN hα u v).toDistr :=
  ((exists_paraproductNeg (F := F) hN hα β).choose_spec.2 u v).choose_spec.1

/-- **Uniform operator norm bound for `paraproductNegCLM`.** The operator norm is bounded by a
constant depending only on `E`, `F`, `φ`, `N`, `α` and `β`, independently of
`p₁, p₂, r, q₁, q₂, q`. -/
theorem exists_norm_paraproductNegCLM_le (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0) (β : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q],
      ‖paraproductNegCLM (F := F) (α := α) (β := β)
        (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂) r q hN hα‖ ≤ C :=
  ⟨_, (exists_paraproductNeg (F := F) hN hα β).choose_spec.1,
    fun {_ _ _ _ _ _} _ _ _ _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _
      (exists_paraproductNeg (F := F) hN hα β).choose_spec.1 _⟩

/-- When `u ∈ B^α_{p₁,q₁}` (`α < 0`) also lies in `L^{p₁}` as `f`, `paraproductNegCLM` and
`paraproductLpCLM` define the same tempered distribution. -/
theorem toDistr_paraproductNegCLM_eq_paraproductLpCLM (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0)
    {u : BesovSpace ℂ φ α p₁ q₁} {f : Lp ℂ p₁ (volume : Measure E)} (huf : u.toDistr = f)
    (v : BesovSpace F φ β p₂ q₂) :
    (paraproductNegCLM r q hN hα u v).toDistr = (paraproductLpCLM r hN f v).toDistr :=
  (hasSum_paraproductNegCLM (r := r) (q := q) hN hα u v).unique
    (hasSum_paraproductLpCLM_of_toDistr_eq (r := r) hN huf v)

/-- Uniform existence and Besov bound for `T_v u = ∑ⱼ Δⱼ u · S_{j - N} v` when `β < 0`. -/
private theorem exists_paraproductRightNeg (hN : φ.rOut < 2 ^ N * φ.rIn) (α : ℝ) (hβ : β < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q]
      (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂),
      ∃ y : BesovSpace F φ (α + β) r q,
        HasSum (fun j ↦ ((u.block j • v.lowPass (j - N) :
          Lp F r (volume : Measure E)) : 𝓢'(E, F))) y.toDistr ∧
        ‖y‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C₀, hC₀, hann⟩ := exists_hasSum_of_paraproduct_annulus (F := F) (α + β) hN
  have hden : 0 ≤ ((2 : ℝ) ^ (-β) - 1)⁻¹ :=
    inv_nonneg.2 (sub_nonneg.2 (Real.one_lt_rpow one_lt_two (neg_pos.2 hβ)).le)
  refine ⟨C₀ * (2 ^ (-β) - 1)⁻¹, by positivity,
    fun {p₁ p₂ r q₁ q₂ q} _ _ _ _ _ _ _ _ u v ↦ ?_⟩
  have hq₁ : q₁ ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set a : lp (fun _ : ℕ ↦ ℝ) q₁ := ⟨fun j ↦ ‖u.weightedBlocks j‖, (lp.memℓp _).norm⟩
  -- Anonymous `lp` elements coerce through `Subtype.val` and have no simp lemma for evaluation.
  have ha_eq (j : ℕ) : a j = ‖u.weightedBlocks j‖ := rfl
  have ha : ‖a‖ ≤ ‖u‖ := by
    rw [← norm_weightedBlocks]
    exact lp.norm_mono hq₁ fun j ↦ (norm_norm _).le
  obtain ⟨b, hb, hbn⟩ := exists_lp_lowPass_sub_le_of_neg hβ N v
  have hB : ∀ _ : ℕ, ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ (1 : ℝ≥0) := fun _ ↦ by simp
  set B := lp.holderL (p := q₁) (q := q₂) q (fun _ ↦ ContinuousLinearMap.mul ℝ ℝ) hB
  set w : lp (fun _ : ℕ ↦ ℝ) q := B a b
  have hw (j : ℕ) : w j = a j * b j := rfl
  have hwn : ‖w‖ ≤ ‖a‖ * ‖b‖ := by
    simpa [w] using
      B.le_of_opNorm₂_le_of_le (lp.norm_holderL_le (p := q₁) (q := q₂) q _ hB) le_rfl le_rfl
  obtain ⟨y, hy, hyn⟩ := hann (fun j ↦ u.block j • v.lowPass (j - N)) w
    (fun j ↦ isVanishingOn_fourier_block_smul_lowPass N j u v) fun j ↦ by
      rw [hw j, ha_eq, u.norm_weightedBlocks_apply]
      calc 2 ^ ((α + β) * j) * ‖u.block j • v.lowPass (j - N)‖
          ≤ 2 ^ ((α + β) * j) * (‖u.block j‖ * ‖v.lowPass (j - N)‖) :=
            mul_le_mul_of_nonneg_left (Lp.norm_smul_le _ _) (by positivity)
        _ = (2 ^ (α * j) * ‖u.block j‖) * (2 ^ (β * j) * ‖v.lowPass (j - N)‖) := by
            rw [add_mul, Real.rpow_add two_pos]; ring
        _ ≤ (2 ^ (α * j) * ‖u.block j‖) * b j :=
            mul_le_mul_of_nonneg_left (hb j) (by positivity)
  refine ⟨y, hy, hyn.trans ?_⟩
  calc C₀ * ‖w‖ ≤ C₀ * (‖a‖ * ‖b‖) := by gcongr
    _ ≤ C₀ * (‖u‖ * ((2 ^ (-β) - 1)⁻¹ * ‖v‖)) := by gcongr
    _ = C₀ * (2 ^ (-β) - 1)⁻¹ * ‖u‖ * ‖v‖ := by ring

variable (r q) in
/-- **Bony's right paraproduct at negative regularity** (Bahouri–Chemin–Danchin, Theorem 2.82). For
`φ.rOut < 2 ^ N * φ.rIn`, any `α ∈ ℝ`, `β < 0`, `1/r = 1/p₁ + 1/p₂`, and `1/q = 1/q₁ + 1/q₂`,
the series `T_v u = ∑ⱼ Δⱼ u · S_{j - N} v` defines a continuous bilinear map
`B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^{α + β}_{r,q}`, with operator norm bounded independently of
`p₁, p₂, r, q₁, q₂, q`. -/
def paraproductRightNegCLM (hN : φ.rOut < 2 ^ N * φ.rIn) (hβ : β < 0) :
    BesovSpace ℂ φ α p₁ q₁ →L[ℂ] BesovSpace F φ β p₂ q₂ →L[ℂ] BesovSpace F φ (α + β) r q :=
  mkContinuousOfHasSum₂ (fun j u v ↦ u.block j • v.lowPass (j - N))
    (fun _ _ _ _ ↦ by simp [block_add, Lp.smul_add])
    (fun _ _ _ _ ↦ by simp [block_smul, Lp.smul_assoc])
    (fun _ _ _ _ ↦ by simp [Lp.add_smul])
    (fun _ _ _ _ ↦ by simp [← Lp.smul_comm])
    (fun u v ↦ (exists_paraproductRightNeg (F := F) hN α hβ).choose_spec.2 u v)

/-- The tempered distribution of `paraproductRightNegCLM r q hN hβ u v` is the sum of the series
`∑ⱼ Δⱼ u · S_{j - N} v`. -/
theorem hasSum_paraproductRightNegCLM (hN : φ.rOut < 2 ^ N * φ.rIn) (hβ : β < 0)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    HasSum (fun j ↦ ((u.block j • v.lowPass (j - N) :
      Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      (paraproductRightNegCLM r q hN hβ u v).toDistr :=
  ((exists_paraproductRightNeg (F := F) hN α hβ).choose_spec.2 u v).choose_spec.1

/-- **Uniform operator norm bound for `paraproductRightNegCLM`.** -/
theorem exists_norm_paraproductRightNegCLM_le (hN : φ.rOut < 2 ^ N * φ.rIn) (α : ℝ) (hβ : β < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q],
      ‖paraproductRightNegCLM (F := F) (α := α) (β := β)
        (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂) r q hN hβ‖ ≤ C :=
  ⟨_, (exists_paraproductRightNeg (F := F) hN α hβ).choose_spec.1,
    fun {_ _ _ _ _ _} _ _ _ _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _
      (exists_paraproductRightNeg (F := F) hN α hβ).choose_spec.1 _⟩

/-- When `v ∈ B^β_{p₂,q₂}` (`β < 0`) also lies in `L^{p₂}` as `g`, `paraproductRightNegCLM` and
`paraproductRightLpCLM` define the same tempered distribution. -/
theorem toDistr_paraproductRightNegCLM_eq_paraproductRightLpCLM (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hβ : β < 0) (u : BesovSpace ℂ φ α p₁ q₁) {v : BesovSpace F φ β p₂ q₂}
    {g : Lp F p₂ (volume : Measure E)} (hvg : v.toDistr = g) :
    (paraproductRightNegCLM r q hN hβ u v).toDistr =
      (paraproductRightLpCLM r hN u g).toDistr :=
  (hasSum_paraproductRightNegCLM (r := r) (q := q) hN hβ u v).unique
    (hasSum_paraproductRightLpCLM_of_toDistr_eq (r := r) hN u hvg)

/-- For scalar-valued factors (`F = ℂ`), `paraproductRightNegCLM r q hN hβ u v` and
`paraproductNegCLM r q hN hβ v u` define the same tempered distribution. -/
theorem toDistr_paraproductRightNegCLM_eq_paraproductNegCLM (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hβ : β < 0) (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace ℂ φ β p₂ q₂) :
    (paraproductRightNegCLM r q hN hβ u v).toDistr =
      (paraproductNegCLM r q hN hβ v u).toDistr :=
  (hasSum_paraproductRightNegCLM (r := r) (q := q) hN hβ u v).unique <|
    (hasSum_paraproductNegCLM (r := r) (q := q) hN hβ v u).congr_fun fun _ ↦
      congrArg _ (Lp.lpSMul_comm _ _)

end ParaproductNeg

end TauCeti.BesovSpace
