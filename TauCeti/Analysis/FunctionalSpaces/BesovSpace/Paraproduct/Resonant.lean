/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Basic
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Estimate
import Mathlib.Analysis.Normed.Lp.lpHolder
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Ball
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.LinftyAlgebra

/-!
# Bony's resonant remainder and Besov multiplication

Let `Δⱼ` be the inhomogeneous Littlewood–Paley blocks of a bump function `φ` and `S_m u` the
low-frequency cut-off (`TauCeti.BesovSpace.lowPass`). For any gap `N : ℕ`, Bony's decomposition
(`TauCeti.BesovSpace.lowPass_smul_lowPass`) splits the truncated product `S_M u · S_M v` into two
paraproducts and the truncated resonant remainder `∑_{j < M} Δⱼ u · ∑_{k < M, |k - j| ≤ N} Δₖ v`.

Unlike the paraproduct pieces, whose Fourier transforms live in dyadic annuli, the `j`-th resonant
piece `Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` (`TauCeti.BesovSpace.resonantTerm`) is only spectrally
localised in the dyadic ball `‖ξ‖ ≤ 2 ^ j (1 + 2 ^ N) φ.rOut`
(`TauCeti.BesovSpace.isVanishingOn_fourier_resonantTerm`). Reconstructing Besov norms from series
supported in dyadic balls (`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_ball`) requires
strictly positive total smoothness `0 < α + β` and yields Bahouri–Chemin–Danchin, Theorem 2.85:

* **Resonant remainder estimate (`TauCeti.BesovSpace.resonantCLM`).** For `0 < α + β`,
  `1/r = 1/p₁ + 1/p₂`, and `1/q = 1/q₁ + 1/q₂`, the series
  `R_N(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` defines a continuous bilinear map
  `B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^{α + β}_{r,q}`, with operator norm bounded independently of
  `p₁, p₂, r, q₁, q₂, q`. Moreover, the truncated resonant sums from `S_M u · S_M v` converge in
  `𝓢'(E, F)` to `R_N(u, v)` (`TauCeti.BesovSpace.tendsto_sum_truncated_resonant`), so scalar
  resonant remainders are symmetric (`TauCeti.BesovSpace.toDistr_resonantCLM_comm`).
* **Bony product at opposite-sign regularities (`TauCeti.BesovSpace.bonyProductCLM`).** When
  `α < 0 < β` and `0 < α + β`, combining `T_u^N v`, `T_v^N u`, and `R_N(u, v)` gives a continuous
  bilinear product `B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^α_{r,q₁}` (specialising at `p₁ = p₂ = r = ∞`,
  `q₁ = q₂ = ∞` to `𝒞^α × 𝒞^β → 𝒞^α`). Because `S_M u · S_M v` converges in `𝓢'(E, F)` to the sum
  `T_u^N v + T_v^N u + R_N(u, v)` for every admissible gap `N` satisfying `φ.rOut < 2 ^ N * φ.rIn`,
  the resulting product is independent of `N` (`TauCeti.BesovSpace.bonyProductCLM_eq`,
  `TauCeti.BesovSpace.tendsto_lowPass_smul_lowPass_bonyProductCLM`).
* **Bony product at positive regularity (`TauCeti.BesovSpace.bonyProductPosCLM`).** For `0 < s`,
  the decomposition yields a continuous bilinear map `B^s_{p₁,q} × B^s_{p₂,q} → B^s_{r,q}`
  (Bahouri–Chemin–Danchin, Corollary 2.86) whose underlying tempered distribution is the pointwise
  `Lʳ` product `(toLpCLM u) • (toLpCLM v)` (`TauCeti.BesovSpace.toDistr_bonyProductPosCLM`).

Finally, we record the two structural checks on Bony's decomposition: when both factors are carried
by the same single dyadic block `j₀`, both paraproducts vanish and the resonant remainder carries
the entire product `Δ_{j₀} u · Δ_{j₀} v`; and when one factor is the constant `1`, `T_1^N v` sums
the blocks `j ≥ N + 1`, `T_v^N 1 = 0`, and `R_N(1, v) = S_{N + 1} v`, summing back to `v`.

## Main declarations

* `TauCeti.BesovSpace.resonantTerm`, `TauCeti.BesovSpace.resonantCLM`: the resonant remainder
  `B^α_{p₁,q₁} × B^β_{p₂,q₂} →L[ℂ] B^{α + β}_{r,q}` for `0 < α + β`, its `HasSum` and truncated-sum
  limits, uniform norm bound, and scalar symmetry.
* `TauCeti.BesovSpace.bonyProductCLM`: the gap-independent Bony product
  `B^α_{p₁,q₁} × B^β_{p₂,q₂} →L[ℂ] B^α_{r,q₁}` for `α < 0 < β` with `0 < α + β`.
* `TauCeti.BesovSpace.bonyProductPosCLM`: the gap-independent Bony product
  `B^s_{p₁,q} × B^s_{p₂,q} →L[ℂ] B^s_{r,q}` for `0 < s`, agreeing with pointwise `Lʳ`
  multiplication.
* Single-block (`paraproductNegCLM_eq_zero_of_block_eq_zero`,
  `toDistr_resonantCLM_of_block_eq_zero`) and constant-`1` (`toDistr_paraproductLpCLM_one`,
  `paraproductRightLpCLM_one_left`, `toDistr_resonantCLM_one_left`, `bonyProductCLM_one_right`,
  `bonyProductPosCLM_one_left`) identities.

## References

* J.-M. Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées
  partielles non linéaires*, Ann. Sci. École Norm. Sup. (4) 14 (1981), 209–246.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Theorem 2.85 and Corollary 2.86.
-/

public section

noncomputable section

open MeasureTheory Metric Filter Topology Distribution FourierTransform TemperedDistribution
open scoped ENNReal NNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

section Resonant

section Term

variable {φ : ContDiffBump (0 : E)} {α β : ℝ} {p₁ p₂ r q₁ q₂ : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [p₁.HolderTriple p₂ r]

variable (r) in
/-- The `j`-th piece `Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` of Bony's resonant remainder with gap `N`, as an
`Lʳ` function (`1/r = 1/p₁ + 1/p₂`). -/
def resonantTerm (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    Lp F r (volume : Measure E) :=
  u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k

/-- Unfolding `TauCeti.BesovSpace.resonantTerm`. -/
theorem resonantTerm_eq (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂)
    (j : ℕ) :
    resonantTerm r N u v j = u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k :=
  (rfl)

@[simp]
theorem resonantTerm_zero_left (N : ℕ) (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N (0 : BesovSpace ℂ φ α p₁ q₁) v j = 0 := by
  simp [resonantTerm_eq]

@[simp]
theorem resonantTerm_zero_right (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁) (j : ℕ) :
    resonantTerm r N u (0 : BesovSpace F φ β p₂ q₂) j = 0 := by
  simp [resonantTerm_eq]

@[simp]
theorem resonantTerm_add_left (N : ℕ) (u₁ u₂ : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N (u₁ + u₂) v j = resonantTerm r N u₁ v j + resonantTerm r N u₂ v j := by
  simp [resonantTerm_eq, Lp.smul_add]

@[simp]
theorem resonantTerm_smul_left (N : ℕ) (c : ℂ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N (c • u) v j = c • resonantTerm r N u v j := by
  simp [resonantTerm_eq, Lp.smul_assoc]

@[simp]
theorem resonantTerm_add_right (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v₁ v₂ : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N u (v₁ + v₂) j = resonantTerm r N u v₁ j + resonantTerm r N u v₂ j := by
  simp [resonantTerm_eq, Finset.sum_add_distrib, Lp.add_smul]

@[simp]
theorem resonantTerm_smul_right (N : ℕ) (c : ℂ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N u (c • v) j = c • resonantTerm r N u v j := by
  rw [resonantTerm_eq, resonantTerm_eq]
  simp_rw [block_smul, ← Finset.smul_sum, ← Lp.smul_comm]

/-- **Spectral localisation of a resonant piece.** The Fourier transform of `resonantTerm r N u v j`
vanishes outside the closed ball of radius `2 ^ j (1 + 2 ^ N) φ.rOut`. -/
theorem isVanishingOn_fourier_resonantTerm [Fact (1 ≤ r)] (N j : ℕ)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    IsVanishingOn (𝓕 ((resonantTerm r N u v j : Lp F r (volume : Measure E)) :
        𝓢'(E, F)) : 𝓢'(E, F))
      (closedBall 0 (2 ^ j * ((1 + 2 ^ N) * φ.rOut)))ᶜ :=
  isVanishingOn_fourier_block_smul_sum_block N j (fun _ hk ↦ (Finset.mem_Icc.1 hk).2) u v

/-- Weighted `Lʳ` bound on `Δⱼ u · ∑_{k ∈ t} Δₖ v` for any window `t ⊆ [j - N, j + N]`: moving the
dyadic weight `2 ^ (β j)` onto `k` costs at most `2 ^ (|β| (N + 1))`. -/
private theorem two_rpow_mul_norm_block_smul_sum_le (N j : ℕ) {t : Finset ℕ}
    (ht : t ⊆ Finset.Icc (j - N) (j + N)) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) :
    2 ^ ((α + β) * j) * ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖ ≤
      2 ^ (|β| * (N + 1 : ℕ)) * ‖u.weightedBlocks j‖ *
        ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v.weightedBlocks k‖ := by
  have hsub : t ⊆ Finset.Ico (j - (N + 1)) (j + (N + 1)) := fun k hk ↦ by
    have hk' := Finset.mem_Icc.1 (ht hk)
    rw [Finset.mem_Ico]
    omega
  have hsum : 2 ^ (β * j) * ‖∑ k ∈ t, v.block k‖ ≤
      2 ^ (|β| * (N + 1 : ℕ)) *
        ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v.weightedBlocks k‖ := by
    calc 2 ^ (β * j) * ‖∑ k ∈ t, v.block k‖
        ≤ 2 ^ (β * j) * ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v.block k‖ := by
          gcongr
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ norm_nonneg _)
      _ = ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), 2 ^ (β * j) * ‖v.block k‖ :=
          Finset.mul_sum ..
      _ ≤ ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)),
            2 ^ (|β| * (N + 1 : ℕ)) * ‖v.weightedBlocks k‖ := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          rw [v.norm_weightedBlocks_apply, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_mul_natCast_le_of_mem_Ico' one_le_two β hk) (norm_nonneg _)
      _ = 2 ^ (|β| * (N + 1 : ℕ)) *
            ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v.weightedBlocks k‖ :=
          (Finset.mul_sum ..).symm
  calc 2 ^ ((α + β) * j) * ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖
      ≤ 2 ^ ((α + β) * j) * (‖u.block j‖ * ‖∑ k ∈ t, v.block k‖) :=
        mul_le_mul_of_nonneg_left (Lp.norm_smul_le _ _) (by positivity)
    _ = ‖u.weightedBlocks j‖ * (2 ^ (β * j) * ‖∑ k ∈ t, v.block k‖) := by
        rw [u.norm_weightedBlocks_apply, add_mul, Real.rpow_add two_pos]; ring
    _ ≤ ‖u.weightedBlocks j‖ * (2 ^ (|β| * (N + 1 : ℕ)) *
          ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v.weightedBlocks k‖) :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = _ := by ring

end Term

variable {φ : ContDiffBump (0 : E)} {α β : ℝ} {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
  [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q]

/-- Uniform existence and Besov bound for Bony's resonant remainder when `0 < α + β`. -/
private theorem exists_resonant (N : ℕ) (α β : ℝ) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q]
      (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂),
      ∃ y : BesovSpace F φ (α + β) r q,
        HasSum (fun j ↦ ((resonantTerm r N u v j : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
          y.toDistr ∧
        ‖y‖ ≤ C * ‖u‖ * ‖v‖ := by
  obtain ⟨C₀, hC₀, hball⟩ :=
    exists_hasSum_toDistr_and_norm_le_of_ball (F := F) φ hαβ ((1 + 2 ^ N) * φ.rOut)
  set K : ℝ := 2 ^ (|β| * (N + 1 : ℕ))
  have : 0 ≤ K := by positivity
  refine ⟨C₀ * K * (2 * (N + 1 : ℕ)), by positivity,
    fun {p₁ p₂ r q₁ q₂ q} _ _ _ _ _ _ _ _ u v ↦ ?_⟩
  have hq₁ : q₁ ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hq₂ : q₂ ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set a : lp (fun _ : ℕ ↦ ℝ) q₁ := ⟨fun j ↦ ‖u.weightedBlocks j‖, (lp.memℓp _).norm⟩
  set b₀ : lp (fun _ : ℕ ↦ ℝ) q₂ := ⟨fun j ↦ ‖v.weightedBlocks j‖, (lp.memℓp _).norm⟩
  set b : lp (fun _ : ℕ ↦ ℝ) q₂ :=
    ⟨fun j ↦ ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), b₀ k,
      (lp.memℓp b₀).sum_Ico_sub_add (N + 1)⟩
  -- Anonymous `lp` elements coerce through `Subtype.val` and have no simp lemma for evaluation.
  have ha_eq (j : ℕ) : a j = ‖u.weightedBlocks j‖ := rfl
  have hb_eq (j : ℕ) : b j = ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), b₀ k := rfl
  have ha : ‖a‖ ≤ ‖u‖ := by
    rw [← norm_weightedBlocks]; exact lp.norm_mono hq₁ fun _ ↦ (norm_norm _).le
  have hb₀ : ‖b₀‖ ≤ ‖v‖ := by
    rw [← norm_weightedBlocks]; exact lp.norm_mono hq₂ fun _ ↦ (norm_norm _).le
  have hb : ‖b‖ ≤ 2 * (N + 1 : ℕ) * ‖b₀‖ := lp.norm_le_of_forall_eq_sum_Ico_sub_add (N + 1) hb_eq
  have hB : ∀ _ : ℕ, ‖ContinuousLinearMap.mul ℝ ℝ‖ ≤ (1 : ℝ≥0) := fun _ ↦ by simp
  set B := lp.holderL (p := q₁) (q := q₂) q (fun _ ↦ ContinuousLinearMap.mul ℝ ℝ) hB
  have hBab_eq (j : ℕ) : (B a b) j = a j * b j := rfl
  have hBab : ‖B a b‖ ≤ ‖a‖ * ‖b‖ := by
    simpa using
      B.le_of_opNorm₂_le_of_le (lp.norm_holderL_le (p := q₁) (q := q₂) q _ hB) le_rfl le_rfl
  obtain ⟨y, hy, hyn⟩ := hball (resonantTerm r N u v) (K • B a b)
    (fun j ↦ isVanishingOn_fourier_resonantTerm N j u v) fun j ↦ by
      simpa only [resonantTerm_eq, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hBab_eq, ha_eq,
        hb_eq, b₀, K, mul_assoc] using
        two_rpow_mul_norm_block_smul_sum_le (r := r) N j Finset.Subset.rfl u v
  refine ⟨y, hy, hyn.trans ?_⟩
  calc C₀ * ‖K • B a b‖ = C₀ * (K * ‖B a b‖) := by rw [norm_smul, Real.norm_of_nonneg ‹0 ≤ K›]
    _ ≤ C₀ * (K * (‖a‖ * (2 * (N + 1 : ℕ) * ‖b₀‖))) := by
        gcongr
        exact hBab.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg a))
    _ ≤ C₀ * (K * (‖u‖ * (2 * (N + 1 : ℕ) * ‖v‖))) := by gcongr
    _ = C₀ * K * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖ := by ring

variable (r q) in
/-- **Bony's resonant remainder** (Bahouri–Chemin–Danchin, Theorem 2.85). For any gap `N : ℕ`,
`0 < α + β`, `1/r = 1/p₁ + 1/p₂`, and `1/q = 1/q₁ + 1/q₂`, the series
`R_N(u, v) = ∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` defines a continuous bilinear map
`B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^{α + β}_{r,q}`, with operator norm bounded independently of
`p₁, p₂, r, q₁, q₂, q`. -/
def resonantCLM (N : ℕ) (hαβ : 0 < α + β) :
    BesovSpace ℂ φ α p₁ q₁ →L[ℂ] BesovSpace F φ β p₂ q₂ →L[ℂ] BesovSpace F φ (α + β) r q :=
  mkContinuousOfHasSum₂ (fun j u v ↦ resonantTerm r N u v j)
    (fun j x₁ x₂ y ↦ resonantTerm_add_left N x₁ x₂ y j)
    (fun j c x y ↦ resonantTerm_smul_left N c x y j)
    (fun j x y₁ y₂ ↦ resonantTerm_add_right N x y₁ y₂ j)
    (fun j c x y ↦ resonantTerm_smul_right N c x y j)
    (fun u v ↦ (exists_resonant (F := F) (φ := φ) N α β hαβ).choose_spec.2 u v)

/-- The tempered distribution of `resonantCLM r q N hαβ u v` is the sum of the resonant series
`∑ⱼ Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v`. -/
theorem hasSum_resonantCLM (N : ℕ) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    HasSum (fun j ↦ ((resonantTerm r N u v j : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      (resonantCLM r q N hαβ u v).toDistr := by
  rw [resonantCLM, mkContinuousOfHasSum₂_apply]
  exact ((exists_resonant (F := F) (φ := φ) N α β hαβ).choose_spec.2 u v).choose_spec.1

/-- **Uniform operator norm bound for `resonantCLM`.** The operator norm is bounded by a constant
depending only on `E`, `F`, `φ`, `N`, `α` and `β`, independently of `p₁, p₂, r, q₁, q₂, q`. -/
theorem exists_norm_resonantCLM_le (N : ℕ) (α β : ℝ) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q],
      ‖resonantCLM (F := F) (φ := φ) (α := α) (β := β)
        (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂) r q N hαβ‖ ≤ C :=
  ⟨_, (exists_resonant (F := F) (φ := φ) N α β hαβ).choose_spec.1,
    fun {_ _ _ _ _ _} _ _ _ _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _
      (exists_resonant (F := F) (φ := φ) N α β hαβ).choose_spec.1 _⟩

omit [Fact (1 ≤ r)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q] in
/-- Geometric decay bound on any partial-window resonant piece when `u ∈ B^α_{p₁,q₁}` and
`v ∈ B^β_{p₂,q₂}`. -/
private theorem norm_block_smul_sum_le_pow (N j : ℕ) {t : Finset ℕ}
    (ht : t ⊆ Finset.Icc (j - N) (j + N)) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) :
    ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖ ≤
      2 ^ (|β| * (N + 1 : ℕ)) * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖ * ((2 : ℝ) ^ (-(α + β))) ^ j := by
  have hρj : ((2 : ℝ) ^ (-(α + β))) ^ j * 2 ^ ((α + β) * j) = 1 := by
    have h0 := Real.rpow_neg_pow_mul_rpow_mul_natCast_add two_pos (α + β) j 0
    rwa [Nat.cast_zero, add_zero, mul_zero, Real.rpow_zero] at h0
  have hu : ‖u.weightedBlocks j‖ ≤ ‖u‖ := by
    simpa [u.norm_weightedBlocks_apply] using u.rpow_mul_norm_block_le j
  have hvsum : ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v.weightedBlocks k‖ ≤
      2 * (N + 1 : ℕ) * ‖v‖ := by
    calc ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v.weightedBlocks k‖
        ≤ ∑ _k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v‖ :=
          Finset.sum_le_sum fun k _ ↦ by
            simpa [v.norm_weightedBlocks_apply] using v.rpow_mul_norm_block_le k
      _ = ((Finset.Ico (j - (N + 1)) (j + (N + 1))).card : ℝ) * ‖v‖ := by simp
      _ ≤ 2 * (N + 1 : ℕ) * ‖v‖ := by
          gcongr
          rw [Nat.card_Ico]
          norm_cast
          omega
  have hmain := two_rpow_mul_norm_block_smul_sum_le (r := r) N j ht u v
  calc ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖
      = ((2 : ℝ) ^ (-(α + β))) ^ j *
          (2 ^ ((α + β) * j) *
            ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖) := by
        rw [← mul_assoc, hρj, one_mul]
    _ ≤ ((2 : ℝ) ^ (-(α + β))) ^ j *
          (2 ^ (|β| * (N + 1 : ℕ)) * ‖u‖ * (2 * (N + 1 : ℕ) * ‖v‖)) :=
        mul_le_mul_of_nonneg_left (hmain.trans (by gcongr)) (by positivity)
    _ = _ := by ring

omit [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q] in
/-- Quantitative `Lʳ` tail bound between the doubly-truncated resonant sum and the partial sum of
`resonantTerm`: only indices `M - N ≤ j < M` differ, contributing `O(2 ^ (-(α + β) (M - N)))`. -/
private theorem norm_sum_truncated_resonant_sub_le (N M : ℕ) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    ‖(∑ j ∈ Finset.range M, (u.block j •
          ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
            Lp F r (volume : Measure E))) -
        ∑ j ∈ Finset.range M, resonantTerm r N u v j‖ ≤
      (N : ℝ) * (2 * (2 ^ (|β| * (N + 1 : ℕ)) * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖)) *
        ((2 : ℝ) ^ (-(α + β))) ^ (M - N) := by
  set tM : ℕ → Finset ℕ := fun j ↦ (Finset.range M).filter fun k ↦ k ≤ j + N ∧ j ≤ k + N
  set ρ : ℝ := 2 ^ (-(α + β))
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hαβ)
  set K : ℝ := 2 ^ (|β| * (N + 1 : ℕ)) * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖
  have heq : (∑ j ∈ Finset.range M, (u.block j • ∑ k ∈ tM j, v.block k :
        Lp F r (volume : Measure E))) - ∑ j ∈ Finset.range M, resonantTerm r N u v j =
      ∑ j ∈ Finset.Ico (M - N) M,
        ((u.block j • ∑ k ∈ tM j, v.block k : Lp F r (volume : Measure E)) -
          resonantTerm r N u v j) := by
    rw [← Finset.sum_sub_distrib, Finset.range_eq_Ico]
    refine (Finset.sum_subset (Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl) ?_).symm
    intro j hj hjnot
    have hjM : j + N < M := by rw [Finset.mem_Ico] at hj hjnot; omega
    have ht : tM j = Finset.Icc (j - N) (j + N) := by
      ext k; simp only [tM, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    simp [resonantTerm_eq, ht]
  rw [heq]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j ∈ Finset.Ico (M - N) M,
        ‖(u.block j • ∑ k ∈ tM j, v.block k : Lp F r (volume : Measure E)) -
          resonantTerm r N u v j‖
      ≤ ∑ _j ∈ Finset.Ico (M - N) M, 2 * K * ρ ^ (M - N) := by
        refine Finset.sum_le_sum fun j hj ↦ ?_
        have hρj : ρ ^ j ≤ ρ ^ (M - N) :=
          pow_le_pow_of_le_one hρ0 hρ1.le (Finset.mem_Ico.1 hj).1
        have ht_sub : tM j ⊆ Finset.Icc (j - N) (j + N) := fun k hk ↦ by
          simp only [tM, Finset.mem_filter, Finset.mem_Icc] at hk ⊢; omega
        have h₁ := norm_block_smul_sum_le_pow (r := r) N j ht_sub u v
        have h₂ := norm_block_smul_sum_le_pow (r := r) N j Finset.Subset.rfl u v
        have : 0 ≤ K := by positivity
        calc ‖(u.block j • ∑ k ∈ tM j, v.block k : Lp F r (volume : Measure E)) -
              resonantTerm r N u v j‖
            ≤ ‖(u.block j • ∑ k ∈ tM j, v.block k : Lp F r (volume : Measure E))‖ +
                ‖resonantTerm r N u v j‖ := norm_sub_le _ _
          _ ≤ K * ρ ^ j + K * ρ ^ j := add_le_add h₁ h₂
          _ = 2 * K * ρ ^ j := by ring
          _ ≤ 2 * K * ρ ^ (M - N) := by gcongr
    _ = ((Finset.Ico (M - N) M).card : ℝ) * (2 * K * ρ ^ (M - N)) := by simp
    _ ≤ (N : ℝ) * (2 * K) * ρ ^ (M - N) := by
        have : 0 ≤ 2 * K * ρ ^ (M - N) := by positivity
        rw [mul_assoc ((N : ℝ))]
        gcongr
        rw [Nat.card_Ico]
        omega

/-- **Convergence of the truncated resonant sums.** For `0 < α + β`, the truncated resonant sums
`∑_{j < M} Δⱼ u · ∑_{k < M, |k - j| ≤ N} Δₖ v` appearing in Bony's decomposition of `S_M u · S_M v`
converge in `𝓢'(E, F)` to `(resonantCLM r q N hαβ u v).toDistr` as `M → ∞`: the inner truncation
`k < M` affects at most the top `N` indices `M - N ≤ j < M`, whose `Lʳ` norms decay as
`O(2^{-(α + β) M})`. -/
theorem tendsto_sum_truncated_resonant (N : ℕ) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((∑ j ∈ Finset.range M, (u.block j •
        ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
          Lp F r (volume : Measure E)) : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (resonantCLM r q N hαβ u v).toDistr) := by
  set S₁ : ℕ → Lp F r (volume : Measure E) := fun M ↦
    ∑ j ∈ Finset.range M, resonantTerm r N u v j
  set S₂ : ℕ → Lp F r (volume : Measure E) := fun M ↦
    ∑ j ∈ Finset.range M, (u.block j •
      ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
        Lp F r (volume : Measure E))
  set ρ : ℝ := 2 ^ (-(α + β))
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hαβ)
  set C : ℝ := (N : ℝ) * (2 * (2 ^ (|β| * (N + 1 : ℕ)) * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖))
  have hzero : Tendsto (fun M ↦ C * ρ ^ (M - N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
        (tendsto_sub_atTop_nat N)).const_mul C
  have hdiff : Tendsto (fun M ↦ S₂ M - S₁ M) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun M ↦ by rw [sub_zero]; exact norm_sum_truncated_resonant_sub_le N M hαβ u v) hzero
  have hS₁ : Tendsto (fun M ↦ (S₁ M : 𝓢'(E, F))) atTop
      (𝓝 (resonantCLM r q N hαβ u v).toDistr) := by
    simpa [S₁] using (hasSum_resonantCLM (r := r) (q := q) N hαβ u v).tendsto_sum_nat
  have hdiff' : Tendsto (fun M ↦ (S₂ M : 𝓢'(E, F)) - (S₁ M : 𝓢'(E, F))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      ((Lp.toTemperedDistributionCLM F volume r).continuous.tendsto 0).comp hdiff
  rw [← add_zero (resonantCLM r q N hαβ u v).toDistr]
  exact (hS₁.add hdiff').congr fun M ↦ add_sub_cancel _ _

/-- **Scalar symmetry of the resonant remainder.** When `F = ℂ` and `0 < α + β`, swapping the two
factors leaves `(resonantCLM r q N hαβ u v).toDistr` unchanged. -/
theorem toDistr_resonantCLM_comm (N : ℕ) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace ℂ φ β p₂ q₂) :
    (resonantCLM r q N hαβ u v).toDistr =
      (resonantCLM r q N (add_comm α β ▸ hαβ) v u).toDistr := by
  refine tendsto_nhds_unique (tendsto_sum_truncated_resonant (r := r) (q := q) N hαβ u v) ?_
  refine (tendsto_sum_truncated_resonant (r := r) (q := q) N (add_comm α β ▸ hαβ) v u).congr
    fun M ↦ congrArg _ ?_
  simp_rw [Lp.smul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  split_ifs with h₁ h₂
  · exact Lp.lpSMul_comm (v.block k) (u.block j)
  · exfalso; omega
  · exfalso; omega
  · rfl

end Resonant

section BonyProduct

section OppositeSign

variable {φ : ContDiffBump (0 : E)} {α β : ℝ} {p₁ p₂ r q₁ q₂ : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
  [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)]

/-- Auxiliary `N`-dependent Bony product at opposite-sign regularities `α < 0 < β`, `0 < α + β`. -/
private def bonyProductAux (r : ℝ≥0∞) [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r] {N : ℕ}
    (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0) (hβ : 0 < β) (hαβ : 0 < α + β) :
    BesovSpace ℂ φ α p₁ q₁ →L[ℂ] BesovSpace F φ β p₂ q₂ →L[ℂ] BesovSpace F φ α r q₁ :=
  ((inclusion F φ r (by linarith : α ≤ α + β) le_rfl).postcomp (BesovSpace F φ β p₂ q₂) ∘L
      (paraproductNegCLM (F := F) r q₁ hN hα).bilinearComp
        (.id ℂ (BesovSpace ℂ φ α p₁ q₁))
        (inclusion F φ p₂ le_rfl (le_top : q₂ ≤ ∞))) +
    (paraproductRightLpCLM (F := F) r hN).bilinearComp
      (.id ℂ (BesovSpace ℂ φ α p₁ q₁)) (toLpCLM F φ p₂ q₂ hβ) +
    ((inclusion F φ r (by linarith : α ≤ α + β) le_rfl).postcomp (BesovSpace F φ β p₂ q₂) ∘L
      (resonantCLM (F := F) r q₁ N hαβ).bilinearComp
        (.id ℂ (BesovSpace ℂ φ α p₁ q₁))
        (inclusion F φ p₂ le_rfl (le_top : q₂ ≤ ∞)))

private theorem bonyProductAux_apply {N : ℕ} (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hα : α < 0) (hβ : 0 < β) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    bonyProductAux r hN hα hβ hαβ u v =
      inclusion F φ r (by linarith) le_rfl
          (paraproductNegCLM r q₁ hN hα u (inclusion F φ p₂ le_rfl le_top v)) +
        paraproductRightLpCLM r hN u (toLpCLM F φ p₂ q₂ hβ v) +
        inclusion F φ r (by linarith) le_rfl
          (resonantCLM r q₁ N hαβ u (inclusion F φ p₂ le_rfl le_top v)) :=
  rfl

/-- For every admissible gap `N`, `S_M u · S_M v` converges in `𝓢'(E, F)` to `bonyProductAux`. -/
private theorem tendsto_lowPass_smul_lowPass_bonyProductAux {N : ℕ}
    (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0) (hβ : 0 < β) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (bonyProductAux r hN hα hβ hαβ u v).toDistr) := by
  rw [bonyProductAux_apply]
  simp only [toDistr_add, toDistr_inclusion]
  set v' : BesovSpace F φ β p₂ ∞ := inclusion F φ p₂ le_rfl le_top v
  have h₁ := (hasSum_paraproductNegCLM (r := r) (q := q₁) hN hα u v').tendsto_sum_nat
  have h₂ := (hasSum_paraproductRightLpCLM_of_toDistr_eq (r := r) hN u
    (coe_toLpCLM hβ v).symm).tendsto_sum_nat
  have h₃ := tendsto_sum_truncated_resonant (r := r) (q := q₁) N hαβ u v'
  refine ((h₁.add h₂).add h₃).congr' (Eventually.of_forall fun M ↦ ?_)
  simp [v', lowPass_smul_lowPass N M u v, block_inclusion]

variable (r) in
/-- **Bony's product at opposite-sign regularities** (`α < 0 < β` with `0 < α + β`). The sum
`T_u v + T_v u + R(u, v)` defines a continuous bilinear map
`B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^α_{r,q₁}` whenever `1/r = 1/p₁ + 1/p₂`, with operator norm bounded
independently of `p₁, p₂, r, q₁, q₂` (`TauCeti.BesovSpace.exists_norm_bonyProductCLM_le`). At
`p₁ = p₂ = r = ∞` and `q₁ = q₂ = ∞` this gives the Hölder–Zygmund product `𝒞^α × 𝒞^β → 𝒞^α`. It is
independent of the admissible gap parameter `N` (`TauCeti.BesovSpace.bonyProductCLM_eq`). -/
def bonyProductCLM (hα : α < 0) (hβ : 0 < β) (hαβ : 0 < α + β) :
    BesovSpace ℂ φ α p₁ q₁ →L[ℂ] BesovSpace F φ β p₂ q₂ →L[ℂ] BesovSpace F φ α r q₁ :=
  bonyProductAux r φ.exists_rOut_lt_two_pow_mul_rIn.choose_spec hα hβ hαβ

/-- **Convergence of `S_M u · S_M v` in `𝓢'(E, F)`.** When `α < 0 < β` and `0 < α + β`, the
products of the low-frequency cut-offs `S_M u · S_M v` converge in `𝓢'(E, F)` to
`(bonyProductCLM r hα hβ hαβ u v).toDistr`. -/
theorem tendsto_lowPass_smul_lowPass_bonyProductCLM (hα : α < 0) (hβ : 0 < β) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (bonyProductCLM r hα hβ hαβ u v).toDistr) :=
  tendsto_lowPass_smul_lowPass_bonyProductAux _ hα hβ hαβ u v

/-- **Independence of the gap parameter `N`.** For every `N` satisfying `φ.rOut < 2 ^ N * φ.rIn`,
`bonyProductCLM r hα hβ hαβ u v` equals `T_u^N v + T_v^N u + R_N(u, v)`. -/
theorem bonyProductCLM_eq {N : ℕ} (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hα : α < 0) (hβ : 0 < β) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    bonyProductCLM r hα hβ hαβ u v =
      inclusion F φ r (by linarith) le_rfl
          (paraproductNegCLM r q₁ hN hα u (inclusion F φ p₂ le_rfl le_top v)) +
        paraproductRightLpCLM r hN u (toLpCLM F φ p₂ q₂ hβ v) +
        inclusion F φ r (by linarith) le_rfl
          (resonantCLM r q₁ N hαβ u (inclusion F φ p₂ le_rfl le_top v)) := by
  rw [← bonyProductAux_apply]
  exact ext <| tendsto_nhds_unique (tendsto_lowPass_smul_lowPass_bonyProductCLM hα hβ hαβ u v)
    (tendsto_lowPass_smul_lowPass_bonyProductAux hN hα hβ hαβ u v)

/-- **Uniform operator norm bound for `bonyProductCLM`.** The operator norm is bounded by a
constant depending only on `E`, `F`, `φ`, `α` and `β`, independently of `p₁, p₂, r, q₁, q₂`. -/
theorem exists_norm_bonyProductCLM_le (hα : α < 0) (hβ : 0 < β) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)],
      ‖bonyProductCLM (F := F) (φ := φ) (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂)
        r hα hβ hαβ‖ ≤ C := by
  set hN := φ.exists_rOut_lt_two_pow_mul_rIn.choose_spec
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_paraproductNegCLM_le (F := F) hN hα β
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_paraproductRightLpCLM_le (F := F) hN α
  obtain ⟨C₃, hC₃, h₃⟩ :=
    exists_norm_resonantCLM_le (F := F) (φ := φ) φ.exists_rOut_lt_two_pow_mul_rIn.choose α β hαβ
  have hden : 0 ≤ (1 - (2 : ℝ) ^ (-β))⁻¹ :=
    inv_nonneg.2 (sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos one_le_two
      (neg_nonpos_of_nonneg hβ.le)))
  refine ⟨C₁ + C₂ * (1 - 2 ^ (-β))⁻¹ + C₃, by positivity,
    fun {_ p₂' r' q₁' q₂'} _ _ _ _ _ _ ↦ ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun u v ↦ ?_
  rw [bonyProductCLM, bonyProductAux_apply]
  set v' : BesovSpace F φ β p₂' ∞ := inclusion F φ p₂' le_rfl le_top v
  have hv' : ‖v'‖ ≤ ‖v‖ := norm_inclusion_le _ _ v
  have hn₁ : ‖inclusion F φ r' (by linarith : α ≤ α + β) le_rfl
      (paraproductNegCLM r' q₁' hN hα u v')‖ ≤ C₁ * ‖u‖ * ‖v‖ :=
    (norm_inclusion_le _ _ _).trans <|
      ((paraproductNegCLM r' q₁' hN hα).le_opNorm₂ u v').trans (by gcongr; exact h₁)
  have hn₂ : ‖paraproductRightLpCLM r' hN u (toLpCLM F φ p₂' q₂' hβ v)‖ ≤
      C₂ * (1 - 2 ^ (-β))⁻¹ * ‖u‖ * ‖v‖ := by
    calc ‖paraproductRightLpCLM r' hN u (toLpCLM F φ p₂' q₂' hβ v)‖
        ≤ ‖paraproductRightLpCLM (F := F) (α := α) (p₁ := _) (p₂ := p₂') (q := q₁') r' hN‖ *
            ‖u‖ * ‖toLpCLM F φ p₂' q₂' hβ v‖ :=
          (paraproductRightLpCLM r' hN).le_opNorm₂ u (toLpCLM F φ p₂' q₂' hβ v)
      _ ≤ C₂ * ‖u‖ * ((1 - 2 ^ (-β))⁻¹ * ‖v‖) := by
          gcongr
          · exact h₂
          · exact norm_toLpCLM_apply_le hβ v
      _ = C₂ * (1 - 2 ^ (-β))⁻¹ * ‖u‖ * ‖v‖ := by ring
  have hn₃ : ‖inclusion F φ r' (by linarith : α ≤ α + β) le_rfl
      (resonantCLM r' q₁' _ hαβ u v')‖ ≤ C₃ * ‖u‖ * ‖v‖ :=
    (norm_inclusion_le _ _ _).trans <|
      ((resonantCLM r' q₁' _ hαβ).le_opNorm₂ u v').trans (by gcongr; exact h₃)
  calc _ ≤ _ + _ + _ := norm_add₃_le
    _ ≤ C₁ * ‖u‖ * ‖v‖ + C₂ * (1 - 2 ^ (-β))⁻¹ * ‖u‖ * ‖v‖ + C₃ * ‖u‖ * ‖v‖ :=
        add_le_add_three hn₁ hn₂ hn₃
    _ = (C₁ + C₂ * (1 - 2 ^ (-β))⁻¹ + C₃) * ‖u‖ * ‖v‖ := by ring

end OppositeSign

section Positive

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p₁ p₂ r q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r] [Fact (1 ≤ q)]

/-- Auxiliary `N`-dependent Bony product at positive regularity `0 < s`. -/
private def bonyProductPosAux (r : ℝ≥0∞) [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r] {N : ℕ}
    (hN : φ.rOut < 2 ^ N * φ.rIn) (hs : 0 < s) :
    BesovSpace ℂ φ s p₁ q →L[ℂ] BesovSpace F φ s p₂ q →L[ℂ] BesovSpace F φ s r q :=
  (paraproductLpCLM (F := F) r hN).bilinearComp (toLpCLM ℂ φ p₁ q hs)
      (.id ℂ (BesovSpace F φ s p₂ q)) +
    (paraproductRightLpCLM (F := F) r hN).bilinearComp
      (.id ℂ (BesovSpace ℂ φ s p₁ q)) (toLpCLM F φ p₂ q hs) +
    ((inclusion F φ r (by linarith : s ≤ s + s) le_rfl).postcomp (BesovSpace F φ s p₂ q) ∘L
      (resonantCLM (F := F) r q N (add_pos hs hs)).bilinearComp
        (.id ℂ (BesovSpace ℂ φ s p₁ q))
        (inclusion F φ p₂ le_rfl (le_top : q ≤ ∞)))

private theorem bonyProductPosAux_apply {N : ℕ} (hN : φ.rOut < 2 ^ N * φ.rIn) (hs : 0 < s)
    (u : BesovSpace ℂ φ s p₁ q) (v : BesovSpace F φ s p₂ q) :
    bonyProductPosAux r hN hs u v =
      paraproductLpCLM r hN (toLpCLM ℂ φ p₁ q hs u) v +
        paraproductRightLpCLM r hN u (toLpCLM F φ p₂ q hs v) +
        inclusion F φ r (by linarith) le_rfl
          (resonantCLM r q N (add_pos hs hs) u (inclusion F φ p₂ le_rfl le_top v)) :=
  rfl

/-- For every admissible gap `N`, `S_M u · S_M v` converges in `𝓢'(E, F)` to
`bonyProductPosAux`. -/
private theorem tendsto_lowPass_smul_lowPass_bonyProductPosAux {N : ℕ}
    (hN : φ.rOut < 2 ^ N * φ.rIn) (hs : 0 < s)
    (u : BesovSpace ℂ φ s p₁ q) (v : BesovSpace F φ s p₂ q) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (bonyProductPosAux r hN hs u v).toDistr) := by
  rw [bonyProductPosAux_apply]
  simp only [toDistr_add, toDistr_inclusion]
  set v' : BesovSpace F φ s p₂ ∞ := inclusion F φ p₂ le_rfl le_top v
  have h₁ := (hasSum_paraproductLpCLM_of_toDistr_eq (r := r) hN (coe_toLpCLM hs u).symm v)
    |>.tendsto_sum_nat
  have h₂ := (hasSum_paraproductRightLpCLM_of_toDistr_eq (r := r) hN u (coe_toLpCLM hs v).symm)
    |>.tendsto_sum_nat
  have h₃ := tendsto_sum_truncated_resonant (r := r) (q := q) N (add_pos hs hs) u v'
  refine ((h₁.add h₂).add h₃).congr' (Eventually.of_forall fun M ↦ ?_)
  simp [v', lowPass_smul_lowPass N M u v, block_inclusion]

variable (r) in
/-- **Bony's product at positive regularity** (Bahouri–Chemin–Danchin, Corollary 2.86). For
`0 < s` and `1/r = 1/p₁ + 1/p₂`, Bony's decomposition defines a continuous bilinear map
`B^s_{p₁,q} × B^s_{p₂,q} → B^s_{r,q}` whose underlying tempered distribution is the pointwise
`Lʳ` product `(toLpCLM u) • (toLpCLM v)` (`TauCeti.BesovSpace.toDistr_bonyProductPosCLM`), with
operator norm bounded independently of `p₁, p₂, r, q`. -/
def bonyProductPosCLM (hs : 0 < s) :
    BesovSpace ℂ φ s p₁ q →L[ℂ] BesovSpace F φ s p₂ q →L[ℂ] BesovSpace F φ s r q :=
  bonyProductPosAux r φ.exists_rOut_lt_two_pow_mul_rIn.choose_spec hs

/-- **Convergence of `S_M u · S_M v` in `𝓢'(E, F)` for `s > 0`.** -/
theorem tendsto_lowPass_smul_lowPass_bonyProductPosCLM (hs : 0 < s)
    (u : BesovSpace ℂ φ s p₁ q) (v : BesovSpace F φ s p₂ q) :
    Tendsto (fun M ↦ ((u.lowPass M • v.lowPass M : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (bonyProductPosCLM r hs u v).toDistr) :=
  tendsto_lowPass_smul_lowPass_bonyProductPosAux _ hs u v

/-- **Independence of the gap parameter `N` for `bonyProductPosCLM`.** -/
theorem bonyProductPosCLM_eq {N : ℕ} (hN : φ.rOut < 2 ^ N * φ.rIn) (hs : 0 < s)
    (u : BesovSpace ℂ φ s p₁ q) (v : BesovSpace F φ s p₂ q) :
    bonyProductPosCLM r hs u v =
      paraproductLpCLM r hN (toLpCLM ℂ φ p₁ q hs u) v +
        paraproductRightLpCLM r hN u (toLpCLM F φ p₂ q hs v) +
        inclusion F φ r (by linarith) le_rfl
          (resonantCLM r q N (add_pos hs hs) u (inclusion F φ p₂ le_rfl le_top v)) := by
  rw [← bonyProductPosAux_apply]
  exact ext <| tendsto_nhds_unique (tendsto_lowPass_smul_lowPass_bonyProductPosCLM hs u v)
    (tendsto_lowPass_smul_lowPass_bonyProductPosAux hN hs u v)

/-- **Identification with pointwise `Lʳ` multiplication.** For `0 < s`, the tempered distribution
of `bonyProductPosCLM r hs u v` is the `Lʳ` product `(toLpCLM u) • (toLpCLM v)`. -/
@[simp]
theorem toDistr_bonyProductPosCLM (hs : 0 < s)
    (u : BesovSpace ℂ φ s p₁ q) (v : BesovSpace F φ s p₂ q) :
    (bonyProductPosCLM r hs u v).toDistr =
      ((toLpCLM ℂ φ p₁ q hs u • toLpCLM F φ p₂ q hs v :
        Lp F r (volume : Measure E)) : 𝓢'(E, F)) := by
  refine tendsto_nhds_unique (tendsto_lowPass_smul_lowPass_bonyProductPosCLM hs u v) ?_
  have hLp := Lp.tendsto_lpSMul (r := r) (tendsto_lowPass hs u) (tendsto_lowPass hs v)
  simpa [Function.comp_def] using
    ((Lp.toTemperedDistributionCLM F volume r).continuous.tendsto _).comp hLp

/-- **Uniform operator norm bound for `bonyProductPosCLM`.** The operator norm is bounded by a
constant depending only on `E`, `F`, `φ` and `s`, independently of `p₁, p₂, r, q`. -/
theorem exists_norm_bonyProductPosCLM_le (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r] [Fact (1 ≤ q)],
      ‖bonyProductPosCLM (F := F) (φ := φ) (p₁ := p₁) (p₂ := p₂) (q := q) r hs‖ ≤ C := by
  set hN := φ.exists_rOut_lt_two_pow_mul_rIn.choose_spec
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_paraproductLpCLM_le (F := F) hN s
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_paraproductRightLpCLM_le (F := F) hN s
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_resonantCLM_le (F := F) (φ := φ)
    φ.exists_rOut_lt_two_pow_mul_rIn.choose s s (add_pos hs hs)
  have hden : 0 ≤ (1 - (2 : ℝ) ^ (-s))⁻¹ :=
    inv_nonneg.2 (sub_nonneg.2 (Real.rpow_le_one_of_one_le_of_nonpos one_le_two
      (neg_nonpos_of_nonneg hs.le)))
  refine ⟨(C₁ + C₂) * (1 - 2 ^ (-s))⁻¹ + C₃, by positivity,
    fun {p₁' p₂' r' q'} _ _ _ _ _ ↦ ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity) fun u v ↦ ?_
  rw [bonyProductPosCLM, bonyProductPosAux_apply]
  set v' : BesovSpace F φ s p₂' ∞ := inclusion F φ p₂' le_rfl le_top v
  have hv' : ‖v'‖ ≤ ‖v‖ := norm_inclusion_le _ _ v
  have hn₁ : ‖paraproductLpCLM r' hN (toLpCLM ℂ φ p₁' q' hs u) v‖ ≤
      C₁ * (1 - 2 ^ (-s))⁻¹ * ‖u‖ * ‖v‖ := by
    calc ‖paraproductLpCLM r' hN (toLpCLM ℂ φ p₁' q' hs u) v‖
        ≤ ‖paraproductLpCLM (F := F) (β := s) (p₁ := p₁') (p₂ := p₂') (q := q') r' hN‖ *
            ‖toLpCLM ℂ φ p₁' q' hs u‖ * ‖v‖ :=
          (paraproductLpCLM r' hN).le_opNorm₂ (toLpCLM ℂ φ p₁' q' hs u) v
      _ ≤ C₁ * ((1 - 2 ^ (-s))⁻¹ * ‖u‖) * ‖v‖ := by
          gcongr
          · exact h₁
          · exact norm_toLpCLM_apply_le hs u
      _ = C₁ * (1 - 2 ^ (-s))⁻¹ * ‖u‖ * ‖v‖ := by ring
  have hn₂ : ‖paraproductRightLpCLM r' hN u (toLpCLM F φ p₂' q' hs v)‖ ≤
      C₂ * (1 - 2 ^ (-s))⁻¹ * ‖u‖ * ‖v‖ := by
    calc ‖paraproductRightLpCLM r' hN u (toLpCLM F φ p₂' q' hs v)‖
        ≤ ‖paraproductRightLpCLM (F := F) (α := s) (p₁ := p₁') (p₂ := p₂') (q := q') r' hN‖ *
            ‖u‖ * ‖toLpCLM F φ p₂' q' hs v‖ :=
          (paraproductRightLpCLM r' hN).le_opNorm₂ u (toLpCLM F φ p₂' q' hs v)
      _ ≤ C₂ * ‖u‖ * ((1 - 2 ^ (-s))⁻¹ * ‖v‖) := by
          gcongr
          · exact h₂
          · exact norm_toLpCLM_apply_le hs v
      _ = C₂ * (1 - 2 ^ (-s))⁻¹ * ‖u‖ * ‖v‖ := by ring
  have hn₃ : ‖inclusion F φ r' (by linarith : s ≤ s + s) le_rfl
      (resonantCLM r' q' _ (add_pos hs hs) u v')‖ ≤ C₃ * ‖u‖ * ‖v‖ :=
    (norm_inclusion_le _ _ _).trans <|
      ((resonantCLM r' q' _ (add_pos hs hs)).le_opNorm₂ u v').trans (by gcongr; exact h₃)
  calc _ ≤ _ + _ + _ := norm_add₃_le
    _ ≤ C₁ * (1 - 2 ^ (-s))⁻¹ * ‖u‖ * ‖v‖ + C₂ * (1 - 2 ^ (-s))⁻¹ * ‖u‖ * ‖v‖ +
          C₃ * ‖u‖ * ‖v‖ := add_le_add_three hn₁ hn₂ hn₃
    _ = ((C₁ + C₂) * (1 - 2 ^ (-s))⁻¹ + C₃) * ‖u‖ * ‖v‖ := by ring

end Positive

end BonyProduct

section Checks

section SingleBlock

variable {φ : ContDiffBump (0 : E)} {N : ℕ} {α β : ℝ} {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
  [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)]

omit [Fact (1 ≤ r)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] in
private theorem lowPass_sub_smul_block_eq_zero_of_block_eq_zero (hN : 1 ≤ N) {j₀ : ℕ}
    {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) (j : ℕ) :
    (u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) = 0 := by
  by_cases hj : j = j₀
  · subst hj
    have hlow : u.lowPass (j - N) = 0 := by
      rw [lowPass_eq_sum]
      refine Finset.sum_eq_zero fun k hk ↦ hu k ?_
      rw [Finset.mem_range] at hk
      omega
    simp [hlow]
  · simp [hv j hj]

omit [Fact (1 ≤ r)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] in
private theorem block_smul_lowPass_sub_eq_zero_of_block_eq_zero (hN : 1 ≤ N) {j₀ : ℕ}
    {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) (j : ℕ) :
    (u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) = 0 := by
  by_cases hj : j = j₀
  · subst hj
    have hlow : v.lowPass (j - N) = 0 := by
      rw [lowPass_eq_sum]
      refine Finset.sum_eq_zero fun k hk ↦ hv k ?_
      rw [Finset.mem_range] at hk
      omega
    simp [hlow]
  · simp [hu j hj]

omit [Fact (1 ≤ q₁)] in
/-- **Same-frequency paraproduct vanishing (`L^{p₁}` form).** When `f` and `v` are both carried by
the single dyadic block `j₀`, `paraproductLpCLM r hN f v = 0`: at `j = j₀` the low-frequency
cut-off `S_{j₀ - N} f` sums only blocks `< j₀ - N < j₀` and vanishes, while for `j ≠ j₀` the block
`Δⱼ v` vanishes. -/
theorem paraproductLpCLM_eq_zero_of_block_eq_zero (hN : φ.rOut < 2 ^ N * φ.rIn) {j₀ : ℕ}
    {u : BesovSpace ℂ φ α p₁ q₁} {f : Lp ℂ p₁ (volume : Measure E)} (huf : u.toDistr = f)
    {v : BesovSpace F φ β p₂ q} (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) :
    paraproductLpCLM r hN f v = 0 := by
  refine ext <| ((hasSum_paraproductLpCLM_of_toDistr_eq (r := r) hN huf v).congr_fun fun j ↦ ?_)
    |>.unique hasSum_zero
  simp [lowPass_sub_smul_block_eq_zero_of_block_eq_zero
    (ContDiffBump.one_le_of_rOut_lt_two_pow_mul_rIn hN) hu hv j]

omit [Fact (1 ≤ q₂)] in
/-- **Same-frequency right-paraproduct vanishing (`L^{p₂}` form).** -/
theorem paraproductRightLpCLM_eq_zero_of_block_eq_zero (hN : φ.rOut < 2 ^ N * φ.rIn) {j₀ : ℕ}
    {u : BesovSpace ℂ φ α p₁ q} {v : BesovSpace F φ β p₂ q₂} {g : Lp F p₂ (volume : Measure E)}
    (hvg : v.toDistr = g) (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) :
    paraproductRightLpCLM r hN u g = 0 := by
  refine ext <| ((hasSum_paraproductRightLpCLM_of_toDistr_eq (r := r) hN u hvg).congr_fun
    fun j ↦ ?_).unique hasSum_zero
  simp [block_smul_lowPass_sub_eq_zero_of_block_eq_zero
    (ContDiffBump.one_le_of_rOut_lt_two_pow_mul_rIn hN) hu hv j]

/-- **Same-frequency paraproduct vanishing (`α < 0` form).** -/
theorem paraproductNegCLM_eq_zero_of_block_eq_zero [q₁.HolderTriple q₂ q]
    (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0) {j₀ : ℕ}
    {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) :
    paraproductNegCLM r q hN hα u v = 0 := by
  refine ext <| ((hasSum_paraproductNegCLM (r := r) (q := q) hN hα u v).congr_fun fun j ↦ ?_)
    |>.unique hasSum_zero
  simp [lowPass_sub_smul_block_eq_zero_of_block_eq_zero
    (ContDiffBump.one_le_of_rOut_lt_two_pow_mul_rIn hN) hu hv j]

/-- **Same-frequency right-paraproduct vanishing (`β < 0` form).** -/
theorem paraproductRightNegCLM_eq_zero_of_block_eq_zero [q₁.HolderTriple q₂ q]
    (hN : φ.rOut < 2 ^ N * φ.rIn) (hβ : β < 0) {j₀ : ℕ}
    {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) :
    paraproductRightNegCLM r q hN hβ u v = 0 := by
  refine ext <| ((hasSum_paraproductRightNegCLM (r := r) (q := q) hN hβ u v).congr_fun
    fun j ↦ ?_).unique hasSum_zero
  simp [block_smul_lowPass_sub_eq_zero_of_block_eq_zero
    (ContDiffBump.one_le_of_rOut_lt_two_pow_mul_rIn hN) hu hv j]

/-- **Same-frequency resonant term carries the product.** When `u` and `v` are both carried by the
single dyadic block `j₀`, `R_N(u, v)` equals `Δ_{j₀} u · Δ_{j₀} v`. -/
theorem toDistr_resonantCLM_of_block_eq_zero [q₁.HolderTriple q₂ q] (N : ℕ) (hαβ : 0 < α + β)
    {j₀ : ℕ} {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) :
    (resonantCLM r q N hαβ u v).toDistr =
      ((u.block j₀ • v.block j₀ : Lp F r (volume : Measure E)) : 𝓢'(E, F)) := by
  refine (hasSum_resonantCLM (r := r) (q := q) N hαβ u v).unique ?_
  have hsingle : HasSum (fun j ↦ ((resonantTerm r N u v j : Lp F r (volume : Measure E)) :
      𝓢'(E, F))) ((resonantTerm r N u v j₀ : Lp F r (volume : Measure E)) : 𝓢'(E, F)) :=
    hasSum_single j₀ fun j hj ↦ by simp [resonantTerm_eq, hu j hj]
  have hj₀ : resonantTerm r N u v j₀ = u.block j₀ • v.block j₀ := by
    rw [resonantTerm_eq, Finset.sum_eq_single j₀ (fun k _ hk ↦ hv k hk)
      (fun h ↦ absurd (Finset.mem_Icc.2 ⟨Nat.sub_le _ _, Nat.le_add_right _ _⟩) h)]
  rwa [hj₀] at hsingle

/-- **Same-frequency Bony product (`α < 0 < β`, `0 < α + β`).** Both paraproducts vanish and the
resonant term carries `Δ_{j₀} u · Δ_{j₀} v`. -/
theorem toDistr_bonyProductCLM_of_block_eq_zero (hα : α < 0) (hβ : 0 < β) (hαβ : 0 < α + β)
    {j₀ : ℕ} {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) :
    (bonyProductCLM r hα hβ hαβ u v).toDistr =
      ((u.block j₀ • v.block j₀ : Lp F r (volume : Measure E)) : 𝓢'(E, F)) := by
  obtain ⟨N, hN⟩ := φ.exists_rOut_lt_two_pow_mul_rIn
  have hv' : ∀ k ≠ j₀, (inclusion F φ p₂ le_rfl (le_top : q₂ ≤ ∞) v).block k = 0 := by
    simpa [block_inclusion] using hv
  rw [bonyProductCLM_eq hN hα hβ hαβ u v,
    paraproductNegCLM_eq_zero_of_block_eq_zero hN hα hu hv',
    paraproductRightLpCLM_eq_zero_of_block_eq_zero hN (coe_toLpCLM hβ v).symm hu hv]
  simp [toDistr_resonantCLM_of_block_eq_zero N hαβ hu hv', block_inclusion]

end SingleBlock

section One

variable {φ : ContDiffBump (0 : E)} {N : ℕ} {α β s : ℝ} {p₁ p₂ q₁ q₂ q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)]

/-- **Left paraproduct with the constant `1` (`L^∞` form).** Because `Δ₀ 1 = 1` and `Δₖ 1 = 0` for
`k ≥ 1`, `S_{j - N} 1` vanishes for `j ≤ N` and equals `1` for `j ≥ N + 1`, so `T_1^N v` sums the
blocks `j ≥ N + 1` and equals `v - S_{N + 1} v`. -/
theorem toDistr_paraproductLpCLM_one (hN : φ.rOut < 2 ^ N * φ.rIn)
    (v : BesovSpace F φ β p₂ q) :
    (paraproductLpCLM p₂ hN (1 : Lp ℂ ∞ (volume : Measure E)) v).toDistr =
      v.toDistr - (v.lowPass (N + 1) : 𝓢'(E, F)) := by
  have hone : (1 : BesovSpace ℂ φ 0 ∞ ∞).toDistr =
      ((1 : Lp ℂ ∞ (volume : Measure E)) : 𝓢'(E, ℂ)) := by simp
  have hsum := hasSum_paraproductLpCLM_of_toDistr_eq (r := p₂) hN hone v
  have hsub := hsum.tendsto_sum_nat.comp (tendsto_add_atTop_nat (N + 1))
  have htail : Tendsto (fun m ↦ (v.lowPass (N + 1 + m) : 𝓢'(E, F)) -
      (v.lowPass (N + 1) : 𝓢'(E, F))) atTop (𝓝 (v.toDistr - (v.lowPass (N + 1) : 𝓢'(E, F)))) := by
    have hv : Tendsto (fun m ↦ (v.lowPass m : 𝓢'(E, F))) atTop (𝓝 v.toDistr) := by
      simpa [coe_lowPass] using tendsto_sum_littlewoodPaleyBlock φ v.toDistr
    exact ((hv.comp (tendsto_add_atTop_nat (N + 1))).congr fun m ↦ by
      simp [Nat.add_comm]).sub_const _
  refine tendsto_nhds_unique (hsub.congr fun m ↦ ?_) htail
  simp only [Function.comp_apply, Nat.add_comm m (N + 1)]
  rw [Finset.sum_range_add]
  have hhead : ∑ j ∈ Finset.range (N + 1),
      (((1 : BesovSpace ℂ φ 0 ∞ ∞).lowPass (j - N) • v.block j :
        Lp F p₂ (volume : Measure E)) : 𝓢'(E, F)) = 0 := by
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    have hjN : j - N = 0 := by rw [Finset.mem_range] at hj; omega
    simp [hjN]
  have hrest : ∑ k ∈ Finset.range m,
      (((1 : BesovSpace ℂ φ 0 ∞ ∞).lowPass (N + 1 + k - N) • v.block (N + 1 + k) :
        Lp F p₂ (volume : Measure E)) : 𝓢'(E, F)) =
      (v.lowPass (N + 1 + m) : 𝓢'(E, F)) - (v.lowPass (N + 1) : 𝓢'(E, F)) := by
    have hidx (k : ℕ) : N + 1 + k - N = k + 1 := by omega
    simp_rw [hidx, lowPass_one_succ, Lp.one_smul]
    rw [lowPass_eq_sum v (N + 1 + m), lowPass_eq_sum v (N + 1), Lp.toTemperedDistribution_sum,
      Lp.toTemperedDistribution_sum, Finset.sum_range_add, add_sub_cancel_left]
  rw [hhead, zero_add, hrest]

/-- **Left paraproduct with `1` at negative regularity.** -/
theorem toDistr_paraproductNegCLM_one [q₁.HolderTriple q₂ q] (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hα : α < 0) (v : BesovSpace F φ β p₂ q₂) :
    (paraproductNegCLM p₂ q hN hα (1 : BesovSpace ℂ φ α ∞ q₁) v).toDistr =
      v.toDistr - (v.lowPass (N + 1) : 𝓢'(E, F)) := by
  rw [toDistr_paraproductNegCLM_eq_paraproductLpCLM hN hα
    (f := (1 : Lp ℂ ∞ (volume : Measure E))) (by simp) v, toDistr_paraproductLpCLM_one hN v]

/-- **Right paraproduct of `1` vanishes (`L^{p₂}` form).** Since `Δ₀ 1` meets `S_{0 - N} g = 0` and
`Δⱼ 1 = 0` for `j ≥ 1`, every term of `T_g^N 1` is zero. -/
@[simp]
theorem paraproductRightLpCLM_one_left (hN : φ.rOut < 2 ^ N * φ.rIn)
    (g : Lp F p₂ (volume : Measure E)) :
    paraproductRightLpCLM p₂ hN (1 : BesovSpace ℂ φ α ∞ q) g = 0 := by
  refine ext <| ((hasSum_paraproductRightLpCLM (r := p₂) hN
    (1 : BesovSpace ℂ φ α ∞ q) g).congr_fun fun j ↦ ?_).unique hasSum_zero
  rcases j with _ | j <;> simp

/-- **Paraproduct onto `1` vanishes (`L^{p₁}` form).** -/
@[simp]
theorem paraproductLpCLM_one_right (hN : φ.rOut < 2 ^ N * φ.rIn)
    (f : Lp ℂ p₁ (volume : Measure E)) :
    paraproductLpCLM p₁ hN f (1 : BesovSpace ℂ φ β ∞ q) = 0 := by
  rw [← paraproductRightLpCLM_eq_paraproductLpCLM hN (1 : BesovSpace ℂ φ β ∞ q) f,
    paraproductRightLpCLM_one_left hN f]

/-- **Right paraproduct of `1` vanishes (`β < 0` form).** -/
@[simp]
theorem paraproductRightNegCLM_one_left [q₁.HolderTriple q₂ q] (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hβ : β < 0) (v : BesovSpace F φ β p₂ q₂) :
    paraproductRightNegCLM p₂ q hN hβ (1 : BesovSpace ℂ φ α ∞ q₁) v = 0 := by
  refine ext <| ((hasSum_paraproductRightNegCLM (r := p₂) (q := q) hN hβ
    (1 : BesovSpace ℂ φ α ∞ q₁) v).congr_fun fun j ↦ ?_).unique hasSum_zero
  rcases j with _ | j <;> simp

/-- **Paraproduct onto `1` vanishes (`α < 0` form).** -/
@[simp]
theorem paraproductNegCLM_one_right [q₁.HolderTriple q₂ q] (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hα : α < 0) (u : BesovSpace ℂ φ α p₁ q₁) :
    paraproductNegCLM p₁ q hN hα u (1 : BesovSpace ℂ φ β ∞ q₂) = 0 := by
  refine ext <| ((hasSum_paraproductNegCLM (r := p₁) (q := q) hN hα u
    (1 : BesovSpace ℂ φ β ∞ q₂)).congr_fun fun j ↦ ?_).unique hasSum_zero
  rcases j with _ | j <;> simp

/-- **Resonant remainder with `1` on the left.** Only the `j = 0` term survives, giving
`R_N(1, v) = ∑_{k ≤ N} Δₖ v = S_{N + 1} v` (at `N = 1`, `Δ₀ v + Δ₁ v`). -/
@[simp]
theorem toDistr_resonantCLM_one_left [q₁.HolderTriple q₂ q] (N : ℕ) (hαβ : 0 < α + β)
    (v : BesovSpace F φ β p₂ q₂) :
    (resonantCLM p₂ q N hαβ (1 : BesovSpace ℂ φ α ∞ q₁) v).toDistr =
      (v.lowPass (N + 1) : 𝓢'(E, F)) := by
  refine (hasSum_resonantCLM (r := p₂) (q := q) N hαβ (1 : BesovSpace ℂ φ α ∞ q₁) v).unique ?_
  have hsingle : HasSum
      (fun j ↦ ((resonantTerm p₂ N (1 : BesovSpace ℂ φ α ∞ q₁) v j :
        Lp F p₂ (volume : Measure E)) : 𝓢'(E, F)))
      ((resonantTerm p₂ N (1 : BesovSpace ℂ φ α ∞ q₁) v 0 :
        Lp F p₂ (volume : Measure E)) : 𝓢'(E, F)) :=
    hasSum_single 0 fun j hj ↦ by
      rcases j with _ | j
      · exact absurd rfl hj
      · simp [resonantTerm_eq]
  have h0 : resonantTerm p₂ N (1 : BesovSpace ℂ φ α ∞ q₁) v 0 = v.lowPass (N + 1) := by
    rw [resonantTerm_eq, block_one_zero, Lp.one_smul, Nat.zero_sub, Nat.zero_add,
      ← Nat.range_succ_eq_Icc_zero, lowPass_eq_sum]
  rwa [h0] at hsingle

/-- **Resonant remainder with `1` on the right (`F = ℂ`).** -/
@[simp]
theorem toDistr_resonantCLM_one_right [q₁.HolderTriple q₂ q] (N : ℕ) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) :
    (resonantCLM p₁ q N hαβ u (1 : BesovSpace ℂ φ β ∞ q₂)).toDistr =
      (u.lowPass (N + 1) : 𝓢'(E, ℂ)) := by
  rw [toDistr_resonantCLM_comm N hαβ u 1, toDistr_resonantCLM_one_left]

/-- **Unitality of `bonyProductPosCLM` on the left:** `1 · v = v` in `B^s_{p₂,q}` (`s > 0`). -/
@[simp]
theorem bonyProductPosCLM_one_left (hs : 0 < s) (v : BesovSpace F φ s p₂ q) :
    bonyProductPosCLM p₂ hs (1 : BesovSpace ℂ φ s ∞ q) v = v :=
  ext <| by simp [toDistr_bonyProductPosCLM]

/-- **Unitality of `bonyProductPosCLM` on the right:** `u · 1 = u` in `B^s_{p₁,q}` (`s > 0`). -/
@[simp]
theorem bonyProductPosCLM_one_right (hs : 0 < s) (u : BesovSpace ℂ φ s p₁ q) :
    bonyProductPosCLM p₁ hs u (1 : BesovSpace ℂ φ s ∞ q) = u :=
  ext <| by simp [toDistr_bonyProductPosCLM]

/-- **Unitality of `bonyProductCLM` on the right (`α < 0 < β`, `0 < α + β`):** `T_u^N 1 = 0`,
`T_1^N u = u - S_{N + 1} u`, and `R_N(u, 1) = S_{N + 1} u` sum to `u`. -/
@[simp]
theorem bonyProductCLM_one_right (hα : α < 0) (hβ : 0 < β) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) :
    bonyProductCLM p₁ hα hβ hαβ u (1 : BesovSpace ℂ φ β ∞ q₂) = u := by
  obtain ⟨N, hN⟩ := φ.exists_rOut_lt_two_pow_mul_rIn
  have hone : inclusion ℂ φ ∞ le_rfl (le_top : q₂ ≤ ∞) (1 : BesovSpace ℂ φ β ∞ q₂) = 1 :=
    ext (by simp)
  apply ext
  rw [bonyProductCLM_eq hN hα hβ hαβ u 1, hone, paraproductNegCLM_one_right hN hα u,
    toLpCLM_one hβ, paraproductRightLpCLM_eq_paraproductLpCLM hN u 1]
  simp [toDistr_paraproductLpCLM_one hN u]

end One

end Checks

end TauCeti.BesovSpace

end
