/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Ball
import TauCeti.Analysis.Normed.Lp.Holder
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Function.Holder

/-!
# Bony's resonant remainder

For a bump function `φ` and gap `N : ℕ`, Bony's decomposition
(`TauCeti.BesovSpace.lowPass_smul_lowPass`) splits `S_M u · S_M v` into two paraproducts and the
truncated resonant remainder. Each piece
`Δⱼ u · ∑_{|k - j| ≤ N} Δₖ v` (`TauCeti.BesovSpace.resonantTerm`) is spectrally supported in the
ball `‖ξ‖ ≤ 2 ^ j (1 + 2 ^ N) φ.rOut` (`TauCeti.BesovSpace.isVanishingOn_fourier_resonantTerm`).
Reconstructing Besov norms from dyadic-ball series (`exists_hasSum_toDistr_and_norm_le_of_ball`)
for `0 < α + β` yields Bahouri–Chemin–Danchin, Theorem 2.85:

* `TauCeti.BesovSpace.resonantCLM`: `B^α_{p₁,q₁} × B^β_{p₂,q₂} →L[ℂ] B^{α + β}_{r,q}` for
  `0 < α + β`, `1/r = 1/p₁ + 1/p₂`, `1/q = 1/q₁ + 1/q₂`, with uniform norm bound, truncated-sum
  convergence (`tendsto_sum_block_smul_sum_resonantCLM`), and scalar symmetry
  (`toDistr_resonantCLM_comm`).
* Single-block (`toDistr_resonantCLM_of_block_eq_zero`) and constant-`1`
  (`toDistr_resonantCLM_one_left`, `toDistr_resonantCLM_one_right`) identities; companion
  paraproduct checks live in `TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Estimate`,
  and the Bony products (`smulL` and `bonyProductPosCLM`) live in
  `TauCeti.Analysis.FunctionalSpaces.BesovSpace.Product`.

## References

* J.-M. Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées
  partielles non linéaires*, Ann. Sci. École Norm. Sup. (4) 14 (1981), 209–246.
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, Theorem 2.85 (resonant remainder).
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
theorem resonantTerm_eq_smul_sum (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂)
    (j : ℕ) :
    resonantTerm r N u v j = u.block j • ∑ k ∈ Finset.Icc (j - N) (j + N), v.block k := by rfl

@[simp] theorem resonantTerm_zero_left (N : ℕ) (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N (0 : BesovSpace ℂ φ α p₁ q₁) v j = 0 := by simp [resonantTerm_eq_smul_sum]

@[simp] theorem resonantTerm_zero_right (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁) (j : ℕ) :
    resonantTerm r N u (0 : BesovSpace F φ β p₂ q₂) j = 0 := by simp [resonantTerm_eq_smul_sum]

@[simp] theorem resonantTerm_add_left (N : ℕ) (u₁ u₂ : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N (u₁ + u₂) v j = resonantTerm r N u₁ v j + resonantTerm r N u₂ v j := by
  simp [resonantTerm_eq_smul_sum, Lp.smul_add]

@[simp] theorem resonantTerm_smul_left (N : ℕ) (c : ℂ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N (c • u) v j = c • resonantTerm r N u v j := by
  simp [resonantTerm_eq_smul_sum, Lp.smul_assoc]

@[simp] theorem resonantTerm_neg_left (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N (-u) v j = -resonantTerm r N u v j := by
  simp [resonantTerm_eq_smul_sum, Lp.neg_smul]

@[simp] theorem resonantTerm_sub_left (N : ℕ) (u₁ u₂ : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N (u₁ - u₂) v j = resonantTerm r N u₁ v j - resonantTerm r N u₂ v j := by
  rw [sub_eq_add_neg, resonantTerm_add_left, resonantTerm_neg_left, ← sub_eq_add_neg]

@[simp] theorem resonantTerm_add_right (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v₁ v₂ : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N u (v₁ + v₂) j = resonantTerm r N u v₁ j + resonantTerm r N u v₂ j := by
  simp [resonantTerm_eq_smul_sum, Finset.sum_add_distrib, Lp.add_smul]

@[simp] theorem resonantTerm_smul_right (N : ℕ) (c : ℂ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N u (c • v) j = c • resonantTerm r N u v j := by
  simp_rw [resonantTerm_eq_smul_sum, block_smul, ← Finset.smul_sum, ← Lp.smul_comm]

@[simp] theorem resonantTerm_neg_right (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N u (-v) j = -resonantTerm r N u v j := by
  simp [resonantTerm_eq_smul_sum, Lp.smul_neg]

@[simp] theorem resonantTerm_sub_right (N : ℕ) (u : BesovSpace ℂ φ α p₁ q₁)
    (v₁ v₂ : BesovSpace F φ β p₂ q₂) (j : ℕ) :
    resonantTerm r N u (v₁ - v₂) j = resonantTerm r N u v₁ j - resonantTerm r N u v₂ j := by
  rw [sub_eq_add_neg, resonantTerm_add_right, resonantTerm_neg_right, ← sub_eq_add_neg]

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
    have := Finset.mem_Icc.1 (ht hk); rw [Finset.mem_Ico]; omega
  have hsum : 2 ^ (β * j) * ‖∑ k ∈ t, v.block k‖ ≤
      2 ^ (|β| * (N + 1 : ℕ)) *
        ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v.weightedBlocks k‖ := by
    simpa [Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub, v.norm_weightedBlocks_apply] using
      TauCeti.two_rpow_mul_norm_sum_Ico_le β (C := 1)
        (g := fun k ↦ if k ∈ t then v.block k else 0) (x := v.block)
        (fun k ↦ by split_ifs <;> simp) j (N + 1)
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
  set a := lp.toNorm u.weightedBlocks
  set b₀ := lp.toNorm v.weightedBlocks
  obtain ⟨b, hb_eq, hb⟩ := lp.exists_eq_sum_Ico_sub_add_and_norm_le b₀ (N + 1)
  obtain ⟨y, hy, hyn⟩ := hball (resonantTerm r N u v) (K • lp.mulL ℝ ℝ q a b)
    (fun j ↦ isVanishingOn_fourier_resonantTerm N j u v) fun j ↦ by
      simpa only [resonantTerm_eq_smul_sum, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        lp.mulL_apply_apply, hb_eq, a, b₀, lp.toNorm_coe, K, mul_assoc] using
        two_rpow_mul_norm_block_smul_sum_le (r := r) N j Finset.Subset.rfl u v
  refine ⟨y, hy, hyn.trans ?_⟩
  have ha : ‖a‖ = ‖u‖ := lp.norm_toNorm.trans u.norm_weightedBlocks
  have hb₀ : ‖b₀‖ = ‖v‖ := lp.norm_toNorm.trans v.norm_weightedBlocks
  calc C₀ * ‖K • lp.mulL ℝ ℝ q a b‖ = C₀ * (K * ‖lp.mulL ℝ ℝ q a b‖) := by
        rw [norm_smul, Real.norm_of_nonneg ‹0 ≤ K›]
    _ ≤ C₀ * (K * (‖a‖ * (2 * (N + 1 : ℕ) * ‖b₀‖))) := by
        gcongr
        exact (lp.norm_mulL_apply_apply_le ℝ ℝ q a b).trans
          (mul_le_mul_of_nonneg_left hb (norm_nonneg a))
    _ = C₀ * K * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖ := by rw [ha, hb₀]; ring

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
      (resonantCLM r q N hαβ u v).toDistr :=
  hasSum_mkContinuousOfHasSum₂ (X := BesovSpace ℂ φ α p₁ q₁) (Y := BesovSpace F φ β p₂ q₂)
    (r := r) (q := q) (γ := α + β) (fun j u v ↦ resonantTerm r N u v j)
    (fun j x₁ x₂ y ↦ resonantTerm_add_left N x₁ x₂ y j)
    (fun j c x y ↦ resonantTerm_smul_left N c x y j)
    (fun j x y₁ y₂ ↦ resonantTerm_add_right N x y₁ y₂ j)
    (fun j c x y ↦ resonantTerm_smul_right N c x y j)
    (fun u v ↦ (exists_resonant (F := F) (φ := φ) N α β hαβ).choose_spec.2 u v) u v

/-- **Uniform operator norm bound for `resonantCLM`.** The operator norm is bounded by a constant
depending only on `E`, `F`, `φ`, `N`, `α` and `β`, independently of `p₁, p₂, r, q₁, q₂, q`. -/
theorem exists_norm_resonantCLM_le (N : ℕ) (α β : ℝ) (hαβ : 0 < α + β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q],
      ‖resonantCLM (F := F) (φ := φ) (α := α) (β := β)
        (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂) r q N hαβ‖ ≤ C :=
  ⟨_, (exists_resonant (F := F) (φ := φ) N α β hαβ).choose_spec.1,
    fun {_ _ _ _ _ _} _ _ _ _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _ _
      (exists_resonant (F := F) (φ := φ) N α β hαβ).choose_spec.1⟩

omit [Fact (1 ≤ r)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q] in
/-- Geometric decay bound on any partial-window resonant piece when `u ∈ B^α_{p₁,q₁}` and
`v ∈ B^β_{p₂,q₂}`. -/
private theorem norm_block_smul_sum_le_pow (N j : ℕ) {t : Finset ℕ}
    (ht : t ⊆ Finset.Icc (j - N) (j + N)) (u : BesovSpace ℂ φ α p₁ q₁)
    (v : BesovSpace F φ β p₂ q₂) :
    ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖ ≤
      2 ^ (|β| * (N + 1 : ℕ)) * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖ * ((2 : ℝ) ^ (-(α + β))) ^ j := by
  have hρj : ((2 : ℝ) ^ (-(α + β))) ^ j * 2 ^ ((α + β) * j) = 1 := by
    simpa using Real.rpow_neg_pow_mul_rpow_mul_natCast_add two_pos (α + β) j 0
  have hu : ‖u.weightedBlocks j‖ ≤ ‖u‖ := by
    simpa [u.norm_weightedBlocks_apply] using u.rpow_mul_norm_block_le j
  have hvsum : ∑ k ∈ Finset.Ico (j - (N + 1)) (j + (N + 1)), ‖v.weightedBlocks k‖ ≤
      2 * (N + 1 : ℕ) * ‖v‖ :=
    (Finset.sum_le_card_nsmul _ _ ‖v‖ fun k _ ↦ by
      simpa [v.norm_weightedBlocks_apply] using v.rpow_mul_norm_block_le k).trans <| by
      rw [nsmul_eq_mul]; gcongr; rw [Nat.card_Ico]; norm_cast; omega
  have hmain := two_rpow_mul_norm_block_smul_sum_le (r := r) N j ht u v
  calc ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖
      = ((2 : ℝ) ^ (-(α + β))) ^ j * (2 ^ ((α + β) * j) *
          ‖(u.block j • ∑ k ∈ t, v.block k : Lp F r (volume : Measure E))‖) := by
        rw [← mul_assoc, hρj, one_mul]
    _ ≤ ((2 : ℝ) ^ (-(α + β))) ^ j *
          (2 ^ (|β| * (N + 1 : ℕ)) * ‖u‖ * (2 * (N + 1 : ℕ) * ‖v‖)) :=
        mul_le_mul_of_nonneg_left (hmain.trans (by gcongr)) (by positivity)
    _ = _ := by ring

omit [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q] in
/-- Quantitative `Lʳ` tail bound between the doubly-truncated resonant sum and the partial sum of
`resonantTerm`: only indices `M - N ≤ j < M` differ, contributing `O(2 ^ (-(α + β) (M - N)))`. -/
private theorem norm_sum_block_smul_sum_sub_le (N M : ℕ) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    ‖(∑ j ∈ Finset.range M, (u.block j •
          ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
            Lp F r (volume : Measure E))) -
        ∑ j ∈ Finset.range M, resonantTerm r N u v j‖ ≤
      (N : ℝ) * (2 * (2 ^ (|β| * (N + 1 : ℕ)) * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖)) *
        ((2 : ℝ) ^ (-(α + β))) ^ (M - N) := by
  set tM : ℕ → Finset ℕ := fun j ↦ (Finset.range M).filter fun k ↦ k ≤ j + N ∧ j ≤ k + N
  set ρ : ℝ := 2 ^ (-(α + β))
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hαβ)
  set K : ℝ := 2 ^ (|β| * (N + 1 : ℕ)) * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖
  have heq : (∑ j ∈ Finset.range M, (u.block j • ∑ k ∈ tM j, v.block k :
        Lp F r (volume : Measure E))) - ∑ j ∈ Finset.range M, resonantTerm r N u v j =
      ∑ j ∈ Finset.Ico (M - N) M, ((u.block j • ∑ k ∈ tM j, v.block k :
        Lp F r (volume : Measure E)) - resonantTerm r N u v j) := by
    rw [← Finset.sum_sub_distrib, Finset.range_eq_Ico]
    refine (Finset.sum_subset (Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl)
      fun j hj hnot ↦ ?_).symm
    have hjM : j + N < M := by rw [Finset.mem_Ico] at hj hnot; omega
    have ht : tM j = Finset.Icc (j - N) (j + N) := by
      ext k; simp only [tM, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]; omega
    simp [resonantTerm_eq_smul_sum, ht]
  rw [heq]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (2 * K * ρ ^ (M - N))
    fun j hj ↦ ?_).trans ?_)
  · have hρj : ρ ^ j ≤ ρ ^ (M - N) := pow_le_pow_of_le_one (by positivity) hρ1.le
      (Finset.mem_Ico.1 hj).1
    have h₁ := norm_block_smul_sum_le_pow (r := r) N j (t := tM j)
      (fun k hk ↦ by simp only [tM, Finset.mem_filter, Finset.mem_Icc] at hk ⊢; omega) u v
    have h₂ := norm_block_smul_sum_le_pow (r := r) N j Finset.Subset.rfl u v
    have : 0 ≤ K := by positivity
    exact (norm_sub_le _ _).trans ((add_le_add h₁ h₂).trans (by
      rw [← two_mul, mul_assoc (2 : ℝ)]; gcongr))
  · have : 0 ≤ 2 * K * ρ ^ (M - N) := by positivity
    rw [nsmul_eq_mul, mul_assoc (N : ℝ)]; gcongr; rw [Nat.card_Ico]; omega

/-- **Convergence of the truncated resonant sums.** For `0 < α + β`, the truncated resonant sums
`∑_{j < M} Δⱼ u · ∑_{k < M, |k - j| ≤ N} Δₖ v` appearing in Bony's decomposition of `S_M u · S_M v`
converge in `𝓢'(E, F)` to `(resonantCLM r q N hαβ u v).toDistr` as `M → ∞`: the inner truncation
`k < M` affects at most the top `N` indices `M - N ≤ j < M`, whose `Lʳ` norms decay as
`O(2^{-(α + β) M})`. -/
theorem tendsto_sum_block_smul_sum_resonantCLM (N : ℕ) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace F φ β p₂ q₂) :
    Tendsto (fun M ↦ ((∑ j ∈ Finset.range M, (u.block j •
        ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
          Lp F r (volume : Measure E)) : Lp F r (volume : Measure E)) : 𝓢'(E, F)))
      atTop (𝓝 (resonantCLM r q N hαβ u v).toDistr) := by
  have hρ1 : (2 : ℝ) ^ (-(α + β)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hαβ)
  set C : ℝ := (N : ℝ) * (2 * (2 ^ (|β| * (N + 1 : ℕ)) * (2 * (N + 1 : ℕ)) * ‖u‖ * ‖v‖))
  have hzero : Tendsto (fun M ↦ C * ((2 : ℝ) ^ (-(α + β))) ^ (M - N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hρ1).comp
        (tendsto_sub_atTop_nat N)).const_mul C
  have hdiff : Tendsto (fun M ↦ (∑ j ∈ Finset.range M, (u.block j •
        ∑ k ∈ (Finset.range M).filter (fun k ↦ k ≤ j + N ∧ j ≤ k + N), v.block k :
          Lp F r (volume : Measure E))) - ∑ j ∈ Finset.range M, resonantTerm r N u v j)
      atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.2 <| squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun M ↦ by rw [sub_zero]; exact norm_sum_block_smul_sum_sub_le N M hαβ u v) hzero
  have hS₁ := (hasSum_resonantCLM (r := r) (q := q) N hαβ u v).tendsto_sum_nat
  have hdiff' := ((Lp.toTemperedDistributionCLM F volume r).continuous.tendsto 0).comp hdiff
  rw [map_zero] at hdiff'
  rw [← add_zero (resonantCLM r q N hαβ u v).toDistr]
  exact (hS₁.add hdiff').congr fun M ↦ by simp

/-- **Scalar symmetry of the resonant remainder.** When `F = ℂ` and `0 < α + β`, swapping the two
factors leaves `(resonantCLM r q N hαβ u v).toDistr` unchanged. -/
theorem toDistr_resonantCLM_comm (N : ℕ) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) (v : BesovSpace ℂ φ β p₂ q₂) :
    (resonantCLM r q N hαβ u v).toDistr =
      (resonantCLM r q N (add_comm α β ▸ hαβ) v u).toDistr := by
  refine tendsto_nhds_unique (tendsto_sum_block_smul_sum_resonantCLM (r := r) (q := q) N hαβ u v) ?_
  refine (tendsto_sum_block_smul_sum_resonantCLM (r := r) (q := q) N
      (add_comm α β ▸ hαβ) v u).congr
    fun M ↦ congrArg _ ?_
  simp_rw [Lp.smul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  split_ifs <;> first | exact Lp.lpSMul_comm (v.block k) (u.block j) | rfl | omega

end Resonant

section Checks

section SingleBlock

variable {φ : ContDiffBump (0 : E)} {α β : ℝ} {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
  [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)]

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
    hasSum_single j₀ fun j hj ↦ by simp [resonantTerm_eq_smul_sum, hu j hj]
  have hj₀ : resonantTerm r N u v j₀ = u.block j₀ • v.block j₀ := by
    rw [resonantTerm_eq_smul_sum, Finset.sum_eq_single j₀ (fun k _ hk ↦ hv k hk)
      (fun h ↦ absurd (Finset.mem_Icc.2 ⟨Nat.sub_le _ _, Nat.le_add_right _ _⟩) h)]
  rwa [hj₀] at hsingle

end SingleBlock

section One

variable {φ : ContDiffBump (0 : E)} {α β : ℝ} {p₁ p₂ q₁ q₂ q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)]

/-- **Resonant remainder with `1` on the left.** Only the `j = 0` term survives, giving
`R_N(1, v) = ∑_{k ≤ N} Δₖ v = S_{N + 1} v` (at `N = 1`, `Δ₀ v + Δ₁ v`). -/
@[simp]
theorem toDistr_resonantCLM_one_left [q₁.HolderTriple q₂ q] (N : ℕ) (hαβ : 0 < α + β)
    (v : BesovSpace F φ β p₂ q₂) :
    (resonantCLM p₂ q N hαβ (1 : BesovSpace ℂ φ α ∞ q₁) v).toDistr =
      (v.lowPass (N + 1) : 𝓢'(E, F)) := by
  refine (hasSum_resonantCLM (r := p₂) (q := q) N hαβ (1 : BesovSpace ℂ φ α ∞ q₁) v).unique ?_
  have h0 : resonantTerm p₂ N (1 : BesovSpace ℂ φ α ∞ q₁) v 0 = v.lowPass (N + 1) := by
    rw [resonantTerm_eq_smul_sum, block_one_zero, Lp.one_smul, Nat.zero_sub, Nat.zero_add,
      ← Nat.range_succ_eq_Icc_zero, lowPass_eq_sum]
  rw [← h0]
  refine hasSum_single 0 fun j hj ↦ ?_
  rcases j with _ | j
  · exact absurd rfl hj
  · simp [resonantTerm_eq_smul_sum]

/-- **Resonant remainder with `1` on the right (`F = ℂ`).** -/
@[simp]
theorem toDistr_resonantCLM_one_right [q₁.HolderTriple q₂ q] (N : ℕ) (hαβ : 0 < α + β)
    (u : BesovSpace ℂ φ α p₁ q₁) :
    (resonantCLM p₁ q N hαβ u (1 : BesovSpace ℂ φ β ∞ q₂)).toDistr =
      (u.lowPass (N + 1) : 𝓢'(E, ℂ)) := by
  rw [toDistr_resonantCLM_comm N hαβ u 1, toDistr_resonantCLM_one_left]

end One

end Checks

end TauCeti.BesovSpace

end
