/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Paraproduct.Basic
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Annulus
import TauCeti.Analysis.Normed.Lp.Holder
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.MeasureTheory.Function.Holder

/-!
# Bony's paraproduct estimates on Besov spaces

For a bump function `φ` and gap `N : ℕ` with `φ.rOut < 2 ^ N * φ.rIn`, the products
`S_{j - N} u · Δⱼ v` and `Δⱼ u · S_{j - N} v` are spectrally supported in dyadic annuli of radii
comparable to `2 ^ j`. Reconstructing Besov norms from annular series
(`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_annulus`) yields Bahouri–Chemin–Danchin,
Theorem 2.82 as continuous bilinear maps:

* **Boundedness from `L^{p₁}`:** `TauCeti.BesovSpace.paraproductLpCLM : L^{p₁} × B^β_{p₂,q} →`
  `B^β_{r,q}` and `TauCeti.BesovSpace.paraproductRightLpCLM : B^α_{p₁,q} × L^{p₂} → B^α_{r,q}` for
  every `α, β ∈ ℝ` and `1/r = 1/p₁ + 1/p₂`, with operator norms independent of `p₁, p₂, r, q`, built
  from the existential series estimates
  `TauCeti.BesovSpace.exists_hasSum_lowPass_smul_block_and_norm_le_of_toDistr_eq` and
  `TauCeti.BesovSpace.exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq`.
* **Negative regularity:** `TauCeti.BesovSpace.paraproductNegCLM` (`α < 0`) and
  `TauCeti.BesovSpace.paraproductRightNegCLM` (`β < 0`) mapping
  `B^α_{p₁,q₁} × B^β_{p₂,q₂} → B^{α + β}_{r,q}` (`1/r = 1/p₁ + 1/p₂`, `1/q = 1/q₁ + 1/q₂`),
  proved via `TauCeti.BesovSpace.exists_lp_lowPass_sub_le_of_neg` and `lp.mulL`.
* **Vanishing and constant-`1` identities:** `paraproductLpCLM_eq_zero`,
  `paraproductRightLpCLM_eq_zero`, `paraproductNegCLM_eq_zero`, `paraproductRightNegCLM_eq_zero`
  (with single-block corollaries) and `toDistr_paraproductLpCLM_one_left`,
  `toDistr_paraproductNegCLM_one_left`, `paraproductRightLpCLM_one_left`,
  `paraproductLpCLM_one_right`, `paraproductRightNegCLM_one_left`, `paraproductNegCLM_one_right`.

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

section Helpers

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
    have : φ.rOut / 2 ^ N < φ.rIn := (div_lt_iff₀ (by positivity)).2 (by linarith); linarith
  obtain ⟨C, hC⟩ := exists_hasSum_toDistr_and_norm_le_of_annulus (F := F) φ s ha (2 * φ.rOut)
  refine ⟨max C 0, le_max_right _ _, fun {r q} _ _ g w hspec hw ↦ ?_⟩
  obtain ⟨y, hy, hyn⟩ := hC g w
    (fun j ↦ (hspec j).mono (Set.compl_subset_compl.2 Set.sdiff_subset))
    (fun j _ ↦ (hspec j).mono fun _ hξ ↦ by rintro ⟨-, h⟩; exact h hξ) hw
  exact ⟨y, hy, hyn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg w))⟩

/-- Combines `exists_hasSum_of_paraproduct_annulus` with `Lp.norm_smul_le` and `lp.mulL` to sum a
sequence of `Lʳ` products `f₁ j • f₂ j` localized in paraproduct annuli whose weighted norms are
majorized by `a ∈ ℓ^{q₁}` and `b ∈ ℓ^{q₂}`. -/
private theorem exists_hasSum_smul_of_paraproduct_annulus {φ : ContDiffBump (0 : E)} {N : ℕ}
    (α β : ℝ) (hN : φ.rOut < 2 ^ N * φ.rIn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q]
      (f₁ : ℕ → Lp ℂ p₁ (volume : Measure E)) (f₂ : ℕ → Lp F p₂ (volume : Measure E))
      (a : lp (fun _ : ℕ ↦ ℝ) q₁) (b : lp (fun _ : ℕ ↦ ℝ) q₂),
      (∀ j : ℕ, IsVanishingOn (𝓕 ((f₁ j • f₂ j : Lp F r (volume : Measure E)) : 𝓢'(E, F)) :
        𝓢'(E, F)) (closedBall 0 (2 ^ j * (2 * φ.rOut)) \
          ball 0 (2 ^ j * ((φ.rIn - φ.rOut / 2 ^ N) / 2)))ᶜ) →
      (∀ j : ℕ, 2 ^ (α * j) * ‖f₁ j‖ ≤ a j) →
      (∀ j : ℕ, 2 ^ (β * j) * ‖f₂ j‖ ≤ b j) →
      ∃ y : BesovSpace F φ (α + β) r q,
        HasSum (fun j ↦ ((f₁ j • f₂ j : Lp F r (volume : Measure E)) : 𝓢'(E, F))) y.toDistr ∧
        ‖y‖ ≤ C * (‖a‖ * ‖b‖) := by
  obtain ⟨C₀, hC₀, hann⟩ := exists_hasSum_of_paraproduct_annulus (F := F) (α + β) hN
  refine ⟨C₀, hC₀, fun {p₁ p₂ r q₁ q₂ q} _ _ _ _ _ _ _ _ f₁ f₂ a b hspec ha hb ↦ ?_⟩
  obtain ⟨y, hy, hyn⟩ := hann (fun j ↦ f₁ j • f₂ j) (lp.mulL ℝ ℝ q a b) hspec fun j ↦ by
    rw [lp.mulL_apply_apply]
    calc 2 ^ ((α + β) * j) * ‖f₁ j • f₂ j‖
        ≤ 2 ^ ((α + β) * j) * (‖f₁ j‖ * ‖f₂ j‖) :=
          mul_le_mul_of_nonneg_left (Lp.norm_smul_le _ _) (by positivity)
      _ = (2 ^ (α * j) * ‖f₁ j‖) * (2 ^ (β * j) * ‖f₂ j‖) := by
          rw [add_mul, Real.rpow_add two_pos]; ring
      _ ≤ a j * b j := mul_le_mul (ha j) (hb j) (by positivity)
          ((by positivity : (0 : ℝ) ≤ 2 ^ (α * j) * ‖f₁ j‖).trans (ha j))
  exact ⟨y, hy, hyn.trans (mul_le_mul_of_nonneg_left (lp.norm_mulL_apply_apply_le ℝ ℝ q a b) hC₀)⟩

end Helpers

section ParaproductLp

variable {φ : ContDiffBump (0 : E)} {N : ℕ} {α β : ℝ} {p₁ p₂ r q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [Fact (1 ≤ q)] [p₁.HolderTriple p₂ r]

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
    (fun f v ↦ (exists_hasSum_lowPass_smul_block_and_norm_le_of_toDistr_eq (F := F) φ β
      hN).choose_spec.2 (ofLpCLM ℂ φ p₁ f) (toDistr_ofLpCLM f) v)

/-- The tempered distribution of `paraproductLpCLM r hN f v` is the sum of the series
`∑ⱼ S_{j - N} f · Δⱼ v`. -/
theorem hasSum_paraproductLpCLM (hN : φ.rOut < 2 ^ N * φ.rIn)
    (f : Lp ℂ p₁ (volume : Measure E)) (v : BesovSpace F φ β p₂ q) :
    HasSum (fun j ↦ (((ofLpCLM ℂ φ p₁ f).lowPass (j - N) • v.block j :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) (paraproductLpCLM r hN f v).toDistr :=
  hasSum_mkContinuousOfHasSum₂ (X := Lp ℂ p₁ (volume : Measure E)) (Y := BesovSpace F φ β p₂ q)
    (r := r) (q := q) (γ := β)
    (fun j f v ↦ ((ofLpCLM ℂ φ p₁ f).lowPass (j - N) • v.block j : Lp F r (volume : Measure E)))
    (fun _ _ _ _ ↦ by simp [Lp.smul_add]) (fun _ _ _ _ ↦ by simp [Lp.smul_assoc])
    (fun _ _ _ _ ↦ by simp [block_add, Lp.add_smul])
    (fun _ _ _ _ ↦ by simp [block_smul, ← Lp.smul_comm])
    (fun f v ↦ (exists_hasSum_lowPass_smul_block_and_norm_le_of_toDistr_eq (F := F) φ β
      hN).choose_spec.2 (ofLpCLM ℂ φ p₁ f) (toDistr_ofLpCLM f) v) f v

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
  ⟨_, (exists_hasSum_lowPass_smul_block_and_norm_le_of_toDistr_eq (F := F) φ β hN).choose_spec.1,
    fun {_ _ _ _} _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _ _
      (exists_hasSum_lowPass_smul_block_and_norm_le_of_toDistr_eq (F := F) φ β hN).choose_spec.1⟩

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
    (fun u g ↦ (exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq (F := F) φ α
      hN).choose_spec.2 u (ofLpCLM F φ p₂ g) (toDistr_ofLpCLM g))

/-- The tempered distribution of `paraproductRightLpCLM r hN u g` is the sum of the series
`∑ⱼ Δⱼ u · S_{j - N} g`. -/
theorem hasSum_paraproductRightLpCLM (hN : φ.rOut < 2 ^ N * φ.rIn)
    (u : BesovSpace ℂ φ α p₁ q) (g : Lp F p₂ (volume : Measure E)) :
    HasSum (fun j ↦ ((u.block j • (ofLpCLM F φ p₂ g).lowPass (j - N) :
      Lp F r (volume : Measure E)) : 𝓢'(E, F))) (paraproductRightLpCLM r hN u g).toDistr :=
  hasSum_mkContinuousOfHasSum₂ (X := BesovSpace ℂ φ α p₁ q) (Y := Lp F p₂ (volume : Measure E))
    (r := r) (q := q) (γ := α)
    (fun j u g ↦ (u.block j • (ofLpCLM F φ p₂ g).lowPass (j - N) : Lp F r (volume : Measure E)))
    (fun _ _ _ _ ↦ by simp [block_add, Lp.smul_add])
    (fun _ _ _ _ ↦ by simp [block_smul, Lp.smul_assoc])
    (fun _ _ _ _ ↦ by simp [Lp.add_smul]) (fun _ _ _ _ ↦ by simp [← Lp.smul_comm])
    (fun u g ↦ (exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq (F := F) φ α
      hN).choose_spec.2 u (ofLpCLM F φ p₂ g) (toDistr_ofLpCLM g)) u g

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
  ⟨_, (exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq (F := F) φ α hN).choose_spec.1,
    fun {_ _ _ _} _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _ _
      (exists_hasSum_block_smul_lowPass_and_norm_le_of_toDistr_eq (F := F) φ α hN).choose_spec.1⟩

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
  obtain ⟨C₀, hC₀, hsmul⟩ := exists_hasSum_smul_of_paraproduct_annulus (F := F) α β hN
  have hden : 0 ≤ ((2 : ℝ) ^ (-α) - 1)⁻¹ :=
    inv_nonneg.2 (sub_nonneg.2 (Real.one_lt_rpow one_lt_two (neg_pos.2 hα)).le)
  refine ⟨C₀ * (2 ^ (-α) - 1)⁻¹, by positivity,
    fun {p₁ p₂ r q₁ q₂ q} _ _ _ _ _ _ _ _ u v ↦ ?_⟩
  obtain ⟨a, ha, han⟩ := exists_lp_lowPass_sub_le_of_neg hα N u
  obtain ⟨y, hy, hyn⟩ := hsmul (r := r) (q := q) (fun j ↦ u.lowPass (j - N)) v.block a
    (lp.toNorm v.weightedBlocks) (fun j ↦ isVanishingOn_fourier_lowPass_smul_block N j u v) ha
    (fun j ↦ by rw [lp.toNorm_coe, v.norm_weightedBlocks_apply])
  exact ⟨y, hy, hyn.trans <| by
    rw [lp.norm_toNorm, v.norm_weightedBlocks]
    calc C₀ * (‖a‖ * ‖v‖) ≤ C₀ * (((2 : ℝ) ^ (-α) - 1)⁻¹ * ‖u‖ * ‖v‖) := by gcongr
      _ = _ := by ring⟩

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
  hasSum_mkContinuousOfHasSum₂ (X := BesovSpace ℂ φ α p₁ q₁) (Y := BesovSpace F φ β p₂ q₂)
    (r := r) (q := q) (γ := α + β)
    (fun j u v ↦ (u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)))
    (fun _ _ _ _ ↦ by simp [Lp.smul_add]) (fun _ _ _ _ ↦ by simp [Lp.smul_assoc])
    (fun _ _ _ _ ↦ by simp [block_add, Lp.add_smul])
    (fun _ _ _ _ ↦ by simp [block_smul, ← Lp.smul_comm])
    (fun u v ↦ (exists_paraproductNeg (F := F) hN hα β).choose_spec.2 u v) u v

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
    fun {_ _ _ _ _ _} _ _ _ _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _ _
      (exists_paraproductNeg (F := F) hN hα β).choose_spec.1⟩

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
  obtain ⟨C₀, hC₀, hsmul⟩ := exists_hasSum_smul_of_paraproduct_annulus (F := F) α β hN
  have hden : 0 ≤ ((2 : ℝ) ^ (-β) - 1)⁻¹ :=
    inv_nonneg.2 (sub_nonneg.2 (Real.one_lt_rpow one_lt_two (neg_pos.2 hβ)).le)
  refine ⟨C₀ * (2 ^ (-β) - 1)⁻¹, by positivity,
    fun {p₁ p₂ r q₁ q₂ q} _ _ _ _ _ _ _ _ u v ↦ ?_⟩
  obtain ⟨b, hb, hbn⟩ := exists_lp_lowPass_sub_le_of_neg hβ N v
  obtain ⟨y, hy, hyn⟩ := hsmul (r := r) (q := q) u.block (fun j ↦ v.lowPass (j - N))
    (lp.toNorm u.weightedBlocks) b (fun j ↦ isVanishingOn_fourier_block_smul_lowPass N j u v)
    (fun j ↦ by rw [lp.toNorm_coe, u.norm_weightedBlocks_apply]) hb
  exact ⟨y, hy, hyn.trans <| by
    rw [lp.norm_toNorm, u.norm_weightedBlocks]
    calc C₀ * (‖u‖ * ‖b‖) ≤ C₀ * (‖u‖ * ((2 ^ (-β) - 1)⁻¹ * ‖v‖)) := by gcongr
      _ = _ := by ring⟩

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
  hasSum_mkContinuousOfHasSum₂ (X := BesovSpace ℂ φ α p₁ q₁) (Y := BesovSpace F φ β p₂ q₂)
    (r := r) (q := q) (γ := α + β)
    (fun j u v ↦ (u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)))
    (fun _ _ _ _ ↦ by simp [block_add, Lp.smul_add])
    (fun _ _ _ _ ↦ by simp [block_smul, Lp.smul_assoc])
    (fun _ _ _ _ ↦ by simp [Lp.add_smul]) (fun _ _ _ _ ↦ by simp [← Lp.smul_comm])
    (fun u v ↦ (exists_paraproductRightNeg (F := F) hN α hβ).choose_spec.2 u v) u v

/-- **Uniform operator norm bound for `paraproductRightNegCLM`.** -/
theorem exists_norm_paraproductRightNegCLM_le (hN : φ.rOut < 2 ^ N * φ.rIn) (α : ℝ) (hβ : β < 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
      [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
      [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)] [q₁.HolderTriple q₂ q],
      ‖paraproductRightNegCLM (F := F) (α := α) (β := β)
        (p₁ := p₁) (p₂ := p₂) (q₁ := q₁) (q₂ := q₂) r q hN hβ‖ ≤ C :=
  ⟨_, (exists_paraproductRightNeg (F := F) hN α hβ).choose_spec.1,
    fun {_ _ _ _ _ _} _ _ _ _ _ _ _ _ ↦ norm_mkContinuousOfHasSum₂_le _ _ _ _ _ _
      (exists_paraproductRightNeg (F := F) hN α hβ).choose_spec.1⟩

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

section Vanishing

variable {φ : ContDiffBump (0 : E)} {N : ℕ} {α β : ℝ} {p₁ p₂ r q₁ q₂ q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ r)] [p₁.HolderTriple p₂ r]
  [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)]

omit [Fact (1 ≤ r)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] in
private theorem lowPass_sub_smul_block_eq_zero {u : BesovSpace ℂ φ α p₁ q₁}
    {v : BesovSpace F φ β p₂ q₂} (h : ∀ k j, k + N < j → u.block k = 0 ∨ v.block j = 0) (j : ℕ) :
    (u.lowPass (j - N) • v.block j : Lp F r (volume : Measure E)) = 0 := by
  by_cases hv : v.block j = 0
  · simp [hv]
  · rw [lowPass_eq_sum, Finset.sum_eq_zero fun k hk ↦
      (h k j (by rw [Finset.mem_range] at hk; omega)).resolve_right hv, Lp.zero_smul]

omit [Fact (1 ≤ r)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] in
private theorem block_smul_lowPass_sub_eq_zero {u : BesovSpace ℂ φ α p₁ q₁}
    {v : BesovSpace F φ β p₂ q₂} (h : ∀ j k, k + N < j → u.block j = 0 ∨ v.block k = 0) (j : ℕ) :
    (u.block j • v.lowPass (j - N) : Lp F r (volume : Measure E)) = 0 := by
  by_cases hu : u.block j = 0
  · simp [hu]
  · rw [lowPass_eq_sum, Finset.sum_eq_zero fun k hk ↦
      (h j k (by rw [Finset.mem_range] at hk; omega)).resolve_left hu, Lp.smul_zero]

/-- **Paraproduct vanishing under separated frequency support (`L^{p₁}` form).** If every pair
`(k, j)` with `k + N < j` has either `Δₖ f = 0` or `Δⱼ v = 0`, then
`paraproductLpCLM r hN f v = 0`. -/
theorem paraproductLpCLM_eq_zero (hN : φ.rOut < 2 ^ N * φ.rIn)
    {f : Lp ℂ p₁ (volume : Measure E)} {v : BesovSpace F φ β p₂ q}
    (h : ∀ k j, k + N < j → littlewoodPaleyBlock ℂ φ k (f : 𝓢'(E, ℂ)) = 0 ∨ v.block j = 0) :
    paraproductLpCLM r hN f v = 0 := by
  refine ext <| ((hasSum_paraproductLpCLM (r := r) hN f v).congr_fun fun j ↦ ?_).unique hasSum_zero
  have h' : ∀ k j, k + N < j → (ofLpCLM ℂ φ p₁ f).block k = 0 ∨ v.block j = 0 := fun k j hkj ↦
    (h k j hkj).imp (fun hf ↦ Lp.toTemperedDistribution_injective (by simp [coe_block, hf])) id
  simp [lowPass_sub_smul_block_eq_zero h' j]

/-- **Right-paraproduct vanishing under separated frequency support (`L^{p₂}` form).** -/
theorem paraproductRightLpCLM_eq_zero (hN : φ.rOut < 2 ^ N * φ.rIn)
    {u : BesovSpace ℂ φ α p₁ q} {g : Lp F p₂ (volume : Measure E)}
    (h : ∀ j k, k + N < j → u.block j = 0 ∨ littlewoodPaleyBlock F φ k (g : 𝓢'(E, F)) = 0) :
    paraproductRightLpCLM r hN u g = 0 := by
  refine ext <| ((hasSum_paraproductRightLpCLM (r := r) hN u g).congr_fun fun j ↦ ?_).unique
    hasSum_zero
  have h' : ∀ j k, k + N < j → u.block j = 0 ∨ (ofLpCLM F φ p₂ g).block k = 0 := fun j k hkj ↦
    (h j k hkj).imp id fun hg ↦ Lp.toTemperedDistribution_injective (by simp [coe_block, hg])
  simp [block_smul_lowPass_sub_eq_zero h' j]

/-- **Paraproduct vanishing under separated frequency support (`α < 0` form).** -/
theorem paraproductNegCLM_eq_zero [q₁.HolderTriple q₂ q] (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hα : α < 0) {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (h : ∀ k j, k + N < j → u.block k = 0 ∨ v.block j = 0) :
    paraproductNegCLM r q hN hα u v = 0 :=
  ext <| ((hasSum_paraproductNegCLM (r := r) (q := q) hN hα u v).congr_fun fun j ↦ by
    simp [lowPass_sub_smul_block_eq_zero h j]).unique hasSum_zero

/-- **Right-paraproduct vanishing under separated frequency support (`β < 0` form).** -/
theorem paraproductRightNegCLM_eq_zero [q₁.HolderTriple q₂ q] (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hβ : β < 0) {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (h : ∀ j k, k + N < j → u.block j = 0 ∨ v.block k = 0) :
    paraproductRightNegCLM r q hN hβ u v = 0 :=
  ext <| ((hasSum_paraproductRightNegCLM (r := r) (q := q) hN hβ u v).congr_fun fun j ↦ by
    simp [block_smul_lowPass_sub_eq_zero h j]).unique hasSum_zero

/-- **Same-frequency paraproduct vanishing (`L^{p₁}` form).** When `f` and `v` are both carried by
the single dyadic block `j₀`, `paraproductLpCLM r hN f v = 0`. -/
theorem paraproductLpCLM_eq_zero_of_block_eq_zero (hN : φ.rOut < 2 ^ N * φ.rIn) {j₀ : ℕ}
    {f : Lp ℂ p₁ (volume : Measure E)} {v : BesovSpace F φ β p₂ q}
    (hf : ∀ k ≠ j₀, littlewoodPaleyBlock ℂ φ k (f : 𝓢'(E, ℂ)) = 0)
    (hv : ∀ k ≠ j₀, v.block k = 0) :
    paraproductLpCLM r hN f v = 0 :=
  paraproductLpCLM_eq_zero hN fun k j hkj ↦ (eq_or_ne j j₀).imp (fun hj ↦ hf k (by omega)) (hv j)

/-- **Same-frequency right-paraproduct vanishing (`L^{p₂}` form).** -/
theorem paraproductRightLpCLM_eq_zero_of_block_eq_zero (hN : φ.rOut < 2 ^ N * φ.rIn) {j₀ : ℕ}
    {u : BesovSpace ℂ φ α p₁ q} {g : Lp F p₂ (volume : Measure E)}
    (hu : ∀ k ≠ j₀, u.block k = 0)
    (hg : ∀ k ≠ j₀, littlewoodPaleyBlock F φ k (g : 𝓢'(E, F)) = 0) :
    paraproductRightLpCLM r hN u g = 0 :=
  paraproductRightLpCLM_eq_zero hN fun j k hkj ↦
    (eq_or_ne j j₀).symm.imp (hu j) fun hj ↦ hg k (by omega)

/-- **Same-frequency paraproduct vanishing (`α < 0` form).** -/
theorem paraproductNegCLM_eq_zero_of_block_eq_zero [q₁.HolderTriple q₂ q]
    (hN : φ.rOut < 2 ^ N * φ.rIn) (hα : α < 0) {j₀ : ℕ}
    {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) :
    paraproductNegCLM r q hN hα u v = 0 :=
  paraproductNegCLM_eq_zero hN hα fun k j hkj ↦
    (eq_or_ne j j₀).imp (fun hj ↦ hu k (by omega)) (hv j)

/-- **Same-frequency right-paraproduct vanishing (`β < 0` form).** -/
theorem paraproductRightNegCLM_eq_zero_of_block_eq_zero [q₁.HolderTriple q₂ q]
    (hN : φ.rOut < 2 ^ N * φ.rIn) (hβ : β < 0) {j₀ : ℕ}
    {u : BesovSpace ℂ φ α p₁ q₁} {v : BesovSpace F φ β p₂ q₂}
    (hu : ∀ k ≠ j₀, u.block k = 0) (hv : ∀ k ≠ j₀, v.block k = 0) :
    paraproductRightNegCLM r q hN hβ u v = 0 :=
  paraproductRightNegCLM_eq_zero hN hβ fun j k hkj ↦
    (eq_or_ne j j₀).symm.imp (hu j) fun hj ↦ hv k (by omega)

end Vanishing

section One

variable {φ : ContDiffBump (0 : E)} {N : ℕ} {α β : ℝ} {p₁ p₂ q₁ q₂ q : ℝ≥0∞}
  [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q₂)] [Fact (1 ≤ q)]

/-- **Left paraproduct with the constant `1` (`L^∞` form).** Because `Δ₀ 1 = 1` and `Δₖ 1 = 0` for
`k ≥ 1`, `S_{j - N} 1` vanishes for `j ≤ N` and equals `1` for `j ≥ N + 1`, so `T_1^N v` sums the
blocks `j ≥ N + 1` and equals `v - S_{N + 1} v`. -/
theorem toDistr_paraproductLpCLM_one_left (hN : φ.rOut < 2 ^ N * φ.rIn)
    (v : BesovSpace F φ β p₂ q) :
    (paraproductLpCLM p₂ hN (1 : Lp ℂ ∞ (volume : Measure E)) v).toDistr =
      v.toDistr - (v.lowPass (N + 1) : 𝓢'(E, F)) := by
  have hsub := (hasSum_paraproductLpCLM_of_toDistr_eq (r := p₂) hN
    (u := (1 : BesovSpace ℂ φ 0 ∞ ∞)) (f := (1 : Lp ℂ ∞ (volume : Measure E)))
    (by simp) v).tendsto_sum_nat.comp (tendsto_add_atTop_nat (N + 1))
  have hv : Tendsto (fun m ↦ (v.lowPass m : 𝓢'(E, F))) atTop (𝓝 v.toDistr) := by
    simpa [coe_lowPass] using tendsto_sum_littlewoodPaleyBlock φ v.toDistr
  have htail := (hv.comp (tendsto_add_atTop_nat (N + 1))).sub_const (v.lowPass (N + 1) : 𝓢'(E, F))
  refine tendsto_nhds_unique (hsub.congr fun m ↦ ?_) htail
  simp only [Function.comp_apply, Nat.add_comm m (N + 1)]
  have hzero : ∀ j ∈ Finset.range (N + 1), j - N = 0 := fun j hj ↦ by
    rw [Finset.mem_range] at hj; omega
  rw [Finset.sum_range_add, Finset.sum_eq_zero fun j hj ↦ by simp [hzero j hj], zero_add]
  have hidx (k : ℕ) : N + 1 + k - N = k + 1 := by omega
  simp_rw [hidx, lowPass_one_succ, Lp.one_smul]
  rw [lowPass_eq_sum v (N + 1 + m), lowPass_eq_sum v (N + 1), Lp.toTemperedDistribution_sum,
    Lp.toTemperedDistribution_sum, Finset.sum_range_add, add_sub_cancel_left]

/-- **Left paraproduct with `1` at negative regularity.** -/
theorem toDistr_paraproductNegCLM_one_left [q₁.HolderTriple q₂ q] (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hα : α < 0) (v : BesovSpace F φ β p₂ q₂) :
    (paraproductNegCLM p₂ q hN hα (1 : BesovSpace ℂ φ α ∞ q₁) v).toDistr =
      v.toDistr - (v.lowPass (N + 1) : 𝓢'(E, F)) := by
  rw [toDistr_paraproductNegCLM_eq_paraproductLpCLM hN hα
    (f := (1 : Lp ℂ ∞ (volume : Measure E))) (by simp) v, toDistr_paraproductLpCLM_one_left hN v]

/-- **Right paraproduct of `1` vanishes (`L^{p₂}` form).** Since `Δ₀ 1` meets `S_{0 - N} g = 0` and
`Δⱼ 1 = 0` for `j ≥ 1`, every term of `T_g^N 1` is zero. -/
@[simp] theorem paraproductRightLpCLM_one_left (hN : φ.rOut < 2 ^ N * φ.rIn)
    (g : Lp F p₂ (volume : Measure E)) :
    paraproductRightLpCLM p₂ hN (1 : BesovSpace ℂ φ α ∞ q) g = 0 :=
  paraproductRightLpCLM_eq_zero hN fun j k hkj ↦
    Or.inl (by cases j with | zero => omega | succ => simp)

/-- **Paraproduct onto `1` vanishes (`L^{p₁}` form).** -/
@[simp] theorem paraproductLpCLM_one_right (hN : φ.rOut < 2 ^ N * φ.rIn)
    (f : Lp ℂ p₁ (volume : Measure E)) :
    paraproductLpCLM p₁ hN f (1 : BesovSpace ℂ φ β ∞ q) = 0 :=
  paraproductLpCLM_eq_zero hN fun k j hkj ↦ Or.inr (by cases j with | zero => omega | succ => simp)

/-- **Right paraproduct of `1` vanishes (`β < 0` form).** -/
@[simp] theorem paraproductRightNegCLM_one_left [q₁.HolderTriple q₂ q] (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hβ : β < 0) (v : BesovSpace F φ β p₂ q₂) :
    paraproductRightNegCLM p₂ q hN hβ (1 : BesovSpace ℂ φ α ∞ q₁) v = 0 :=
  paraproductRightNegCLM_eq_zero hN hβ fun j k hkj ↦
    Or.inl (by cases j with | zero => omega | succ => simp)

/-- **Paraproduct onto `1` vanishes (`α < 0` form).** -/
@[simp] theorem paraproductNegCLM_one_right [q₁.HolderTriple q₂ q] (hN : φ.rOut < 2 ^ N * φ.rIn)
    (hα : α < 0) (u : BesovSpace ℂ φ α p₁ q₁) :
    paraproductNegCLM p₁ q hN hα u (1 : BesovSpace ℂ φ β ∞ q₂) = 0 :=
  paraproductNegCLM_eq_zero hN hα fun k j hkj ↦
    Or.inr (by cases j with | zero => omega | succ => simp)

end One

end TauCeti.BesovSpace
