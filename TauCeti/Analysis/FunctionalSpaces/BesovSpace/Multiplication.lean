/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Bernstein
import TauCeti.Analysis.Distribution.TemperedDistribution.FourierMultiplier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
import TauCeti.Analysis.Normed.Lp.Reindex
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Multiplication by smooth functions on Besov spaces

Let `s ∈ ℝ` and let `g : E → ℂ` be a function of temperate growth whose derivatives of order at
most `N` are bounded, for a natural number `N > |s|`. Multiplication by `g` maps every
inhomogeneous Besov space `B^s_{p,q}`, `1 ≤ p, q ≤ ∞`, boundedly to itself
(`TemperedDistribution.MemBesov.smulLeftCLM`, `TauCeti.BesovSpace.smulLeftCLM`). The operator norm
is at most `C G`, where `C` depends only on the bump function `φ`, on `s` and on `N`, and `G`
bounds the derivatives of `g` of order at most `N`
(`TauCeti.BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le`). In particular the bound does
not depend on `p` or `q`, and it covers the Hölder–Zygmund scale `𝒞^s = B^s_{∞,∞}` and the
negative orders `s < 0`. Scalar smooth multipliers are the scalar case of the matrix-valued
changes of frame needed for Besov norms of sections of vector bundles.

The proof estimates how multiplication by `g` moves frequencies between the Littlewood–Paley
blocks: for `N` derivatives of `g` bounded by `G`,

`‖Δⱼ (g Δₖ u)‖_p ≤ K G 2^{-N |j - k|} ‖Δₖ u‖_p`

(`TauCeti.exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le`).

* For `j > k`, the spectrum of `Δⱼ (g Δₖ u)` lies in the `j`-th dyadic annulus, where the reverse
  Bernstein inequality bounds a function by `2^{-jN}` times its derivatives of order `N`. By the
  Leibniz rule and Bernstein's inequality for `Δₖ u`, those derivatives are `O(2^{kN})`.
* For `j < k`, the block `Δₖ u` lies in the `k`-th annulus, so `Δₖ u = ∑ᵢ ∂_{bᵢ} hᵢ` with
  `‖hᵢ‖_p = O(2^{-k} ‖Δₖ u‖_p)` (`OrthonormalBasis.exists_eq_sum_lineDerivOp_and_norm_le`). The
  identity `g ∂_{bᵢ} hᵢ = ∂_{bᵢ} (g hᵢ) - (∂_{bᵢ} g) hᵢ` moves the derivative onto `Δⱼ`, where it
  costs `2^j`. Repeating this `N` times gains `2^{N (j - k)}`.
* For `j = k` the multiplication and the block are bounded on `Lᵖ`.

Summing over `u = ∑ₖ Δₖ u` with `N > |s|`, the weighted blocks `2^{js} Δⱼ (g u)` are controlled by
`∑ₖ r^{|j - k|} 2^{ks} ‖Δₖ u‖_p` with `r = 2^{|s| - N} < 1`. Grouping the terms by the offset
`d = k - j ∈ ℤ` gives a series in `ℓ^q(ℕ, Lᵖ)` whose `d`-th term has norm `O(r^{|d|} ‖u‖)`. It
converges absolutely, and its sum is the sequence of weighted blocks of `g u`.

## Main declarations

* `TauCeti.exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le`: the block estimate above.
* `TauCeti.BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le`: multiplication by `g` maps
  `B^s_{p,q}` to itself with norm at most `C G`, uniformly in `p` and `q`.
* `TemperedDistribution.MemBesov.smulLeftCLM`: `B^s_{p,q}` is stable under multiplication by
  functions of temperate growth whose derivatives of order at most `⌊|s|⌋₊ + 1` are bounded.
* `TauCeti.BesovSpace.smulLeftCLM`: the multiplication as a bounded operator on `B^s_{p,q}`, with
  operator norm at most `C G` (`TauCeti.BesovSpace.exists_norm_smulLeftCLM_le`).

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8.2 (smooth functions as
  pointwise multipliers of Besov spaces).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, §2.1 (Bernstein's inequalities).
-/

public section

noncomputable section

open MeasureTheory Metric Distribution FourierTransform
open scoped ENNReal SchwartzMap LineDeriv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

open TemperedDistribution

/-! ### Interaction of a multiplication with the Littlewood–Paley blocks -/

/-- There is `K`, depending only on `φ`, such that for a function `g` of temperate growth bounded
by `G` and `f ∈ Lᵖ`, every block `Δⱼ (g f)` is an `Lᵖ` function of norm at most `K G ‖f‖_p`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le_of_norm_le
    (φ : ContDiffBump (0 : E)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ x, ‖g x‖ ≤ G) → ∀ (j : ℕ) (f : Lp F p (volume : Measure E)),
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (f : 𝓢'(E, F))) = v ∧ ‖v‖ ≤ K * G * ‖f‖ := by
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  refine ⟨max CΔ 0, le_max_right _ _, fun {p} _ {g G} hg hG j f ↦ ?_⟩
  obtain ⟨h, hh, hhn⟩ := Lp.exists_smulLeftCLM_toTemperedDistribution_eq_and_norm_le hg hG f
  obtain ⟨w, hw, hwn⟩ := hΔ j h
  refine ⟨w, by rw [hh, hw], ?_⟩
  calc ‖w‖ ≤ CΔ * ‖h‖ := hwn
    _ ≤ max CΔ 0 * (G * ‖f‖) :=
      mul_le_mul (le_max_left _ _) hhn (norm_nonneg _) (le_max_right _ _)
    _ = _ := by ring

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The outer radius `2^{k+1} φ.rOut` of the `(k+1)`-st dyadic annulus is `B` times its inner
radius `2^k φ.rIn`, for `B = 2 φ.rOut / φ.rIn`. -/
private theorem two_mul_rOut_div_rIn_mul (φ : ContDiffBump (0 : E)) (k : ℕ) :
    2 * φ.rOut / φ.rIn * (2 ^ k * φ.rIn) = 2 ^ (k + 1) * φ.rOut := by
  field_simp [φ.rIn_pos.ne']
  ring

/-- **High output frequency, low input frequency.** Let `M` be a natural number. There is `K`,
depending only on `φ` and `M`, with the following property. Let `g` be a function of temperate
growth whose derivatives of order at most `M` are bounded by `G`, and let `f ∈ Lᵖ` have spectrum
in the ball of radius `2^k φ.rOut`. Then for `j > k` the block `Δⱼ (g f)` is an `Lᵖ` function of
norm at most `K G (2^k / 2^j)^M ‖f‖_p`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le_of_lt
    (φ : ContDiffBump (0 : E)) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ {j k : ℕ}, k < j →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (closedBall 0 (2 ^ k * φ.rOut))ᶜ →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (f : 𝓢'(E, F))) = v ∧
        ‖v‖ ≤ K * G * ((2 : ℝ) ^ k / 2 ^ j) ^ M * ‖f‖ := by
  -- On the annulus carrying `Δⱼ`, the reverse Bernstein inequality bounds `Δⱼ (g f)` by `2^{-jM}`
  -- times its derivatives of order `M`, and the Leibniz rule with Bernstein's inequality for `f`
  -- bounds these derivatives by `2^{kM}`.
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨Cr, hCr, hrev⟩ :=
    b.exists_norm_le_div_pow_mul_sum_norm_of_iteratedLineDerivOp_eq (F := F)
      (2 * φ.rOut / φ.rIn)
  obtain ⟨CL, -, hleib⟩ :=
    exists_iteratedLineDerivOp_smulLeftCLM_eq_and_norm_le (E := E) (F := F)
  obtain ⟨CΔ, hΔ⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := F) φ
  obtain ⟨K₀, -, h₀⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le_of_norm_le (F := F) φ
  set A := 2 * 2 * Cr * Module.finrank ℝ E * max 1 (CL * φ.rOut) / φ.rIn
  have hA : 0 ≤ A := by have := φ.rIn_pos; positivity
  refine ⟨A ^ M * max CΔ 0, by positivity, fun {p} _ {g G} hg hgG {j k} hkj f hf ↦ ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hG, hg₀⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG
  -- The block `w = Δⱼ (g f)` is an `Lᵖ` function with annular spectrum.
  obtain ⟨w, hw, -⟩ := h₀ hg hg₀ (j + 1) f
  refine ⟨w, hw, ?_⟩
  have hR : (0 : ℝ) < 2 ^ j * φ.rIn := by have := φ.rIn_pos; positivity
  have hwv : IsVanishingOn (𝓕 (w : 𝓢'(E, F)) : 𝓢'(E, F))
      (ball 0 (2 ^ j * φ.rIn) ∪ (closedBall 0 (2 * φ.rOut / φ.rIn * (2 ^ j * φ.rIn)))ᶜ) := by
    rw [two_mul_rOut_div_rIn_mul, ← hw]
    simpa only [Set.compl_sdiff, Set.union_comm] using
      isVanishingOn_fourier_littlewoodPaleyBlock_succ φ j _
  -- The derivatives of order `M` of `w` along the basis are the blocks of those of `g f`.
  have hR' : (0 : ℝ) < 2 ^ k * φ.rOut := by have := φ.rOut_pos; positivity
  choose y hy hyn using fun i : Fin M → Fin (Module.finrank ℝ E) ↦
    hleib M hg hgG hR' f hf (b ∘ i)
  choose z hz hzn using fun i : Fin M → Fin (Module.finrank ℝ E) ↦ hΔ (j + 1) (y i)
  have hder (i : Fin M → Fin (Module.finrank ℝ E)) : ∂^{⇑b ∘ i} (w : 𝓢'(E, F)) = z i := by
    rw [← hw, ← littlewoodPaleyBlock_iteratedLineDerivOp, hy i, hz i]
  -- The Leibniz bound at radius `2^k φ.rOut` grows like `2^{kM}`.
  have hmax : max 1 (CL * (2 ^ k * φ.rOut)) ≤ 2 ^ k * max 1 (CL * φ.rOut) := by
    have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
    refine max_le ?_ ?_
    · nlinarith [le_max_left 1 (CL * φ.rOut)]
    · rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
  have hz' (i : Fin M → Fin (Module.finrank ℝ E)) :
      ‖z i‖ ≤ max CΔ 0 * ((2 * (2 ^ k * max 1 (CL * φ.rOut))) ^ M * G * ‖f‖) := by
    have hyi := hyn i
    simp only [Function.comp_apply, b.orthonormal.1, Finset.prod_const_one, mul_one] at hyi
    refine (hzn i).trans (mul_le_mul (le_max_left _ _) (hyi.trans ?_) (norm_nonneg _)
      (le_max_right _ _))
    gcongr
  calc ‖w‖ ≤ (Cr / (2 ^ j * φ.rIn)) ^ M * ∑ i, ‖z i‖ := hrev M hR w z hwv hder
    _ ≤ (Cr / (2 ^ j * φ.rIn)) ^ M * ∑ _i : Fin M → Fin (Module.finrank ℝ E),
          max CΔ 0 * ((2 * (2 ^ k * max 1 (CL * φ.rOut))) ^ M * G * ‖f‖) := by
        gcongr with i
        exact hz' i
    _ = A ^ M * max CΔ 0 * G * ((2 : ℝ) ^ k / 2 ^ (j + 1)) ^ M * ‖f‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, A, div_pow, mul_pow, pow_succ]
        have := φ.rIn_pos
        push_cast
        field_simp

/-- **Low output frequency, high input frequency.** Let `B` be a real number and `M` a natural
number. There is `K`, depending only on `φ`, `B` and `M`, with the following property. Let `g` be
a function of temperate growth whose derivatives of order at most `M` are bounded by `G`, and let
`f ∈ Lᵖ` have spectrum in the annulus `R ≤ ‖ξ‖ ≤ B R`. Then every block `Δⱼ (g f)` is an `Lᵖ`
function of norm at most `K G (2^j / R)^M ‖f‖_p`. -/
private theorem exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le_of_annulus
    (φ : ContDiffBump (0 : E)) (B : ℝ) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ (j : ℕ) {R : ℝ}, 0 < R →
      ∀ f : Lp F p (volume : Measure E),
      IsVanishingOn (𝓕 (f : 𝓢'(E, F)) : 𝓢'(E, F)) (ball 0 R ∪ (closedBall 0 (B * R))ᶜ) →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (f : 𝓢'(E, F))) = v ∧
        ‖v‖ ≤ K * G * ((2 : ℝ) ^ j / R) ^ M * ‖f‖ := by
  -- Induction on `M`. On the annulus, `f = ∑ᵢ ∂_{bᵢ} hᵢ` with `‖hᵢ‖_p` of order `R⁻¹ ‖f‖_p`, and
  -- `g ∂_{bᵢ} hᵢ = ∂_{bᵢ} (g hᵢ) - (∂_{bᵢ} g) hᵢ`; Bernstein's inequality bounds `∂_{bᵢ}` on the
  -- spectrum of `Δⱼ` by `2^j`. Each step gains `2^j / R`.
  set b := stdOrthonormalBasis ℝ E
  obtain ⟨Crep, hCrep, hrep⟩ := b.exists_eq_sum_lineDerivOp_and_norm_le (F := F) B
  obtain ⟨CB, hCB, hB⟩ :=
    exists_lineDerivOp_eq_and_norm_le_of_isVanishingOn_fourier (E := E) (F := F)
  obtain ⟨K₀, hK₀, h₀⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le_of_norm_le (F := F) φ
  induction M with
  | zero =>
    refine ⟨K₀, hK₀, fun {p} _ {g G} hg hgG j R _ f _ ↦ ?_⟩
    obtain ⟨w, hw, hwn⟩ := h₀ hg (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).2 j f
    exact ⟨w, hw, by simpa using hwn⟩
  | succ M ih =>
    obtain ⟨K, hK, hKb⟩ := ih
    refine ⟨Module.finrank ℝ E * Crep * (CB * φ.rOut + 1) * K, by have := φ.rOut_pos; positivity,
      fun {p} _ {g G} hg hgG j R hR f hf ↦ ?_⟩
    obtain ⟨hG, -⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG
    obtain ⟨h, hfh, hh⟩ := hrep hR f hf
    -- `Δⱼ (g hᵢ)` is band-limited to the ball of radius `2^j φ.rOut`, so Bernstein's inequality
    -- bounds its derivative.
    choose y hy hyn using fun i ↦ hKb hg (fun n hn ↦ hgG n (by omega)) j hR (h i) (hh i).1
    have hR' : (0 : ℝ) < 2 ^ j * φ.rOut := by have := φ.rOut_pos; positivity
    choose y' hy' hy'n using fun i ↦ hB hR' (y i) (by
      rw [← hy i]; exact isVanishingOn_fourier_littlewoodPaleyBlock φ j _) (b i)
    have hgb (i : Fin (Module.finrank ℝ E)) :
        ∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n (fun y ↦ fderiv ℝ g y (b i)) x‖ ≤ G := by
      simpa [b.orthonormal.1] using hg.1.norm_iteratedFDeriv_fderiv_apply_le_of_forall_le (by
        rw [minSmoothness_of_isRCLikeNormedField]; exact_mod_cast le_top) hgG (b i)
    choose z hz hzn using fun i ↦ hKb (hg.fderiv_apply (b i)) (hgb i) j hR (h i) (hh i).1
    refine ⟨∑ i, (y' i - z i), ?_, ?_⟩
    · -- `g ∂_{bᵢ} hᵢ = ∂_{bᵢ} (g hᵢ) - (∂_{bᵢ} g) hᵢ`.
      have hleib (i : Fin (Module.finrank ℝ E)) :
          smulLeftCLM F g (∂_{b i} (h i : 𝓢'(E, F))) =
            ∂_{b i} (smulLeftCLM F g (h i : 𝓢'(E, F))) -
              smulLeftCLM F (fun y ↦ fderiv ℝ g y (b i)) (h i : 𝓢'(E, F)) := by
        rw [lineDerivOp_smulLeftCLM hg]
        abel
      rw [hfh, map_sum, map_sum]
      simp_rw [hleib, map_sub, littlewoodPaleyBlock_lineDerivOp, hy, hy', hz,
        Lp.toTemperedDistribution_sum, Lp.toTemperedDistribution_sub]
    · have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ one_le_two
      have hterm (i : Fin (Module.finrank ℝ E)) : ‖y' i - z i‖ ≤
          Crep * (CB * φ.rOut + 1) * K * G * ((2 : ℝ) ^ j / R) ^ (M + 1) * ‖f‖ := by
        have hy'i := hy'n i
        rw [b.orthonormal.1 i, mul_one] at hy'i
        calc ‖y' i - z i‖ ≤ ‖y' i‖ + ‖z i‖ := norm_sub_le _ _
          _ ≤ CB * (2 ^ j * φ.rOut) * (K * G * ((2 : ℝ) ^ j / R) ^ M * ‖h i‖) +
              K * G * ((2 : ℝ) ^ j / R) ^ M * ‖h i‖ := by
            gcongr
            · exact hy'i.trans (by gcongr; exact hyn i)
            · exact hzn i
          _ = (CB * φ.rOut * 2 ^ j + 1) * (K * G * ((2 : ℝ) ^ j / R) ^ M) * ‖h i‖ := by ring
          _ ≤ (CB * φ.rOut + 1) * 2 ^ j * (K * G * ((2 : ℝ) ^ j / R) ^ M) * (Crep / R * ‖f‖) := by
            have hle : CB * φ.rOut * 2 ^ j + 1 ≤ (CB * φ.rOut + 1) * 2 ^ j := by linarith
            exact mul_le_mul (mul_le_mul_of_nonneg_right hle (by positivity)) (hh i).2
              (norm_nonneg _) (by have := φ.rOut_pos; positivity)
          _ = _ := by
            rw [pow_succ]
            field_simp
      calc ‖∑ i, (y' i - z i)‖ ≤ ∑ i, ‖y' i - z i‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin (Module.finrank ℝ E),
            Crep * (CB * φ.rOut + 1) * K * G * ((2 : ℝ) ^ j / R) ^ (M + 1) * ‖f‖ :=
          Finset.sum_le_sum fun i _ ↦ hterm i
        _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring

/-- **Off-diagonal decay of a multiplication between Littlewood–Paley blocks.** Let `M` be a
natural number. There is `K`, depending only on `φ` and `M`, with the following property. Let `g`
be a function of temperate growth whose derivatives of order at most `M` are bounded by `G`, let
`1 ≤ p ≤ ∞`, and let the block `Δₖ u` of a tempered distribution be an `Lᵖ` function `f`. Then
for every `j` the block `Δⱼ (g f)` is an `Lᵖ` function of norm at most
`K G 2^{-M |j - k|} ‖f‖_p`. -/
theorem exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le
    (φ : ContDiffBump (0 : E)) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ (j k : ℕ) (u : 𝓢'(E, F))
      (f : Lp F p (volume : Measure E)), littlewoodPaleyBlock F φ k u = f →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (f : 𝓢'(E, F))) = v ∧
        ‖v‖ ≤ K * G * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
  obtain ⟨K₁, hK₁, h₁⟩ := exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le_of_lt (F := F) φ M
  obtain ⟨K₂, hK₂, h₂⟩ := exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le_of_annulus
    (F := F) φ (2 * φ.rOut / φ.rIn) M
  obtain ⟨K₀, hK₀, h₀⟩ :=
    exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le_of_norm_le (F := F) φ
  have hrIn := φ.rIn_pos
  refine ⟨K₁ + K₂ * (2 / φ.rIn) ^ M + K₀, by positivity,
    fun {p} _ {g G} hg hgG j k u f hf ↦ ?_⟩
  obtain ⟨hG, hg₀⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG
  have h₂' : 0 ≤ K₂ * (2 / φ.rIn) ^ M := by positivity
  have hK (K : ℝ) (hKK : K ≤ K₁ + K₂ * (2 / φ.rIn) ^ M + K₀) :
      K * G * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ ≤
        (K₁ + K₂ * (2 / φ.rIn) ^ M + K₀) * G * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
    gcongr
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · -- High output frequency: the block `f` is band-limited to the ball of radius `2^k φ.rOut`.
    obtain ⟨v, hv, hvn⟩ := h₁ hg hgG hkj f
      (hf ▸ isVanishingOn_fourier_littlewoodPaleyBlock φ k u)
    refine ⟨v, hv, (hvn.trans_eq ?_).trans (hK K₁ (by linarith))⟩
    rw [Real.pow_div_pow_pow_eq_rpow_of_le two_pos hkj.le]
  · -- Equal frequencies: the multiplication and the block are bounded on `Lᵖ`.
    obtain ⟨v, hv, hvn⟩ := h₀ hg hg₀ k f
    refine ⟨v, hv, ?_⟩
    calc ‖v‖ ≤ K₀ * G * (2 : ℝ) ^ (-(M * |(k : ℝ) - k|)) * ‖f‖ := by simpa using hvn
      _ ≤ _ := hK _ (by linarith)
  · -- High input frequency: the block `f` has spectrum in the `k`-th dyadic annulus.
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hR : (0 : ℝ) < 2 ^ k * φ.rIn := by positivity
    obtain ⟨v, hv, hvn⟩ := h₂ hg hgG j hR f (by
      rw [two_mul_rOut_div_rIn_mul, ← hf]
      simpa only [Set.compl_sdiff, Set.union_comm] using
        isVanishingOn_fourier_littlewoodPaleyBlock_succ φ k u)
    refine ⟨v, hv, (hvn.trans_eq ?_).trans (hK (K₂ * (2 / φ.rIn) ^ M) (by linarith))⟩
    rw [abs_sub_comm, ← Real.pow_div_pow_pow_eq_rpow_of_le two_pos hjk.le, div_pow, div_pow,
      div_pow, mul_pow, pow_succ]
    field_simp
    ring

/-! ### Multiplication on Besov spaces -/

/-- **Multiplication by a smooth function is bounded on Besov spaces.** Let `N` be a natural
number with `|s| < N`. There is `C`, depending only on `φ`, `s` and `N`, with the following
property. Let `g` be a function of temperate growth whose derivatives of order at most `N` are
bounded by `G`. Then for all `1 ≤ p, q ≤ ∞` and every `u ∈ B^s_{p,q}`, the product `g u` lies in
`B^s_{p,q}` and `‖g u‖ ≤ C G ‖u‖`. -/
theorem BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le (φ : ContDiffBump (0 : E))
    {s : ℝ} {N : ℕ} (hN : |s| < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : E → ℂ} {G : ℝ}, g.HasTemperateGrowth →
      (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) →
      ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace F φ s p q),
      ∃ v : BesovSpace F φ s p q, v.toDistr = smulLeftCLM F g u.toDistr ∧ ‖v‖ ≤ C * G * ‖u‖ := by
  -- With `N > |s|`, the weighted interaction `2^{js} 2^{-N |j - k|} 2^{-ks}` of the blocks `j`
  -- and `k` is at most `r^{|j - k|}` with `r = 2^{|s| - N} < 1`, and the weighted blocks of
  -- `g u` are the row sums of a matrix with geometric decay away from the diagonal.
  set r : ℝ := 2 ^ (|s| - N)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  obtain ⟨K, hK, hblock⟩ := exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le (F := F) φ N
  refine ⟨K * ∑' d : ℤ, r ^ d.natAbs, by positivity, fun {g G} hg hgG {p q} _ _ u ↦ ?_⟩
  obtain ⟨hG, -⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG
  set c : ℕ → ℂ := fun j ↦ (((2 : ℝ) ^ (s * j) : ℝ) : ℂ)
  -- `Δⱼ (g Δₖ u)` is an `Lᵖ` function `v j k`, and `2^{js} v j k` is dominated by
  -- `K G r^{|k - j|}` times the weighted block `2^{ks} Δₖ u`.
  choose v hv hvn using fun j k ↦
    hblock hg hgG j k u.toDistr (u.block k) (u.coe_block k).symm
  have hentry (j k : ℕ) :
      ‖c j • v j k‖ ≤ K * G * r ^ ((k : ℤ) - j).natAbs * ‖u.weightedBlocks k‖ := by
    have hexp : s * j + -(N * |(j : ℝ) - k|) ≤ (|s| - N) * |(j : ℝ) - k| + s * k := by
      have := (le_abs_self (s * (j - k))).trans_eq (abs_mul s ((j : ℝ) - k))
      nlinarith
    have hr : r ^ ((k : ℤ) - j).natAbs = (2 : ℝ) ^ ((|s| - N) * |(j : ℝ) - k|) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, Nat.cast_natAbs, Int.cast_abs,
        abs_sub_comm, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
    rw [norm_smul, Complex.norm_of_nonneg (by positivity), u.norm_weightedBlocks_apply k, hr]
    calc (2 : ℝ) ^ (s * j) * ‖v j k‖
        ≤ (2 : ℝ) ^ (s * j) * (K * G * (2 : ℝ) ^ (-(N * |(j : ℝ) - k|)) * ‖u.block k‖) := by
          gcongr
          exact hvn j k
      _ = K * G * (2 : ℝ) ^ (s * j + -(N * |(j : ℝ) - k|)) * ‖u.block k‖ := by
          rw [Real.rpow_add two_pos]
          ring
      _ ≤ K * G * (2 : ℝ) ^ ((|s| - N) * |(j : ℝ) - k| + s * k) * ‖u.block k‖ := by
          gcongr
          exact one_le_two
      _ = _ := by
          rw [Real.rpow_add two_pos]
          ring
  have hsum : Summable fun d : ℤ ↦ r ^ d.natAbs :=
    summable_int_iff_summable_nat_and_neg.2
      ⟨by simpa using summable_geometric_of_lt_one hr0 hr1,
        by simpa using summable_geometric_of_lt_one hr0 hr1⟩
  obtain ⟨W, hWj, hWn⟩ := lp.exists_hasSum_and_norm_le_of_summable u.weightedBlocks
    (fun d ↦ by positivity) hsum (by positivity) (fun j k ↦ c j • v j k) hentry
  -- The tempered distribution of `W j` is `2^{js} Δⱼ (g u)`, the limit of
  -- `2^{js} Δⱼ (g ∑_{k < n} Δₖ u)`.
  have hW (j : ℕ) : (W j : 𝓢'(E, F)) = c j • littlewoodPaleyBlock F φ j
      (smulLeftCLM F g u.toDistr) := by
    have h₁ := ((Lp.toTemperedDistributionCLM F volume p).continuous.tendsto _).comp
      (hWj j).tendsto_sum_nat
    have h₂ := ((c j • (littlewoodPaleyBlock F φ j ∘L smulLeftCLM F g)).continuous.tendsto _).comp
      (tendsto_sum_littlewoodPaleyBlock φ u.toDistr)
    refine tendsto_nhds_unique h₁ (h₂.congr fun n ↦ ?_)
    simp only [Function.comp_apply, map_sum, map_smul, smul_apply,
      ContinuousLinearMap.comp_apply, Lp.toTemperedDistributionCLM_apply]
    simp_rw [← u.coe_block, hv]
  refine ⟨⟨smulLeftCLM F g u.toDistr, W, hW⟩, rfl, ?_⟩
  rw [← norm_weightedBlocks, ← u.norm_weightedBlocks]
  exact hWn.trans_eq (by ring)

end TauCeti

namespace TemperedDistribution

open TauCeti

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Smooth multipliers of Besov spaces.** If `u ∈ B^s_{p,q}` and `g` is a function of temperate
growth whose derivatives of order at most `⌊|s|⌋₊ + 1`, the least natural number exceeding `|s|`,
are bounded, then `g u ∈ B^s_{p,q}`. -/
theorem MemBesov.smulLeftCLM {u : 𝓢'(E, F)} (hu : u.MemBesov φ s p q) {g : E → ℂ}
    (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    (smulLeftCLM F g u).MemBesov φ s p q := by
  obtain ⟨C, -, hC⟩ := BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le (F := F) φ
    (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _)
  obtain ⟨G, hG⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_exists hbd
  obtain ⟨v, hv, -⟩ := hC hg hG hu.toBesovSpace
  rw [← hu.toDistr_toBesovSpace, ← hv]
  exact v.memBesov_toDistr

end TemperedDistribution

namespace TauCeti.BesovSpace

open TemperedDistribution

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (F φ s p q) in
/-- **Multiplication by a smooth function** `g` of temperate growth whose derivatives of order at
most `⌊|s|⌋₊ + 1` are bounded, as a bounded operator on `B^s_{p,q}`. Its norm is bounded by a
constant depending only on `φ`, `s` and `N` times a bound for the derivatives of `g` of order at
most `N`, for any natural number `N > |s|` (`TauCeti.BesovSpace.exists_norm_smulLeftCLM_le`). -/
def smulLeftCLM (g : E → ℂ) (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) :
    BesovSpace F φ s p q →L[ℂ] BesovSpace F φ s p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := (u.memBesov_toDistr.smulLeftCLM hg hbd).toBesovSpace
      map_add' _ _ := ext (by simp)
      map_smul' _ _ := ext (by simp) } <| by
    obtain ⟨C, -, hC⟩ := exists_toDistr_eq_smulLeftCLM_and_norm_le (F := F) φ
      (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _)
    obtain ⟨G, hG⟩ := exists_forall_norm_iteratedFDeriv_le_of_forall_exists hbd
    refine ⟨C * G, fun u ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := hC hg hG (p := p) (q := q) u
    have : (u.memBesov_toDistr.smulLeftCLM hg hbd).toBesovSpace = v := ext (by simp [hv])
    simpa [this] using hvn

@[simp]
theorem toDistr_smulLeftCLM {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C) (u : BesovSpace F φ s p q) :
    (smulLeftCLM F φ s p q g hg hbd u).toDistr = TemperedDistribution.smulLeftCLM F g u.toDistr :=
  by simp [smulLeftCLM]

/-- **The norm of a smooth multiplier of Besov spaces.** Let `N` be a natural number with
`|s| < N`. There is `C`, depending only on `φ`, `s` and `N`, with the following property. If the
derivatives of order at most `N` of `g` are bounded by `G`, then multiplication by `g` has operator
norm at most `C G` on `B^s_{p,q}` for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_smulLeftCLM_le (φ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {g : E → ℂ}
      (hg : g.HasTemperateGrowth) (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
      {G : ℝ}, (∀ n ≤ N, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) →
      ‖smulLeftCLM F φ s p q g hg hbd‖ ≤ C * G := by
  obtain ⟨C, hC, hmul⟩ := exists_toDistr_eq_smulLeftCLM_and_norm_le (F := F) φ hN
  refine ⟨C, hC, fun {p q} _ _ g hg hbd G hgG ↦ ?_⟩
  have hG := (nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG).1
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  obtain ⟨v, hv, hvn⟩ := hmul hg hgG (p := p) (q := q) u
  have : smulLeftCLM F φ s p q g hg hbd u = v := ext (by simp [hv])
  rwa [this]

end TauCeti.BesovSpace
