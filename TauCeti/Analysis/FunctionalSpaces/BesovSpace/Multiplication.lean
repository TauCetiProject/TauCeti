/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.ChangeOfVariables
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.AlmostDiagonal
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft

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

(`TauCeti.exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le`). It is the case `Φ = id` of the
estimate for `g` times a pullback `Φ^*`
(`TauCeti.exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le`), which is proved by the
argument below combined with the chain rule for `Φ^*`.

* For `j > k`, the spectrum of `Δⱼ (g Δₖ u)` lies in the `j`-th dyadic annulus, where the reverse
  Bernstein inequality bounds a function by `2^{-jN}` times its derivatives of order `N`. By the
  Leibniz rule and Bernstein's inequality for `Δₖ u`, those derivatives are `O(2^{kN})`.
* For `j < k`, the block `Δₖ u` lies in the `k`-th annulus, so `Δₖ u = ∑ᵢ ∂_{bᵢ} hᵢ` with
  `‖hᵢ‖_p = O(2^{-k} ‖Δₖ u‖_p)` (`OrthonormalBasis.exists_eq_sum_lineDerivOp_and_norm_le`). The
  identity `g ∂_{bᵢ} hᵢ = ∂_{bᵢ} (g hᵢ) - (∂_{bᵢ} g) hᵢ` moves the derivative onto `Δⱼ`, where it
  costs `2^j`. Repeating this `N` times gains `2^{N (j - k)}`.
* For `j = k` the multiplication and the block are bounded on `Lᵖ`.

So multiplication by `g` is almost diagonal, and for `N > |s|` it is bounded on `B^s_{p,q}`
(`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le`): the weighted blocks
`2^{js} Δⱼ (g u)` are controlled by `∑ₖ r^{|j - k|} 2^{ks} ‖Δₖ u‖_p` with `r = 2^{|s| - N} < 1`.

## Main declarations

* `TauCeti.exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le`: the block estimate above.
* `TauCeti.BesovSpace.exists_toDistr_eq_smulLeftCLM_and_norm_le`: multiplication by `g` maps
  `B^s_{p,q}` to itself with norm at most `C G`, uniformly in `p` and `q`.
* `TemperedDistribution.MemBesov.smulLeftCLM`: `B^s_{p,q}` is stable under multiplication by
  functions of temperate growth whose derivatives of order at most `⌊|s|⌋₊ + 1` are bounded.
* `TauCeti.BesovSpace.smulLeftCLM`: the multiplication as a bounded operator on `B^s_{p,q}`, with
  operator norm at most `C G` (`TauCeti.BesovSpace.exists_norm_smulLeftCLM_le`).
* `TauCeti.BesovSpace.compCLM_smulLeftCLM`: pulling back `g u` along a diffeomorphism `Φ` gives
  `(g ∘ Φ) Φ^* u`.

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

/-- **Off-diagonal decay of a multiplication between Littlewood–Paley blocks.** Let `M` be a
natural number. There is `K`, depending only on `φ` and `M`, with the following property. Let `g`
be a function whose derivatives of order at most `M` are bounded by `G`, let `1 ≤ p ≤ ∞`, and let
the block `Δₖ u` of a tempered distribution be an `Lᵖ` function `f`. Then for every `j` the block
`Δⱼ (g f)` is an `Lᵖ` function of norm at most `K G 2^{-M |j - k|} ‖f‖_p`. If `g` does not have
temperate growth, `g f` is the junk value `0`. This is the case `Φ = id` of
`TauCeti.exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le`. -/
theorem exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le
    (φ : ContDiffBump (0 : E)) (M : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {g : E → ℂ} {G : ℝ},
      (∀ n ≤ M, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ G) → ∀ (j k : ℕ) (u : 𝓢'(E, F))
      (f : Lp F p (volume : Measure E)), littlewoodPaleyBlock F φ k u = f →
      ∃ v : Lp F p (volume : Measure E),
        littlewoodPaleyBlock F φ j (smulLeftCLM F g (f : 𝓢'(E, F))) = v ∧
        ‖v‖ ≤ K * G * (2 : ℝ) ^ (-(M * |(j : ℝ) - k|)) * ‖f‖ := by
  obtain ⟨K, hK, h⟩ := exists_littlewoodPaleyBlock_smulLeftCLM_compCLM_eq_and_norm_le (F := F) φ 1 M
  refine ⟨K, hK, fun {p} _ {g G} hgG j k u f hf ↦ ?_⟩
  have hid : ((Equiv.refl E : E ≃ E) : E → E).HasTemperateGrowth := by
    simpa using (ContinuousLinearMap.id ℝ E).hasTemperateGrowth
  have hid' : ((Equiv.refl E).symm : E → E).HasTemperateGrowth := by
    rw [Equiv.refl_symm]
    exact hid
  -- The derivatives of positive order of the identity are bounded by `1`.
  have hidL (n : ℕ) (hn : 1 ≤ n) (x : E) : ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ 1 := by
    simpa using norm_iteratedFDeriv_id_le_one (𝕜 := ℝ) hn x
  simpa only [compCLM_refl, ContinuousLinearMap.id_apply] using h hid hid'
    (fun n h₁ _ x ↦ hidL n h₁ x) (fun n h₁ _ x ↦ by simpa using hidL n h₁ x) hgG j k u f hf

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
  -- `g` is almost diagonal: its interaction between the blocks `j` and `k` decays like
  -- `2^{-N |j - k|}`.
  obtain ⟨K, hK, hblock⟩ := exists_littlewoodPaleyBlock_smulLeftCLM_eq_and_norm_le (F := F) φ N
  refine ⟨K * ∑' d : ℤ, ((2 : ℝ) ^ (|s| - N)) ^ d.natAbs, by positivity,
    fun {g G} _ hgG {p q} _ _ u ↦ ?_⟩
  obtain ⟨hG, -⟩ := nonneg_and_norm_le_of_norm_iteratedFDeriv_le hgG
  obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_le
    (smulLeftCLM F g) hN (mul_nonneg hK hG) u fun j k ↦
      hblock hgG j k u.toDistr (u.block k) (u.coe_block k).symm
  exact ⟨v, hv, hvn.trans_eq (by ring)⟩

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

/-- Pulling back `g u` along `Φ` on `B^s_{p,q}` gives `(g ∘ Φ) Φ^* u`. -/
theorem compCLM_smulLeftCLM {Φ : E ≃ E}
    (hΦ : (Φ : E → E).HasTemperateGrowth) (hΨ : (Φ.symm : E → E).HasTemperateGrowth)
    (hΦb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ x‖ ≤ C)
    (hΨb : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n Φ.symm x‖ ≤ C)
    {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbd : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
    (hbdΦ : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (g ∘ Φ) x‖ ≤ C)
    (u : BesovSpace F φ s p q) :
    BesovSpace.compCLM F φ s p q Φ hΦ hΨ hΦb hΨb (smulLeftCLM F φ s p q g hg hbd u) =
      smulLeftCLM F φ s p q (g ∘ Φ) (hg.comp hΦ) hbdΦ
        (BesovSpace.compCLM F φ s p q Φ hΦ hΨ hΦb hΨb u) :=
  ext (by simp [TemperedDistribution.compCLM_smulLeftCLM hΦ hΨ hg])

end TauCeti.BesovSpace
