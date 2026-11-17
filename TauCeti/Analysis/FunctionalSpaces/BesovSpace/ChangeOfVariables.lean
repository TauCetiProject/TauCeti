/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Multiplication
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley.ChangeOfVariables

/-!
# Pullback of Besov spaces along diffeomorphisms with bounded derivatives

Let `E` be a finite-dimensional real inner product space, `F` a complete complex normed space,
`χ : ContDiffBump (0 : E)` a Littlewood–Paley bump function, `s ∈ ℝ`, and `1 ≤ p, q ≤ ∞`. Let
`φ : E ≃ E` be a bijection such that `φ` and `φ⁻¹` have temperate growth and uniformly bounded
iterated derivatives of positive orders (`1 ≤ n ≤ N` for `φ` and `1 ≤ n ≤ N + 1` for `φ⁻¹`, with
`N > |s|`; in particular any smooth diffeomorphism whose derivatives of every positive order, and
those of its inverse, are uniformly bounded).

Pullback `TemperedDistribution.compCLM F φ` restricts to a bounded linear map on the inhomogeneous
Besov space `B^s_{p,q}(E; F)` (`TauCeti.BesovSpace.compCLM`), and when both `φ` and `φ⁻¹` satisfy
the positive-order derivative bounds up to `⌊|s|⌋₊ + 2`, it is a bounded linear equivalence
`B^s_{p,q}(E; F) ≃L[ℂ] B^s_{p,q}(E; F)` (`TauCeti.BesovSpace.compEquiv`,
`TauCeti.BesovSpace.compEquivOfContDiff`), inverse to pullback by `φ⁻¹` and agreeing with
distributional pullback on `𝓢'(E, F)`.

Crucially:
* The operator norm bound `C` depends only on the partition bump `χ` (hence `E` and `finrank ℝ E`),
  the smoothness `s`, `N`, and the uniform bound `L` on positive-order derivatives — **not** on
  `p` or `q` (`TauCeti.BesovSpace.exists_norm_compCLM_le`,
  `TauCeti.BesovSpace.exists_norm_compEquiv_le`).
* Zero-th order bounds on `‖φ x‖` never enter: translations `x ↦ x + a` induce bounded linear
  equivalences of `B^s_{p,q}(E; F)` with operator norms bounded uniformly in `a`, `p`, and `q`
  (`TauCeti.BesovSpace.translateEquiv`, `TauCeti.BesovSpace.exists_norm_translateEquiv_le`).

## Mathematical proof

By the off-diagonal Littlewood–Paley block decay estimate
`TauCeti.exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le` (proved in
`TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley.ChangeOfVariables`),

`‖Δⱼ (φ^* Δₖ u)‖_p ≤ K 2^{-N |j - k|} ‖Δₖ u‖_p`

for every `1 ≤ p ≤ ∞`. Applying the operator-independent off-diagonal boundedness criterion
`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_offDiagonal_decay` with `N > |s|` yields
boundedness on `B^s_{p,q}` uniformly in `1 ≤ p, q ≤ ∞`.

## Main declarations

* `TauCeti.BesovSpace.exists_toDistr_eq_compCLM_and_norm_le`: quantitative Besov norm bound for
  pullback along `φ`, uniform in `1 ≤ p, q ≤ ∞`.
* `TemperedDistribution.MemBesov.compCLM`, `TemperedDistribution.memBesov_compCLM_iff`: stability
  and invariance of `MemBesov` under diffeomorphism pullback.
* `TauCeti.BesovSpace.compCLM`, `TauCeti.BesovSpace.exists_norm_compCLM_le`: pullback as a
  continuous linear map on `B^s_{p,q}` with `p, q`-independent operator norm bound.
* `TauCeti.BesovSpace.compEquiv`, `TauCeti.BesovSpace.compEquivOfContDiff`,
  `TauCeti.BesovSpace.exists_norm_compEquiv_le`,
  `TauCeti.BesovSpace.exists_norm_compEquivOfContDiff_le`: diffeomorphism pullback as a bounded
  linear automorphism of `B^s_{p,q}`, inverse to pullback by `φ⁻¹`.
* `TauCeti.BesovSpace.translateEquiv`, `TauCeti.BesovSpace.compContinuousLinearEquiv`: translations
  and continuous linear automorphisms on `B^s_{p,q}`.

## References

* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, §4.3 (diffeomorphism invariance of
  `B^s_{p,q}`).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Springer, 2011, §2.7.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti

open TemperedDistribution

/-! ### Quantitative pullback bound on Besov spaces -/

/-- **Pullback along a diffeomorphism is bounded on Besov spaces.** Let `N` be a natural number
with `|s| < N`, and let `L` be a real number. There is `C ≥ 0`, depending only on `χ`, `s`, `N`
and `L`, with the following property. Let `φ : E ≃ E` be a bijection such that `φ` and `φ⁻¹` have
temperate growth, the derivatives of `φ` of order `1 ≤ n ≤ N` are bounded by `L`, and those of
`φ⁻¹` of order `1 ≤ n ≤ N + 1` are bounded by `L`. Then for all `1 ≤ p, q ≤ ∞` and every
`u ∈ B^s_{p,q}`, the pullback `φ^* u` lies in `B^s_{p,q}` with `‖φ^* u‖ ≤ C ‖u‖`. -/
theorem BesovSpace.exists_toDistr_eq_compCLM_and_norm_le (χ : ContDiffBump (0 : E))
    {s : ℝ} {N : ℕ} (hN : |s| < N) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth),
      (∀ n, 1 ≤ n → n ≤ N → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (u : BesovSpace F χ s p q),
      ∃ v : BesovSpace F χ s p q, v.toDistr = compCLM F φ hφ hψ u.toDistr ∧ ‖v‖ ≤ C * ‖u‖ := by
  obtain ⟨K, hK, hblock⟩ := exists_littlewoodPaleyBlock_compCLM_eq_and_norm_le (F := F) χ N L
  have hr1 : (2 : ℝ) ^ (|s| - N) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  refine ⟨K * ((1 + (2 : ℝ) ^ (|s| - N)) / (1 - (2 : ℝ) ^ (|s| - N))),
    by have := sub_pos.2 hr1; positivity, fun {φ} hφ hψ hφL hψL {p q} _ _ u ↦ ?_⟩
  exact BesovSpace.exists_toDistr_eq_and_norm_le_of_offDiagonal_decay hN hK
    (compCLM F φ hφ hψ) u
    fun j k ↦ hblock hφ hψ hφL hψL j k u.toDistr (u.block k) (u.coe_block k).symm

end TauCeti

/-! ### Stability and invariance of `MemBesov` -/

namespace TemperedDistribution

open TauCeti

variable {χ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- **Diffeomorphism pullback preserves `MemBesov`.** If `u ∈ B^s_{p,q}`, `φ` and `φ⁻¹` have
temperate growth, `φ` has bounded derivatives of orders `1 ≤ n ≤ ⌊|s|⌋₊ + 1`, and `φ⁻¹` has
bounded derivatives of orders `1 ≤ n ≤ ⌊|s|⌋₊ + 2`, then `φ^* u ∈ B^s_{p,q}`. -/
theorem MemBesov.compCLM {u : 𝓢'(E, F)} (hu : u.MemBesov χ s p q) {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    (TemperedDistribution.compCLM F φ hφ hψ u).MemBesov χ s p q := by
  obtain ⟨L₁, hL₁⟩ := exists_forall_norm_iteratedFDeriv_le_of_pos hbdφ
  obtain ⟨L₂, hL₂⟩ := exists_forall_norm_iteratedFDeriv_le_of_pos hbdψ
  obtain ⟨C, -, hC⟩ := BesovSpace.exists_toDistr_eq_compCLM_and_norm_le (F := F) χ
    (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _) (max L₁ L₂)
  obtain ⟨v, hv, -⟩ := hC hφ hψ
    (fun n hn1 hn2 x ↦ (hL₁ n hn1 hn2 x).trans (le_max_left _ _))
    (fun n hn1 hn2 y ↦ (hL₂ n hn1 hn2 y).trans (le_max_right _ _)) hu.toBesovSpace
  rw [← hu.toDistr_toBesovSpace, ← hv]
  exact v.memBesov_toDistr

/-- **Diffeomorphism invariance of `MemBesov`.** When both `φ` and `φ⁻¹` have temperate growth and
bounded derivatives of positive orders `1 ≤ n ≤ ⌊|s|⌋₊ + 2`, a tempered distribution `u` lies in
`B^s_{p,q}` if and only if `φ^* u` does. -/
theorem memBesov_compCLM_iff {u : 𝓢'(E, F)} {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    (TemperedDistribution.compCLM F φ hφ hψ u).MemBesov χ s p q ↔ u.MemBesov χ s p q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.compCLM hφ hψ (fun n hn1 hn2 ↦ hbdφ n hn1 (by omega)) hbdψ⟩
  simpa only [compCLM_symm_compCLM hφ hψ hφ] using
    h.compCLM hψ hφ (fun n hn1 hn2 ↦ hbdψ n hn1 (by omega)) hbdφ

end TemperedDistribution

/-! ### Continuous linear maps and equivalences on `BesovSpace` -/

namespace TauCeti.BesovSpace

open TemperedDistribution

variable {χ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (F χ s p q) in
/-- **Pullback of Besov spaces** along a bijection `φ : E ≃ E` such that `φ` and `φ⁻¹` have
temperate growth and bounded positive-order derivatives (`1 ≤ n ≤ ⌊|s|⌋₊ + 1` for `φ` and
`1 ≤ n ≤ ⌊|s|⌋₊ + 2` for `φ⁻¹`), as a bounded linear operator on `B^s_{p,q}`. Its operator norm
is bounded independently of `p` and `q` (`TauCeti.BesovSpace.exists_norm_compCLM_le`). -/
def compCLM (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := (u.memBesov_toDistr.compCLM hφ hψ hbdφ hbdψ).toBesovSpace
      map_add' _ _ := ext (by simp)
      map_smul' _ _ := ext (by simp) } <| by
    obtain ⟨L₁, hL₁⟩ := exists_forall_norm_iteratedFDeriv_le_of_pos hbdφ
    obtain ⟨L₂, hL₂⟩ := exists_forall_norm_iteratedFDeriv_le_of_pos hbdψ
    obtain ⟨C, -, hC⟩ := exists_toDistr_eq_compCLM_and_norm_le (F := F) χ
      (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _) (max L₁ L₂)
    refine ⟨C, fun u ↦ ?_⟩
    obtain ⟨v, hv, hvn⟩ := hC hφ hψ
      (fun n hn1 hn2 x ↦ (hL₁ n hn1 hn2 x).trans (le_max_left _ _))
      (fun n hn1 hn2 y ↦ (hL₂ n hn1 hn2 y).trans (le_max_right _ _)) (p := p) (q := q) u
    have : (u.memBesov_toDistr.compCLM hφ hψ hbdφ hbdψ).toBesovSpace = v := ext (by simp [hv])
    simpa [this] using hvn

@[simp]
theorem toDistr_compCLM {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    (compCLM F χ s p q φ hφ hψ hbdφ hbdψ u).toDistr =
      TemperedDistribution.compCLM F φ hφ hψ u.toDistr := by
  simp [compCLM]

/-- **Uniform operator norm bound for Besov pullback.** Let `N` be a natural number with `|s| < N`,
and let `L` be a real number. There is `C ≥ 0`, depending only on `χ`, `s`, `N` and `L`, such that
whenever `φ` has derivatives of order `1 ≤ n ≤ N` bounded by `L` and `φ⁻¹` has derivatives of
order `1 ≤ n ≤ N + 1` bounded by `L`, the operator norm of `BesovSpace.compCLM` on `B^s_{p,q}` is
at most `C` for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_compCLM_le (χ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
      (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
      (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C),
      (∀ n, 1 ≤ n → n ≤ N → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ‖compCLM F χ s p q φ hφ hψ hbdφ hbdψ‖ ≤ C := by
  obtain ⟨C, hC, hcomp⟩ := exists_toDistr_eq_compCLM_and_norm_le (F := F) χ hN L
  refine ⟨C, hC, fun {p q} _ _ φ hφ hψ hbdφ hbdψ hφL hψL ↦ ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun u ↦ ?_
  obtain ⟨v, hv, hvn⟩ := hcomp hφ hψ hφL hψL (p := p) (q := q) u
  have : compCLM F χ s p q φ hφ hψ hbdφ hbdψ u = v := ext (by simp [hv])
  rwa [this]

/-- Pullback along the identity equivalence is the identity on `B^s_{p,q}`. -/
@[simp]
theorem compCLM_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth)
    (hbd₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (Equiv.refl E).symm y‖ ≤ C) :
    compCLM F χ s p q (Equiv.refl E) h₁ h₂ hbd₁ hbd₂ = ContinuousLinearMap.id ℂ _ := by
  ext u : 2
  simp

/-- **Contravariant functoriality of Besov pullback**: `(ψ ∘ φ)^* = φ^* ∘ ψ^*`. -/
theorem compCLM_trans {φ ψ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hφs : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdφs : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hψ : (ψ : E → E).HasTemperateGrowth) (hψs : (ψ.symm : E → E).HasTemperateGrowth)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ C)
    (hbdψs : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n ψ.symm y‖ ≤ C)
    (h₁ : (φ.trans ψ : E → E).HasTemperateGrowth)
    (h₂ : ((φ.trans ψ).symm : E → E).HasTemperateGrowth)
    (hbd₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (φ.trans ψ) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (φ.trans ψ).symm y‖ ≤ C) :
    compCLM F χ s p q (φ.trans ψ) h₁ h₂ hbd₁ hbd₂ =
      compCLM F χ s p q φ hφ hφs hbdφ hbdφs ∘L compCLM F χ s p q ψ hψ hψs hbdψ hbdψs := by
  ext u : 2
  simp [TemperedDistribution.compCLM_trans hφ hφs hψ hψs h₁ h₂]

/-- Pulling back along `φ` and then along `φ⁻¹` gives back the Besov element. -/
@[simp]
theorem compCLM_symm_compCLM {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hbdψ' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hbdφ' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ.symm.symm x‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    compCLM F χ s p q φ.symm hψ hφ' hbdψ' hbdφ' (compCLM F χ s p q φ hφ hψ hbdφ hbdψ u) = u := by
  ext1
  simp

/-- Pulling back along `φ⁻¹` and then along `φ` gives back the Besov element. -/
@[simp]
theorem compCLM_compCLM_symm {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hφ' : (φ.symm.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hbdψ' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hbdφ' : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ.symm.symm x‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    compCLM F χ s p q φ hφ hψ hbdφ hbdψ (compCLM F χ s p q φ.symm hψ hφ' hbdψ' hbdφ' u) = u := by
  ext1
  simp

/-- Pulling back `g • u` along `φ` on `B^s_{p,q}` equals `(g ∘ φ) • φ^* u`. -/
theorem compCLM_smulLeftCLM {φ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 1 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hbdg : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n g x‖ ≤ C)
    (hbdgφ : ∀ n ≤ ⌊|s|⌋₊ + 1, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (g ∘ φ) x‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    compCLM F χ s p q φ hφ hψ hbdφ hbdψ (smulLeftCLM F χ s p q g hg hbdg u) =
      smulLeftCLM F χ s p q (g ∘ φ) (hg.comp hφ) hbdgφ
        (compCLM F χ s p q φ hφ hψ hbdφ hbdψ u) := by
  ext1
  simp [TemperedDistribution.compCLM_smulLeftCLM hφ hψ hg]

variable (F χ s p q) in
/-- **Diffeomorphism invariance of Besov spaces.** Let `φ : E ≃ E` be a bijection such that `φ`
and `φ⁻¹` have temperate growth and bounded derivatives of positive orders `1 ≤ n ≤ ⌊|s|⌋₊ + 2`.
Then pullback along `φ` is a bounded linear equivalence `B^s_{p,q}(E; F) ≃L[ℂ] B^s_{p,q}(E; F)`,
with inverse the pullback along `φ⁻¹`. -/
def compEquiv (φ : E ≃ E) (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    BesovSpace F χ s p q ≃L[ℂ] BesovSpace F χ s p q :=
  ContinuousLinearEquiv.equivOfInverse
    (compCLM F χ s p q φ hφ hψ (fun n hn1 hn2 ↦ hbdφ n hn1 (by omega)) hbdψ)
    (compCLM F χ s p q φ.symm hψ hφ (fun n hn1 hn2 ↦ hbdψ n hn1 (by omega)) hbdφ)
    (compCLM_symm_compCLM hφ hψ hφ _ hbdψ _ hbdφ)
    (compCLM_compCLM_symm hφ hψ hφ _ hbdψ _ hbdφ)

theorem compEquiv_apply {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    compEquiv F χ s p q φ hφ hψ hbdφ hbdψ u =
      compCLM F χ s p q φ hφ hψ (fun n hn1 hn2 ↦ hbdφ n hn1 (by omega)) hbdψ u :=
  (rfl)

@[simp]
theorem compEquiv_symm {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    (compEquiv F χ s p q φ hφ hψ hbdφ hbdψ).symm =
      compEquiv F χ s p q φ.symm hψ hφ hbdψ hbdφ := by
  ext u
  rfl

@[simp]
theorem toDistr_compEquiv {φ : E ≃ E} (hφ : (φ : E → E).HasTemperateGrowth)
    (hψ : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    (compEquiv F χ s p q φ hφ hψ hbdφ hbdψ u).toDistr =
      TemperedDistribution.compCLM F φ hφ hψ u.toDistr := by
  simp [compEquiv_apply]

@[simp]
theorem compEquiv_refl (h₁ : (Equiv.refl E : E → E).HasTemperateGrowth)
    (h₂ : ((Equiv.refl E).symm : E → E).HasTemperateGrowth)
    (hbd₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (Equiv.refl E).symm y‖ ≤ C) :
    compEquiv F χ s p q (Equiv.refl E) h₁ h₂ hbd₁ hbd₂ = ContinuousLinearEquiv.refl ℂ _ := by
  ext u : 3
  simp

/-- **Contravariant functoriality of `compEquiv`**: `(ψ ∘ φ)^* = φ^* ∘ ψ^*`. -/
theorem compEquiv_trans {φ ψ : E ≃ E}
    (hφ : (φ : E → E).HasTemperateGrowth) (hφs : (φ.symm : E → E).HasTemperateGrowth)
    (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdφs : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hψ : (ψ : E → E).HasTemperateGrowth) (hψs : (ψ.symm : E → E).HasTemperateGrowth)
    (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ C)
    (hbdψs : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n ψ.symm y‖ ≤ C)
    (h₁ : (φ.trans ψ : E → E).HasTemperateGrowth)
    (h₂ : ((φ.trans ψ).symm : E → E).HasTemperateGrowth)
    (hbd₁ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (φ.trans ψ) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 →
      ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (φ.trans ψ).symm y‖ ≤ C) :
    compEquiv F χ s p q (φ.trans ψ) h₁ h₂ hbd₁ hbd₂ =
      (compEquiv F χ s p q ψ hψ hψs hbdψ hbdψs).trans
        (compEquiv F χ s p q φ hφ hφs hbdφ hbdφs) := by
  ext u : 3
  simp [TemperedDistribution.compCLM_trans hφ hφs hψ hψs h₁ h₂]

/-- **Uniform operator norm bounds for `compEquiv` and its inverse.** Let `N` be a natural number
with `|s| < N`, and let `L` be a real number. There is `C ≥ 0`, depending only on `χ`, `s`, `N`
and `L`, such that whenever both `φ` and `φ⁻¹` have derivatives of order `1 ≤ n ≤ N + 1` bounded by
`L`, both `compEquiv` and its inverse have operator norm at most `C` on `B^s_{p,q}` for all
`1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_compEquiv_le (χ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {φ : E ≃ E}
      (hφ : (φ : E → E).HasTemperateGrowth) (hψ : (φ.symm : E → E).HasTemperateGrowth)
      (hbdφ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
      (hbdψ : ∀ n, 1 ≤ n → n ≤ ⌊|s|⌋₊ + 2 → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C),
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ‖(compEquiv F χ s p q φ hφ hψ hbdφ hbdψ :
        BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C ∧
      ‖((compEquiv F χ s p q φ hφ hψ hbdφ hbdψ).symm :
        BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := exists_norm_compCLM_le (F := F) (s := s) χ hN L
  refine ⟨C, hC, fun {p q} _ _ φ hφ hψ hbdφ hbdψ hφL hψL ↦ ⟨?_, ?_⟩⟩
  · exact hnorm hφ hψ (fun n hn1 hn2 ↦ hbdφ n hn1 (by omega)) hbdψ
      (fun n hn1 hn2 ↦ hφL n hn1 (by omega)) hψL
  · rw [compEquiv_symm]
    exact hnorm hψ hφ (fun n hn1 hn2 ↦ hbdψ n hn1 (by omega)) hbdφ
      (fun n hn1 hn2 ↦ hψL n hn1 (by omega)) hφL

variable (F χ s p q) in
/-- **Pullback isomorphism for smooth diffeomorphisms with bounded derivatives of every positive
order.** If `φ : E ≃ E` and `φ⁻¹` are smooth with uniformly bounded derivatives of every positive
order, then pullback along `φ` is a bounded linear equivalence of `B^s_{p,q}(E; F)`, inverse to
pullback along `φ⁻¹` and agreeing with distributional pullback. -/
def compEquivOfContDiff (φ : E ≃ E) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ φ.symm)
    (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    BesovSpace F χ s p q ≃L[ℂ] BesovSpace F χ s p q :=
  compEquiv F χ s p q φ
    (.of_norm_iteratedFDeriv_le_of_pos hφ hbdφ)
    (.of_norm_iteratedFDeriv_le_of_pos hψ hbdψ)
    (fun n hn _ ↦ hbdφ n hn) (fun n hn _ ↦ hbdψ n hn)

@[simp]
theorem toDistr_compEquivOfContDiff {φ : E ≃ E} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ φ.symm)
    (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (u : BesovSpace F χ s p q) :
    (compEquivOfContDiff F χ s p q φ hφ hψ hbdφ hbdψ u).toDistr =
      TemperedDistribution.compCLM F φ
        (.of_norm_iteratedFDeriv_le_of_pos hφ hbdφ)
        (.of_norm_iteratedFDeriv_le_of_pos hψ hbdψ) u.toDistr := by
  simp [compEquivOfContDiff]

@[simp]
theorem compEquivOfContDiff_symm {φ : E ≃ E} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ φ.symm)
    (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C) :
    (compEquivOfContDiff F χ s p q φ hφ hψ hbdφ hbdψ).symm =
      compEquivOfContDiff F χ s p q φ.symm hψ hφ hbdψ hbdφ := by
  ext u
  rfl

@[simp]
theorem compEquivOfContDiff_refl (h₁ : ContDiff ℝ ∞ (Equiv.refl E))
    (h₂ : ContDiff ℝ ∞ (Equiv.refl E).symm)
    (hbd₁ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (Equiv.refl E) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (Equiv.refl E).symm y‖ ≤ C) :
    compEquivOfContDiff F χ s p q (Equiv.refl E) h₁ h₂ hbd₁ hbd₂ =
      ContinuousLinearEquiv.refl ℂ _ :=
  compEquiv_refl _ _ _ _

theorem compEquivOfContDiff_trans {φ ψ : E ≃ E}
    (hφ : ContDiff ℝ ∞ φ) (hφs : ContDiff ℝ ∞ φ.symm)
    (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
    (hbdφs : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C)
    (hψ : ContDiff ℝ ∞ ψ) (hψs : ContDiff ℝ ∞ ψ.symm)
    (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n ψ x‖ ≤ C)
    (hbdψs : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n ψ.symm y‖ ≤ C)
    (h₁ : ContDiff ℝ ∞ (φ.trans ψ)) (h₂ : ContDiff ℝ ∞ (φ.trans ψ).symm)
    (hbd₁ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n (φ.trans ψ) x‖ ≤ C)
    (hbd₂ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (φ.trans ψ).symm y‖ ≤ C) :
    compEquivOfContDiff F χ s p q (φ.trans ψ) h₁ h₂ hbd₁ hbd₂ =
      (compEquivOfContDiff F χ s p q ψ hψ hψs hbdψ hbdψs).trans
        (compEquivOfContDiff F χ s p q φ hφ hφs hbdφ hbdφs) :=
  compEquiv_trans _ _ _ _ _ _ _ _ _ _ _ _

/-- **Uniform operator norm bounds for `compEquivOfContDiff` and its inverse.** Let `N` be a
natural number with `|s| < N`, and let `L` be a real number. There is `C ≥ 0`, depending only on
`χ`, `s`, `N` and `L` (and **not** on `p` or `q`), such that whenever both `φ` and `φ⁻¹` have
derivatives of order `1 ≤ n ≤ N + 1` bounded by `L`, both `compEquivOfContDiff` and its inverse
have operator norm at most `C` on `B^s_{p,q}` for all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_compEquivOfContDiff_le (χ : ContDiffBump (0 : E)) {N : ℕ} (hN : |s| < N)
    (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {φ : E ≃ E}
      (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ φ.symm)
      (hbdφ : ∀ n, 1 ≤ n → ∃ C, ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ C)
      (hbdψ : ∀ n, 1 ≤ n → ∃ C, ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ C),
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ L) →
      (∀ n, 1 ≤ n → n ≤ N + 1 → ∀ y, ‖iteratedFDeriv ℝ n φ.symm y‖ ≤ L) →
      ‖(compEquivOfContDiff F χ s p q φ hφ hψ hbdφ hbdψ :
        BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C ∧
      ‖((compEquivOfContDiff F χ s p q φ hφ hψ hbdφ hbdψ).symm :
        BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := exists_norm_compEquiv_le (F := F) (s := s) χ hN L
  exact ⟨C, hC, fun hφ hψ hbdφ hbdψ hφL hψL ↦ hnorm _ _ _ _ hφL hψL⟩

/-! ### Translations and continuous linear automorphisms -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
private theorem compCLM_congr_equiv {φ₁ φ₂ : E ≃ E} (h : φ₁ = φ₂)
    (hφ₁ : (φ₁ : E → E).HasTemperateGrowth) (hψ₁ : (φ₁.symm : E → E).HasTemperateGrowth)
    (hφ₂ : (φ₂ : E → E).HasTemperateGrowth) (hψ₂ : (φ₂.symm : E → E).HasTemperateGrowth) :
    TemperedDistribution.compCLM F φ₁ hφ₁ hψ₁ = TemperedDistribution.compCLM F φ₂ hφ₂ hψ₂ := by
  subst h
  rfl

variable (F χ s p q) in
/-- **Translation equivalence on Besov spaces.** Translating by `a ∈ E` (`u ↦ u(· + a)`) is a
bounded linear automorphism of `B^s_{p,q}(E; F)` whose operator norm is bounded uniformly in `a`,
`p`, and `q` (`TauCeti.BesovSpace.exists_norm_translateEquiv_le`). -/
def translateEquiv (a : E) : BesovSpace F χ s p q ≃L[ℂ] BesovSpace F χ s p q :=
  compEquiv F χ s p q (Equiv.addRight a)
    (by dsimp only [Equiv.coe_addRight]; fun_prop)
    (by dsimp only [Equiv.addRight_symm_apply]; fun_prop)
    (fun _ hn _ ↦ ⟨1, norm_iteratedFDeriv_addRight_le a hn⟩)
    (fun _ hn _ ↦ ⟨1, norm_iteratedFDeriv_addRight_le (-a) hn⟩)

@[simp]
theorem toDistr_translateEquiv (a : E) (u : BesovSpace F χ s p q) :
    (translateEquiv F χ s p q a u).toDistr =
      TemperedDistribution.compCLM F (Equiv.addRight a)
        (by dsimp only [Equiv.coe_addRight]; fun_prop)
        (by dsimp only [Equiv.addRight_symm_apply]; fun_prop) u.toDistr := by
  rw [translateEquiv, toDistr_compEquiv]

@[simp]
theorem translateEquiv_zero :
    translateEquiv F χ s p q (0 : E) = ContinuousLinearEquiv.refl ℂ _ := by
  ext u : 3
  have h := DFunLike.congr_fun (compCLM_congr_equiv (F := F)
    (φ₁ := Equiv.addRight (0 : E)) (φ₂ := Equiv.refl E) (by ext x; simp)
    (by dsimp only [Equiv.coe_addRight]; fun_prop)
    (by dsimp only [Equiv.addRight_symm_apply]; fun_prop) .id .id) u.toDistr
  exact (toDistr_translateEquiv 0 u).trans
    (h.trans (DFunLike.congr_fun (TemperedDistribution.compCLM_refl .id .id) u.toDistr))

@[simp]
theorem translateEquiv_symm (a : E) :
    (translateEquiv F χ s p q a).symm = translateEquiv F χ s p q (-a) := by
  ext u : 3
  rw [translateEquiv, compEquiv_symm, toDistr_compEquiv, toDistr_translateEquiv,
    compCLM_congr_equiv (Equiv.addRight_symm a)]

theorem translateEquiv_add (a b : E) :
    translateEquiv F χ s p q (a + b) =
      (translateEquiv F χ s p q b).trans (translateEquiv F χ s p q a) := by
  ext u : 3
  have hab : Equiv.addRight (a + b) = (Equiv.addRight a).trans (Equiv.addRight b) := by
    ext x; simp [add_assoc]
  have h₁ : ((Equiv.addRight a).trans (Equiv.addRight b) : E → E).HasTemperateGrowth := by
    rw [← hab, Equiv.coe_addRight]; fun_prop
  have h₂ : (((Equiv.addRight a).trans (Equiv.addRight b)).symm : E → E).HasTemperateGrowth := by
    rw [← hab, Equiv.addRight_symm, Equiv.coe_addRight]; fun_prop
  rw [ContinuousLinearEquiv.trans_apply, toDistr_translateEquiv, toDistr_translateEquiv,
    toDistr_translateEquiv, compCLM_congr_equiv hab _ _ h₁ h₂,
    TemperedDistribution.compCLM_trans, ContinuousLinearMap.comp_apply]

/-- **Uniform translation invariance of Besov norms.** For every `χ` and `s`, there is `C ≥ 0`
such that `‖translateEquiv F χ s p q a‖ ≤ C` for all `a ∈ E` and all `1 ≤ p, q ≤ ∞`. -/
theorem exists_norm_translateEquiv_le (χ : ContDiffBump (0 : E)) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (a : E),
      ‖(translateEquiv F χ s p q a : BesovSpace F χ s p q →L[ℂ] BesovSpace F χ s p q)‖ ≤ C := by
  obtain ⟨C, hC, hnorm⟩ := exists_norm_compEquiv_le (F := F) (s := s) χ
    (N := ⌊|s|⌋₊ + 1) (by push_cast; exact Nat.lt_floor_add_one _) 1
  exact ⟨C, hC, fun {p q} _ _ a ↦ (hnorm _ _ _ _
    (fun _ hn _ x ↦ norm_iteratedFDeriv_addRight_le a hn x)
    (fun _ hn _ y ↦ norm_iteratedFDeriv_addRight_le (-a) hn y)).1⟩

variable (F χ s p q) in
/-- **Pullback along a continuous linear equivalence** `e : E ≃L[ℝ] E` on `B^s_{p,q}(E; F)`. -/
def compContinuousLinearEquiv (e : E ≃L[ℝ] E) :
    BesovSpace F χ s p q ≃L[ℂ] BesovSpace F χ s p q :=
  compEquiv F χ s p q e.toEquiv
    e.hasTemperateGrowth
    e.symm.hasTemperateGrowth
    (fun _ hn _ ↦ ⟨‖(e : E →L[ℝ] E)‖, (e : E →L[ℝ] E).norm_iteratedFDeriv_le_norm hn⟩)
    (fun _ hn _ ↦ ⟨‖(e.symm : E →L[ℝ] E)‖, (e.symm : E →L[ℝ] E).norm_iteratedFDeriv_le_norm hn⟩)

@[simp]
theorem toDistr_compContinuousLinearEquiv (e : E ≃L[ℝ] E) (u : BesovSpace F χ s p q) :
    (compContinuousLinearEquiv F χ s p q e u).toDistr =
      TemperedDistribution.compCLM F e.toEquiv
        e.hasTemperateGrowth e.symm.hasTemperateGrowth u.toDistr :=
  toDistr_compEquiv (φ := e.toEquiv) e.hasTemperateGrowth e.symm.hasTemperateGrowth _ _ u

@[simp]
theorem compContinuousLinearEquiv_symm (e : E ≃L[ℝ] E) :
    (compContinuousLinearEquiv F χ s p q e).symm =
      compContinuousLinearEquiv F χ s p q e.symm := by
  ext u
  rfl

@[simp]
theorem compContinuousLinearEquiv_refl :
    compContinuousLinearEquiv F χ s p q (ContinuousLinearEquiv.refl ℝ E) =
      ContinuousLinearEquiv.refl ℂ _ := by
  ext u : 3
  have h := DFunLike.congr_fun (compCLM_congr_equiv (F := F)
    (φ₁ := (ContinuousLinearEquiv.refl ℝ E).toEquiv) (φ₂ := Equiv.refl E) rfl
    (ContinuousLinearEquiv.refl ℝ E).hasTemperateGrowth
    (ContinuousLinearEquiv.refl ℝ E).symm.hasTemperateGrowth .id .id) u.toDistr
  exact (toDistr_compContinuousLinearEquiv _ u).trans
    (h.trans (DFunLike.congr_fun (TemperedDistribution.compCLM_refl .id .id) u.toDistr))

theorem compContinuousLinearEquiv_trans (e₁ e₂ : E ≃L[ℝ] E) :
    compContinuousLinearEquiv F χ s p q (e₁.trans e₂) =
      (compContinuousLinearEquiv F χ s p q e₂).trans
        (compContinuousLinearEquiv F χ s p q e₁) := by
  ext u : 3
  rw [ContinuousLinearEquiv.trans_apply, toDistr_compContinuousLinearEquiv,
    toDistr_compContinuousLinearEquiv, toDistr_compContinuousLinearEquiv]
  exact DFunLike.congr_fun (TemperedDistribution.compCLM_trans
    (φ := e₁.toEquiv) (χ := e₂.toEquiv)
    e₁.hasTemperateGrowth e₁.symm.hasTemperateGrowth
    e₂.hasTemperateGrowth e₂.symm.hasTemperateGrowth
    (e₁.trans e₂).hasTemperateGrowth (e₁.trans e₂).symm.hasTemperateGrowth) u.toDistr

end TauCeti.BesovSpace
