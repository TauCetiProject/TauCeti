/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.Besov
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Distribution.TemperedDistribution.Norming
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Annulus
import TauCeti.Analysis.Normed.Lp.Dual

/-!
# Besov norms of negative order by duality

Let `s : ℝ`, let `1 < p < ∞` and `1 ≤ q ≤ ∞`, and let `p'` and `q'` be the Hölder conjugate
exponents. If a tempered distribution `u` is bounded on the Schwartz functions in the norm of
`B^s_{p,q}`,

`‖u f‖ ≤ A ‖f‖_{B^s_{p,q}}` for every Schwartz function `f`,

then `u` lies in `B^{-s}_{p',q'}` with `‖u‖_{B^{-s}_{p',q'}} ≤ C A`, where `C` depends only on the
bump function and on `s`, not on the exponents
(`TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_norm_apply_le`; Bahouri–Chemin–Danchin,
Proposition 2.76). In particular every continuous linear functional `Λ` on `B^s_{p,q}` is, on the
Schwartz functions, the pairing with an element of `B^{-s}_{p',q'}` of norm at most `C ‖Λ‖`
(`TauCeti.BesovSpace.exists_toDistr_apply_eq_and_norm_le`). Mathematically, this is the converse
half of the duality `(B^s_{p,q})^* = B^{-s}_{p',q'}` for `1 < p < ∞` and `q < ∞`. With the
bound of the pairing between `B^{-s}_{p',q'}` and `B^s_{p,q}` and the density of the Schwartz
functions in `B^s_{p,q}`, it gives the identification itself, `TauCeti.BesovSpace.strongDualEquiv`
in `TauCeti.Analysis.FunctionalSpaces.BesovSpace.StrongDual`. The case `p = 1` is not covered.

## The argument

The blocks are symmetric for the pairing with Schwartz functions, `(Δⱼ u) g = u (Δⱼ g)`, because
the pieces `ψⱼ` of the Littlewood–Paley partition are even. A finite sum `∑_{j ∈ t} Δⱼ gⱼ` of
blocks of Schwartz functions has Besov norm at most `K ‖w‖_{ℓ^q}` whenever
`2^{js} ‖gⱼ‖_p ≤ wⱼ`, since its pieces have spectra in dyadic annuli
(`TauCeti.BesovSpace.exists_hasSum_toDistr_and_norm_le_of_annulus`).

* *Each block is an `L^{p'}` function.* With a single block, `‖(Δⱼ u) g‖ ≤ A K 2^{js} ‖g‖_p`, so
  `Δⱼ u` is an `L^{p'}` function `hⱼ` with `‖hⱼ‖_{p'} ≤ A K 2^{js}`
  (`TemperedDistribution.exists_eq_toTemperedDistribution_and_norm_le`, which uses `1 < p < ∞`).
* *The weighted norms are in `ℓ^{q'}`.* Choose Schwartz functions `gⱼ` with `‖gⱼ‖_p ≤ 1` and
  `‖hⱼ‖_{p'} ≤ 2 ‖(Δⱼ u) gⱼ‖`, by norming `L^{p'}` with Schwartz functions. For a finite set `t`
  the functional `c ↦ ∑_{j ∈ t} cⱼ 2^{-js} (Δⱼ u) gⱼ` on `ℓ^q` is
  `c ↦ u (∑_{j ∈ t} Δⱼ (cⱼ 2^{-js} gⱼ))`, of norm at most `A K`. The coordinates of a
  functional on `ℓ^q` lie in `ℓ^{q'}` with norm at most its norm
  (`ContinuousLinearMap.sum_norm_lp_single_rpow_le`), so the partial sums of
  `(2^{-js} ‖hⱼ‖_{p'})^{q'}` are at most `(2 A K)^{q'}`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Proposition 2.76.
* H. Triebel, *Theory of Function Spaces*, Section 2.11.2.
-/

public section

noncomputable section

open MeasureTheory FourierTransform Distribution TemperedDistribution Metric
open scoped ENNReal SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TauCeti.BesovSpace

variable (φ : ContDiffBump (0 : E))

/-- **Blocks of Schwartz functions as `Lᵖ` functions.** There is `C₀ ≥ 0`, depending only on `φ`,
such that the block `Δⱼ g` of a Schwartz function satisfies `‖Δⱼ g‖_p ≤ C₀ ‖g‖_p`, and its spectrum
lies in the closed ball of radius `2^j φ.rOut` and, for `j > 0`, outside the open ball of radius
`2^j (φ.rIn / 2)`. -/
private theorem exists_norm_toLp_fourierMultiplierCLM_le :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ) (g : 𝓢(E, ℂ)),
      ‖(SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
          g).toLp p‖ ≤ C₀ * ‖g.toLp p‖ ∧
      IsVanishingOn (𝓕 ((SchwartzMap.fourierMultiplierCLM ℂ
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) g).toLp p : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ))
        (closedBall 0 (2 ^ j * φ.rOut))ᶜ ∧
      (0 < j → IsVanishingOn (𝓕 ((SchwartzMap.fourierMultiplierCLM ℂ
          (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) g).toLp p : 𝓢'(E, ℂ)) : 𝓢'(E, ℂ))
        (ball 0 (2 ^ j * (φ.rIn / 2)))) := by
  obtain ⟨C₀, hC₀⟩ := exists_littlewoodPaleyBlock_eq_and_norm_le (F := ℂ) φ
  refine ⟨max C₀ 0, le_max_right _ _, fun {p} _ j g ↦ ?_⟩
  have hM : ((SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
      g).toLp p : 𝓢'(E, ℂ)) = littlewoodPaleyBlock ℂ φ j (g.toLp p : 𝓢'(E, ℂ)) := by
    rw [Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq,
      littlewoodPaleyBlock_toTemperedDistributionCLM_eq]
  refine ⟨?_, by rw [hM]; exact isVanishingOn_fourier_littlewoodPaleyBlock φ j _, fun hj ↦ ?_⟩
  · obtain ⟨G, hG, hGn⟩ := hC₀ j (g.toLp p)
    rw [← hM] at hG
    rw [Lp.toTemperedDistribution_injective hG]
    exact hGn.trans (by gcongr; exact le_max_left _ _)
  · -- The spectrum of `Δ_{k+1} g` avoids the ball of radius `2^k φ.rIn`.
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hj.ne'
    rw [hM]
    refine (isVanishingOn_fourier_littlewoodPaleyBlock_succ φ k _).mono fun ξ hξ ↦ ?_
    rw [Set.mem_compl_iff, Set.mem_sdiff, not_and, not_not]
    intro _
    rw [mem_ball_zero_iff] at hξ ⊢
    calc ‖ξ‖ < 2 ^ (k + 1) * (φ.rIn / 2) := hξ
      _ = 2 ^ k * φ.rIn := by ring

/-- **Finite sums of blocks of Schwartz functions.** There is `K ≥ 0`, depending only on `φ` and
`s`, such that `‖∑_{j ∈ t} Δⱼ gⱼ‖_{B^s_{p,q}} ≤ K ‖w‖_{ℓ^q}` for Schwartz functions `gⱼ` and a
nonnegative `w ∈ ℓ^q` with `2^{js} ‖gⱼ‖_p ≤ wⱼ` for `j ∈ t`. -/
private theorem exists_norm_toBesovSpaceCLM_sum_le (s : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {p : ℝ≥0∞} [Fact (1 ≤ p)] {q : ℝ≥0∞} [Fact (1 ≤ q)] (t : Finset ℕ)
      (g : ℕ → 𝓢(E, ℂ)) (w : lp (fun _ : ℕ ↦ ℝ) q), (∀ j, 0 ≤ w j) →
      (∀ j ∈ t, 2 ^ (s * j) * ‖(g j).toLp p‖ ≤ w j) →
      ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q (∑ j ∈ t, SchwartzMap.fourierMultiplierCLM ℂ
        (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) (g j))‖ ≤ K * ‖w‖ := by
  obtain ⟨C, hC⟩ :=
    exists_hasSum_toDistr_and_norm_le_of_annulus (F := ℂ) φ s (half_pos φ.rIn_pos) φ.rOut
  obtain ⟨C₀, hC₀, hpiece⟩ := exists_norm_toLp_fourierMultiplierCLM_le φ
  refine ⟨max C 0 * C₀, by positivity, fun {p} _ {q} _ t g w hw0 hw ↦ ?_⟩
  -- The pieces `uⱼ = Δⱼ gⱼ` for `j ∈ t` and `0` otherwise, as `Lᵖ` functions.
  obtain ⟨g', hg'⟩ : ∃ g' : ℕ → 𝓢(E, ℂ), ∀ j, g' j = if j ∈ t then g j else 0 :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → Lp ℂ p (volume : Measure E), ∀ j, u j =
      (SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ))
        (g' j)).toLp p := ⟨_, fun _ ↦ rfl⟩
  have hu0 (j : ℕ) (hj : j ∉ t) : u j = 0 := by
    rw [hu, hg', ite_eq_right hj, map_zero, ← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_zero]
  have hweight (j : ℕ) : 2 ^ (s * j) * ‖u j‖ ≤ (C₀ • w) j := by
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j ∈ t
    · calc 2 ^ (s * j) * ‖u j‖ ≤ 2 ^ (s * j) * (C₀ * ‖(g j).toLp p‖) := by
            gcongr
            simpa [hu, hg', hj] using (hpiece j (g' j)).1
        _ = C₀ * (2 ^ (s * j) * ‖(g j).toLp p‖) := by ring
        _ ≤ C₀ * w j := by gcongr; exact hw j hj
    · simpa [hu0 j hj] using mul_nonneg hC₀ (hw0 j)
  obtain ⟨v, hv, hvn⟩ := hC u (C₀ • w) (fun j ↦ hu j ▸ (hpiece j (g' j)).2.1)
    (fun j hj ↦ hu j ▸ (hpiece j (g' j)).2.2 hj) hweight
  -- The series is the finite sum over `t`, so `v` is the Besov element of `∑_{j ∈ t} Δⱼ gⱼ`.
  have hsum : HasSum (fun j ↦ (u j : 𝓢'(E, ℂ))) (∑ j ∈ t, (u j : 𝓢'(E, ℂ))) :=
    hasSum_sum_of_ne_finset_zero fun j hj ↦ by rw [hu0 j hj, Lp.toTemperedDistribution_zero]
  have hvt : SchwartzMap.toBesovSpaceCLM ℂ φ s p q (∑ j ∈ t, SchwartzMap.fourierMultiplierCLM ℂ
      (fun ξ ↦ (φ.inhomogeneousLittlewoodPaley j ξ : ℂ)) (g j)) = v := by
    refine ext ?_
    rw [SchwartzMap.toDistr_toBesovSpaceCLM, hv.unique hsum]
    simp only [hu, Lp.toTemperedDistribution_toLp_eq, ← map_sum]
    exact congrArg _ (Finset.sum_congr rfl fun j hj ↦ by simp [hg', hj])
  rw [hvt]
  calc ‖v‖ ≤ C * ‖C₀ • w‖ := hvn
    _ ≤ max C 0 * ‖C₀ • w‖ := by gcongr; exact le_max_left _ _
    _ = max C 0 * C₀ * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hC₀, mul_assoc]

/-- **The pairing with blocks of nearly norming functions.** If pairing `u` with finite sums of
blocks of Schwartz functions costs `A K` times an `ℓ^q` majorant of `2^{js} ‖gⱼ‖_p`, and
`‖gⱼ‖_p ≤ 1`, then `‖∑_{j ∈ t} cⱼ 2^{-js} (Δⱼ u) gⱼ‖ ≤ A K ‖c‖_q` for every `c ∈ ℓ^q`. -/
private theorem norm_sum_mul_littlewoodPaleyBlock_apply_le {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] {s A K : ℝ} (hAK : 0 ≤ A * K) (u : 𝓢'(E, ℂ)) (g : ℕ → 𝓢(E, ℂ))
    (hg : ∀ j, ‖(g j).toLp p‖ ≤ 1)
    (hpair : ∀ (t : Finset ℕ) (G : ℕ → 𝓢(E, ℂ)) (w : lp (fun _ : ℕ ↦ ℝ) q), (∀ j, 0 ≤ w j) →
      (∀ j ∈ t, 2 ^ (s * j) * ‖(G j).toLp p‖ ≤ w j) →
      ‖∑ j ∈ t, littlewoodPaleyBlock ℂ φ j u (G j)‖ ≤ A * K * ‖w‖)
    (t : Finset ℕ) (c : lp (fun _ : ℕ ↦ ℂ) q) :
    ‖∑ j ∈ t, c j * ((((2 : ℝ) ^ (-(s * j)) : ℝ) : ℂ) * littlewoodPaleyBlock ℂ φ j u (g j))‖ ≤
      A * K * ‖c‖ := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  -- The sum is the pairing of `u` with `∑_{j ∈ t} Δⱼ (cⱼ 2^{-js} gⱼ)`.
  have heq :
      ∑ j ∈ t, c j * ((((2 : ℝ) ^ (-(s * j)) : ℝ) : ℂ) * littlewoodPaleyBlock ℂ φ j u (g j)) =
      ∑ j ∈ t, littlewoodPaleyBlock ℂ φ j u ((c j * (((2 : ℝ) ^ (-(s * j)) : ℝ) : ℂ)) • g j) :=
    Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul, mul_assoc]
  have hw (j : ℕ) :
      (2 : ℝ) ^ (s * j) * ‖((c j * (((2 : ℝ) ^ (-(s * j)) : ℝ) : ℂ)) • g j).toLp p‖ ≤ ‖c j‖ := by
    rw [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_smul, SchwartzMap.toLpCLM_apply, norm_smul,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have h1 : (2 : ℝ) ^ (s * j) * 2 ^ (-(s * j)) = 1 := by
      rw [← Real.rpow_add two_pos, add_neg_cancel, Real.rpow_zero]
    have hx := hg j
    have hy := norm_nonneg (c j)
    generalize ‖(g j).toLp p‖ = x at hx ⊢
    generalize ‖c j‖ = y at hy ⊢
    calc (2 : ℝ) ^ (s * j) * (y * 2 ^ (-(s * j)) * x) = y * (2 ^ (s * j) * 2 ^ (-(s * j))) * x := by
          ring
      _ ≤ y := by rw [h1, mul_one]; exact mul_le_of_le_one_right hy hx
  rw [heq]
  calc _ ≤ A * K * ‖(⟨fun j ↦ ‖c j‖, (lp.memℓp c).norm⟩ : lp (fun _ : ℕ ↦ ℝ) q)‖ :=
        hpair t _ _ (fun j ↦ norm_nonneg _) fun j _ ↦ hw j
    _ ≤ A * K * ‖c‖ := by
        refine mul_le_mul_of_nonneg_left ?_ hAK
        exact lp.norm_mono (x := ⟨fun j ↦ ‖c j‖, (lp.memℓp c).norm⟩) (y := c) hq0
          fun j ↦ (norm_norm (c j)).le

/-- **Assembling the blocks.** Let `u` be a tempered distribution whose blocks `Δⱼ u` are
`L^{p'}` functions `hⱼ`. If there are `zⱼ` with `2^{-js} ‖hⱼ‖ ≤ 2 ‖zⱼ‖` whose finite pairings with
`ℓ^q` satisfy `‖∑_{j ∈ t} cⱼ zⱼ‖ ≤ B ‖c‖_q`, then `u` is an element of `B^{-s}_{p',q'}` of norm at
most `2 B`. -/
private theorem exists_toDistr_eq_and_norm_le_of_forall_norm_sum_mul_le {p' q q' : ℝ≥0∞}
    [Fact (1 ≤ p')] [Fact (1 ≤ q)] [Fact (1 ≤ q')] [q'.HolderConjugate q] {s B : ℝ} (hB : 0 ≤ B)
    (u : 𝓢'(E, ℂ)) (h : ℕ → Lp ℂ p' (volume : Measure E))
    (hh : ∀ j, littlewoodPaleyBlock ℂ φ j u = h j)
    (z : ℕ → ℂ) (hz : ∀ j : ℕ, (2 : ℝ) ^ (-s * j) * ‖h j‖ ≤ 2 * ‖z j‖)
    (hzc : ∀ (t : Finset ℕ) (c : lp (fun _ : ℕ ↦ ℂ) q), ‖∑ j ∈ t, c j * z j‖ ≤ B * ‖c‖) :
    ∃ v : BesovSpace ℂ φ (-s) p' q', v.toDistr = u ∧ ‖v‖ ≤ 2 * B := by
  obtain ⟨hx, hxn⟩ := lp.exists_memℓp_and_norm_le_of_forall_norm_sum_mul_le (p := q')
    (x := fun j : ℕ ↦ (2 : ℝ) ^ (-s * j) * ‖h j‖) z zero_le_two hB
    (fun j ↦ (Real.norm_of_nonneg (by positivity)).trans_le (hz j)) hzc
  obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_and_norm_le_of_littlewoodPaleyBlock_eq h ⟨_, hx⟩ hh
    fun j ↦ le_rfl
  exact ⟨v, hv, hvn.trans hxn⟩

/-- **Besov norms of negative order by duality** (Bahouri–Chemin–Danchin, Proposition 2.76). Let
`s : ℝ`. There is `C`, depending only on `φ` and `s`, with the following property. Let
`1 < p < ∞` and `1 ≤ q ≤ ∞`, with Hölder conjugate exponents `p'` and `q'`. If a tempered
distribution `u` satisfies `‖u f‖ ≤ A ‖f‖_{B^s_{p,q}}` for every Schwartz function `f`, then `u`
is an element of `B^{-s}_{p',q'}` of norm at most `C A`. -/
theorem exists_toDistr_eq_and_norm_le_of_norm_apply_le (s : ℝ) :
    ∃ C : ℝ, ∀ {p p' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [p'.HolderConjugate p]
      {q q' : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ q')] [q'.HolderConjugate q], 1 < p → p ≠ ∞ →
      ∀ (u : 𝓢'(E, ℂ)) {A : ℝ}, 0 ≤ A →
      (∀ f : 𝓢(E, ℂ), ‖u f‖ ≤ A * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q f‖) →
      ∃ v : BesovSpace ℂ φ (-s) p' q', v.toDistr = u ∧ ‖v‖ ≤ C * A := by
  obtain ⟨K, hK, hKt⟩ := exists_norm_toBesovSpaceCLM_sum_le φ s
  refine ⟨2 * K, fun {p p'} _ _ _ {q q'} _ _ _ hp hp_top u A hA hu ↦ ?_⟩
  -- Pairing `u` with a finite sum of blocks costs `A K` times an `ℓ^q` majorant.
  have hpair (t : Finset ℕ) (G : ℕ → 𝓢(E, ℂ)) (w : lp (fun _ : ℕ ↦ ℝ) q) (hw0 : ∀ j, 0 ≤ w j)
      (hw : ∀ j ∈ t, 2 ^ (s * j) * ‖(G j).toLp p‖ ≤ w j) :
      ‖∑ j ∈ t, littlewoodPaleyBlock ℂ φ j u (G j)‖ ≤ A * K * ‖w‖ := by
    simp_rw [littlewoodPaleyBlock_apply_apply, ← map_sum]
    calc _ ≤ A * (K * ‖w‖) := (hu _).trans (by gcongr; exact hKt t G w hw0 hw)
      _ = A * K * ‖w‖ := by ring
  -- Each block of `u` is an `L^{p'}` function `hⱼ` with `‖hⱼ‖ ≤ A K 2^{js}`.
  have hblock (j : ℕ) : ∃ h : Lp ℂ p' (volume : Measure E),
      (h : 𝓢'(E, ℂ)) = littlewoodPaleyBlock ℂ φ j u ∧ ‖h‖ ≤ A * K * 2 ^ (s * j) := by
    refine exists_eq_toTemperedDistribution_and_norm_le hp hp_top _ (by positivity) fun g ↦ ?_
    have := hpair {j} (fun _ ↦ g) (lp.single q j (2 ^ (s * j) * ‖g.toLp p‖))
      (fun i ↦ by
        rw [lp.single_apply, Pi.single_apply]
        split_ifs <;> positivity)
      (by simp)
    rw [Finset.sum_singleton, lp.norm_single (zero_lt_one.trans_le Fact.out),
      Real.norm_of_nonneg (by positivity)] at this
    exact this.trans_eq (by ring)
  choose h hh _ using hblock
  -- Schwartz functions `gⱼ` with `‖gⱼ‖_p ≤ 1` nearly norming `hⱼ`.
  have hnear (j : ℕ) : ∃ g : 𝓢(E, ℂ), ‖g.toLp p‖ ≤ 1 ∧ ‖h j‖ ≤ 2 * ‖(h j : 𝓢'(E, ℂ)) g‖ := by
    rcases (norm_nonneg (h j)).eq_or_lt with h0 | h0
    · refine ⟨0, ?_, by rw [← h0]; positivity⟩
      rw [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_zero, norm_zero]
      exact zero_le_one
    obtain ⟨g, hg1, hg⟩ :=
      Lp.exists_lt_norm_toTemperedDistribution_apply_of_lt_norm hp_top (h j) (half_lt_self h0)
    exact ⟨g, hg1.le, by linarith⟩
  choose g hg1 hg using hnear
  have hz (j : ℕ) : (2 : ℝ) ^ (-s * j) * ‖h j‖ ≤
      2 * ‖(((2 : ℝ) ^ (-(s * j)) : ℝ) : ℂ) * littlewoodPaleyBlock ℂ φ j u (g j)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), ← hh j, neg_mul]
    calc 2 ^ (-(s * j)) * ‖h j‖ ≤ 2 ^ (-(s * j)) * (2 * ‖(h j : 𝓢'(E, ℂ)) (g j)‖) := by
          gcongr
          exact hg j
      _ = 2 * (2 ^ (-(s * j)) * ‖(h j : 𝓢'(E, ℂ)) (g j)‖) := by ring
  obtain ⟨v, hv, hvn⟩ := exists_toDistr_eq_and_norm_le_of_forall_norm_sum_mul_le φ (q' := q')
    (by positivity) u h (fun j ↦ (hh j).symm) _ hz
    (norm_sum_mul_littlewoodPaleyBlock_apply_le φ (by positivity) u g hg1 hpair)
  exact ⟨v, hv, hvn.trans_eq (by ring)⟩

/-- **Functionals on `B^s_{p,q}` are pairings with `B^{-s}_{p',q'}`.** Let `s : ℝ`. There is `C`,
depending only on `φ` and `s`, with the following property. Let `1 < p < ∞` and `1 ≤ q ≤ ∞`, with
Hölder conjugate exponents `p'` and `q'`. For every continuous linear functional `Λ` on
`B^s_{p,q}` there is `v ∈ B^{-s}_{p',q'}` with `‖v‖ ≤ C ‖Λ‖` whose pairing with every Schwartz
function `f` is `Λ f`. -/
theorem exists_toDistr_apply_eq_and_norm_le (s : ℝ) :
    ∃ C : ℝ, ∀ {p p' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [p'.HolderConjugate p]
      {q q' : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ q')] [q'.HolderConjugate q], 1 < p → p ≠ ∞ →
      ∀ Λ : StrongDual ℂ (BesovSpace ℂ φ s p q), ∃ v : BesovSpace ℂ φ (-s) p' q',
        (∀ f : 𝓢(E, ℂ), v.toDistr f = Λ (SchwartzMap.toBesovSpaceCLM ℂ φ s p q f)) ∧
          ‖v‖ ≤ C * ‖Λ‖ := by
  obtain ⟨C, hC⟩ := exists_toDistr_eq_and_norm_le_of_norm_apply_le φ s
  refine ⟨C, fun {p p'} _ _ _ {q q'} _ _ _ hp hp_top Λ ↦ ?_⟩
  -- The restriction of `Λ` to the Schwartz functions, as a tempered distribution.
  have hu (f : 𝓢(E, ℂ)) : ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) 𝓢(E, ℂ) ℂ
      (Λ ∘L SchwartzMap.toBesovSpaceCLM ℂ φ s p q) f =
        Λ (SchwartzMap.toBesovSpaceCLM ℂ φ s p q f) := by
    rw [ContinuousLinearMap.toPointwiseConvergenceCLM_apply]
    exact ContinuousLinearMap.comp_apply Λ _ f
  obtain ⟨v, hv, hvn⟩ := hC (p' := p') (q' := q') hp hp_top
    (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) 𝓢(E, ℂ) ℂ
      (Λ ∘L SchwartzMap.toBesovSpaceCLM ℂ φ s p q)) (norm_nonneg Λ) fun f ↦ by
      rw [hu]
      exact Λ.le_opNorm _
  exact ⟨v, fun f ↦ by rw [hv, hu], hvn⟩

end TauCeti.BesovSpace
