/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.Torus.Smooth
public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Basic
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Multiplication by smooth functions on periodic Besov spaces

Let `B^s_{p,q}(𝕋ᵈ)` be the periodic Besov space (`TauCeti.UnitAddTorus.BesovSpace φ s p q`) of
formal Fourier series `c : ℤᵈ → ℂ`, for `s : ℝ` and `1 ≤ p, q ≤ ∞`. This file proves that
multiplication by a smooth function `g` on the torus is a bounded operator on `B^s_{p,q}(𝕋ᵈ)` for
every `s`, `p` and `q` (`TauCeti.UnitAddTorus.BesovSpace.smulLeftCLM`). On Fourier coefficients
the product is the convolution

`(g c)(n) = ∑ₘ ĝ(m) c(n - m)`

(`TauCeti.UnitAddTorus.BesovSpace.coeff_smulLeftCLM`), and when `c` is the coefficient sequence of
an integrable function `f` this is the coefficient sequence of the pointwise product `g f`
(`TauCeti.UnitAddTorus.BesovSpace.coeff_smulLeftCLM_eq_mFourierCoeff_mul`); for the monomial
`g = eₘ` it is the shift `(eₘ c)(n) = c(n - m)`
(`TauCeti.UnitAddTorus.BesovSpace.smulLeftCLM_mFourierSmooth`). The operator norm is
bounded by a constant times any bound `M` for the derivatives of `g` of order at most
`⌈|s|⌉₊ + card d + 2` (`TauCeti.UnitAddTorus.BesovSpace.exists_norm_smulLeftCLM_le`), and it is
additive and homogeneous in `g` (`TauCeti.UnitAddTorus.BesovSpace.smulLeftCLM_add` and
`TauCeti.UnitAddTorus.BesovSpace.smulLeftCLM_smul`). This is the periodic counterpart of
`TauCeti.BesovSpace.smulLeftCLM` on `ℝᵈ`.

## The argument

The building blocks are the multiplications by the Fourier monomials `eₘ`, which shift the
frequencies by `m`: `(eₘ c)(n) = c(n - m)` (`TauCeti.UnitAddTorus.BesovSpace.mulMFourier`).

* **Shifted blocks.** The block `Δⱼ (eₘ c)` has the coefficients `ψⱼ(n) c(n - m)`. Since the
  `ψₖ(n - m)` sum to one, it is the sum of the `Δⱼ (eₘ (ψₖ c))`, and the translate `ψⱼ(· + m)`
  only meets the pieces `ψₖ` with `2^{|j - k|} ≤ c_φ (1 + ‖m‖)`
  (`ContDiffBump.two_pow_le_of_inhomogeneousLittlewoodPaley_add_ne_zero`). So only the indices `k`
  in a window `|j - k| < L` contribute, where `2^L` is comparable to `1 + ‖m‖`.
* **One shifted block.** `eₘ (Δₖ c)` is the trigonometric polynomial `Δₖ c` multiplied by `eₘ`, so
  it has the same `Lᵖ` norm (`TauCeti.UnitAddTorus.norm_sum_smul_mFourierLp_add`), and the block
  `Δⱼ` is bounded on `Lᵖ` uniformly in `j`
  (`TauCeti.UnitAddTorus.exists_eLpNorm_littlewoodPaleyBlock_le`).
  Hence `‖Δⱼ (eₘ (ψₖ c))‖_p ≤ A ‖Δₖ c‖_p`.
* **The weights.** Within the window `2^{js} ≤ 2^{|s| L} 2^{ks}`, and the window sums of an `ℓ^q`
  sequence have norm at most `2L` times its norm. This bounds the operator norm of `eₘ` by
  `C (1 + ‖m‖)^{|s| + 1}`, with `C` independent of `m`, `p` and `q`
  (`TauCeti.UnitAddTorus.BesovSpace.exists_norm_mulMFourier_le`).
* **Smooth functions.** The Fourier coefficients of a smooth `g` decay faster than every power,
  so the series `∑ₘ ĝ(m) eₘ` converges absolutely in the operator norm on `B^s_{p,q}(𝕋ᵈ)`; its sum
  is the multiplication by `g`.

## References

* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (pointwise multipliers of the periodic Besov spaces).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.8.2 (smooth functions as pointwise
  multipliers of Besov spaces).
-/

public section

noncomputable section

open Filter MeasureTheory Topology
open scoped lp ENNReal NNReal

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d] {φ : ContDiffBump (0 : EuclideanSpace ℝ d)}

section Blocks

-- The periodic Littlewood–Paley blocks and Mathlib's monomials `mFourierLp` live on `Lᵖ` for the
-- product of the Haar probability measures on the circle factors, given by this instance; use it
-- here so that the blocks are those of the periodic Besov spaces. The section ends before the
-- operators, so that their statements, such as integrability, refer to the ordinary torus volume.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

/-! ### Shifted blocks -/

/-- **Shifted blocks meet only nearby blocks.** If `c_φ (1 + ‖m‖) < 2^L` for
`c_φ = 2 (φ.rOut + 1) / φ.rIn`, then the block `Δⱼ` of the shifted series `n ↦ c(n - m)` is the sum
over `j - L ≤ k < j + L` of the blocks `Δⱼ` of the shifted series `n ↦ ψₖ(n - m) c(n - m)`. -/
theorem littlewoodPaleyBlockLp_shift_eq_sum_Ico {m : d → ℤ} {L : ℕ}
    (hL : 2 * (φ.rOut + 1) / φ.rIn * (1 + ‖latticePoint m‖) < 2 ^ L) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (j : ℕ) (c : (d → ℤ) → ℂ) :
    littlewoodPaleyBlockLp φ p j (fun n ↦ c (n - m)) = ∑ k ∈ Finset.Ico (j - L) (j + L),
      littlewoodPaleyBlockLp φ p j
        (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint (n - m)) : ℂ) * c (n - m)) := by
  rw [← map_sum]
  refine littlewoodPaleyBlockLp_congr fun n ↦ ?_
  set ζ := latticePoint (n - m)
  have hζ : latticePoint n = ζ + latticePoint m := by
    simp only [ζ, latticePoint_sub, sub_add_cancel]
  set c' := 2 * (φ.rOut + 1) / φ.rIn * (1 + ‖latticePoint m‖)
  -- `ψⱼ(ζ + m) = ∑ₖ ψⱼ(ζ + m) ψₖ(ζ)`, and only the indices `k` near `j` contribute.
  have hsum : HasSum (fun k ↦ φ.inhomogeneousLittlewoodPaley j (ζ + latticePoint m) *
      φ.inhomogeneousLittlewoodPaley k ζ)
      (φ.inhomogeneousLittlewoodPaley j (ζ + latticePoint m)) := by
    simpa using (φ.hasSum_inhomogeneousLittlewoodPaley ζ).mul_left
      (φ.inhomogeneousLittlewoodPaley j (ζ + latticePoint m))
  have hfin : HasSum (fun k ↦ φ.inhomogeneousLittlewoodPaley j (ζ + latticePoint m) *
      φ.inhomogeneousLittlewoodPaley k ζ) (∑ k ∈ Finset.Ico (j - L) (j + L),
        φ.inhomogeneousLittlewoodPaley j (ζ + latticePoint m) *
          φ.inhomogeneousLittlewoodPaley k ζ) := by
    refine hasSum_sum_of_ne_finset_zero fun k hk ↦
      φ.inhomogeneousLittlewoodPaley_add_mul_eq_zero (fun h ↦ ?_) ζ
    have h2L : (0 : ℝ) < 2 ^ L := by positivity
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
    rcases hk with hk | hk
    · -- `k + L < j`, so `2^j ≥ 2^L 2^k > c' 2^k`.
      have : (2 : ℝ) ^ (k + L) ≤ 2 ^ j := pow_le_pow_right₀ one_le_two (by omega)
      rw [pow_add] at this
      nlinarith [h.1, pow_pos (two_pos (α := ℝ)) k]
    · -- `j + L ≤ k`, so `2^k ≥ 2^L 2^j > c' 2^j`.
      have : (2 : ℝ) ^ (j + L) ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk
      rw [pow_add] at this
      nlinarith [h.2, pow_pos (two_pos (α := ℝ)) j]
  have key : (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) =
      ∑ k ∈ Finset.Ico (j - L) (j + L),
        (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) *
          φ.inhomogeneousLittlewoodPaley k ζ := by
    rw [hζ]
    exact_mod_cast hsum.unique hfin
  rw [Finset.sum_apply, Finset.mul_sum]
  nth_rw 1 [key]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

variable (φ) in
/-- **One shifted block.** There is `A ≥ 0`, depending only on `φ`, such that the block `Δⱼ` of the
shifted series `n ↦ ψₖ(n - m) c(n - m)`, the coefficients of `eₘ Δₖ c`, has `Lᵖ` norm at most
`A ‖Δₖ c‖_p`, for all `j`, `k`, `m`, `1 ≤ p ≤ ∞` and `c`. -/
theorem exists_norm_littlewoodPaleyBlockLp_shift_mul_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (j k : ℕ) (m : d → ℤ) (c : (d → ℤ) → ℂ),
      ‖littlewoodPaleyBlockLp φ p j
          (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint (n - m)) : ℂ) * c (n - m))‖ ≤
        A * ‖littlewoodPaleyBlockLp φ p k c‖ := by
  obtain ⟨A, hA⟩ := exists_eLpNorm_littlewoodPaleyBlock_le φ
  refine ⟨A, A.coe_nonneg, fun p _ j k m c ↦ ?_⟩
  classical
  set S := (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ k * φ.rOut)).toFinset
  set b : (d → ℤ) → ℂ := fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint n) : ℂ) * c n
  -- The trigonometric polynomial `eₘ Δₖ c`, in `Lʳ` for every `r`, reindexed by its frequencies.
  set S' := S.map (addRightEmbedding m)
  have hreindex (r : ℝ≥0∞) [Fact (1 ≤ r)] :
      (∑ n ∈ S, b n • mFourierLp r (n + m) : Lp ℂ r (volume : Measure (UnitAddTorus d))) =
        ∑ n ∈ S', b (n - m) • mFourierLp r n := by
    simp [S', Finset.sum_map]
  have hb : ∀ n, (if n ∈ S' then b (n - m) else 0) = b (n - m) := fun n ↦ by
    split_ifs with hn
    · rfl
    · have : n - m ∉ S := fun h ↦ hn (Finset.mem_map.2 ⟨n - m, h, by simp⟩)
      simp [b, inhomogeneousLittlewoodPaley_eq_zero_of_notMem k this]
  set f : Lp ℂ 2 (volume : Measure (UnitAddTorus d)) := ∑ n ∈ S', b (n - m) • mFourierLp 2 n
  have hf : littlewoodPaleyBlock φ j f = littlewoodPaleyBlockLp φ 2 j (fun n ↦ b (n - m)) := by
    rw [← littlewoodPaleyBlockLp_mFourierCoeff]
    congr 1
    funext n
    rw [mFourierCoeff_sum_smul_mFourierLp, hb]
  have h := hA j (Fact.out : (1 : ℝ≥0∞) ≤ p) f
  rw [hf, eLpNorm_congr_ae (coeFn_littlewoodPaleyBlockLp_ae_eq 2 p j _),
    eLpNorm_congr_ae ((coeFn_sum_smul_mFourierLp 2 S' _).trans
      (coeFn_sum_smul_mFourierLp p S' _).symm)] at h
  -- The `Lᵖ` norm of `eₘ Δₖ c` is that of `Δₖ c`.
  have hmod : ‖(∑ n ∈ S', b (n - m) • mFourierLp p n :
      Lp ℂ p (volume : Measure (UnitAddTorus d)))‖ = ‖littlewoodPaleyBlockLp φ p k c‖ := by
    rw [← hreindex, norm_sum_smul_mFourierLp_add,
      littlewoodPaleyBlockLp_eq_sum fun n hn ↦ inhomogeneousLittlewoodPaley_eq_zero_of_notMem k hn]
  rw [← hmod, Lp.norm_def, Lp.norm_def]
  calc (eLpNorm (littlewoodPaleyBlockLp φ p j fun n ↦ b (n - m)) p volume).toReal
      ≤ (A * eLpNorm (∑ n ∈ S', b (n - m) • mFourierLp p n :
          Lp ℂ p (volume : Measure (UnitAddTorus d))) p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (Lp.eLpNorm_ne_top _)) h
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.coe_toReal]

variable (φ) in
/-- The window length for a shift by `m`: there is `L` with `c_φ (1 + ‖m‖) < 2^L ≤ 2 c_φ (1 + ‖m‖)`
for `c_φ = 2 (φ.rOut + 1) / φ.rIn`. -/
private theorem exists_window (m : d → ℤ) :
    ∃ L : ℕ, 2 * (φ.rOut + 1) / φ.rIn * (1 + ‖latticePoint m‖) < 2 ^ L ∧
      (2 : ℝ) ^ L ≤ 2 * (2 * (φ.rOut + 1) / φ.rIn * (1 + ‖latticePoint m‖)) := by
  have hc : 1 ≤ 2 * (φ.rOut + 1) / φ.rIn * (1 + ‖latticePoint m‖) := by
    have := φ.rIn_lt_rOut
    have := φ.rIn_pos
    have h1 : 1 ≤ 2 * (φ.rOut + 1) / φ.rIn := by rw [le_div_iff₀ φ.rIn_pos]; linarith
    nlinarith [norm_nonneg (latticePoint m)]
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hc one_lt_two
  exact ⟨n + 1, hn', by rw [pow_succ]; linarith⟩

/-! ### Membership -/

section MemBesov

variable {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

variable (φ s) in
/-- **The weighted blocks of a shifted series.** There is `A ≥ 0`, depending only on `φ`, such
that for every shift `m` there is a window length `L` with `2^L ≤ 2 c_φ (1 + ‖m‖)` and
`2^{js} ‖Δⱼ (eₘ c)‖_p ≤ A 2^{|s| L} ∑_{j - L ≤ k < j + L} 2^{ks} ‖Δₖ c‖_p` for all `j`, `p` and
`c`. Here `c_φ = 2 (φ.rOut + 1) / φ.rIn` and `eₘ c` is the shifted series `n ↦ c(n - m)`. -/
theorem exists_rpow_mul_norm_littlewoodPaleyBlockLp_shift_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : d → ℤ, ∃ L : ℕ,
      (2 : ℝ) ^ L ≤ 2 * (2 * (φ.rOut + 1) / φ.rIn * (1 + ‖latticePoint m‖)) ∧
      ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) (c : (d → ℤ) → ℂ),
        2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j (fun n ↦ c (n - m))‖ ≤
          A * 2 ^ (|s| * L) * ∑ k ∈ Finset.Ico (j - L) (j + L),
            2 ^ (s * k) * ‖littlewoodPaleyBlockLp φ p k c‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_norm_littlewoodPaleyBlockLp_shift_mul_le φ
  refine ⟨A, hA0, fun m ↦ ?_⟩
  obtain ⟨L, hL, hL'⟩ := exists_window φ m
  refine ⟨L, hL', fun p _ j c ↦ ?_⟩
  rw [littlewoodPaleyBlockLp_shift_eq_sum_Ico hL p j c]
  have h := TauCeti.two_rpow_mul_norm_sum_Ico_le s
    (g := fun k ↦ littlewoodPaleyBlockLp φ p j
      (fun n ↦ (φ.inhomogeneousLittlewoodPaley k (latticePoint (n - m)) : ℂ) * c (n - m)))
    (x := fun k ↦ littlewoodPaleyBlockLp φ p k c) (fun k ↦ hA p j k m c) j L
  rwa [max_eq_left hA0] at h

/-- **Shifts preserve the periodic Besov spaces.** If `c ∈ B^s_{p,q}(𝕋ᵈ)`, then so is the shifted
series `n ↦ c(n - m)`, the coefficients of `eₘ c`. -/
theorem MemBesov.shift {c : (d → ℤ) → ℂ} (hc : MemBesov φ s p q c) (m : d → ℤ) :
    MemBesov φ s p q (fun n ↦ c (n - m)) := by
  obtain ⟨A, -, hA⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_shift_le φ s
  obtain ⟨L, -, hL⟩ := hA m
  refine memBesov_def.2 <|
    ((Memℓp.sum_Ico_sub_add (memBesov_def.1 hc) L).const_mul (A * 2 ^ (|s| * L))).mono fun j ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact hL p j c

end MemBesov

end Blocks

namespace BesovSpace

variable {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-! ### Multiplication by Fourier monomials -/

variable (φ) in
/-- The operator norm of the multiplication by `eₘ` on `B^s_{p,q}(𝕋ᵈ)` grows at most polynomially
in `m`: there is `C`, depending only on `φ` and `s`, with
`‖eₘ u‖ ≤ C (1 + ‖m‖)^{|s| + 1} ‖u‖` for all `m`, `p`, `q` and `u`, where `‖m‖` is the Euclidean
norm of the lattice point `m`. -/
private theorem exists_norm_shift_le (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (m : d → ℤ)
      (u : BesovSpace φ s p q),
      ‖(⟨fun n ↦ u.coeff (n - m), u.memBesov_coeff.shift m⟩ : BesovSpace φ s p q)‖ ≤
        C * (1 + ‖latticePoint m‖) ^ (|s| + 1) * ‖u‖ := by
  obtain ⟨A, hA0, hA⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_shift_le φ s
  set c₀ := 2 * (φ.rOut + 1) / φ.rIn
  have hc₀ : 0 ≤ c₀ := by have := φ.rIn_pos; have := φ.rOut_pos; positivity
  refine ⟨A * (2 * c₀) ^ (|s| + 1) * 2, by positivity, fun p q _ _ m u ↦ ?_⟩
  obtain ⟨L, hL2, hL⟩ := hA m
  set K := A * 2 ^ (|s| * L)
  -- The weighted block norms of `u`, and their window sums, as elements of `ℓ^q`.
  set b := lp.normSeq u.weightedBlocks
  obtain ⟨w, hw, hwn⟩ := lp.exists_eq_sum_Ico_sub_add_and_norm_le b L
  have hnorm : ‖(⟨fun n ↦ u.coeff (n - m), u.memBesov_coeff.shift m⟩ :
      BesovSpace φ s p q)‖ ≤ K * (2 * L) * ‖u‖ := by
    rw [← norm_weightedBlocks]
    calc ‖(⟨fun n ↦ u.coeff (n - m), u.memBesov_coeff.shift m⟩ :
          BesovSpace φ s p q).weightedBlocks‖
        ≤ ‖K • w‖ := lp.norm_mono (zero_lt_one.trans_le Fact.out).ne' fun j ↦ by
          rw [norm_weightedBlocks_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hw]
          refine (hL p j u.coeff).trans ((le_of_eq ?_).trans (Real.le_norm_self _))
          simp only [b, K, lp.normSeq_apply, norm_weightedBlocks_apply]
      _ = K * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ K * (2 * L * ‖b‖) := by gcongr
      _ = K * (2 * L) * ‖u‖ := by rw [lp.norm_normSeq, norm_weightedBlocks, mul_assoc K]
  refine hnorm.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
  -- `2^{|s| L} 2 L ≤ 2 (2^L)^{|s| + 1} ≤ 2 (2 c₀ (1 + ‖m‖))^{|s| + 1}`.
  have hL1 : (L : ℝ) ≤ 2 ^ L := by exact_mod_cast (Nat.lt_two_pow_self).le
  have h2L : (2 : ℝ) ^ (|s| * L) * L ≤ ((2 : ℝ) ^ L) ^ (|s| + 1) := by
    rw [Real.rpow_add_one (by positivity), ← Real.rpow_natCast_mul zero_le_two, mul_comm (L : ℝ)]
    gcongr
  have hpow : ((2 : ℝ) ^ L) ^ (|s| + 1) ≤
      (2 * c₀) ^ (|s| + 1) * (1 + ‖latticePoint m‖) ^ (|s| + 1) := by
    rw [← Real.mul_rpow (by positivity) (by positivity), mul_assoc]
    gcongr
  calc K * (2 * L) = A * 2 * (2 ^ (|s| * L) * L) := by ring
    _ ≤ A * 2 * ((2 * c₀) ^ (|s| + 1) * (1 + ‖latticePoint m‖) ^ (|s| + 1)) :=
        mul_le_mul_of_nonneg_left (h2L.trans hpow) (by positivity)
    _ = _ := by ring

variable (φ s p q) in
/-- **Multiplication by a Fourier monomial.** Multiplying by `eₘ` shifts the Fourier coefficients
by `m`, `(eₘ u)(n) = u(n - m)`, and is a bounded operator on `B^s_{p,q}(𝕋ᵈ)`, of norm at most a
polynomial in `m` (`TauCeti.UnitAddTorus.BesovSpace.exists_norm_mulMFourier_le`). -/
def mulMFourier (m : d → ℤ) : BesovSpace φ s p q →L[ℂ] BesovSpace φ s p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := ⟨fun n ↦ u.coeff (n - m), u.memBesov_coeff.shift m⟩
      map_add' _ _ := ext rfl
      map_smul' _ _ := ext rfl } <| by
    obtain ⟨C, -, hC⟩ := exists_norm_shift_le φ (d := d) s
    exact ⟨C * (1 + ‖latticePoint m‖) ^ (|s| + 1), fun u ↦ hC p q m u⟩

@[simp]
theorem coeff_mulMFourier (m : d → ℤ) (u : BesovSpace φ s p q) :
    (mulMFourier φ s p q m u).coeff = fun n ↦ u.coeff (n - m) := (rfl)

/-- Multiplication by `e₀ = 1` is the identity. -/
@[simp]
theorem mulMFourier_zero : mulMFourier φ s p q (0 : d → ℤ) = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun u ↦ ext (by simp)

/-- Multiplication by `e_{m + m'} = eₘ e_{m'}` is the composite of the multiplications by `eₘ` and
`e_{m'}`. -/
theorem mulMFourier_add (m m' : d → ℤ) :
    mulMFourier φ s p q (m + m') = (mulMFourier φ s p q m).comp (mulMFourier φ s p q m') :=
  ContinuousLinearMap.ext fun u ↦ ext <| funext fun n ↦ by simp [sub_add_eq_sub_sub]

variable (φ s) in
/-- **The multiplications by Fourier monomials are bounded polynomially.** There is `C`, depending
only on `φ` and `s`, such that multiplication by `eₘ` on `B^s_{p,q}(𝕋ᵈ)` has operator norm at most
`C (1 + ‖m‖)^{|s| + 1}` for all `m`, `p` and `q`, where `‖m‖` is the Euclidean norm of the lattice
point `m`. -/
theorem exists_norm_mulMFourier_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (m : d → ℤ),
      ‖mulMFourier φ s p q m‖ ≤ C * (1 + ‖latticePoint m‖) ^ (|s| + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_shift_le φ (d := d) s
  exact ⟨C, hC0, fun p q _ _ m ↦
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ hC p q m u⟩

/-! ### Multiplication by smooth functions -/

variable (φ s) in
/-- The bound `exists_norm_mulMFourier_le` with a natural exponent and the supremum norm of `m`:
there is `C ≥ 0`, depending only on `φ` and `s`, such that multiplication by `eₘ` on
`B^s_{p,q}(𝕋ᵈ)` has operator norm at most `C (1 + ‖m‖)^{⌈|s|⌉₊ + 1}` for all `m`, `p` and `q`. -/
private theorem exists_norm_mulMFourier_le_pow :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (m : d → ℤ),
      ‖mulMFourier φ s p q m‖ ≤ C * (1 + ‖m‖) ^ (⌈|s|⌉₊ + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_mulMFourier_le φ (d := d) s
  refine ⟨C * (1 + Fintype.card d) ^ (⌈|s|⌉₊ + 1), by positivity,
    fun p q _ _ m ↦ (hC p q m).trans ?_⟩
  have hx : (1 : ℝ) ≤ 1 + ‖latticePoint m‖ := le_add_of_nonneg_right (norm_nonneg _)
  calc C * (1 + ‖latticePoint m‖) ^ (|s| + 1)
      ≤ C * (1 + ‖latticePoint m‖) ^ ((⌈|s|⌉₊ + 1 : ℕ) : ℝ) := by
        gcongr
        push_cast
        linarith [Nat.le_ceil |s|]
    _ = C * (1 + ‖latticePoint m‖) ^ (⌈|s|⌉₊ + 1) := by rw [Real.rpow_natCast]
    _ ≤ C * ((1 + Fintype.card d) * (1 + ‖m‖)) ^ (⌈|s|⌉₊ + 1) := by
        gcongr
        nlinarith [norm_latticePoint_le m, norm_nonneg m,
          (Nat.cast_nonneg (Fintype.card d) : (0 : ℝ) ≤ Fintype.card d)]
    _ = _ := by rw [mul_pow, mul_assoc]

/-- The series `∑ₘ ĝ(m) eₘ` of multiplications by Fourier monomials converges absolutely in the
operator norm on `B^s_{p,q}(𝕋ᵈ)`, for every smooth `g`. -/
private theorem summable_mFourierCoeff_smul_mulMFourier {g : UnitAddTorus d → ℂ}
    (hg : g ∈ smoothFunctions d) :
    Summable fun m ↦ mFourierCoeff g m • mulMFourier φ s p q m := by
  obtain ⟨C, -, hC⟩ := exists_norm_mulMFourier_le_pow φ (d := d) s
  exact summable_mFourierCoeff_smul_of_norm_le hg (hC p q)

variable (φ s p q) in
/-- **Multiplication by a smooth function on a periodic Besov space.** For a smooth function `g`
on the torus, multiplication by `g` is a bounded operator on `B^s_{p,q}(𝕋ᵈ)`, for every `s` and
`1 ≤ p, q ≤ ∞`. It is the sum `∑ₘ ĝ(m) eₘ` of the multiplications by the Fourier monomials, which
converges absolutely in operator norm, so on Fourier coefficients it is the convolution
`(g u)(n) = ∑ₘ ĝ(m) u(n - m)` (`TauCeti.UnitAddTorus.BesovSpace.coeff_smulLeftCLM`). -/
def smulLeftCLM (g : smoothFunctions d) : BesovSpace φ s p q →L[ℂ] BesovSpace φ s p q :=
  ∑' m, mFourierCoeff (g : UnitAddTorus d → ℂ) m • mulMFourier φ s p q m

/-- The multiplication by a smooth `g` is the absolutely convergent sum `∑ₘ ĝ(m) eₘ` of the
multiplications by the Fourier monomials. -/
theorem hasSum_mFourierCoeff_smul_mulMFourier (g : smoothFunctions d) :
    HasSum (fun m ↦ mFourierCoeff (g : UnitAddTorus d → ℂ) m • mulMFourier φ s p q m)
      (smulLeftCLM φ s p q g) :=
  (summable_mFourierCoeff_smul_mulMFourier g.property).hasSum

/-- **The coefficients of a product.** The Fourier coefficients of `g u` are the convolution
`(g u)(n) = ∑ₘ ĝ(m) u(n - m)`, the series converging absolutely. -/
theorem hasSum_coeff_smulLeftCLM (g : smoothFunctions d) (u : BesovSpace φ s p q) (n : d → ℤ) :
    HasSum (fun m ↦ mFourierCoeff (g : UnitAddTorus d → ℂ) m * u.coeff (n - m))
      ((smulLeftCLM φ s p q g u).coeff n) := by
  have h := ((hasSum_mFourierCoeff_smul_mulMFourier (φ := φ) (s := s) (p := p) (q := q) g).mapL
    (ContinuousLinearMap.apply ℂ _ u)).mapL (coeffCLM φ s p q n)
  simpa using h

/-- The Fourier coefficients of `g u` are the convolution `∑ₘ ĝ(m) u(n - m)`. -/
theorem coeff_smulLeftCLM (g : smoothFunctions d) (u : BesovSpace φ s p q) (n : d → ℤ) :
    (smulLeftCLM φ s p q g u).coeff n =
      ∑' m, mFourierCoeff (g : UnitAddTorus d → ℂ) m * u.coeff (n - m) :=
  (hasSum_coeff_smulLeftCLM g u n).tsum_eq.symm

/-- **The product with an integrable function.** If the coefficients of `u ∈ B^s_{p,q}(𝕋ᵈ)` are
those of an integrable function `f`, then the coefficients of `g u` are those of the pointwise
product `g f`. -/
theorem coeff_smulLeftCLM_eq_mFourierCoeff_mul (g : smoothFunctions d) {u : BesovSpace φ s p q}
    {f : UnitAddTorus d → ℂ} (hf : Integrable f) (hu : u.coeff = mFourierCoeff f) :
    (smulLeftCLM φ s p q g u).coeff = mFourierCoeff (fun x ↦ (g : UnitAddTorus d → ℂ) x * f x) := by
  funext n
  refine (hasSum_coeff_smulLeftCLM g u n).unique ?_
  rw [hu]
  have hsum : Summable fun m ↦ ‖mFourierCoeff (g : UnitAddTorus d → ℂ) m‖ := by
    simpa using summable_norm_mFourierCoeff_mul_pow g.property le_rfl 0
  exact hasSum_mFourierCoeff_mul (g := ⟨g, continuous_of_mem_smoothFunctions g.property⟩)
    hsum.of_norm hf n

/-- Multiplication by smooth functions is additive in the function: `(g + g') u = g u + g' u`. -/
theorem smulLeftCLM_add (g g' : smoothFunctions d) :
    smulLeftCLM φ s p q (g + g') = smulLeftCLM φ s p q g + smulLeftCLM φ s p q g' := by
  refine (hasSum_mFourierCoeff_smul_mulMFourier (g + g')).unique ?_
  convert (hasSum_mFourierCoeff_smul_mulMFourier g).add
    (hasSum_mFourierCoeff_smul_mulMFourier g') using 1
  funext m
  rw [Submodule.coe_add, _root_.UnitAddTorus.mFourierCoeff_add
    (integrable_of_mem_smoothFunctions g.property)
    (integrable_of_mem_smoothFunctions g'.property), add_smul]

/-- Multiplication by smooth functions is homogeneous in the function: `(c g) u = c (g u)`. -/
theorem smulLeftCLM_smul (c : ℂ) (g : smoothFunctions d) :
    smulLeftCLM φ s p q (c • g) = c • smulLeftCLM φ s p q g := by
  refine (hasSum_mFourierCoeff_smul_mulMFourier (c • g)).unique ?_
  convert (hasSum_mFourierCoeff_smul_mulMFourier g).const_smul c using 1
  funext m
  rw [Submodule.coe_smul, _root_.UnitAddTorus.mFourierCoeff_smul, smul_eq_mul, mul_smul]

/-- Multiplication by the smooth function `eₘ` is the multiplication by the Fourier monomial `eₘ`,
the shift of the Fourier coefficients by `m`. -/
@[simp]
theorem smulLeftCLM_mFourierSmooth (m : d → ℤ) :
    smulLeftCLM φ s p q (mFourierSmooth m) = mulMFourier φ s p q m := by
  refine (hasSum_mFourierCoeff_smul_mulMFourier (φ := φ) (s := s) (p := p) (q := q)
    (mFourierSmooth m)).unique ?_
  convert hasSum_ite_eq m (mulMFourier φ s p q m) using 2 with k
  split_ifs with hk <;> simp [mFourierCoeff_mFourier, hk]

variable (φ s) in
/-- **The norm of a multiplication by a smooth function.** There is `C`, depending only on `φ` and
`s`, such that multiplication by `g` on `B^s_{p,q}(𝕋ᵈ)` has operator norm at most `C M` for all
`p`, `q` and every smooth `g` whose derivatives of order at most `⌈|s|⌉₊ + card d + 2` are bounded
by `M` (`TauCeti.UnitAddTorus.DerivBound`). -/
theorem exists_norm_smulLeftCLM_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (g : smoothFunctions d)
      {M : ℝ}, DerivBound (⌈|s|⌉₊ + 1 + Fintype.card d + 1) M (g : UnitAddTorus d → ℂ) →
        ‖smulLeftCLM φ s p q g‖ ≤ C * M := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_mulMFourier_le_pow φ (d := d) s
  refine ⟨C * 2 ^ (⌈|s|⌉₊ + 1 + Fintype.card d + 2) *
    ∑' m : d → ℤ, ((1 + ‖m‖) ^ (Fintype.card d + 1))⁻¹, by positivity,
    fun p q _ _ g M hM ↦ ?_⟩
  exact norm_tsum_mFourierCoeff_smul_le g.property (hC p q) hM

end BesovSpace

end TauCeti.UnitAddTorus
