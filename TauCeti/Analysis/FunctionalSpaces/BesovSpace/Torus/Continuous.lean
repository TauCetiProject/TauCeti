/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous

/-!
# Periodic Besov spaces of order `s > d/p` consist of continuous functions

Let `φ` be a smooth bump function on `EuclideanSpace ℝ d`. The Littlewood–Paley block
`Δⱼ c = ∑ₙ ψⱼ(n) c(n) eₙ` of a formal Fourier series `c : ℤᵈ → ℂ` on the torus `𝕋ᵈ = UnitAddTorus d`
is a trigonometric polynomial, recorded here as a continuous function
(`TauCeti.UnitAddTorus.littlewoodPaleyBlockContinuousMap`); its `L^∞` norm is its supremum norm.

For `s > 0` the blocks of `c ∈ B^s_{∞,q}(𝕋ᵈ)` decay like `2^{-js}` in the supremum norm, so they sum
uniformly to a continuous function whose Fourier coefficients are `c`. With the Bernstein embedding
`B^s_{p,q}(𝕋ᵈ) ⊆ B^{s - d/p}_{∞,q}(𝕋ᵈ)` the same holds in `B^s_{p,q}(𝕋ᵈ)` for `s > d/p`
(`TauCeti.UnitAddTorus.MemBesov.exists_mFourierCoeff_eq`).

## Main declarations

* `TauCeti.UnitAddTorus.littlewoodPaleyBlockContinuousMap`: the block `Δⱼ c` as a continuous
  function on the torus, with Fourier coefficients `ψⱼ(n) c(n)`
  (`TauCeti.UnitAddTorus.mFourierCoeff_littlewoodPaleyBlockContinuousMap`) and the same `L^∞` norm
  as `TauCeti.UnitAddTorus.littlewoodPaleyBlockLp`
  (`TauCeti.UnitAddTorus.norm_littlewoodPaleyBlockLp_top`).
* `TauCeti.UnitAddTorus.MemBesov.exists_mFourierCoeff_eq`: the elements of `B^s_{p,q}(𝕋ᵈ)`,
  `s > d/p`, are continuous functions.

## References

* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (the periodic Besov spaces).
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- The periodic Besov spaces live on `Lᵖ` for the product of the Haar probability measures on the
-- circle factors, given by this instance; use it here as well.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable (φ : ContDiffBump (0 : EuclideanSpace ℝ d))

/-- The finite set of frequencies of norm at most `2^j φ.rOut`, outside of which `ψⱼ` vanishes
(`TauCeti.UnitAddTorus.inhomogeneousLittlewoodPaley_eq_zero_of_notMem`). -/
private def frequencies (j : ℕ) : Finset (d → ℤ) :=
  (finite_setOf_norm_latticePoint_le (ι := d) (2 ^ j * φ.rOut)).toFinset

/-- The Littlewood–Paley block `Δⱼ c = ∑ₙ ψⱼ(n) c(n) eₙ` as a continuous function on the torus. -/
def littlewoodPaleyBlockContinuousMap (j : ℕ) (c : (d → ℤ) → ℂ) : C(UnitAddTorus d, ℂ) :=
  ∑ n ∈ frequencies φ j, ((φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n) •
    mFourier n

private theorem coe_littlewoodPaleyBlockContinuousMap_eq_sum (j : ℕ) (c : (d → ℤ) → ℂ) :
    ⇑(littlewoodPaleyBlockContinuousMap φ j c) = fun z ↦ ∑ n ∈ frequencies φ j,
      (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n * mFourier n z :=
  funext fun z ↦ by simp [littlewoodPaleyBlockContinuousMap, ContinuousMap.sum_apply]

/-- The values of the block `Δⱼ c`; only finitely many terms of the series are nonzero. -/
theorem coe_littlewoodPaleyBlockContinuousMap (j : ℕ) (c : (d → ℤ) → ℂ) :
    ⇑(littlewoodPaleyBlockContinuousMap φ j c) = fun z ↦ ∑' n : d → ℤ,
      (φ.inhomogeneousLittlewoodPaley j (latticePoint n) : ℂ) * c n * mFourier n z := by
  rw [coe_littlewoodPaleyBlockContinuousMap_eq_sum]
  exact funext fun z ↦ (tsum_eq_sum (s := frequencies φ j)
    fun n hn ↦ by simp [inhomogeneousLittlewoodPaley_eq_zero_of_notMem j hn]).symm

/-- The block `Δⱼ c` in `L^∞(𝕋ᵈ)` is the class of the continuous block. -/
theorem littlewoodPaleyBlockLp_top_eq_toLp (j : ℕ) (c : (d → ℤ) → ℂ) :
    littlewoodPaleyBlockLp φ ∞ j c =
      ContinuousMap.toLp (E := ℂ) ∞ volume ℂ (littlewoodPaleyBlockContinuousMap φ j c) :=
  Lp.ext <| (coeFn_littlewoodPaleyBlockLp
    (fun _ hn ↦ inhomogeneousLittlewoodPaley_eq_zero_of_notMem j hn) c).trans <|
      EventuallyEq.trans
        (Eventually.of_forall fun z ↦
          (congrFun (coe_littlewoodPaleyBlockContinuousMap_eq_sum φ j c) z).symm)
        (ContinuousMap.coeFn_toLp (𝕜 := ℂ) volume (littlewoodPaleyBlockContinuousMap φ j c)).symm

/-- The `L^∞` norm of the block `Δⱼ c` is the supremum norm of the continuous block. -/
theorem norm_littlewoodPaleyBlockLp_top (j : ℕ) (c : (d → ℤ) → ℂ) :
    ‖littlewoodPaleyBlockLp φ ∞ j c‖ = ‖littlewoodPaleyBlockContinuousMap φ j c‖ := by
  rw [littlewoodPaleyBlockLp_top_eq_toLp, ContinuousMap.norm_toLp_top]

/-- The Fourier coefficients of the block `Δⱼ c` are `ψⱼ(n) c(n)`. -/
@[simp]
theorem mFourierCoeff_littlewoodPaleyBlockContinuousMap (j : ℕ) (c : (d → ℤ) → ℂ) (n : d → ℤ) :
    mFourierCoeff (littlewoodPaleyBlockContinuousMap φ j c) n =
      φ.inhomogeneousLittlewoodPaley j (latticePoint n) * c n := by
  rw [coe_littlewoodPaleyBlockContinuousMap_eq_sum, mFourierCoeff_sum_mul_mFourier]
  split_ifs with hn
  · rfl
  · simp [inhomogeneousLittlewoodPaley_eq_zero_of_notMem j hn]

variable {φ}

/-- For `s > 0`, the blocks of `c ∈ B^s_{∞,q}(𝕋ᵈ)` decay like `2^{-js}` in the supremum norm, so
their sum converges uniformly to a continuous function whose Fourier coefficients are `c`. -/
private theorem MemBesov.exists_mFourierCoeff_eq_of_top {s : ℝ} (hs : 0 < s) {q : ℝ≥0∞}
    {c : (d → ℤ) → ℂ} (hc : MemBesov φ s ∞ q c) :
    ∃ f : C(UnitAddTorus d, ℂ), mFourierCoeff f = c := by
  obtain ⟨M, hM⟩ := memℓp_infty_iff.1 (memBesov_def.1 (hc.mono le_rfl le_top))
  set r : ℝ := ((2 : ℝ) ^ s)⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ (Real.one_lt_rpow one_lt_two hs)
  -- The blocks decay geometrically: `‖Δⱼ c‖_∞ ≤ M 2^{-js}`.
  have hblock (j : ℕ) : ‖littlewoodPaleyBlockContinuousMap φ j c‖ ≤ M * r ^ j := by
    have h := hM ⟨j, rfl⟩
    beta_reduce at h
    rw [Real.norm_of_nonneg (by positivity), norm_littlewoodPaleyBlockLp_top] at h
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity), mul_comm]
    exact h
  have hsum : Summable fun j ↦ littlewoodPaleyBlockContinuousMap φ j c :=
    .of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left M) hblock
  refine ⟨∑' j, littlewoodPaleyBlockContinuousMap φ j c, funext fun n ↦ ?_⟩
  rw [← mFourierCoeffContinuousMapCLM_apply, (mFourierCoeffContinuousMapCLM n).map_tsum hsum]
  simp only [mFourierCoeffContinuousMapCLM_apply, mFourierCoeff_littlewoodPaleyBlockContinuousMap]
  exact ((Complex.ofRealCLM.hasSum (φ.hasSum_inhomogeneousLittlewoodPaley
    (latticePoint n))).mul_right (c n)).tsum_eq.trans (by simp)

/-- **Elements of `B^s_{p,q}(𝕋ᵈ)` of order `s > d/p` are continuous functions.** If
`d (1/p) < s`, which for `p = ∞` reads `0 < s`, every `c ∈ B^s_{p,q}(𝕋ᵈ)` is the coefficient
sequence of a continuous function on the torus. -/
theorem MemBesov.exists_mFourierCoeff_eq {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] {c : (d → ℤ) → ℂ}
    (hs : Fintype.card d * p.toReal⁻¹ < s) (hc : MemBesov φ s p q c) :
    ∃ f : C(UnitAddTorus d, ℂ), mFourierCoeff f = c := by
  -- The Bernstein embedding `B^s_{p,q}(𝕋ᵈ) ⊆ B^{s - d/p}_{∞,q}(𝕋ᵈ)` reduces to `p = ∞`.
  have h := hc.mono_exponent (r := ∞) le_top
  rw [ENNReal.toReal_top, inv_zero, sub_zero] at h
  exact h.exists_mFourierCoeff_eq_of_top (sub_pos.2 hs)

end TauCeti.UnitAddTorus
