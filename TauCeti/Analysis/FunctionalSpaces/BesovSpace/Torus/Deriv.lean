/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
import TauCeti.Analysis.Fourier.Torus.Bernstein
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Partial derivatives on periodic Besov spaces

On the torus `𝕋ᵈ = UnitAddTorus d` the `i`-th partial derivative acts on a formal Fourier series
`c : ℤᵈ → ℂ` by `(∂ᵢ c)(n) = 2πi nᵢ c(n)` (`TauCeti.UnitAddTorus.partialDeriv`). This file shows
that one derivative is exactly one order on the periodic Besov scale `B^s_{p,q}(𝕋ᵈ)`
(`TauCeti.UnitAddTorus.BesovSpace`): for all `s ∈ ℝ` and `1 ≤ p ≤ ∞`,

`c ∈ B^{s+1}_{p,q}(𝕋ᵈ) ↔ ∂ᵢ c ∈ B^s_{p,q}(𝕋ᵈ)` for every `i`

(`TauCeti.UnitAddTorus.memBesov_add_one_iff`), with the norm estimates

`‖∂ᵢ u‖_{B^s_{p,q}} ≤ C ‖u‖_{B^{s+1}_{p,q}}` and
`‖u‖_{B^{s+1}_{p,q}} ≤ ‖Δ₀ u‖_p + C ∑ᵢ ‖∂ᵢ u‖_{B^s_{p,q}}`,

where `C` depends only on the bump function `φ` and on `d`, not on `s`, `p` or `q`
(`TauCeti.UnitAddTorus.BesovSpace.exists_norm_partialDerivCLM_le` and
`TauCeti.UnitAddTorus.BesovSpace.exists_norm_le_norm_littlewoodPaleyBlockLp_zero_add_mul_sum`).
No integrability of `c` itself is needed in the converse direction: the low-frequency block
`Δ₀ c` is a trigonometric polynomial.

Both directions are blockwise. The block `Δⱼ c` is a trigonometric polynomial with frequencies of
size at most of order `2^j`, so Bernstein's inequality
(`TauCeti.UnitAddTorus.exists_eLpNorm_le_of_mFourierCoeff_eq_prod_smul`) gives
`‖Δⱼ ∂ᵢ c‖_p ≤ C 2^j ‖Δⱼ c‖_p`. For `j ≥ 1` the frequencies of `Δⱼ c` lie in the annulus
`2^{j-1} φ.rIn ≤ ‖n‖ ≤ 2^j φ.rOut`, where the reverse Bernstein inequality
(`TauCeti.UnitAddTorus.exists_eLpNorm_le_div_mul_sum_eLpNorm_of_mFourierCoeff_eq`) gives
`2^j ‖Δⱼ c‖_p ≤ C ∑ᵢ ‖Δⱼ ∂ᵢ c‖_p`. The argument is the periodic counterpart of the whole-space
lifting `TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_lineDerivOp_eq`
(`TauCeti/Analysis/FunctionalSpaces/BesovSpace/LineDeriv.lean`), with the same annulus ratio
`2 φ.rOut / φ.rIn`.

## Main declarations

* `TauCeti.UnitAddTorus.partialDeriv`: the partial derivative of a formal Fourier series.
* `TauCeti.UnitAddTorus.exists_norm_littlewoodPaleyBlockLp_partialDeriv_le` and
  `TauCeti.UnitAddTorus.exists_pow_mul_norm_littlewoodPaleyBlockLp_succ_le_mul_sum`: the two
  Bernstein inequalities for the periodic blocks.
* `TauCeti.UnitAddTorus.MemBesov.partialDeriv` and `TauCeti.UnitAddTorus.memBesov_add_one_iff`:
  membership in `B^{s+1}_{p,q}(𝕋ᵈ)` through the partial derivatives.
* `TauCeti.UnitAddTorus.BesovSpace.partialDerivCLM`: the partial derivative as a continuous linear
  map `B^{s+1}_{p,q}(𝕋ᵈ) → B^s_{p,q}(𝕋ᵈ)`.

## References

* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (periodic Besov spaces and the lifting property).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Lemma 2.1
  (Bernstein's inequalities).
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*}

-- The periodic Besov spaces live on `Lᵖ` for the product of the Haar probability measures on the
-- circle factors; use the same measure here.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

/-! ### The partial derivatives of a formal Fourier series -/

/-- The `i`-th **partial derivative** of a formal Fourier series `c : ℤᵈ → ℂ`, with coefficients
`(∂ᵢ c)(n) = 2πi nᵢ c(n)`. When `c` is the coefficient sequence of a function whose lift to `ℝᵈ`
is `C¹`, these are the coefficients of its `i`-th partial derivative
(`TauCeti.UnitAddTorus.mFourierCoeff_eq_prod_smul_of_iteratedFDeriv`). -/
def partialDeriv (i : d) : ((d → ℤ) → ℂ) →ₗ[ℂ] (d → ℤ) → ℂ where
  toFun c n := 2 * Real.pi * Complex.I * n i * c n
  map_add' c c' := by
    funext n
    simp only [Pi.add_apply, mul_add]
  map_smul' a c := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem partialDeriv_apply (i : d) (c : (d → ℤ) → ℂ) (n : d → ℤ) :
    partialDeriv i c n = 2 * Real.pi * Complex.I * n i * c n :=
  (rfl)

variable [Fintype d] {φ : ContDiffBump (0 : EuclideanSpace ℝ d)}

/-- The Fourier coefficients of the block `Δⱼ ∂ᵢ c` are those of `Δⱼ c` multiplied by `2πi nᵢ`:
the blocks commute with the partial derivatives. -/
theorem mFourierCoeff_littlewoodPaleyBlockLp_partialDeriv {p : ℝ≥0∞} [Fact (1 ≤ p)] (i : d)
    (j : ℕ) (c : (d → ℤ) → ℂ) (n : d → ℤ) :
    mFourierCoeff (littlewoodPaleyBlockLp φ p j (partialDeriv i c)) n =
      (2 * Real.pi * Complex.I * n i) • mFourierCoeff (littlewoodPaleyBlockLp φ p j c) n := by
  simp only [mFourierCoeff_littlewoodPaleyBlockLp, partialDeriv_apply, smul_eq_mul]
  ring

/-! ### Bernstein's inequalities for the blocks -/

/-- The blocks are integrable for the global volume on the torus, built from Mathlib's
`AddCircle.measureSpace`, the measure for which the Bernstein inequalities are stated:
`volume_eq_pi_haarAddCircle` identifies it with the product of the Haar probability measures,
which is by definition the file-local `volume`. -/
private theorem integrable_littlewoodPaleyBlockLp {p : ℝ≥0∞} [Fact (1 ≤ p)] (j : ℕ)
    (c : (d → ℤ) → ℂ) :
    letI : MeasureSpace UnitAddCircle := AddCircle.measureSpace 1
    Integrable (littlewoodPaleyBlockLp φ p j c : UnitAddTorus d → ℂ) := by
  have : IsFiniteMeasure (volume : Measure (UnitAddTorus d)) :=
    inferInstanceAs (IsFiniteMeasure (Measure.pi fun _ ↦ AddCircle.haarAddCircle))
  rw [volume_eq_pi_haarAddCircle]
  exact (Lp.memLp _).integrable Fact.out

variable (φ) in
/-- **Bernstein's inequality for the periodic blocks.** There is `C ≥ 0`, depending only on `d` and
`φ`, such that for every `1 ≤ p ≤ ∞`, every `i`, every `j` and every formal Fourier series `c`,
`‖Δⱼ ∂ᵢ c‖_p ≤ C 2^j ‖Δⱼ c‖_p`. -/
theorem exists_norm_littlewoodPaleyBlockLp_partialDeriv_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : d) (j : ℕ) (c : (d → ℤ) → ℂ),
      ‖littlewoodPaleyBlockLp φ p j (partialDeriv i c)‖ ≤
        C * 2 ^ j * ‖littlewoodPaleyBlockLp φ p j c‖ := by
  classical
  obtain ⟨C₀, -, hB⟩ := exists_eLpNorm_le_of_mFourierCoeff_eq_prod_smul (d := d)
  set M : ℝ := max 1 φ.rOut
  have hM : 1 ≤ M := le_max_left _ _
  refine ⟨C₀ ^ 2 * M, by positivity, fun p _ i j c ↦ ?_⟩
  set f := littlewoodPaleyBlockLp φ p j c
  set g := littlewoodPaleyBlockLp φ p j (partialDeriv i c)
  -- Bernstein's inequality at the radius `2^j M ≥ 1`, beyond which `f̂` vanishes, for the
  -- derivative along the `i`-th coordinate vector.
  have hR : 1 ≤ 2 ^ j * M := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hM
  have h := hB (p := p) (q := p) Fact.out le_rfl 1 (fun _ ↦ Pi.single i 1) hR
    (f := (f : UnitAddTorus d → ℂ)) (g := (g : UnitAddTorus d → ℂ))
    (integrable_littlewoodPaleyBlockLp j c) (integrable_littlewoodPaleyBlockLp j _)
    (fun n hn ↦ by
      rw [mFourierCoeff_littlewoodPaleyBlockLp,
        inhomogeneousLittlewoodPaley_latticePoint_eq_zero hn, Complex.ofReal_zero, zero_mul])
    fun n ↦ by
      rw [mFourierCoeff_littlewoodPaleyBlockLp_partialDeriv, Fin.prod_univ_one]
      congr 1
      rw [Finset.sum_eq_single i (fun x _ hx ↦ by simp [hx]) (by simp)]
      simp
  rw [volume_eq_pi_haarAddCircle] at h
  have hv : ‖(Pi.single i 1 : d → ℝ)‖ = 1 := by simp [Pi.norm_single]
  -- The specialised bound, stated for the product of the Haar measures (the file-local `volume`).
  have h' : eLpNorm g p (Measure.pi fun _ ↦ AddCircle.haarAddCircle) ≤
      ENNReal.ofReal (C₀ ^ 2 * (2 ^ j * M)) *
        eLpNorm f p (Measure.pi fun _ ↦ AddCircle.haarAddCircle) := by
    simpa [hv] using h
  rw [Lp.norm_def, Lp.norm_def]
  calc (eLpNorm g p volume).toReal
      ≤ (ENNReal.ofReal (C₀ ^ 2 * (2 ^ j * M)) * eLpNorm f p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) h'
    _ = C₀ ^ 2 * M * 2 ^ j * (eLpNorm f p volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
        ring

variable (φ) in
/-- **The reverse Bernstein inequality for the periodic blocks.** There is `C ≥ 0`, depending only
on `d` and `φ`, such that for every `1 ≤ p ≤ ∞`, every `j` and every formal Fourier series `c`,
`2^j ‖Δ_{j+1} c‖_p ≤ C ∑ᵢ ‖Δ_{j+1} ∂ᵢ c‖_p`. The frequencies of `Δ_{j+1} c` lie in the annulus
`2^j φ.rIn ≤ ‖n‖ ≤ 2^{j+1} φ.rOut`. -/
theorem exists_pow_mul_norm_littlewoodPaleyBlockLp_succ_le_mul_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) (c : (d → ℤ) → ℂ),
      2 ^ j * ‖littlewoodPaleyBlockLp φ p (j + 1) c‖ ≤
        C * ∑ i, ‖littlewoodPaleyBlockLp φ p (j + 1) (partialDeriv i c)‖ := by
  obtain ⟨C₀, hC₀, hrev⟩ :=
    exists_eLpNorm_le_div_mul_sum_eLpNorm_of_mFourierCoeff_eq (d := d) (2 * φ.rOut / φ.rIn)
  have hrIn := φ.rIn_pos
  refine ⟨C₀ / φ.rIn, by positivity, fun p _ j c ↦ ?_⟩
  set f := littlewoodPaleyBlockLp φ p (j + 1) c
  set g : d → Lp ℂ p (volume : Measure (UnitAddTorus d)) := fun i ↦
    littlewoodPaleyBlockLp φ p (j + 1) (partialDeriv i c)
  have hR : (0 : ℝ) < 2 ^ j * φ.rIn := by positivity
  have hθR : 2 * φ.rOut / φ.rIn * (2 ^ j * φ.rIn) = 2 ^ (j + 1) * φ.rOut := by
    field_simp
    ring
  have h := hrev (p := p) Fact.out hR (f := (f : UnitAddTorus d → ℂ))
    (g := fun i ↦ (g i : UnitAddTorus d → ℂ))
    (integrable_littlewoodPaleyBlockLp _ c) (fun i ↦ integrable_littlewoodPaleyBlockLp _ _)
    (fun n hn ↦ by
      rw [hθR] at hn
      rw [mFourierCoeff_littlewoodPaleyBlockLp]
      rcases hn with hn | hn <;>
        simp [φ.inhomogeneousLittlewoodPaley_succ_eq_zero_of_norm_le,
          φ.inhomogeneousLittlewoodPaley_eq_zero_of_le_norm, hn.le])
    fun i n ↦ mFourierCoeff_littlewoodPaleyBlockLp_partialDeriv i (j + 1) c n
  rw [volume_eq_pi_haarAddCircle] at h
  have hfin (i : d) : eLpNorm (g i) p volume ≠ ∞ := Lp.eLpNorm_ne_top _
  have hle : ‖f‖ ≤ C₀ / (2 ^ j * φ.rIn) * ∑ i, ‖g i‖ := by
    rw [Lp.norm_def]
    calc (eLpNorm f p volume).toReal
        ≤ (ENNReal.ofReal (C₀ / (2 ^ j * φ.rIn)) * ∑ i, eLpNorm (g i) p volume).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.sum_ne_top.2 fun i _ ↦ hfin i)) h
      _ = _ := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_sum fun i _ ↦ hfin i]
          simp only [Lp.norm_def]
  calc 2 ^ j * ‖f‖ ≤ 2 ^ j * (C₀ / (2 ^ j * φ.rIn) * ∑ i, ‖g i‖) := by gcongr
    _ = C₀ / φ.rIn * ∑ i, ‖g i‖ := by
        field_simp

/-! ### Membership in the periodic Besov spaces -/

section MemBesov

variable {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

variable (φ) in
/-- The weighted form of `exists_norm_littlewoodPaleyBlockLp_partialDeriv_le`: the weight
`2^{j(s+1)}` controls the weighted blocks of order `s` of every partial derivative. -/
private theorem exists_rpow_mul_norm_littlewoodPaleyBlockLp_partialDeriv_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : d) (j : ℕ) (c : (d → ℤ) → ℂ),
      2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j (partialDeriv i c)‖ ≤
        C * (2 ^ ((s + 1) * j) * ‖littlewoodPaleyBlockLp φ p j c‖) := by
  obtain ⟨C, hC, h⟩ := exists_norm_littlewoodPaleyBlockLp_partialDeriv_le φ
  refine ⟨C, hC, fun s p _ i j c ↦ ?_⟩
  have h2 : (2 : ℝ) ^ ((s + 1) * j) = 2 ^ (s * j) * 2 ^ j := by
    rw [add_mul, one_mul, Real.rpow_add two_pos, Real.rpow_natCast]
  calc 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j (partialDeriv i c)‖
      ≤ 2 ^ (s * j) * (C * 2 ^ j * ‖littlewoodPaleyBlockLp φ p j c‖) := by
        gcongr
        exact h p i j c
    _ = _ := by rw [h2]; ring

variable (φ) in
/-- The weighted form of `exists_pow_mul_norm_littlewoodPaleyBlockLp_succ_le_mul_sum`, for every
index `j`: the weighted block of order `s + 1` is bounded by the low-frequency block `Δ₀ c` when
`j = 0`, and by the weighted blocks of order `s` of the partial derivatives otherwise. -/
private theorem exists_rpow_mul_norm_littlewoodPaleyBlockLp_le_ite_add_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) (c : (d → ℤ) → ℂ),
      2 ^ ((s + 1) * j) * ‖littlewoodPaleyBlockLp φ p j c‖ ≤
        (if j = 0 then ‖littlewoodPaleyBlockLp φ p 0 c‖ else 0) +
          C * ∑ i, 2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j (partialDeriv i c)‖ := by
  obtain ⟨C, hC, h⟩ := exists_pow_mul_norm_littlewoodPaleyBlockLp_succ_le_mul_sum φ
  refine ⟨2 * C, by positivity, fun s p _ j c ↦ ?_⟩
  rcases j with _ | j
  · simp only [↓reduceIte, CharP.cast_eq_zero, mul_zero, Real.rpow_zero, one_mul]
    exact le_add_of_nonneg_right (by positivity)
  simp only [Nat.add_one_ne_zero, ↓reduceIte, zero_add]
  have h2 : (2 : ℝ) ^ ((s + 1) * ((j + 1 : ℕ) : ℝ)) =
      2 ^ (s * ((j + 1 : ℕ) : ℝ)) * (2 * 2 ^ j) := by
    rw [add_mul, one_mul, Real.rpow_add two_pos, Real.rpow_natCast, pow_succ, mul_comm 2]
  calc 2 ^ ((s + 1) * ((j + 1 : ℕ) : ℝ)) * ‖littlewoodPaleyBlockLp φ p (j + 1) c‖
      = 2 * 2 ^ (s * ((j + 1 : ℕ) : ℝ)) * (2 ^ j * ‖littlewoodPaleyBlockLp φ p (j + 1) c‖) := by
        rw [h2]
        ring
    _ ≤ 2 * 2 ^ (s * ((j + 1 : ℕ) : ℝ)) *
          (C * ∑ i, ‖littlewoodPaleyBlockLp φ p (j + 1) (partialDeriv i c)‖) :=
        mul_le_mul_of_nonneg_left (h p j c) (by positivity)
    _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **One derivative costs one order.** If `c ∈ B^{s+1}_{p,q}(𝕋ᵈ)`, then every partial derivative
`∂ᵢ c` lies in `B^s_{p,q}(𝕋ᵈ)`. -/
theorem MemBesov.partialDeriv {c : (d → ℤ) → ℂ} (hc : MemBesov φ (s + 1) p q c) (i : d) :
    MemBesov φ s p q (partialDeriv i c) := by
  obtain ⟨C, -, h⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_partialDeriv_le φ
  refine memBesov_def.2 (((memBesov_def.1 hc).const_mul C).mono fun j ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact h s p i j c

/-- **Besov regularity from the partial derivatives.** A formal Fourier series lies in
`B^{s+1}_{p,q}(𝕋ᵈ)` exactly when all its partial derivatives lie in `B^s_{p,q}(𝕋ᵈ)`. -/
theorem memBesov_add_one_iff {c : (d → ℤ) → ℂ} :
    MemBesov φ (s + 1) p q c ↔ ∀ i, MemBesov φ s p q (partialDeriv i c) := by
  refine ⟨fun hc i ↦ hc.partialDeriv i, fun hc ↦ ?_⟩
  obtain ⟨C, -, h⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_le_ite_add_sum φ
  -- The majorant: the low-frequency block at `j = 0`, and the reverse Bernstein bound beyond.
  set b : ℕ → ℝ := fun j ↦ if j = 0 then ‖littlewoodPaleyBlockLp φ p 0 c‖ else 0
  have hb : Memℓp b q :=
    (memℓp_zero ((Set.finite_singleton 0).subset fun j hj ↦ by
      by_contra h0
      rw [Set.mem_singleton_iff] at h0
      exact hj (by simp [b, h0]))).of_exponent_ge bot_le
  -- A finite sum of `ℓ^q` sequences is an `ℓ^q` sequence, since `ℓ^q` is an additive subgroup.
  have hsum : Memℓp (∑ i, fun j : ℕ ↦
      2 ^ (s * j) * ‖littlewoodPaleyBlockLp φ p j (partialDeriv i c)‖) q :=
    AddSubgroup.sum_mem (lp (fun _ : ℕ ↦ ℝ) q) fun i _ ↦ memBesov_def.1 (hc i)
  refine memBesov_def.2 ((hb.add (hsum.const_mul C)).mono fun j ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  simpa only [b, Pi.add_apply, Finset.sum_apply] using h s p j c

end MemBesov

/-! ### The partial derivatives as bounded operators -/

namespace BesovSpace

variable {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable (φ s p q) in
/-- The `i`-th partial derivative `∂ᵢ : B^{s+1}_{p,q}(𝕋ᵈ) → B^s_{p,q}(𝕋ᵈ)`, a continuous linear
map whose norm is bounded uniformly in `s`, `p` and `q`
(`TauCeti.UnitAddTorus.BesovSpace.exists_norm_partialDerivCLM_le`). -/
def partialDerivCLM (i : d) : BesovSpace φ (s + 1) p q →L[ℂ] BesovSpace φ s p q :=
  LinearMap.mkContinuousOfExistsBound
    { toFun u := ⟨UnitAddTorus.partialDeriv i u.coeff, u.memBesov_coeff.partialDeriv i⟩
      map_add' u v := ext (map_add _ u.coeff v.coeff)
      map_smul' a u := ext (map_smul _ a u.coeff) } <| by
    obtain ⟨C, hC, h⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_partialDeriv_le φ
    exact ⟨C, fun u ↦ norm_le_mul_norm_of_forall_rpow_mul_norm_le hC fun j ↦ h s p i j u.coeff⟩

@[simp]
theorem coeff_partialDerivCLM (i : d) (u : BesovSpace φ (s + 1) p q) :
    (partialDerivCLM φ s p q i u).coeff = UnitAddTorus.partialDeriv i u.coeff :=
  (rfl)

variable (φ) in
/-- **The partial derivatives are bounded uniformly in `s`, `p` and `q`.** There is `C ≥ 0`,
depending only on `d` and `φ`, with `‖∂ᵢ u‖_{B^s_{p,q}} ≤ C ‖u‖_{B^{s+1}_{p,q}}`. -/
theorem exists_norm_partialDerivCLM_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (i : d)
      (u : BesovSpace φ (s + 1) p q), ‖partialDerivCLM φ s p q i u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, h⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_partialDeriv_le φ
  exact ⟨C, hC, fun {s p q} _ _ i u ↦
    norm_le_mul_norm_of_forall_rpow_mul_norm_le hC fun j ↦ h s p i j u.coeff⟩

variable (φ) in
/-- **The norm of `B^{s+1}_{p,q}(𝕋ᵈ)` through the partial derivatives.** There is `C ≥ 0`,
depending only on `d` and `φ`, with
`‖u‖_{B^{s+1}_{p,q}} ≤ ‖Δ₀ u‖_p + C ∑ᵢ ‖∂ᵢ u‖_{B^s_{p,q}}` for every `s`, `p`, `q` and `u`.
Together with `TauCeti.UnitAddTorus.BesovSpace.exists_norm_partialDerivCLM_le` and the bound
`‖Δ₀ u‖_p ≤ ‖u‖`, this is an equivalence of norms. -/
theorem exists_norm_le_norm_littlewoodPaleyBlockLp_zero_add_mul_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
      (u : BesovSpace φ (s + 1) p q),
      ‖u‖ ≤ ‖littlewoodPaleyBlockLp φ p 0 u.coeff‖ + C * ∑ i, ‖partialDerivCLM φ s p q i u‖ := by
  obtain ⟨C, hC, h⟩ := exists_rpow_mul_norm_littlewoodPaleyBlockLp_le_ite_add_sum φ
  refine ⟨C, hC, fun {s p q} _ _ u ↦ ?_⟩
  have hq : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  -- The majorant of the weighted blocks of `u`, as an element of `ℓ^q`.
  set e : lp (fun _ : ℕ ↦ ℝ) q := lp.single q 0 (1 : ℝ)
  set B : lp (fun _ : ℕ ↦ ℝ) q := ‖littlewoodPaleyBlockLp φ p 0 u.coeff‖ • e +
    C • ∑ i, lp.normSeq (partialDerivCLM φ s p q i u).weightedBlocks
  have he : ‖e‖ = 1 := by rw [lp.norm_single (zero_lt_one.trans_le Fact.out), norm_one]
  rw [← norm_weightedBlocks]
  calc ‖u.weightedBlocks‖ ≤ ‖B‖ := lp.norm_mono hq fun j ↦ ?_
    _ ≤ ‖‖littlewoodPaleyBlockLp φ p 0 u.coeff‖ • e‖ +
          ‖C • ∑ i, lp.normSeq (partialDerivCLM φ s p q i u).weightedBlocks‖ := norm_add_le _ _
    _ ≤ _ := by
        rw [norm_smul, norm_smul, he, mul_one, norm_norm, Real.norm_of_nonneg hC]
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
        rw [lp.norm_normSeq, norm_weightedBlocks]
  rw [norm_weightedBlocks_apply]
  refine le_trans ?_ (Real.le_norm_self _)
  simp only [B, e, lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sum, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, lp.single_apply, Pi.single_apply, lp.normSeq_apply,
    norm_weightedBlocks_apply, coeff_partialDerivCLM, mul_ite, mul_one, mul_zero]
  exact h s p j u.coeff

end BesovSpace

end TauCeti.UnitAddTorus
