/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus
public import TauCeti.Analysis.Holder.Zygmund
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Torus.Transference
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Torus.Continuous

/-!
# The periodic Hölder–Zygmund spaces of non-integer order are the Hölder spaces

Let `φ` be a smooth bump function on `EuclideanSpace ℝ d` and let `𝒞^s(𝕋ᵈ) = B^s_{∞,∞}(𝕋ᵈ)` be the
periodic Hölder–Zygmund space built from it (`TauCeti.UnitAddTorus.MemBesov`), a space of formal
Fourier series `c : ℤᵈ → ℂ`. A function on the torus `𝕋ᵈ = UnitAddTorus d` is read through its
lift `x ↦ f (x mod ℤᵈ)` to `EuclideanSpace ℝ d`, the `ℤᵈ`-periodic function whose derivatives and
Hölder seminorms are those of `f`. This file proves that, for `k : ℕ` and `0 < α < 1`,

`𝒞^{k+α}(𝕋ᵈ) = C^{k,α}(𝕋ᵈ)` with equivalent norms:

`c ∈ 𝒞^{k+α}(𝕋ᵈ)` exactly when `c` is the coefficient sequence `f̂` of a continuous `f` on the torus
whose lift is `C^k` with `α`-Hölder `k`-th derivative
(`TauCeti.UnitAddTorus.memBesov_iff_exists_mFourierCoeff_eq_and_contDiff_and_holderWith`), and the
norm of `c` bounds the derivatives through order `k` and the Hölder constant of the lift, and
conversely (`exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith` and
`exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith`, in the namespace
`TauCeti.UnitAddTorus`). This is the periodic
form of the identification `𝒞^{k+α}(ℝᵈ) = C_b^{k,α}(ℝᵈ)` of
`TauCeti.Analysis.Holder.Zygmund`.

## The argument

The identification is transferred from `ℝᵈ` rather than proved again. By the transference of
Schwartz multipliers (`TauCeti.Analysis.Fourier.Torus.Transference`), for the symbols `ψⱼ` of the
Littlewood–Paley partition the Euclidean blocks `Δⱼ F` of the lift `F` of a continuous function
`f` on the torus are the lifts of the periodic blocks `Δⱼ f̂`, which have the same supremum norm.
Hence `f̂ ∈ B^s_{∞,q}(𝕋ᵈ)` exactly when `F ∈ B^s_{∞,q}(ℝᵈ)`
(`TauCeti.UnitAddTorus.memBesov_mFourierCoeff_iff`), and the `B^s_{∞,∞}` norms are equal
(`TauCeti.UnitAddTorus.norm_eq_norm_of_coeff_eq_mFourierCoeff`). Every element of `𝒞^s(𝕋ᵈ)`,
`s > 0`, is the coefficient sequence of a continuous function
(`TauCeti.UnitAddTorus.MemBesov.exists_mFourierCoeff_eq`), so the Euclidean identification
applies to its lift.

## Main declarations

* `TauCeti.UnitAddTorus.memBesov_mFourierCoeff_iff` and
  `TauCeti.UnitAddTorus.norm_eq_norm_of_coeff_eq_mFourierCoeff`: a continuous function lies in
  `B^s_{∞,q}(𝕋ᵈ)` exactly when its lift lies in `B^s_{∞,q}(ℝᵈ)`, and for `q = ∞` the two norms
  are equal.
* `exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith`, in the
  namespace `TauCeti.UnitAddTorus`: `𝒞^{k+α}(𝕋ᵈ) ⊆ C^{k,α}(𝕋ᵈ)`, for `0 < α < 1`, with a norm
  bound.
* `TauCeti.UnitAddTorus.exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith`:
  `C^{k,α}(𝕋ᵈ) ⊆ 𝒞^{k+α}(𝕋ᵈ)`, for `α ≥ 0`, with a norm bound.
* `TauCeti.UnitAddTorus.memBesov_iff_exists_mFourierCoeff_eq_and_contDiff_and_holderWith`: the
  identification `𝒞^{k+α}(𝕋ᵈ) = C^{k,α}(𝕋ᵈ)`, `0 < α < 1`.

## References

* H.-J. Schmeisser and H. Triebel, *Topics in Fourier Analysis and Function Spaces*, Wiley, 1987,
  Chapter 3 (the periodic Besov spaces and the periodic Hölder–Zygmund spaces).
* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Grundlehren der mathematischen Wissenschaften 343, Springer, 2011, Section 2.7.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap BoundedContinuousFunction

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d]

-- The periodic Besov spaces live on `Lᵖ` for the product of the Haar probability measures on the
-- circle factors, given by this instance; use it here as well.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance instIsProbabilityMeasureVolumeUnitAddCircleHolder :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

variable (φ : ContDiffBump (0 : EuclideanSpace ℝ d))

/-! ### Periodic and Euclidean Besov spaces of a continuous function -/

open TemperedDistribution in
/-- The Euclidean blocks of the lift of `f` are the lifts of the periodic blocks of `f`. -/
private theorem littlewoodPaleyBlock_toLpTop_eq (f : C(UnitAddTorus d, ℂ))
    {F : EuclideanSpace ℝ d →ᵇ ℂ} (hF : ∀ x, F x = f (fun i ↦ (x i : UnitAddCircle))) (j : ℕ) :
    TemperedDistribution.littlewoodPaleyBlock ℂ φ j
        (BoundedContinuousFunction.toLpTop volume ℂ F : 𝓢'(EuclideanSpace ℝ d, ℂ)) =
      (BoundedContinuousFunction.toLpTop volume ℂ
        (euclideanLift (littlewoodPaleyBlockContinuousMap φ j (mFourierCoeff f))) :
          𝓢'(EuclideanSpace ℝ d, ℂ)) := by
  rw [littlewoodPaleyBlock_apply, ← φ.coe_inhomogeneousLittlewoodPaleySchwartz]
  refine fourierMultiplierCLM_toLpTop_eq_toLpTop _ f hF fun x ↦ ?_
  simp only [euclideanLift_apply, coe_littlewoodPaleyBlockContinuousMap,
    φ.coe_inhomogeneousLittlewoodPaleySchwartz]

private theorem norm_toLpTop_euclideanLift_block (j : ℕ) (c : (d → ℤ) → ℂ) :
    ‖BoundedContinuousFunction.toLpTop volume ℂ
      (euclideanLift (littlewoodPaleyBlockContinuousMap φ j c))‖ =
        ‖littlewoodPaleyBlockLp φ ∞ j c‖ := by
  rw [BoundedContinuousFunction.norm_toLpTop, norm_euclideanLift, norm_littlewoodPaleyBlockLp_top]

/-- **Periodic and Euclidean Besov spaces of a continuous function agree.** Let `F` be the lift
to `EuclideanSpace ℝ d` of a continuous function `f` on the torus. The Fourier coefficients of `f`
lie in the periodic Besov space `B^s_{∞,q}(𝕋ᵈ)` exactly when `F` lies in `B^s_{∞,q}(ℝᵈ)`. -/
theorem memBesov_mFourierCoeff_iff (f : C(UnitAddTorus d, ℂ)) {F : EuclideanSpace ℝ d →ᵇ ℂ}
    (hF : ∀ x, F x = f (fun i ↦ (x i : UnitAddCircle))) {s : ℝ} {q : ℝ≥0∞} :
    MemBesov φ s ∞ q (mFourierCoeff f) ↔
      (BoundedContinuousFunction.toLpTop volume ℂ F : 𝓢'(EuclideanSpace ℝ d, ℂ)).MemBesov
        φ s ∞ q := by
  rw [memBesov_def, TemperedDistribution.memBesov_iff]
  constructor
  · refine fun h ↦ ⟨fun j ↦ BoundedContinuousFunction.toLpTop volume ℂ
      (euclideanLift (littlewoodPaleyBlockContinuousMap φ j (mFourierCoeff f))),
        littlewoodPaleyBlock_toLpTop_eq φ f hF, ?_⟩
    simpa only [norm_toLpTop_euclideanLift_block] using h
  · rintro ⟨g, hg, hmem⟩
    have hgj (j : ℕ) : g j = BoundedContinuousFunction.toLpTop volume ℂ
        (euclideanLift (littlewoodPaleyBlockContinuousMap φ j (mFourierCoeff f))) :=
      Lp.toTemperedDistribution_injective ((hg j).symm.trans
        (littlewoodPaleyBlock_toLpTop_eq φ f hF j))
    simpa only [hgj, norm_toLpTop_euclideanLift_block] using hmem

/-- **The norms agree.** If `u ∈ 𝒞^s(𝕋ᵈ)` has the Fourier coefficients of a continuous function
`f` on the torus and `w ∈ 𝒞^s(ℝᵈ)` is the lift of `f`, then `‖u‖ = ‖w‖`. -/
theorem norm_eq_norm_of_coeff_eq_mFourierCoeff {f : C(UnitAddTorus d, ℂ)}
    {F : EuclideanSpace ℝ d →ᵇ ℂ} (hF : ∀ x, F x = f (fun i ↦ (x i : UnitAddCircle))) {s : ℝ}
    {u : BesovSpace φ s ∞ ∞} {w : TauCeti.BesovSpace ℂ φ s ∞ ∞}
    (hu : u.coeff = mFourierCoeff f)
    (hw : w.toDistr = BoundedContinuousFunction.toLpTop volume ℂ F) : ‖u‖ = ‖w‖ := by
  rw [BesovSpace.norm_eq_ciSup, TauCeti.BesovSpace.norm_eq_ciSup]
  congr 1 with j
  have hj : w.block j = BoundedContinuousFunction.toLpTop volume ℂ
      (euclideanLift (littlewoodPaleyBlockContinuousMap φ j (mFourierCoeff f))) :=
    Lp.toTemperedDistribution_injective (by
      beta_reduce
      rw [TauCeti.BesovSpace.coe_block, hw, littlewoodPaleyBlock_toLpTop_eq φ f hF])
  rw [hj, norm_toLpTop_euclideanLift_block, hu]

/-! ### The identification `𝒞^{k+α}(𝕋ᵈ) = C^{k,α}(𝕋ᵈ)` -/

/-- **Periodic Hölder–Zygmund classes of non-integer order are `C^{k,α}` functions.** Let `k : ℕ`
and `0 < α < 1`. There is `C` such that every `u ∈ 𝒞^{k+α}(𝕋ᵈ) = B^{k+α}_{∞,∞}(𝕋ᵈ)` is the
coefficient sequence of a continuous function `f` on the torus whose lift
`x ↦ f (x mod ℤᵈ)` to `EuclideanSpace ℝ d` is `C^k`, with derivatives through order `k` bounded
by `C ‖u‖` and `α`-Hölder `k`-th derivative with constant `C ‖u‖`. -/
theorem exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith (k : ℕ)
    {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ≥0, ∀ u : BesovSpace φ (k + α) ∞ ∞, ∃ f : C(UnitAddTorus d, ℂ),
      mFourierCoeff f = u.coeff ∧
      ContDiff ℝ k (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) ∧
      (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i
        (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ C * ‖u‖) ∧
      HolderWith (C * ‖u‖₊) α
        (iteratedFDeriv ℝ k fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) := by
  obtain ⟨C, hC⟩ :=
    TauCeti.BesovSpace.exists_toLpTop_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith
      (F := ℂ) φ k hα0 hα1
  refine ⟨C, fun u ↦ ?_⟩
  obtain ⟨f, hf⟩ := u.memBesov_coeff.exists_mFourierCoeff_eq (by
    rw [ENNReal.toReal_top, inv_zero, mul_zero]
    exact add_pos_of_nonneg_of_pos k.cast_nonneg (by exact_mod_cast hα0))
  have hmem := (memBesov_mFourierCoeff_iff φ f (euclideanLift_apply f)).1 (hf ▸ u.memBesov_coeff)
  have hnorm : ‖u‖ = ‖hmem.toBesovSpace‖ := norm_eq_norm_of_coeff_eq_mFourierCoeff φ
    (euclideanLift_apply f) hf.symm hmem.toDistr_toBesovSpace
  obtain ⟨g, hg, hgk, hgb, hgH⟩ := hC hmem.toBesovSpace
  obtain rfl : g = euclideanLift f :=
    BoundedContinuousFunction.toTemperedDistribution_toLpTop_injective
      (hg.trans hmem.toDistr_toBesovSpace)
  have hnnorm : ‖u‖₊ = ‖hmem.toBesovSpace‖₊ := NNReal.eq (by rw [coe_nnNorm, coe_nnNorm, hnorm])
  rw [← hnorm] at hgb
  rw [← hnnorm] at hgH
  rw [coe_euclideanLift] at hgk hgb hgH
  exact ⟨f, hf, hgk, hgb, hgH⟩

/-- **`C^{k,α}` functions on the torus are periodic Hölder–Zygmund classes.** Let `k : ℕ` and
`α ≥ 0`. There is `C` such that if the lift `x ↦ f (x mod ℤᵈ)` of a continuous function `f` on the
torus is `C^k`, with derivatives through order `k` bounded by `M` and `α`-Hölder `k`-th derivative
with constant `H`, then the Fourier coefficients of `f` form an element of
`𝒞^{k+α}(𝕋ᵈ) = B^{k+α}_{∞,∞}(𝕋ᵈ)` of norm at most `C (M + H)`. -/
theorem exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith (k : ℕ) (α : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : C(UnitAddTorus d, ℂ),
      ContDiff ℝ k (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) →
      ∀ {M : ℝ} {H : ℝ≥0}, (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i
        (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ M) →
      HolderWith H α
        (iteratedFDeriv ℝ k fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) →
      ∃ u : BesovSpace φ (k + α) ∞ ∞, u.coeff = mFourierCoeff f ∧ ‖u‖ ≤ C * (M + H) := by
  obtain ⟨C, hC0, hC⟩ :=
    TauCeti.BesovSpace.exists_toDistr_eq_and_norm_le_of_contDiff_of_holderWith (F := ℂ) φ k α
  refine ⟨C, hC0, fun f hf M H hM hH ↦ ?_⟩
  obtain ⟨w, hw, hwn⟩ := hC (euclideanLift f) (by rwa [coe_euclideanLift])
    (by rwa [coe_euclideanLift]) (by rwa [coe_euclideanLift])
  have hmem := (memBesov_mFourierCoeff_iff φ f (euclideanLift_apply f)).2 (hw ▸ w.memBesov_toDistr)
  exact ⟨⟨_, hmem⟩, rfl,
    (norm_eq_norm_of_coeff_eq_mFourierCoeff φ (euclideanLift_apply f) rfl hw).trans_le hwn⟩

/-- **`𝒞^{k+α}(𝕋ᵈ)` is the space of `C^{k,α}` functions on the torus.** For `k : ℕ` and
`0 < α < 1`, a formal Fourier series `c` lies in the periodic Hölder–Zygmund space
`𝒞^{k+α}(𝕋ᵈ) = B^{k+α}_{∞,∞}(𝕋ᵈ)` exactly when it is the coefficient sequence of a continuous
function `f` on the torus whose lift `x ↦ f (x mod ℤᵈ)` to `EuclideanSpace ℝ d` is `C^k` with
`α`-Hölder `k`-th derivative. The two quantitative inclusions, which make the norms equivalent,
are `exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith` and
`exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith`. -/
theorem memBesov_iff_exists_mFourierCoeff_eq_and_contDiff_and_holderWith (k : ℕ) {α : ℝ≥0}
    (hα0 : 0 < α) (hα1 : α < 1) {c : (d → ℤ) → ℂ} :
    MemBesov φ (k + α) ∞ ∞ c ↔ ∃ f : C(UnitAddTorus d, ℂ), mFourierCoeff f = c ∧
      ContDiff ℝ k (fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) ∧
      ∃ H : ℝ≥0, HolderWith H α
        (iteratedFDeriv ℝ k fun x : EuclideanSpace ℝ d ↦ f fun i ↦ (x i : UnitAddCircle)) := by
  constructor
  · intro hc
    obtain ⟨C, hC⟩ :=
      exists_mFourierCoeff_eq_and_contDiff_and_norm_iteratedFDeriv_le_and_holderWith φ k hα0 hα1
    obtain ⟨f, hf, hfk, -, hfH⟩ := hC ⟨c, hc⟩
    exact ⟨f, hf, hfk, _, hfH⟩
  · rintro ⟨f, rfl, hf, H, hH⟩
    obtain ⟨M, hM⟩ := exists_forall_norm_iteratedFDeriv_euclidean_le f hf
    obtain ⟨C, -, hC⟩ := exists_coeff_eq_and_norm_le_of_contDiff_of_holderWith φ k α
    obtain ⟨u, hu, -⟩ := hC f hf hM hH
    exact hu ▸ u.memBesov_coeff

end TauCeti.UnitAddTorus
