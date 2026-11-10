/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.MihlinHormander
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous

/-!
# The Beurling operator on Lp

The Beurling symbol is `conj ξ / ξ`, assigned the value zero at the origin. It is smooth away
from zero, homogeneous of degree zero and bounded in modulus by one. The Fourier multiplier
`TauCeti.beurlingL2` therefore acts on L². The Mihlin–Hörmander theorem bounds it in each Lp norm
for `1 < p < ∞`, and extension from the dense Schwartz functions gives the continuous
complex-linear operator `TauCeti.beurlingLp` on all of Lp.

The extension is characterized by its action on Schwartz functions. The coefficient space may
be any complex Hilbert space. `TauCeti.Analysis.Complex.Wirtinger.Beurling.Cauchy` shows that on
smooth compactly supported functions the operator agrees almost everywhere with the Wirtinger
derivative of the Cauchy transform.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.2 (the Beurling transform and Cauchy–Riemann estimates).
* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter IV.
* t4v1/damian_formalizare, `MorseFloer/Part2/CauchyPompeiu.lean` and `CauchyHolder.lean`,
  revision `545ebb1a7d4c55299b1f59787a7ff0d4d703af27` (Cauchy/Beurling Hölder estimates).
  Its raw principal-value integral requires the factor `-π⁻¹` for the normalization here.
-/

public noncomputable section

open MeasureTheory FourierTransform Complex ComplexConjugate
open scoped ENNReal NNReal FourierTransform SchwartzMap Real ContDiff

namespace TauCeti

/-- The symbol of the planar Beurling transform, with value zero at the origin. -/
def beurlingSymbol (ξ : ℂ) : ℂ := conj ξ * ξ⁻¹

@[simp]
theorem beurlingSymbol_zero : beurlingSymbol 0 = 0 := by simp [beurlingSymbol]

/-- Multiplying the Beurling symbol by the frequency gives its conjugate, also at zero. -/
@[simp]
theorem beurlingSymbol_mul (ξ : ℂ) : beurlingSymbol ξ * ξ = conj ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · exact inv_mul_cancel_right₀ hξ _

/-- The symbol has modulus one at every nonzero frequency. -/
@[simp]
theorem norm_beurlingSymbol {ξ : ℂ} (hξ : ξ ≠ 0) : ‖beurlingSymbol ξ‖ = 1 := by
  rw [beurlingSymbol, norm_mul, norm_conj, norm_inv, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ)]

/-- The chosen value at zero also satisfies the global modulus bound. -/
theorem norm_beurlingSymbol_le (ξ : ℂ) : ‖beurlingSymbol ξ‖ ≤ 1 := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  · exact (norm_beurlingSymbol hξ).le

/-- Real dilation by a nonzero scalar leaves the symbol unchanged. -/
@[simp]
theorem beurlingSymbol_real_mul {t : ℝ} (ht : t ≠ 0) (ξ : ℂ) :
    beurlingSymbol ((t : ℂ) * ξ) = beurlingSymbol ξ := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [beurlingSymbol, beurlingSymbol, map_mul, conj_ofReal]
  field_simp

/-- The Beurling symbol is smooth away from its singular frequency. -/
theorem contDiffOn_beurlingSymbol : ContDiffOn ℝ ∞ beurlingSymbol {0}ᶜ :=
  fun _ hξ ↦ ContDiffAt.contDiffWithinAt <|
    Complex.conjCLE.contDiff.contDiffAt.mul ((contDiffAt_inv ℂ hξ).restrict_scalars ℝ)

/-- The symbol is in L-infinity for every measure on the complex plane. -/
theorem memLp_beurlingSymbol (μ : Measure ℂ) : MemLp beurlingSymbol ∞ μ :=
  memLp_top_of_bound (by unfold beurlingSymbol; fun_prop) 1 (.of_forall norm_beurlingSymbol_le)

/-- The bounded symbol as an L-infinity class for planar volume. -/
def beurlingSymbolLinf : Lp ℂ ∞ (volume : Measure ℂ) :=
  (memLp_beurlingSymbol volume).toLp beurlingSymbol

/-- A representative of the symbol class agrees with the explicit symbol almost everywhere. -/
theorem coeFn_beurlingSymbolLinf : beurlingSymbolLinf =ᵐ[volume] beurlingSymbol :=
  (memLp_beurlingSymbol volume).coeFn_toLp

/-- The essential-supremum norm of the Beurling symbol is at most one. -/
theorem norm_beurlingSymbolLinf_le : ‖beurlingSymbolLinf‖ ≤ 1 := by
  rw [beurlingSymbolLinf, Lp.norm_toLp]
  apply ENNReal.toReal_le_of_le_ofReal zero_le_one
  rw [eLpNorm_exponent_top (memLp_beurlingSymbol volume).aestronglyMeasurable]
  exact eLpNormEssSup_le_of_ae_bound (.of_forall norm_beurlingSymbol_le)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (F) in
/-- The Beurling Fourier multiplier on L² with complex Hilbert coefficients. -/
def beurlingL2 : Lp F 2 (volume : Measure ℂ) →L[ℂ] Lp F 2 (volume : Measure ℂ) :=
  Lp.fourierMultiplierCLM F beurlingSymbolLinf

variable (F) in
/-- The L² Beurling operator is the Fourier multiplier with the Beurling symbol. -/
theorem beurlingL2_def : beurlingL2 F = Lp.fourierMultiplierCLM F beurlingSymbolLinf :=
  (rfl)

/-- On the Fourier side the L² operator multiplies by the Beurling symbol. -/
@[simp]
theorem fourier_beurlingL2 (u : Lp F 2 (volume : Measure ℂ)) :
    𝓕 (beurlingL2 F u) = (beurlingSymbolLinf • 𝓕 u : Lp F 2 (volume : Measure ℂ)) :=
  Lp.fourier_fourierMultiplierCLM beurlingSymbolLinf u

/-- The Beurling operator on L² has norm at most one. -/
theorem norm_beurlingL2_le : ‖beurlingL2 F‖ ≤ 1 :=
  (Lp.norm_fourierMultiplierCLM_le _).trans norm_beurlingSymbolLinf_le

/-- The Mihlin–Hörmander bound for the Beurling multiplier, measured in any finite Lp norm with
`1 < p`. The input may be any L² function. -/
theorem exists_eLpNorm_beurlingL2_le {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ u : Lp F 2 (volume : Measure ℂ),
      eLpNorm (beurlingL2 F u) p volume ≤ C * eLpNorm u p volume := by
  obtain ⟨A, hA⟩ := exists_norm_iteratedFDeriv_le_div_pow_of_smul_eq (N := 2)
    (contDiffOn_beurlingSymbol.of_le (by simp)) fun t ht ξ ↦ by
      simpa only [Complex.real_smul] using beurlingSymbol_real_mul ht.ne' ξ
  obtain ⟨C, hC⟩ := exists_eLpNorm_fourierMultiplierCLM_le_of_norm_iteratedFDeriv_le
    (V := ℂ) (F := F) (N := 2) (by simp [Complex.finrank_real_complex]) hp hp_top
  exact ⟨C * A, fun u ↦ by
    simpa only [beurlingL2, ENNReal.coe_mul] using
      hC contDiffOn_beurlingSymbol hA beurlingSymbolLinf coeFn_beurlingSymbolLinf u⟩

/-- The L² realization preserves membership in every other Lp class with `1 < p < ∞`. -/
theorem memLp_beurlingL2 {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (u : Lp F 2 (volume : Measure ℂ)) (hu : MemLp u p volume) :
    MemLp (beurlingL2 F u) p volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_beurlingL2_le (F := F) hp hp_top
  exact (hC u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu.eLpNorm_lt_top)

private theorem memLp_beurlingL2_schwartz {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (u : 𝓢(ℂ, F)) : MemLp (beurlingL2 F (u.toLp 2 (volume : Measure ℂ))) p volume :=
  memLp_beurlingL2 hp hp_top _ ((u.memLp p).ae_eq (u.coeFn_toLp 2 volume).symm)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def beurlingSchwartzToLp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    𝓢(ℂ, F) →ₗ[ℂ] Lp F p (volume : Measure ℂ) where
  toFun u := (memLp_beurlingL2_schwartz hp hp_top u).toLp
    (beurlingL2 F (u.toLp 2 (volume : Measure ℂ)))
  map_add' u v := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    have h : (u + v).toLp 2 (volume : Measure ℂ) =
        u.toLp 2 (volume : Measure ℂ) + v.toLp 2 (volume : Measure ℂ) :=
      (SchwartzMap.toLpCLM ℂ F 2 (volume : Measure ℂ)).map_add u v
    rw [h, map_add]
    exact Lp.coeFn_add _ _
  map_smul' c u := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    have h : (c • u).toLp 2 (volume : Measure ℂ) = c • u.toLp 2 (volume : Measure ℂ) :=
      (SchwartzMap.toLpCLM ℂ F 2 (volume : Measure ℂ)).map_smul c u
    rw [h, map_smul]
    exact Lp.coeFn_smul c _

omit [Fact (1 ≤ p)] in
private theorem coeFn_beurlingSchwartzToLp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : 𝓢(ℂ, F)) :
    beurlingSchwartzToLp hp hp_top u =ᵐ[volume] beurlingL2 F (u.toLp 2 (volume : Measure ℂ)) :=
  (memLp_beurlingL2_schwartz hp hp_top u).coeFn_toLp

omit [Fact (1 ≤ p)] in
private theorem norm_beurlingSchwartzToLp_le_of_bound (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {C : ℝ≥0}
    (hC : ∀ u : Lp F 2 (volume : Measure ℂ),
      eLpNorm (beurlingL2 F u) p volume ≤ C * eLpNorm u p volume) (u : 𝓢(ℂ, F)) :
    ‖beurlingSchwartzToLp hp hp_top u‖ ≤ C * ‖u.toLp p (volume : Measure ℂ)‖ := by
  have h := hC (u.toLp 2 (volume : Measure ℂ))
  rw [eLpNorm_congr_ae (u.coeFn_toLp 2 volume)] at h
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (coeFn_beurlingSchwartzToLp hp hp_top u),
    eLpNorm_congr_ae (u.coeFn_toLp p volume)]
  exact (ENNReal.toReal_mono
    (ENNReal.mul_lt_top ENNReal.coe_lt_top (u.memLp p volume).eLpNorm_lt_top).ne h).trans_eq
      (by simp [ENNReal.toReal_mul])

omit [Fact (1 ≤ p)] in
private theorem norm_beurlingSchwartzToLp_le (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    ∃ C : ℝ≥0, ∀ u : 𝓢(ℂ, F),
      ‖beurlingSchwartzToLp hp hp_top u‖ ≤ C * ‖u.toLp p (volume : Measure ℂ)‖ := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_beurlingL2_le (F := F) hp hp_top
  exact ⟨C, norm_beurlingSchwartzToLp_le_of_bound hp hp_top hC⟩

/-- The Beurling operator on all of Lp, for `1 < p < ∞`, as the bounded extension from Schwartz
functions of the L² Fourier multiplier. -/
def beurlingLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) :
    Lp F p (volume : Measure ℂ) →L[ℂ] Lp F p (volume : Measure ℂ) :=
  (beurlingSchwartzToLp hp hp_top).extendOfNorm
    (SchwartzMap.toLpCLM ℂ F p (volume : Measure ℂ)).toLinearMap

/-- The bounded Lp operator agrees almost everywhere with the L² multiplier on every Schwartz
function. This fixes the extension uniquely. -/
theorem beurlingLp_toLp (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) (u : 𝓢(ℂ, F)) :
    beurlingLp p hp hp_top (u.toLp p (volume : Measure ℂ)) =ᵐ[volume]
      beurlingL2 F (u.toLp 2 (volume : Measure ℂ)) := by
  obtain ⟨C, hC⟩ := norm_beurlingSchwartzToLp_le (F := F) hp hp_top
  have hd : DenseRange (SchwartzMap.toLpCLM ℂ F p (volume : Measure ℂ)).toLinearMap :=
    SchwartzMap.denseRange_toLpCLM (E := ℂ) (F := F) (μ := volume) hp_top
  have heq : beurlingLp p hp hp_top (u.toLp p (volume : Measure ℂ)) =
      beurlingSchwartzToLp hp hp_top u :=
    LinearMap.extendOfNorm_eq hd ⟨C, hC⟩ u
  rw [heq]
  exact coeFn_beurlingSchwartzToLp hp hp_top u

/-- Any Lp estimate for the L² multiplier passes with the same constant to the operator on
all of Lp. In particular the Mihlin–Hörmander bound controls its operator norm. -/
theorem norm_beurlingLp_le (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {C : ℝ≥0}
    (hC : ∀ u : Lp F 2 (volume : Measure ℂ),
      eLpNorm (beurlingL2 F u) p volume ≤ C * eLpNorm u p volume) :
    ‖beurlingLp (F := F) p hp hp_top‖ ≤ C := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℂ F p (volume : Measure ℂ)).toLinearMap :=
    SchwartzMap.denseRange_toLpCLM (E := ℂ) (F := F) (μ := volume) hp_top
  exact LinearMap.opNorm_extendOfNorm_le hd C.2
    (norm_beurlingSchwartzToLp_le_of_bound hp hp_top hC)

/-- A continuous linear operator on Lp is the Beurling operator exactly when it agrees with the
spectral L² operator on Schwartz inputs. -/
theorem eq_beurlingLp_iff (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (T : Lp F p (volume : Measure ℂ) →L[ℂ] Lp F p (volume : Measure ℂ)) :
    T = beurlingLp p hp hp_top ↔ ∀ u : 𝓢(ℂ, F),
      T (u.toLp p (volume : Measure ℂ)) =ᵐ[volume]
        beurlingL2 F (u.toLp 2 (volume : Measure ℂ)) := by
  constructor
  · rintro rfl u
    exact beurlingLp_toLp hp hp_top u
  · intro h
    have hd : DenseRange (SchwartzMap.toLpCLM ℂ F p (volume : Measure ℂ)) :=
      SchwartzMap.denseRange_toLpCLM (E := ℂ) (F := F) (μ := volume) hp_top
    apply DFunLike.coe_injective
    exact hd.equalizer T.continuous (beurlingLp p hp hp_top).continuous
      (funext fun u ↦ Lp.ext ((h u).trans (beurlingLp_toLp hp hp_top u).symm))

omit [Fact (1 ≤ p)] in
/-- At exponent two the Lp extension is the original spectral operator. -/
@[simp]
theorem beurlingLp_two : beurlingLp (F := F) 2 (by norm_num) (by norm_num) = beurlingL2 F := by
  symm
  apply (eq_beurlingLp_iff (p := 2) (by norm_num) (by norm_num) (beurlingL2 F)).2
  intro u
  exact Filter.EventuallyEq.rfl

end TauCeti
