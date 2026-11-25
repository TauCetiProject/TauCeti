/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Chart
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.RealChart
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Vortex.FramedGauge.LieGroup
import TauCeti.Analysis.PDE.Vortex.Gauge.Laplacian
import TauCeti.Analysis.PDE.Vortex.Gauge.Slice
import TauCeti.Analysis.PDE.Vortex.Gauge.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Real

/-!
# Existence of the Coulomb gauge near a framed plane vortex field

For an integer `k ≥ 3`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) acts on the continuous fields of the affine space
`A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.SobolevFieldSpace`). At a field `x` the Coulomb
slice `TauCeti.Vortex.SobolevFieldSpace.coulombSlice x` is cut out by the gauge-fixing condition
`d₀* (y - x) = 0`, with `d₀* = gaugeAdjoint x` the formal `L²` adjoint of the infinitesimal gauge
action at `x`.

This file proves the existence half of the slice theorem at `x`: every field `y` near `x` is moved
into the Coulomb slice of `x` by a gauge `exp (i Φ y)` near `1`. The phase `Φ y` is a smooth
function of the real coordinates of `y`, and it vanishes when `y` already lies in the slice
(`SobolevFieldSpace.exists_isOpen_contDiffOn_coulombPhase`); in particular the gauge depends
continuously on `y` (`SobolevFieldSpace.exists_mem_nhds_continuousOn_forall_smul_mem_coulombSlice`).
The uniqueness half, that the slice meets each nearby orbit only once near `1`, is not treated here;
together the two halves give the slice charts of the quotient `A_m^k / G_(k+1)` near `x`.

**The equation.** Write `x = (b₁, b₂, p, q)`. For a real phase `f`, the Coulomb defect of the gauge
transform `e^{if} y` (`TauCeti.Vortex.phaseGauge`) is

`d₀* (e^{if} y - x) = d₀* (y - x) - Δf + sin f (p y₂ + q y₃) + (cos f - 1) (p y₃ - q y₂)`

(`TauCeti.Vortex.gaugeAdjoint_phaseGauge`). At `y = x` its linearization in `f` is the gauge
Laplacian `d₀* d₀ f = -Δf + (p² + q²) f`, which is an isomorphism `H^(k+1)_ℝ → H^(k-1)_ℝ` of the
real Bessel-potential spaces (`TauCeti.Vortex.realGaugeLaplacian`).

**The inverse function theorem.** In the real chart of `A_m^k`
(`TauCeti.Vortex.SobolevFieldSpace.realSubRefHomeomorph`) the defect is a map
`(H^k_ℝ)⁴ × H^(k+1)_ℝ → H^(k-1)_ℝ`: the linear part `d₀* (y - x) + d₀* d₀ f` plus a remainder built
from products in the algebra `H^k(ℂ)` and from `sin f - f` and `cos f - 1`. These are the real
and imaginary parts of `exp (i f) - 1 - i f`, which vanishes to second order at `f = 0` because
`f ↦ exp (i f) - 1` is smooth with derivative `φ ↦ i φ` at `0`
(`TauCeti.Vortex.contDiff_subOne_expGauge`, `TauCeti.Vortex.hasFDerivAt_subOne_expGauge_zero`).
So the defect is strictly differentiable
at `(x, 0)` with derivative `(v, φ) ↦ d₀* v + d₀* d₀ φ`, and `(y, f) ↦ (y, d₀* (e^{if} y - x))` has
an invertible strict derivative there. The inverse function theorem gives a branch of zeros
`y ↦ (y, f(y))` with `f(x) = 0`, and `g y = exp (i f(y))`. The defect is a smooth function of
`(y, f)`, so its local inverse, and with it the branch, is smooth
(`HasStrictFDerivAt.contDiffOn_toOpenPartialHomeomorph_symm`); the local inverse fixes the zeros
`(y, 0)` near `(x, 0)`, so `f(y) = 0` for `y` in the slice.

**From the Sobolev identity to every point.** The identity in `H^(k-1)` computes the defect almost
everywhere. Its gauge Laplacian term is the classical `d₀* d₀ f` by the weak equation of
`realGaugeLaplacian`
(`TauCeti.Vortex.realGaugeLaplacian_eq_iff`,
`TauCeti.Vortex.gaugeAdjoint_gaugeDirection_eq_of_integral_mul_eq`),
and all terms are continuous, so the Coulomb condition holds at every point.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter Topology BesselPotentialSpace TemperedDistribution Module
open SobolevTopologicalGaugeGroup
open scoped Laplacian ContDiff BesselPotentialSpace

/-! ### The Coulomb map in the real chart -/

section CoulombMap

variable {f : ContDiffBump (0 : ℝ)} {m j : ℕ}

private theorem natCast_succ_add_one_le (j : ℕ) : ((j + 1 : ℕ) : ℝ) + 1 ≤ ((j + 2 : ℕ) : ℝ) := by
  push_cast
  linarith

private theorem natCast_succ_add_one_le_add_one (j : ℕ) :
    ((j + 1 : ℕ) : ℝ) + 1 ≤ ((j + 2 : ℕ) : ℝ) + 1 := by
  push_cast
  linarith

private theorem finrank_lt_two_mul_natCast_succ_add_one (j : ℕ) :
    (finrank ℝ ℂ : ℝ) < 2 * (((j + 1 : ℕ) : ℝ) + 1) :=
  finrank_real_complex_lt_two_mul (by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])

private theorem finrank_lt_two_mul_natCast_add_two_add_one (j : ℕ) :
    (finrank ℝ ℂ : ℝ) < 2 * (((j + 2 : ℕ) : ℝ) + 1) :=
  finrank_real_complex_lt_two_mul (by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])

private theorem natCast_add_two_add_one_nonneg (j : ℕ) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) + 1 := by
  positivity

private theorem natCast_add_two_add_one (j : ℕ) :
    ((j + 2 : ℕ) : ℝ) + 1 = ((j + 1 + 2 : ℕ) : ℝ) := by
  push_cast
  ring

private theorem one_lt_natCast_add_two_add_one (j : ℕ) : 1 < ((j + 2 : ℕ) : ℝ) + 1 := by
  push_cast
  linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

/-- **The gauge Laplacian on the real phases** of `H^(j+3)(ℂ)`, at a continuous field `x` of
`A_m^(j+2)`: `realGaugeLaplacian`, with its domain written as the real elements of order
`(j + 2) + 1`. It is the derivative of the Coulomb map in the phase. -/
private def coulombPhaseDeriv (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    realSubmodule ℂ (natCast_add_two_add_one_nonneg j) ≃L[ℝ]
      realSubmodule ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ)) :=
  (realSubmoduleCongr ℂ (natCast_add_two_add_one j) _ (Nat.cast_nonneg _)).trans
    (realGaugeLaplacian (k := j + 2) (j := j + 1) (by omega) (by omega) x.mem_framedFieldSpace
      x.continuous)

/-- **The weak equation of `coulombPhaseDeriv`**: if `d₀* d₀ F = G`, then
`∫ F · d₀* d₀ φ = ∫ G φ` for the continuous representatives and every smooth compactly supported
`φ`. -/
private theorem integral_mul_gaugeAdjoint_gaugeDirection_eq_of_coulombPhaseDeriv_eq (hj : 1 ≤ j)
    (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) {F G} (hFG : coulombPhaseDeriv x F = G)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, continuousRep F z * gaugeAdjoint x (gaugeDirection x φ) z =
      ∫ z, continuousRep G z * φ z := by
  rw [coulombPhaseDeriv, ContinuousLinearEquiv.trans_apply] at hFG
  rw [← continuousRep_realSubmoduleCongr
    (finrank_lt_two_mul_natCast_add_two_add_one j)
    (natCast_add_two_add_one j) (Nat.cast_nonneg _) F]
  exact (realGaugeLaplacian_eq_iff (by omega) (by omega) (by omega) x.mem_framedFieldSpace
    x.continuous).1 hFG φ hφ hc

/-! #### The sine and cosine of a real phase -/

/-- The remainder `exp (i F) - 1 - i F` of a real phase `F` of `H^(j+3)(ℂ)`, from the
exponential `expGauge` of the gauge group. -/
private def expIRemainder (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    H^{((j + 2 : ℕ) : ℝ) + 1}(ℂ) :=
  subOne (expGauge (one_lt_natCast_add_two_add_one j) F) -
    Complex.I • (F : H^{((j + 2 : ℕ) : ℝ) + 1}(ℂ))

/-- `sin f - f` for a real phase `F` with continuous representative `f`
(`coeFn_inclusionLp_sinSubSelf`). -/
private def sinSubSelf (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    realSubmodule ℂ (natCast_add_two_add_one_nonneg j) :=
  realPartCLM ℂ _ (-Complex.I • expIRemainder F)

/-- `cos f - 1` for a real phase `F` with continuous representative `f`
(`coeFn_inclusionLp_cosSubOne`). -/
private def cosSubOne (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    realSubmodule ℂ (natCast_add_two_add_one_nonneg j) :=
  realPartCLM ℂ _ (expIRemainder F)

/-- `expIRemainder` is the smooth map `F ↦ exp (i F) - 1` minus the continuous linear map
`F ↦ i F`. -/
private theorem expIRemainder_eq_sub :
    (expIRemainder : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) → _) =
      fun F ↦ subOne (expGauge (one_lt_natCast_add_two_add_one j) F) -
        (Complex.I • (realSubmodule ℂ (natCast_add_two_add_one_nonneg j)).subtypeL) F := by
  funext F
  rw [expIRemainder, smul_apply, Submodule.subtypeL_apply]

private theorem expIRemainder_zero :
    expIRemainder (0 : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) = 0 := by
  rw [expIRemainder, AddChar.map_zero_eq_one, subOne_one, ZeroMemClass.coe_zero, smul_zero,
    sub_zero]

@[simp]
private theorem sinSubSelf_zero :
    sinSubSelf (0 : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) = 0 := by
  simp [sinSubSelf, expIRemainder_zero]

@[simp]
private theorem cosSubOne_zero :
    cosSubOne (0 : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) = 0 := by
  simp [cosSubOne, expIRemainder_zero]

/-- The `L²` function of `exp (i F) - 1 - i F` is `exp (i f) - 1 - i f`. -/
private theorem coeFn_inclusionLp_expIRemainder
    (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    ⇑(inclusionLp (natCast_add_two_add_one_nonneg j) (expIRemainder F)) =ᵐ[volume]
      fun z ↦ Complex.exp (continuousRep F z * Complex.I) - 1 -
        Complex.I * continuousRep F z := by
  have hexp := coeFn_toLp_inclusion_subOne_expGauge (one_lt_natCast_add_two_add_one j)
    (natCast_add_two_add_one_nonneg j) F
  rw [toLp_inclusion] at hexp
  filter_upwards [coeFn_inclusionLp_sub_ae_eq _ hexp (coeFn_inclusionLp_smul_ae_eq _ Complex.I
    (coeFn_inclusionLp_ae_eq_continuousRep
      (finrank_lt_two_mul_natCast_add_two_add_one j) F))] with z hz
  rw [expIRemainder, hz, Circle.coe_exp, smul_eq_mul]

/-- The function of `sinSubSelf F` is `sin f - f`, for the continuous representative `f` of
`F`. -/
private theorem coeFn_inclusionLp_sinSubSelf
    (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    ⇑(inclusionLp (natCast_add_two_add_one_nonneg j)
        (sinSubSelf F : H^{((j + 2 : ℕ) : ℝ) + 1}(ℂ))) =ᵐ[volume]
      fun z ↦ ((Real.sin (continuousRep F z) - continuousRep F z : ℝ) : ℂ) := by
  filter_upwards [coeFn_inclusionLp_realPartCLM (h := natCast_add_two_add_one_nonneg j)
    (-Complex.I • expIRemainder F), coeFn_inclusionLp_smul_ae_eq _ (-Complex.I)
      (coeFn_inclusionLp_expIRemainder F)] with z h₁ h₂
  rw [sinSubSelf, h₁, h₂, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re]

/-- The function of `cosSubOne F` is `cos f - 1`, for the continuous representative `f` of
`F`. -/
private theorem coeFn_inclusionLp_cosSubOne
    (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    ⇑(inclusionLp (natCast_add_two_add_one_nonneg j)
        (cosSubOne F : H^{((j + 2 : ℕ) : ℝ) + 1}(ℂ))) =ᵐ[volume]
      fun z ↦ ((Real.cos (continuousRep F z) - 1 : ℝ) : ℂ) := by
  filter_upwards [coeFn_inclusionLp_realPartCLM (h := natCast_add_two_add_one_nonneg j)
    (expIRemainder F), coeFn_inclusionLp_expIRemainder F] with z h₁ h₂
  rw [cosSubOne, h₁, h₂, Complex.exp_mul_I]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.mul_re]

/-- The remainder `exp (i F) - 1 - i F` has strict derivative `0` at `0`, since `F ↦ exp (i F) - 1`
is smooth (`contDiff_subOne_expGauge`) with derivative `G ↦ i G` at `0`
(`hasFDerivAt_subOne_expGauge_zero`). -/
private theorem hasStrictFDerivAt_expIRemainder_zero :
    HasStrictFDerivAt expIRemainder
      (0 : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) →L[ℝ]
        H^{((j + 2 : ℕ) : ℝ) + 1}(ℂ)) 0 := by
  have hs := one_lt_natCast_add_two_add_one j
  have h := (contDiff_subOne_expGauge (hs := hs)).contDiffAt.hasStrictFDerivAt
    hasFDerivAt_subOne_expGauge_zero (by simp)
  have hL := (Complex.I • (realSubmodule ℂ (natCast_add_two_add_one_nonneg j)).subtypeL
    ).hasStrictFDerivAt (x := 0)
  rw [expIRemainder_eq_sub,
    ← sub_self (Complex.I • (realSubmodule ℂ (natCast_add_two_add_one_nonneg j)).subtypeL)]
  exact h.sub hL

/-- **`sin f - f` vanishes to second order at `0`**: its strict derivative at `0` is `0`. -/
private theorem hasStrictFDerivAt_sinSubSelf_zero :
    HasStrictFDerivAt sinSubSelf
      (0 : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) →L[ℝ]
        realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) 0 := by
  have hS := ((realPartCLM ℂ (natCast_add_two_add_one_nonneg j)).comp
    ((-Complex.I : ℂ) • ContinuousLinearMap.id ℝ H^{((j + 2 : ℕ) : ℝ) + 1}(ℂ))
    ).hasStrictFDerivAt.comp 0 hasStrictFDerivAt_expIRemainder_zero
  have hfun : (sinSubSelf : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) → _) =
      ((realPartCLM ℂ (natCast_add_two_add_one_nonneg j)).comp
        ((-Complex.I : ℂ) • ContinuousLinearMap.id ℝ H^{((j + 2 : ℕ) : ℝ) + 1}(ℂ))) ∘
          expIRemainder := by
    funext F
    rw [Function.comp_apply, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, sinSubSelf]
  rw [ContinuousLinearMap.comp_zero] at hS
  rw [hfun]
  exact hS

/-- **`cos f - 1` vanishes to second order at `0`**: its strict derivative at `0` is `0`. -/
private theorem hasStrictFDerivAt_cosSubOne_zero :
    HasStrictFDerivAt cosSubOne
      (0 : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) →L[ℝ]
        realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) 0 := by
  have hC := (realPartCLM ℂ (natCast_add_two_add_one_nonneg j)).hasStrictFDerivAt.comp 0
    hasStrictFDerivAt_expIRemainder_zero
  have hfun : (cosSubOne : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) → _) =
      realPartCLM ℂ (natCast_add_two_add_one_nonneg j) ∘ expIRemainder := by
    funext F
    rw [Function.comp_apply, cosSubOne]
  rw [ContinuousLinearMap.comp_zero] at hC
  rw [hfun]
  exact hC

variable (j) in
/-- The complexified coordinates in `H^(j+2)(ℂ)` of real coordinates of a field of `A_m^(j+2)`. -/
private def coordW :
    (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) →L[ℝ]
      (Fin 4 → H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)) :=
  ContinuousLinearMap.pi fun a ↦ (((inclusion (natCast_succ_add_one_le j)).restrictScalars ℝ).comp
    (realSubmodule ℂ _).subtypeL).comp (ContinuousLinearMap.proj a)

private theorem coordW_apply
    (u : Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ)))
    (a : Fin 4) : coordW j u a = inclusion (natCast_succ_add_one_le j) (u a : H^{_}(ℂ)) :=
  (rfl)

variable (j) in
/-- A real phase of `H^(j+3)(ℂ)` as an element of `H^(j+2)(ℂ)`. -/
private def phaseW :
    realSubmodule ℂ (natCast_add_two_add_one_nonneg j) →L[ℝ] H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ) :=
  ((inclusion (natCast_succ_add_one_le_add_one j)).restrictScalars ℝ).comp
    (realSubmodule ℂ _).subtypeL

variable (j) in
/-- The multiplication of `H^(j+2)(ℂ)` as a real bilinear map. -/
private def mulR :
    H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ) →L[ℝ] H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ) →L[ℝ]
      H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ) :=
  (mulCLM (finrank_lt_two_mul_natCast_succ_add_one j)).bilinearRestrictScalars ℝ

private theorem mulR_apply (a b : H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)) :
    mulR j a b = mulCLM (finrank_lt_two_mul_natCast_succ_add_one j) a b :=
  (rfl)

/-- Multiplication by the section coordinates `(p, q)` of `x` in the Coulomb pairing
`p v₂ + q v₃`, as a bounded operator `H^(j+2)(ℂ)⁴ → H^(j+2)(ℂ)`. -/
private def sectionPairing (ξ : Fin 4 → H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)) :
    (Fin 4 → H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)) →L[ℝ] H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ) :=
  (((fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) ξ 2).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 ↦ H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ))
        2)) +
    ((fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) ξ 3).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 4 ↦ H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ))
        3))).restrictScalars ℝ

/-- `sectionPairing ξ v` is `ξ₂ v₂ + ξ₃ v₃`. -/
private theorem sectionPairing_apply (ξ v : Fin 4 → H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)) :
    sectionPairing (f := f) (m := m) ξ v =
      fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) ξ 2 (v 2) +
        fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) ξ 3 (v 3) :=
  (rfl)

/-- The nonlinear part of the Coulomb defect of `e^{iF} y` at `x`, for real coordinates
`p = (u, F)` of the field `y` and of the phase:
`F (p (y₂ - p) + q (y₃ - q)) + (sin F - F) (p y₂ + q y₃) + (cos F - 1) (p y₃ - q y₂)`, where
`x = (b₁, b₂, p, q)`. -/
private def coulombNonlinear (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (p : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) ×
      realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) : H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ) :=
  let ξ := coordW j (x.realSubRef _)
  let M a := fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) ξ a
  let Y a v :=
    fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 a v + mulR j (coordW j p.1 a) v
  let S := phaseW j (sinSubSelf p.2)
  let C := phaseW j (cosSubOne p.2)
  mulR j (phaseW j p.2) (sectionPairing (f := f) (m := m) ξ (coordW j p.1 - ξ)) + M 2 (Y 2 S) +
    M 3 (Y 3 S) + M 2 (Y 3 C) - M 3 (Y 2 C)

/-- **The Coulomb map in the real chart.** At a continuous field `x` of `A_m^(j+2)`, the Coulomb
defect `d₀* (e^{iF} y - x)` of the gauge transform of the field `y` with real coordinates `u` by
the phase `F`, as a map `(H^(j+2)_ℝ)⁴ × H^(j+3)_ℝ → H^(j+1)_ℝ`: the linear part
`d₀* (y - x) + d₀* d₀ F` plus `coulombNonlinear`. -/
private def coulombMap (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (p : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) ×
      realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    realSubmodule ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ)) :=
  realPartCLM ℂ _ (sobolevGaugeAdjoint f m (by omega : 1 ≤ j + 1) (coordW j (x.realSubRef _))
      (coordW j p.1 - coordW j (x.realSubRef _)) +
    inclusion (lt_add_one _).le (coulombNonlinear x p)) + coulombPhaseDeriv x p.2

/-- `coulombNonlinear x (u, F)` with its abbreviations unfolded, for `ξ` the coordinates of `x`,
`S = sin F - F` and `C = cos F - 1`. -/
private theorem coulombNonlinear_eq (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (u : Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ)))
    (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    coulombNonlinear x (u, F) =
      mulR j (phaseW j F) (sectionPairing (f := f) (m := m) (coordW j (x.realSubRef _))
          (coordW j u - coordW j (x.realSubRef _))) +
        fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) (coordW j (x.realSubRef _)) 2
          (fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 2 (phaseW j (sinSubSelf F)) +
            mulR j (coordW j u 2) (phaseW j (sinSubSelf F))) +
        fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) (coordW j (x.realSubRef _)) 3
          (fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 3 (phaseW j (sinSubSelf F)) +
            mulR j (coordW j u 3) (phaseW j (sinSubSelf F))) +
        fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) (coordW j (x.realSubRef _)) 2
          (fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 3 (phaseW j (cosSubOne F)) +
            mulR j (coordW j u 3) (phaseW j (cosSubOne F))) -
        fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) (coordW j (x.realSubRef _)) 3
          (fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 2 (phaseW j (cosSubOne F)) +
            mulR j (coordW j u 2) (phaseW j (cosSubOne F))) :=
  (rfl)

/-- `coulombMap x (u, F)` in `H^(j+1)(ℂ)`: the real part of `d₀* (y - x)` plus the nonlinear part,
plus the gauge Laplacian of `F`. -/
private theorem coe_coulombMap (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (u : Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ)))
    (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    (coulombMap x (u, F) : H^{((j + 1 : ℕ) : ℝ)}(ℂ)) =
      (realPartCLM ℂ (Nat.cast_nonneg (j + 1)) (sobolevGaugeAdjoint f m (by omega : 1 ≤ j + 1)
          (coordW j (x.realSubRef _)) (coordW j u - coordW j (x.realSubRef _)) +
        inclusion (lt_add_one _).le (coulombNonlinear x (u, F))) : H^{((j + 1 : ℕ) : ℝ)}(ℂ)) +
      (coulombPhaseDeriv x F : H^{((j + 1 : ℕ) : ℝ)}(ℂ)) :=
  (rfl)

private theorem coulombNonlinear_self (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    coulombNonlinear x (x.realSubRef _, 0) = 0 := by
  simp [coulombNonlinear, phaseW]

private theorem coulombMap_self (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    coulombMap x (x.realSubRef _, 0) = 0 := by
  simp [coulombMap, coulombNonlinear_self]

/-- The derivative of the Coulomb map at `(x, 0)` in the field coordinates: `d₀*` at `x`. -/
private def coulombFieldDeriv (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) →L[ℝ]
      realSubmodule ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ)) :=
  (realPartCLM ℂ _).comp
    (((sobolevGaugeAdjoint f m (by omega : 1 ≤ j + 1) (coordW j (x.realSubRef _))).restrictScalars
      ℝ).comp (coordW j))

/-- A product `x_a (y_b S)` with a term `S` vanishing to second order at `(x, 0)` vanishes to second
order there; `y_b S` is the sum of the products with the reference coordinate and with the
coordinate of `y - x_m`. -/
private theorem hasStrictFDerivAt_fieldMul_add_mulR (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (a b : Fin 4)
    {S : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) ×
      realSubmodule ℂ (natCast_add_two_add_one_nonneg j) → H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)}
    (hS : HasStrictFDerivAt S (0 : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) :
      (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) × realSubmodule ℂ (natCast_add_two_add_one_nonneg j) →L[ℝ]
        H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)) (x.realSubRef _, 0))
    (hS0 : S (x.realSubRef _, 0) = 0) :
    HasStrictFDerivAt (fun p ↦ fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1)
        (coordW j (x.realSubRef _)) a (fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 b
          (S p) + mulR j (coordW j p.1 b) (S p)))
      (0 : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) ×
        realSubmodule ℂ (natCast_add_two_add_one_nonneg j) →L[ℝ] H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ))
      (x.realSubRef _, 0) := by
  have hu := (((ContinuousLinearMap.proj b).comp (coordW j)).comp
    (ContinuousLinearMap.fst ℝ _ (realSubmodule ℂ (natCast_add_two_add_one_nonneg j)))
    ).hasStrictFDerivAt (x := (x.realSubRef (Nat.cast_nonneg (j + 2)), 0))
  have h₁ := ((fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 b).restrictScalars
    ℝ).hasStrictFDerivAt.comp _ hS
  have h₂ := (mulR j).hasStrictFDerivAt_of_bilinear hu hS
  simp only [hS0, map_zero, add_zero] at h₂
  rw [ContinuousLinearMap.comp_zero] at h₁
  simpa using ((fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) (coordW j (x.realSubRef _))
    a).restrictScalars ℝ).hasStrictFDerivAt.comp _ (h₁.add h₂)

/-- The nonlinear part of the Coulomb map vanishes to second order at `(x, 0)`. -/
private theorem hasStrictFDerivAt_coulombNonlinear (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    HasStrictFDerivAt (coulombNonlinear x)
      (0 : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) ×
        realSubmodule ℂ (natCast_add_two_add_one_nonneg j) →L[ℝ] H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ))
      (x.realSubRef _, 0) := by
  set V := Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))
  set P := realSubmodule ℂ (natCast_add_two_add_one_nonneg j)
  set W := H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)
  set p₀ : V × P := (x.realSubRef _, 0)
  set ξ := coordW j (x.realSubRef _)
  -- The phase, its sine and cosine remainders, and the Coulomb pairing of `y - x`.
  have hF : HasStrictFDerivAt (fun p : V × P ↦ phaseW j p.2)
      ((phaseW j).comp (ContinuousLinearMap.snd ℝ V P)) p₀ :=
    ((phaseW j).comp (ContinuousLinearMap.snd ℝ V P)).hasStrictFDerivAt
  have hS : HasStrictFDerivAt (fun p : V × P ↦ phaseW j (sinSubSelf p.2))
      (0 : V × P →L[ℝ] W) p₀ := by
    simpa using (phaseW j).hasStrictFDerivAt.comp p₀
      (hasStrictFDerivAt_sinSubSelf_zero.comp p₀ hasStrictFDerivAt_snd)
  have hC : HasStrictFDerivAt (fun p : V × P ↦ phaseW j (cosSubOne p.2))
      (0 : V × P →L[ℝ] W) p₀ := by
    simpa using (phaseW j).hasStrictFDerivAt.comp p₀
      (hasStrictFDerivAt_cosSubOne_zero.comp p₀ hasStrictFDerivAt_snd)
  have hd : HasStrictFDerivAt
      (fun p : V × P ↦ sectionPairing (f := f) (m := m) ξ (coordW j p.1 - ξ))
      (((sectionPairing (f := f) (m := m) ξ).comp (coordW j)).comp (ContinuousLinearMap.fst ℝ V P))
      p₀ := by
    have h := (((sectionPairing (f := f) (m := m) ξ).comp (coordW j)).comp
      (ContinuousLinearMap.fst ℝ V P)).hasStrictFDerivAt.sub_const
        (x := p₀) (sectionPairing (f := f) (m := m) ξ ξ)
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_fst', map_sub] using h
  -- The product of the phase with the pairing vanishes to second order.
  have h₁ := (mulR j).hasStrictFDerivAt_of_bilinear hF hd
  rw [show phaseW j p₀.2 = 0 by simp [p₀], show sectionPairing (f := f) (m := m) ξ
    (coordW j p₀.1 - ξ) = 0 by simp [p₀, ξ], map_zero, map_zero, zero_apply, add_zero] at h₁
  have hS0 : phaseW j (sinSubSelf (p₀.2)) = 0 := by simp [p₀]
  have hC0 : phaseW j (cosSubOne (p₀.2)) = 0 := by simp [p₀]
  have key := ((((h₁.add (hasStrictFDerivAt_fieldMul_add_mulR x 2 2 hS hS0)).add
    (hasStrictFDerivAt_fieldMul_add_mulR x 3 3 hS hS0)).add
      (hasStrictFDerivAt_fieldMul_add_mulR x 2 3 hC hC0)).sub
        (hasStrictFDerivAt_fieldMul_add_mulR x 3 2 hC hC0))
  simp only [add_zero, sub_zero] at key
  rw [show coulombNonlinear x = fun p ↦ _ from funext fun p ↦ coulombNonlinear_eq x p.1 p.2]
  exact key

/-- **The strict derivative of the Coulomb map** at `(x, 0)`: `(v, G) ↦ d₀* v + d₀* d₀ G`. -/
private theorem hasStrictFDerivAt_coulombMap (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    HasStrictFDerivAt (coulombMap x)
      ((coulombFieldDeriv x).comp (ContinuousLinearMap.fst ℝ _ _) +
        ((coulombPhaseDeriv x : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) →L[ℝ]
          realSubmodule ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))).comp
            (ContinuousLinearMap.snd ℝ _ _)))
      (x.realSubRef _, 0) := by
  set V := Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))
  set P := realSubmodule ℂ (natCast_add_two_add_one_nonneg j)
  set p₀ : V × P := (x.realSubRef _, 0)
  set ξ := coordW j (x.realSubRef _)
  set D := (sobolevGaugeAdjoint f m (by omega : 1 ≤ j + 1) ξ).restrictScalars ℝ
  have hA : HasStrictFDerivAt (fun p : V × P ↦ D (coordW j p.1 - ξ))
      ((D.comp (coordW j)).comp (ContinuousLinearMap.fst ℝ V P)) p₀ := by
    have h := ((D.comp (coordW j)).comp (ContinuousLinearMap.fst ℝ V P)).hasStrictFDerivAt.sub_const
      (x := p₀) (D ξ)
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_fst', map_sub] using h
  have hN :=
    ((inclusion (lt_add_one ((j + 1 : ℕ) : ℝ)).le).restrictScalars ℝ).hasStrictFDerivAt.comp p₀
      (hasStrictFDerivAt_coulombNonlinear x)
  have hR := (realPartCLM ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))
    ).hasStrictFDerivAt.comp p₀ (hA.add hN)
  have hT := ((coulombPhaseDeriv x : P →L[ℝ]
    realSubmodule ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))).comp
      (ContinuousLinearMap.snd ℝ V P)).hasStrictFDerivAt (x := p₀)
  -- The definition of `coulombMap x`, with the abbreviations of this proof.
  have hfun : coulombMap x = fun p : V × P ↦ realPartCLM ℂ _ (D (coordW j p.1 - ξ) +
      inclusion (lt_add_one ((j + 1 : ℕ) : ℝ)).le (coulombNonlinear x p)) +
        coulombPhaseDeriv x p.2 := by
    ext1 p
    simp only [coulombMap, D, ξ, ContinuousLinearMap.coe_restrictScalars']
  rw [hfun]
  refine (hR.add hT).congr_fderiv (ContinuousLinearMap.ext fun p ↦ ?_)
  simp [coulombFieldDeriv, D, ξ]

/-! #### Smoothness of the Coulomb map -/

/-- The remainder `exp (i F) - 1 - i F` is a smooth function of the real phase `F`. -/
private theorem contDiff_expIRemainder :
    ContDiff ℝ ∞ (expIRemainder : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) → _) := by
  rw [expIRemainder_eq_sub]
  exact (contDiff_subOne_expGauge (hs := one_lt_natCast_add_two_add_one j)).sub
    (Complex.I • (realSubmodule ℂ (natCast_add_two_add_one_nonneg j)).subtypeL).contDiff

private theorem contDiff_sinSubSelf :
    ContDiff ℝ ∞ (sinSubSelf : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) → _) :=
  (realPartCLM ℂ (natCast_add_two_add_one_nonneg j)).contDiff.comp
    (contDiff_expIRemainder.const_smul (-Complex.I))

private theorem contDiff_cosSubOne :
    ContDiff ℝ ∞ (cosSubOne : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) → _) :=
  (realPartCLM ℂ (natCast_add_two_add_one_nonneg j)).contDiff.comp contDiff_expIRemainder

/-- The nonlinear part of the Coulomb map is a smooth function of the field and the phase. -/
private theorem contDiff_coulombNonlinear (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    ContDiff ℝ ∞ (coulombNonlinear x) := by
  set V := Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))
  set P := realSubmodule ℂ (natCast_add_two_add_one_nonneg j)
  set W := H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)
  set ξ := coordW j (x.realSubRef _)
  have hu (b : Fin 4) : ContDiff ℝ ∞ fun p : V × P ↦ coordW j p.1 b :=
    (((ContinuousLinearMap.proj b).comp (coordW j)).comp
      (ContinuousLinearMap.fst ℝ V P)).contDiff
  have hM (a : Fin 4) {S : V × P → W} (hS : ContDiff ℝ ∞ S) :
      ContDiff ℝ ∞ fun p ↦ fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) ξ a (S p) :=
    ((fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) ξ a).contDiff.restrict_scalars
      ℝ).comp hS
  have hY (a b : Fin 4) {S : V × P → W} (hS : ContDiff ℝ ∞ S) :
      ContDiff ℝ ∞ fun p ↦ fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) ξ a
        (fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 b (S p) +
          mulR j (coordW j p.1 b) (S p)) :=
    hM a ((((fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 b).contDiff.restrict_scalars
      ℝ).comp hS).add (((mulR j).contDiff.comp (hu b)).clm_apply hS))
  have hS : ContDiff ℝ ∞ fun p : V × P ↦ phaseW j (sinSubSelf p.2) :=
    (phaseW j).contDiff.comp (contDiff_sinSubSelf.comp contDiff_snd)
  have hC : ContDiff ℝ ∞ fun p : V × P ↦ phaseW j (cosSubOne p.2) :=
    (phaseW j).contDiff.comp (contDiff_cosSubOne.comp contDiff_snd)
  have hd : ContDiff ℝ ∞ fun p : V × P ↦ sectionPairing (f := f) (m := m) ξ (coordW j p.1 - ξ) :=
    (sectionPairing (f := f) (m := m) ξ).contDiff.comp
      (((coordW j).contDiff.comp contDiff_fst).sub contDiff_const)
  have hF : ContDiff ℝ ∞ fun p : V × P ↦ phaseW j p.2 := (phaseW j).contDiff.comp contDiff_snd
  rw [show coulombNonlinear x = fun p ↦ _ from funext fun p ↦ coulombNonlinear_eq x p.1 p.2]
  exact (((((mulR j).contDiff.comp hF).clm_apply hd).add (hY 2 2 hS)).add (hY 3 3 hS)).add
    (hY 2 3 hC) |>.sub (hY 3 2 hC)

/-- **The Coulomb map is smooth** in the field and the phase. -/
private theorem contDiff_coulombMap (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    ContDiff ℝ ∞ (coulombMap x) := by
  set ξ := coordW j (x.realSubRef _)
  have hA : ContDiff ℝ ∞ fun p : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) :
      (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) × realSubmodule ℂ (natCast_add_two_add_one_nonneg j) ↦
        sobolevGaugeAdjoint f m (by omega : 1 ≤ j + 1) ξ (coordW j p.1 - ξ) :=
    ((sobolevGaugeAdjoint f m (by omega : 1 ≤ j + 1) ξ).contDiff.restrict_scalars ℝ).comp
      (((coordW j).contDiff.comp contDiff_fst).sub contDiff_const)
  have hN := ((inclusion (lt_add_one ((j + 1 : ℕ) : ℝ)).le :
    H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ) →L[ℂ] H^{((j + 1 : ℕ) : ℝ)}(ℂ)).contDiff.restrict_scalars
      ℝ).comp (contDiff_coulombNonlinear x)
  exact ((realPartCLM ℂ _).contDiff.comp (hA.add hN)).add
    ((coulombPhaseDeriv x).contDiff.comp contDiff_snd)

/-- **The Coulomb phase.** Near the real coordinates of a continuous field `x` of `A_m^(j+2)`, the
Coulomb map has a smooth branch of zeros `u ↦ (u, Φ u)` through `(x, 0)`, defined on an open set
`U`. It is the only branch of zeros near `(x, 0)`: if `u ∈ U` and `(u, 0)` is already a zero,
then `Φ u = 0`. This is the inverse function theorem for `(u, F) ↦ (u, coulombMap x (u, F))`,
whose derivative at `(x, 0)` is invertible because the gauge Laplacian is
(`realGaugeLaplacian`), and whose local inverse is smooth because the Coulomb map is. -/
private theorem exists_coulombPhase (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    ∃ U, IsOpen U ∧ x.realSubRef (Nat.cast_nonneg (j + 2)) ∈ U ∧
      ∃ Φ : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) →
        realSubmodule ℂ (natCast_add_two_add_one_nonneg j),
      ContDiffOn ℝ ∞ Φ U ∧ Φ (x.realSubRef _) = 0 ∧ (∀ u ∈ U, coulombMap x (u, Φ u) = 0) ∧
        ∀ u ∈ U, coulombMap x (u, 0) = 0 → Φ u = 0 := by
  set V := Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))
  set P := realSubmodule ℂ (natCast_add_two_add_one_nonneg j)
  set T := realSubmodule ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))
  set p₀ : V × P := (x.realSubRef _, 0)
  set e : (V × P) ≃L[ℝ] V × T :=
    (ContinuousLinearEquiv.refl ℝ V).skewProd (coulombPhaseDeriv x) (coulombFieldDeriv x)
  set Ψ : V × P → V × T := fun p ↦ (p.1, coulombMap x p)
  have hΨ : HasStrictFDerivAt Ψ (e : V × P →L[ℝ] V × T) p₀ := by
    refine (hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_coulombMap x)).congr_fderiv
      (ContinuousLinearMap.ext fun p ↦ ?_)
    simp [e, add_comm]
  set H := hΨ.toOpenPartialHomeomorph Ψ
  have hHΨ : ⇑H = Ψ := hΨ.toOpenPartialHomeomorph_coe
  set q₀ : V × T := (x.realSubRef _, 0)
  have hΨ₀ : Ψ p₀ = q₀ := Prod.ext rfl (coulombMap_self x)
  have hmem : q₀ ∈ H.target := hΨ₀ ▸ hΨ.image_mem_toOpenPartialHomeomorph_target
  have hι : Continuous fun u : V ↦ ((u, 0) : V × T) := continuous_id.prodMk continuous_const
  have hι' : Continuous fun u : V ↦ ((u, 0) : V × P) := continuous_id.prodMk continuous_const
  -- The local inverse of `Ψ` is smooth, since `Ψ` is.
  have hsmooth : ContDiffOn ℝ ∞ H.symm H.target :=
    HasStrictFDerivAt.contDiffOn_toOpenPartialHomeomorph_symm hΨ
      (contDiff_fst.prodMk (contDiff_coulombMap x)).contDiffOn
  refine ⟨(fun u : V ↦ ((u, 0) : V × T)) ⁻¹' H.target ∩ (fun u : V ↦ ((u, 0) : V × P)) ⁻¹' H.source,
    (H.open_target.preimage hι).inter (H.open_source.preimage hι'),
    ⟨hmem, hΨ.mem_toOpenPartialHomeomorph_source⟩, fun u ↦ (H.symm (u, 0)).2, ?_, ?_,
    fun u hu ↦ ?_, fun u hu h0 ↦ ?_⟩
  · exact (contDiff_snd.comp_contDiffOn (hsmooth.comp
      (contDiff_id.prodMk contDiff_const).contDiffOn fun _ hu ↦ hu)).mono
      Set.inter_subset_left
  · have h : H.symm q₀ = p₀ := by
      rw [← hΨ₀, ← hHΨ]
      exact H.left_inv hΨ.mem_toOpenPartialHomeomorph_source
    exact congrArg Prod.snd h
  · have h := H.right_inv hu.1
    rw [hHΨ] at h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    rwa [show H.symm (u, 0) = (u, (H.symm (u, 0)).2) from Prod.ext h₁ rfl] at h₂
  · -- `(u, 0)` is a zero in the source of `H`, so `H` fixes it and its inverse returns it.
    have h : H (u, 0) = (u, 0) := by rw [hHΨ]; exact Prod.ext rfl h0
    have h' := H.left_inv hu.2
    rw [h] at h'
    exact congrArg Prod.snd h'

/-! ### The Coulomb map computes the Coulomb defect -/

private theorem natCast_succ_add_one_nonneg (j : ℕ) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) + 1 := by
  positivity

/-- The `L²` functions of the complexified coordinates of a field `w` are the coordinates of
`w - x_m`. -/
private theorem coeFn_inclusionLp_coordW (w : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (a : Fin 4) :
    ⇑(inclusionLp (natCast_succ_add_one_nonneg j)
        (coordW j (w.realSubRef (Nat.cast_nonneg (j + 2))) a)) =ᵐ[volume]
      fun z ↦ (((⇑w - referenceField f m) z a : ℝ) : ℂ) := by
  rw [coordW_apply, inclusionLp_inclusion]
  refine (SobolevFieldSpace.coeFn_inclusionLp_realSubRef _ w a).trans
    (Eventually.of_forall fun z ↦ ?_)
  simp

/-- The `L²` functions of the differences of the complexified coordinates of fields `y` and `x`
are the coordinates of `y - x`. -/
private theorem coeFn_inclusionLp_coordW_sub (x y : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (a : Fin 4) :
    ⇑(inclusionLp (natCast_succ_add_one_nonneg j)
        ((coordW j (y.realSubRef (Nat.cast_nonneg (j + 2))) -
          coordW j (x.realSubRef (Nat.cast_nonneg (j + 2)))) a)) =ᵐ[volume]
      fun z ↦ (((⇑y - ⇑x) z a : ℝ) : ℂ) := by
  filter_upwards [coeFn_inclusionLp_sub_ae_eq (natCast_succ_add_one_nonneg j)
    (coeFn_inclusionLp_coordW y a) (coeFn_inclusionLp_coordW x a)] with z hz
  rw [Pi.sub_apply, hz]
  simp

/-- Multiplication by the coordinate `a` of a field `x` computes the pointwise product. -/
private theorem coeFn_inclusionLp_fieldMul_coordW (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (a : Fin 4) {v : H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)} {g : ℂ → ℝ}
    (hv : ⇑(inclusionLp (natCast_succ_add_one_nonneg j) v) =ᵐ[volume] fun z ↦ (g z : ℂ)) :
    ⇑(inclusionLp (natCast_succ_add_one_nonneg j) (fieldMulOrderPreservingCLM f m
        (by omega : 1 ≤ j + 1) (coordW j (x.realSubRef (Nat.cast_nonneg (j + 2)))) a v))
      =ᵐ[volume] fun z ↦ ((x z a * g z : ℝ) : ℂ) := by
  simpa using coeFn_inclusionLp_fieldMulOrderPreservingCLM_ae_eq (f := f) (m := m)
    (by omega : 1 ≤ j + 1) (coeFn_inclusionLp_coordW x) a hv

/-- Multiplication by the coordinate `a` of the reference field computes the pointwise product. -/
private theorem coeFn_inclusionLp_fieldMul_zero (a : Fin 4) {v : H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)}
    {g : ℂ → ℝ}
    (hv : ⇑(inclusionLp (natCast_succ_add_one_nonneg j) v) =ᵐ[volume] fun z ↦ (g z : ℂ)) :
    ⇑(inclusionLp (natCast_succ_add_one_nonneg j)
        (fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 a v))
      =ᵐ[volume] fun z ↦ ((referenceField f m z a * g z : ℝ) : ℂ) := by
  have h0 : ∀ b, ⇑(inclusionLp (natCast_succ_add_one_nonneg j)
      ((0 : Fin 4 → H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)) b)) =ᵐ[volume]
        fun z ↦ (((0 : ℂ → EuclideanSpace ℝ (Fin 4)) z b : ℝ) : ℂ) := fun b ↦ by
    rw [Pi.zero_apply, map_zero]
    refine (Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)).trans (Eventually.of_forall fun _ ↦ ?_)
    simp
  simpa using coeFn_inclusionLp_fieldMulOrderPreservingCLM_ae_eq (f := f) (m := m)
    (by omega : 1 ≤ j + 1) h0 a hv

/-- The product `mulR` computes the pointwise product. -/
private theorem coeFn_inclusionLp_mulR {a b : H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)} {g₁ g₂ : ℂ → ℝ}
    (ha : ⇑(inclusionLp (natCast_succ_add_one_nonneg j) a) =ᵐ[volume] fun z ↦ (g₁ z : ℂ))
    (hb : ⇑(inclusionLp (natCast_succ_add_one_nonneg j) b) =ᵐ[volume] fun z ↦ (g₂ z : ℂ)) :
    ⇑(inclusionLp (natCast_succ_add_one_nonneg j) (mulR j a b)) =ᵐ[volume]
      fun z ↦ ((g₁ z * g₂ z : ℝ) : ℂ) := by
  have h := coeFn_toLp_inclusion_mulCLM (finrank_lt_two_mul_natCast_succ_add_one j)
    (natCast_succ_add_one_nonneg j) a b
  simp only [toLp_inclusion] at h
  filter_upwards [h, ha, hb] with z hz h₁ h₂
  rw [mulR_apply, hz, h₁, h₂, Complex.ofReal_mul]

/-- **The nonlinear part of the Coulomb defect.** For continuous fields `x, y` of `A_m^(j+2)` and
a real phase `F` with continuous representative `f`, the `L²` function of
`coulombNonlinear x (y, F)` is `-(p² + q²) f + sin f (p y₂ + q y₃) + (cos f - 1) (p y₃ - q y₂)`,
where `x = (b₁, b₂, p, q)`. -/
private theorem coeFn_inclusionLp_coulombNonlinear (x y : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    ⇑(inclusionLp (natCast_succ_add_one_nonneg j)
        (coulombNonlinear x (y.realSubRef (Nat.cast_nonneg (j + 2)), F))) =ᵐ[volume]
      fun z ↦ ((-(x z 2 ^ 2 + x z 3 ^ 2) * continuousRep F z +
        Real.sin (continuousRep F z) * (x z 2 * y z 2 + x z 3 * y z 3) +
        (Real.cos (continuousRep F z) - 1) * (x z 2 * y z 3 - x z 3 * y z 2) : ℝ) : ℂ) := by
  have h0W := natCast_succ_add_one_nonneg j
  have hsP := finrank_lt_two_mul_natCast_add_two_add_one j
  set ξ := coordW j (x.realSubRef (Nat.cast_nonneg (j + 2)))
  set u := y.realSubRef (Nat.cast_nonneg (j + 2))
  -- Multiplication by the coordinate `b` of `y`.
  have hY (b : Fin 4) {v : H^{((j + 1 : ℕ) : ℝ) + 1}(ℂ)} {g : ℂ → ℝ}
      (hv : ⇑(inclusionLp h0W v) =ᵐ[volume] fun z ↦ (g z : ℂ)) :
      ⇑(inclusionLp h0W (fieldMulOrderPreservingCLM f m (by omega : 1 ≤ j + 1) 0 b v +
        mulR j (coordW j u b) v)) =ᵐ[volume] fun z ↦ ((y z b * g z : ℝ) : ℂ) := by
    filter_upwards [coeFn_inclusionLp_add_ae_eq h0W (coeFn_inclusionLp_fieldMul_zero b hv)
      (coeFn_inclusionLp_mulR (coeFn_inclusionLp_coordW y b) hv)] with z hz
    rw [hz, ← Complex.ofReal_add]
    congr 1
    simp only [Pi.sub_apply, PiLp.sub_apply]
    ring
  -- The phase, its remainders and the Coulomb pairing of `y - x`.
  have hF : ⇑(inclusionLp h0W (phaseW j F)) =ᵐ[volume] fun z ↦ (continuousRep F z : ℂ) := by
    simpa [phaseW, inclusionLp_inclusion] using coeFn_inclusionLp_ae_eq_continuousRep hsP F
  have hS : ⇑(inclusionLp h0W (phaseW j (sinSubSelf F))) =ᵐ[volume]
      fun z ↦ ((Real.sin (continuousRep F z) - continuousRep F z : ℝ) : ℂ) := by
    simpa [phaseW, inclusionLp_inclusion] using coeFn_inclusionLp_sinSubSelf F
  have hC : ⇑(inclusionLp h0W (phaseW j (cosSubOne F))) =ᵐ[volume]
      fun z ↦ ((Real.cos (continuousRep F z) - 1 : ℝ) : ℂ) := by
    simpa [phaseW, inclusionLp_inclusion] using coeFn_inclusionLp_cosSubOne F
  have hpair : ⇑(inclusionLp h0W (sectionPairing (f := f) (m := m) ξ (coordW j u - ξ)))
      =ᵐ[volume] fun z ↦ ((x z 2 * (y z 2 - x z 2) + x z 3 * (y z 3 - x z 3) : ℝ) : ℂ) := by
    filter_upwards [coeFn_inclusionLp_add_ae_eq h0W (coeFn_inclusionLp_fieldMul_coordW x 2
      (coeFn_inclusionLp_coordW_sub x y 2)) (coeFn_inclusionLp_fieldMul_coordW x 3
        (coeFn_inclusionLp_coordW_sub x y 3))] with z hz
    rw [sectionPairing_apply, hz]
    simp
  have h := coeFn_inclusionLp_sub_ae_eq h0W (coeFn_inclusionLp_add_ae_eq h0W
    (coeFn_inclusionLp_add_ae_eq h0W (coeFn_inclusionLp_add_ae_eq h0W
      (coeFn_inclusionLp_mulR hF hpair) (coeFn_inclusionLp_fieldMul_coordW x 2 (hY 2 hS)))
        (coeFn_inclusionLp_fieldMul_coordW x 3 (hY 3 hS)))
          (coeFn_inclusionLp_fieldMul_coordW x 2 (hY 3 hC)))
            (coeFn_inclusionLp_fieldMul_coordW x 3 (hY 2 hC))
  rw [coulombNonlinear_eq]
  refine h.trans (Eventually.of_forall fun z ↦ ?_)
  push_cast
  ring

/-- **The Coulomb map computes the Coulomb defect.** For continuous fields `x, y` of `A_m^(j+2)`,
`j ≥ 1`, and a real phase `F` with continuous representative `f`, the `L²` function of
`coulombMap x (y, F)` is almost everywhere
`d₀* (y - x) - (p² + q²) f + sin f (p y₂ + q y₃) + (cos f - 1) (p y₃ - q y₂) + d₀* d₀ F`, where
`x = (b₁, b₂, p, q)` and the last term is the continuous representative of
`coulombPhaseDeriv x F`. -/
private theorem coeFn_inclusionLp_coulombMap (hj : 1 ≤ j)
    (x y : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    ⇑(inclusionLp (Nat.cast_nonneg (j + 1))
        (coulombMap x (y.realSubRef (Nat.cast_nonneg (j + 2)), F) : H^{((j + 1 : ℕ) : ℝ)}(ℂ)))
      =ᵐ[volume] fun z ↦ ((gaugeAdjoint x (⇑y - ⇑x) z -
        (x z 2 ^ 2 + x z 3 ^ 2) * continuousRep F z +
        Real.sin (continuousRep F z) * (x z 2 * y z 2 + x z 3 * y z 3) +
        (Real.cos (continuousRep F z) - 1) * (x z 2 * y z 3 - x z 3 * y z 2) +
        continuousRep (coulombPhaseDeriv x F) z : ℝ) : ℂ) := by
  have hj' : 1 ≤ j + 1 := by omega
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hd2 : (finrank ℝ ℂ : ℝ) < 2 * ((j + 1 : ℕ) : ℝ) :=
    finrank_real_complex_lt_two_mul (by push_cast; linarith)
  set ξ := coordW j (x.realSubRef (Nat.cast_nonneg (j + 2)))
  set u := y.realSubRef (Nat.cast_nonneg (j + 2))
  -- The linear part `d₀* (y - x)`.
  have hA : ⇑(inclusionLp (Nat.cast_nonneg (j + 1))
      (sobolevGaugeAdjoint f m hj' ξ (coordW j u - ξ))) =ᵐ[volume]
        fun z ↦ ((gaugeAdjoint x (⇑y - ⇑x) z : ℝ) : ℂ) := by
    have hyx : ContDiff ℝ 1 (⇑y - ⇑x) :=
      (y.contDiff (by push_cast; linarith)).sub (x.contDiff (by push_cast; linarith))
    have hc (i : Fin 4) : ContDiff ℝ 1 fun z ↦ (⇑y - ⇑x) z i :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hyx
    have h := coeFn_inclusionLp_sobolevGaugeAdjoint_ae_eq (f := f) (m := m) hj'
      (coeFn_inclusionLp_coordW x) (coeFn_inclusionLp_coordW_sub x y) (hc 0) (hc 1)
    rwa [add_sub_cancel] at h
  -- The nonlinear part, the real part and the gauge Laplacian.
  have hlin := coeFn_inclusionLp_add_ae_eq (Nat.cast_nonneg (j + 1)) hA
    ((inclusionLp_inclusion (lt_add_one ((j + 1 : ℕ) : ℝ)).le (Nat.cast_nonneg (j + 1))
      (coulombNonlinear x (u, F))).symm ▸ coeFn_inclusionLp_coulombNonlinear x y F)
  have hre := coeFn_inclusionLp_realPartCLM (h := (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ _))
    (sobolevGaugeAdjoint f m hj' ξ (coordW j u - ξ) +
      inclusion (lt_add_one ((j + 1 : ℕ) : ℝ)).le (coulombNonlinear x (u, F)))
  have hsum := coeFn_inclusionLp_add_ae_eq (Nat.cast_nonneg (j + 1)) hre
    (coeFn_inclusionLp_ae_eq_continuousRep hd2 (coulombPhaseDeriv x F))
  rw [coe_coulombMap]
  refine hsum.trans ?_
  filter_upwards [hlin] with z hz'
  simp only [hz', Complex.add_re, Complex.ofReal_re]
  push_cast
  ring

/-- **A zero of the Coulomb map is a Coulomb gauge.** For continuous fields `x, y` of `A_m^(j+2)`,
`j ≥ 1`, if `coulombMap x (y, F) = 0`, then the gauge transform `e^{iF} y` lies in the Coulomb slice
of `x`: `d₀* (e^{iF} y - x) = 0` at every point. -/
private theorem gaugeAdjoint_phaseGauge_sub_eq_zero_of_coulombMap_eq_zero (hj : 1 ≤ j)
    (x y : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    {F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)}
    (hF : coulombMap x (y.realSubRef (Nat.cast_nonneg (j + 2)), F) = 0) (z : ℂ) :
    gaugeAdjoint x (phaseGauge y (continuousRep F) - x) z = 0 := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hd2 : (finrank ℝ ℂ : ℝ) < 2 * ((j + 1 : ℕ) : ℝ) :=
    finrank_real_complex_lt_two_mul (by push_cast; linarith)
  have hx1 : ContDiff ℝ 1 x := x.contDiff (by push_cast; linarith)
  have hy1 : ContDiff ℝ 1 y := y.contDiff (by push_cast; linarith)
  have hφ : ContDiff ℝ 2 (continuousRep F) :=
    contDiff_continuousRep (finrank_real_complex_add_two_mul_lt_two_mul (by push_cast; linarith)) F
  set φ := continuousRep F
  set G := coulombPhaseDeriv x F
  -- The continuous representative of `d₀* d₀ F` is minus the rest of the Coulomb defect.
  have hGR : continuousRep G = fun z ↦ -(gaugeAdjoint x (⇑y - ⇑x) z -
      (x z 2 ^ 2 + x z 3 ^ 2) * φ z + Real.sin (φ z) * (x z 2 * y z 2 + x z 3 * y z 3) +
      (Real.cos (φ z) - 1) * (x z 2 * y z 3 - x z 3 * y z 2)) := by
    have hgA := continuous_gaugeAdjoint x.continuous (hy1.sub hx1)
    have hxc := x.continuous
    have hyc := y.continuous
    have hφc := hφ.continuous
    refine (Continuous.ae_eq_iff_eq volume (continuous_continuousRep hd2 G) (by fun_prop)).1 ?_
    have h := coeFn_inclusionLp_coulombMap hj x y F
    rw [hF, ZeroMemClass.coe_zero, map_zero] at h
    filter_upwards [h, Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z h₁ h₂
    have h₃ := h₁.symm.trans h₂
    rw [Pi.zero_apply] at h₃
    norm_cast at h₃
    linarith
  -- The weak equation makes `d₀* d₀ F` classical.
  have hLap : gaugeAdjoint x (gaugeDirection x φ) z = continuousRep G z :=
    gaugeAdjoint_gaugeDirection_eq_of_integral_mul_eq x.continuous hφ
      (continuous_continuousRep hd2 G)
      (fun ψ hψ hc ↦ integral_mul_gaugeAdjoint_gaugeDirection_eq_of_coulombPhaseDeriv_eq hj x
        rfl hψ hc) z
  rw [gaugeAdjoint_gaugeDirection x hφ.contDiffAt, hGR] at hLap
  -- The Coulomb defect of `e^{iF} y - x`.
  have hdy := differentiable_euclidean.1 (hy1.differentiable one_ne_zero)
  have hdx := differentiable_euclidean.1 (hx1.differentiable one_ne_zero)
  have hdφ (v : ℂ) : DifferentiableAt ℝ (fun w ↦ fderiv ℝ φ w v) z :=
    (((hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) z).clm_apply
      (differentiableAt_const v)
  have hp₀ : DifferentiableAt ℝ (fun w ↦ phaseGauge y φ w 0) z := by
    simpa only [phaseGauge_apply_zero] using (hdy 0 z).fun_sub (hdφ 1)
  have hp₁ : DifferentiableAt ℝ (fun w ↦ phaseGauge y φ w 1) z := by
    simpa only [phaseGauge_apply_one] using (hdy 1 z).fun_sub (hdφ Complex.I)
  have hyx := gaugeAdjoint_sub x (hdy 0 z) (hdy 1 z) (hdx 0 z) (hdx 1 z)
  rw [gaugeAdjoint_sub x hp₀ hp₁ (hdx 0 z) (hdx 1 z),
    gaugeAdjoint_phaseGauge x (hdy 0 z) (hdy 1 z) hφ.contDiffAt]
  linear_combination hLap - hyx

/-- **The phase `0` is a zero of the Coulomb map at a field of the Coulomb slice.** For continuous
fields `x, y` of `A_m^(j+2)`, `j ≥ 1`, with `d₀* (y - x) = 0` at every point,
`coulombMap x (y, 0) = 0`. -/
private theorem coulombMap_realSubRef_zero_eq_zero (hj : 1 ≤ j)
    (x y : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) (hy : ∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0) :
    coulombMap x (y.realSubRef (Nat.cast_nonneg (j + 2)), 0) = 0 := by
  refine Subtype.ext (inclusionLp_injective (Nat.cast_nonneg (j + 1)) ?_)
  rw [ZeroMemClass.coe_zero, map_zero]
  refine Lp.ext ?_
  filter_upwards [coeFn_inclusionLp_coulombMap hj x y 0, Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)]
    with z h₁ h₂
  simp only [h₁, h₂, map_zero, Pi.zero_apply, hy z, Real.sin_zero, Real.cos_zero]
  norm_num

end CoulombMap

/-! ### Existence of the Coulomb gauge -/

namespace SobolevFieldSpace

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

omit [Fact (1 < k)] in
/-- **The Coulomb slice** through a continuous field `x` of `A_m^k`: the fields `y` with
`d₀* (y - x) = 0`, where `d₀* = gaugeAdjoint x` is the formal adjoint of the infinitesimal gauge
action at `x`. -/
def coulombSlice (x : SobolevFieldSpace f m k) : Set (SobolevFieldSpace f m k) :=
  {y | ∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0}

omit [Fact (1 < k)] in
@[simp]
theorem mem_coulombSlice {x y : SobolevFieldSpace f m k} :
    y ∈ coulombSlice x ↔ ∀ z, gaugeAdjoint x (⇑y - ⇑x) z = 0 :=
  Iff.rfl

omit [Fact (1 < k)] in
/-- A field lies in its own Coulomb slice. -/
theorem self_mem_coulombSlice (x : SobolevFieldSpace f m k) : x ∈ coulombSlice x := by
  simp [gaugeAdjoint_def]

variable (hs) in
/-- **The smooth Coulomb gauge near a field.** Let `x` be a continuous field of `A_m^k`, `k ≥ 3`.
There are an open set `U` of real coordinates containing those of `x` and a real phase `Φ`,
smooth on `U` with `Φ x = 0`, such that for every field `y` with coordinates in `U`:

* the gauge transform `exp (i Φ y) · y` lies in the Coulomb slice `coulombSlice x` of `x`;
* if `y` already lies in the Coulomb slice of `x`, then `Φ y = 0`.

The phase is the branch of zeros of the Coulomb defect `d₀* (exp (i F) · y - x)` through `(x, 0)`
given by the inverse function theorem, which is smooth because the defect is a smooth function of
the coordinates of `y` and of `F`. -/
theorem exists_isOpen_contDiffOn_coulombPhase (hk : 3 ≤ k) (x : SobolevFieldSpace f m k) :
    ∃ U : Set (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg k : (0 : ℝ) ≤ k)), IsOpen U ∧
      x.realSubRef (Nat.cast_nonneg k) ∈ U ∧
      ∃ Φ : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg k : (0 : ℝ) ≤ k)) →
          realSubmodule ℂ (zero_le_one.trans hs.le),
        ContDiffOn ℝ ∞ Φ U ∧ Φ (x.realSubRef (Nat.cast_nonneg k)) = 0 ∧
        (∀ y : SobolevFieldSpace f m k, y.realSubRef (Nat.cast_nonneg k) ∈ U →
          expGauge hs (Φ (y.realSubRef (Nat.cast_nonneg k))) • y ∈ coulombSlice x) ∧
        ∀ y : SobolevFieldSpace f m k, y.realSubRef (Nat.cast_nonneg k) ∈ U →
          y ∈ coulombSlice x → Φ (y.realSubRef (Nat.cast_nonneg k)) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hj : 1 ≤ j := by omega
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨U, hU, hxU, Φ, hΦc, hΦ0, hΦ, huniq⟩ := exists_coulombPhase x
  refine ⟨U, hU, hxU, Φ, hΦc, hΦ0, fun y hy z ↦ ?_, fun y hy hyS ↦
    huniq _ hy (coulombMap_realSubRef_zero_eq_zero hj x y (mem_coulombSlice.1 hyS))⟩
  set F := Φ (y.realSubRef (Nat.cast_nonneg (j + 2)))
  have hφ : ContDiff ℝ 2 (continuousRep F) :=
    contDiff_continuousRep
      (finrank_real_complex_add_two_mul_lt_two_mul (by push_cast; linarith)) _
  have hact : ⇑(expGauge hs F • y) = phaseGauge y (continuousRep F) := by
    rw [coe_smul, toSubgroup_expGauge]
    exact gaugeTransform_exp (hφ.differentiable two_ne_zero) y
  rw [hact]
  exact gaugeAdjoint_phaseGauge_sub_eq_zero_of_coulombMap_eq_zero hj x y (hΦ _ hy) z

variable (hs) in
/-- **Existence of the Coulomb gauge near a field.** Let `x` be a continuous field of `A_m^k`,
`k ≥ 3`. There are a neighbourhood `U` of `x` and a map `g` to the Sobolev gauge group `G_(k+1)`,
continuous on `U` with `g x = 1`, such that `g y · y` lies in the Coulomb slice `coulombSlice x`
of `x` for every `y ∈ U`: `d₀* (g y · y - x) = 0`. The gauge is `exp (i Φ)` for the smooth phase
of `exists_isOpen_contDiffOn_coulombPhase`. -/
theorem exists_mem_nhds_continuousOn_forall_smul_mem_coulombSlice (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U ∈ 𝓝 x, ∃ g : SobolevFieldSpace f m k → SobolevTopologicalGaugeGroup hs,
      ContinuousOn g U ∧ g x = 1 ∧ ∀ y ∈ U, g y • y ∈ coulombSlice x := by
  obtain ⟨U, hU, hxU, Φ, hΦc, hΦ0, hΦ, -⟩ := exists_isOpen_contDiffOn_coulombPhase hs hk x
  have hc := continuous_realSubRef (f := f) (m := m) (Nat.cast_nonneg k)
  refine ⟨realSubRef (Nat.cast_nonneg k) ⁻¹' U, hc.continuousAt.preimage_mem_nhds
    (hU.mem_nhds hxU), fun y ↦ expGauge hs (Φ (y.realSubRef (Nat.cast_nonneg k))), ?_, ?_,
    fun y hy ↦ hΦ y hy⟩
  · exact (continuous_expGauge hs).comp_continuousOn
      (hΦc.continuousOn.comp hc.continuousOn fun _ h ↦ h)
  · simp only [hΦ0]
    exact AddChar.map_zero_eq_one _

end SobolevFieldSpace

end TauCeti.Vortex
