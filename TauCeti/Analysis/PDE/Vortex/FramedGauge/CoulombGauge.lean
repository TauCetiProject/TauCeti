/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Chart
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Quotient
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.Vortex.FramedGauge.RealChart
import TauCeti.Analysis.PDE.Vortex.Gauge.Laplacian
import TauCeti.Analysis.PDE.Vortex.Gauge.Sobolev
import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Real
import TauCeti.Analysis.Sobolev.BesselPotential.Trigonometric

/-!
# Existence of the Coulomb gauge near a framed plane vortex field

For an integer `k ≥ 3`, the Sobolev framed gauge group `G_(k+1)`
(`TauCeti.Vortex.SobolevTopologicalGaugeGroup`) acts on the continuous fields of the affine space
`A_m^k = x_m + H^k(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.SobolevFieldSpace`). At a field `x` the Coulomb
slice is cut out by the gauge-fixing condition `d₀* (y - x) = 0`, with `d₀* = gaugeAdjoint x` the
formal `L²` adjoint of the infinitesimal gauge action at `x`.

This file proves the existence half of the slice theorem at `x`: every field `y` near `x` is moved
into the Coulomb slice of `x` by a gauge `g y` near `1`, depending continuously on `y`
(`SobolevFieldSpace.exists_mem_nhds_continuousOn_forall_gaugeAdjoint_smul_sub_eq_zero`).
The uniqueness half, that the slice meets each nearby orbit only once near `1`, is not treated here;
together the two halves give the slice charts of the quotient `A_m^k / G_(k+1)` near `x`.

**The equation.** Write `x = (b₁, b₂, p, q)`. For a real phase `f`, the Coulomb defect of the gauge
transform `e^{if} y` (`TauCeti.Vortex.phaseGauge`) is

`d₀* (e^{if} y - x) = d₀* (y - x) - Δf + sin f (p y₂ + q y₃) + (cos f - 1) (p y₃ - q y₂)`.

At `y = x` its linearization in `f` is the gauge Laplacian `d₀* d₀ f = -Δf + (p² + q²) f`, which is
an isomorphism `H^(k+1) → H^(k-1)` (`TauCeti.Vortex.sobolevGaugeLaplacianEquiv`).

**The inverse function theorem.** In the real chart of `A_m^k`
(`TauCeti.Vortex.SobolevFieldSpace.realSubRefHomeomorph`) the defect is a map
`(H^k_ℝ)⁴ × H^(k+1)_ℝ → H^(k-1)_ℝ`: the linear part `d₀* (y - x) + d₀* d₀ f` plus a remainder built
from products in the algebra `H^k(ℂ)` and from `sin f - f` and `cos f - 1`, which vanish to second
order at `f = 0` (`BesselPotentialSpace.hasStrictFDerivAt_sinSubSelf_zero`,
`BesselPotentialSpace.hasStrictFDerivAt_cosSubOne_zero`). So the defect is strictly differentiable
at `(x, 0)` with derivative `(v, φ) ↦ d₀* v + d₀* d₀ φ`, and `(y, f) ↦ (y, d₀* (e^{if} y - x))` has
an invertible strict derivative there. The inverse function theorem gives a continuous branch of
zeros `y ↦ (y, f(y))` with `f(x) = 0`, and `g y = exp (i f(y))`.

**From the Sobolev identity to every point.** The identity in `H^(k-1)` computes the defect almost
everywhere. Its gauge Laplacian term is the classical `d₀* d₀ f` by the weak equation of
`sobolevGaugeLaplacianEquiv` (`TauCeti.Vortex.gaugeAdjoint_gaugeDirection_eq_of_integral_mul_eq`),
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
open scoped Laplacian ContDiff BesselPotentialSpace

/-! ### The Coulomb defect of a phase gauge transformation -/

/-- The Coulomb defect at `x = (b₁, b₂, p, q)` of the gauge transform `e^{iF} y`:
`d₀* (e^{iF} y) = d₀* y - ΔF + sin F (p y₂ + q y₃) + (cos F - 1) (p y₃ - q y₂)`. -/
private theorem gaugeAdjoint_phaseGauge (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} {F : ℂ → ℝ} {z : ℂ}
    (hy₀ : DifferentiableAt ℝ (fun w ↦ y w 0) z) (hy₁ : DifferentiableAt ℝ (fun w ↦ y w 1) z)
    (hF : ContDiffAt ℝ 2 F z) :
    gaugeAdjoint x (phaseGauge y F) z = gaugeAdjoint x y z - Δ F z +
      Real.sin (F z) * (x z 2 * y z 2 + x z 3 * y z 3) +
        (Real.cos (F z) - 1) * (x z 2 * y z 3 - x z 3 * y z 2) := by
  have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd (v : ℂ) : DifferentiableAt ℝ (fun w ↦ fderiv ℝ F w v) z :=
    hdf.clm_apply (differentiableAt_const v)
  simp only [gaugeAdjoint_def, phaseGauge_apply_zero, phaseGauge_apply_one,
    phaseGauge_apply_two, phaseGauge_apply_three]
  rw [fderiv_fun_sub hy₀ (hd 1), fderiv_fun_sub hy₁ (hd Complex.I),
    laplacian_eq_sum_fderiv_fderiv_apply Complex.orthonormalBasisOneI hdf]
  simp only [Fin.isValue, sub_apply, Complex.coe_orthonormalBasisOneI,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ### The gauge Laplacian on the real Sobolev scale -/

section GaugeLaplacian

variable {f : ContDiffBump (0 : ℝ)} {m j : ℕ}

private theorem natCast_add_two_add_one (j : ℕ) :
    ((j + 2 : ℕ) : ℝ) + 1 = ((j + 1 + 2 : ℕ) : ℝ) := by
  push_cast
  ring

/-- **The gauge Laplacian on real phases.** At a continuous field `x` of `A_m^(j+2)`, the gauge
Laplacian `d₀* d₀ = -Δ + (p² + q²)` as a continuous real-linear isomorphism from the real elements
of `H^(j+3)(ℂ)` onto those of `H^(j+1)(ℂ)`: the isomorphism `sobolevGaugeLaplacianEquiv` of the
weak-derivative Sobolev spaces, read through `TauCeti.Wkp.toRealSubmodule`. -/
private def realGaugeLaplacian (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    realSubmodule ℂ (by positivity : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ) + 1) ≃L[ℝ]
      realSubmodule ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ)) :=
  (realSubmoduleCongr ℂ (natCast_add_two_add_one j) _ (Nat.cast_nonneg _)).trans <|
    (Wkp.toRealSubmodule (E := ℂ) (j + 1 + 2)).symm.trans <|
      (sobolevGaugeLaplacianEquiv (k := j + 2) (j := j + 1) (by omega) (by omega)
        x.mem_framedFieldSpace x.continuous).trans (Wkp.toRealSubmodule (E := ℂ) (j + 1))

/-- **The weak equation of the real gauge Laplacian**: if `d₀* d₀ F = G`, then
`∫ F · d₀* d₀ φ = ∫ G φ` for the continuous representatives and every smooth compactly supported
`φ`. -/
private theorem integral_mul_gaugeAdjoint_gaugeDirection_eq_of_realGaugeLaplacian_eq
    (hj : 1 ≤ j) (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) {F G}
    (hFG : realGaugeLaplacian x F = G)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, continuousRep F z * gaugeAdjoint x (gaugeDirection x φ) z =
      ∫ z, continuousRep G z * φ z := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hd (n : ℕ) (hn : 2 ≤ n) : (finrank ℝ ℂ : ℝ) < 2 * (n : ℝ) := by
    rw [Complex.finrank_real_complex]
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    linarith
  set w := (Wkp.toRealSubmodule (E := ℂ) (j + 1 + 2)).symm
    (realSubmoduleCongr ℂ (natCast_add_two_add_one j) _ (Nat.cast_nonneg _) F)
  have hL : sobolevGaugeLaplacianEquiv (k := j + 2) (j := j + 1) (by omega) (by omega)
      x.mem_framedFieldSpace x.continuous w = (Wkp.toRealSubmodule (E := ℂ) (j + 1)).symm G := by
    rw [ContinuousLinearEquiv.eq_symm_apply]
    exact hFG
  have hweak := (sobolevGaugeLaplacianEquiv_eq_iff _ _ _ _).1 hL φ hφ hc
  -- The values of the Sobolev functions are the continuous representatives.
  have hw : (Wkp.value (j + 1 + 2) w : ℂ → ℝ) =ᵐ[volume] continuousRep F := by
    have h := Wkp.value_ae_eq_continuousRep_toRealSubmodule (hd _ (by omega)) w
    rwa [ContinuousLinearEquiv.apply_symm_apply, continuousRep_realSubmoduleCongr
      (finrank_real_complex_lt_two_mul (by push_cast; linarith))] at h
  have hg : (Wkp.value (j + 1) ((Wkp.toRealSubmodule (E := ℂ) (j + 1)).symm G) : ℂ → ℝ)
      =ᵐ[volume] continuousRep G := by
    have h := Wkp.value_ae_eq_continuousRep_toRealSubmodule (hd _ (by omega))
      ((Wkp.toRealSubmodule (E := ℂ) (j + 1)).symm G)
    rwa [ContinuousLinearEquiv.apply_symm_apply] at h
  calc ∫ z, continuousRep F z * gaugeAdjoint x (gaugeDirection x φ) z
      = ∫ z, Wkp.value (j + 1 + 2) w z * gaugeAdjoint x (gaugeDirection x φ) z :=
        integral_congr_ae (hw.mono fun z hz ↦ by dsimp only; rw [hz])
    _ = _ := hweak
    _ = ∫ z, continuousRep G z * φ z :=
        integral_congr_ae (hg.mono fun z hz ↦ by dsimp only; rw [hz])

end GaugeLaplacian

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

/-- The scalar tower `ℝ → ℂ → H^s(ℂ)`. Instance search does not find it: the real action on
`H^s(ℂ)` comes from its complex normed space structure, and agrees with the action restricted
from `ℂ` only up to definitional unfolding, which closes the last step. -/
private theorem isScalarTower_real_complex (s : ℝ) : IsScalarTower ℝ ℂ H^{s}(ℂ) :=
  ⟨fun r c v ↦ by rw [Complex.real_smul, mul_smul, Complex.coe_smul]; rfl⟩

attribute [local instance] isScalarTower_real_complex

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
  let S := phaseW j (sinSubSelf _ (finrank_lt_two_mul_natCast_add_two_add_one j) p.2)
  let C := phaseW j (cosSubOne _ (finrank_lt_two_mul_natCast_add_two_add_one j) p.2)
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
    inclusion (lt_add_one _).le (coulombNonlinear x p)) + realGaugeLaplacian x p.2

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
  have hsP := finrank_lt_two_mul_natCast_add_two_add_one j
  -- The phase, its sine and cosine remainders, and the Coulomb pairing of `y - x`.
  have hF : HasStrictFDerivAt (fun p : V × P ↦ phaseW j p.2)
      ((phaseW j).comp (ContinuousLinearMap.snd ℝ V P)) p₀ :=
    ((phaseW j).comp (ContinuousLinearMap.snd ℝ V P)).hasStrictFDerivAt
  have hS : HasStrictFDerivAt (fun p : V × P ↦ phaseW j (sinSubSelf _ hsP p.2))
      (0 : V × P →L[ℝ] W) p₀ := by
    simpa using (phaseW j).hasStrictFDerivAt.comp p₀
      ((hasStrictFDerivAt_sinSubSelf_zero hsP).comp p₀ hasStrictFDerivAt_snd)
  have hC : HasStrictFDerivAt (fun p : V × P ↦ phaseW j (cosSubOne _ hsP p.2))
      (0 : V × P →L[ℝ] W) p₀ := by
    simpa using (phaseW j).hasStrictFDerivAt.comp p₀
      ((hasStrictFDerivAt_cosSubOne_zero hsP).comp p₀ hasStrictFDerivAt_snd)
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
  have hS0 : phaseW j (sinSubSelf _ hsP (p₀.2)) = 0 := by simp [p₀]
  have hC0 : phaseW j (cosSubOne _ hsP (p₀.2)) = 0 := by simp [p₀]
  have key := ((((h₁.add (hasStrictFDerivAt_fieldMul_add_mulR x 2 2 hS hS0)).add
    (hasStrictFDerivAt_fieldMul_add_mulR x 3 3 hS hS0)).add
      (hasStrictFDerivAt_fieldMul_add_mulR x 2 3 hC hC0)).sub
        (hasStrictFDerivAt_fieldMul_add_mulR x 3 2 hC hC0))
  simp only [add_zero, sub_zero] at key
  exact key

/-- **The strict derivative of the Coulomb map** at `(x, 0)`: `(v, G) ↦ d₀* v + d₀* d₀ G`. -/
private theorem hasStrictFDerivAt_coulombMap (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    HasStrictFDerivAt (coulombMap x)
      ((coulombFieldDeriv x).comp (ContinuousLinearMap.fst ℝ _ _) +
        ((realGaugeLaplacian x : realSubmodule ℂ (natCast_add_two_add_one_nonneg j) →L[ℝ]
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
  have hT := ((realGaugeLaplacian x : P →L[ℝ]
    realSubmodule ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))).comp
      (ContinuousLinearMap.snd ℝ V P)).hasStrictFDerivAt (x := p₀)
  -- The definition of `coulombMap x`, with the abbreviations of this proof.
  have hfun : coulombMap x = fun p : V × P ↦ realPartCLM ℂ _ (D (coordW j p.1 - ξ) +
      inclusion (lt_add_one ((j + 1 : ℕ) : ℝ)).le (coulombNonlinear x p)) +
        realGaugeLaplacian x p.2 :=
    rfl
  rw [hfun]
  refine (hR.add hT).congr_fderiv (ContinuousLinearMap.ext fun p ↦ ?_)
  simp [coulombFieldDeriv, D, ξ]

/-- **The Coulomb phase.** Near the real coordinates of a continuous field `x` of `A_m^(j+2)`, the
Coulomb map has a continuous branch of zeros `u ↦ (u, Φ u)` through `(x, 0)`. This is the inverse
function theorem for `(u, F) ↦ (u, coulombMap x (u, F))`, whose derivative at `(x, 0)` is
invertible because the gauge Laplacian is (`realGaugeLaplacian`). -/
private theorem exists_coulombPhase (x : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ)) :
    ∃ U ∈ 𝓝 (x.realSubRef (Nat.cast_nonneg (j + 2))),
      ∃ Φ : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))) →
        realSubmodule ℂ (natCast_add_two_add_one_nonneg j),
      ContinuousOn Φ U ∧ Φ (x.realSubRef _) = 0 ∧ ∀ u ∈ U, coulombMap x (u, Φ u) = 0 := by
  set V := Fin 4 → realSubmodule ℂ (Nat.cast_nonneg (j + 2) : (0 : ℝ) ≤ ((j + 2 : ℕ) : ℝ))
  set P := realSubmodule ℂ (natCast_add_two_add_one_nonneg j)
  set T := realSubmodule ℂ (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ))
  set p₀ : V × P := (x.realSubRef _, 0)
  set e : (V × P) ≃L[ℝ] V × T :=
    (ContinuousLinearEquiv.refl ℝ V).skewProd (realGaugeLaplacian x) (coulombFieldDeriv x)
  set Ψ : V × P → V × T := fun p ↦ (p.1, coulombMap x p)
  have hΨ : HasStrictFDerivAt Ψ (e : V × P →L[ℝ] V × T) p₀ := by
    refine (hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_coulombMap x)).congr_fderiv
      (ContinuousLinearMap.ext fun p ↦ ?_)
    simp [e, add_comm]
  set H := hΨ.toOpenPartialHomeomorph Ψ
  set q₀ : V × T := (x.realSubRef _, 0)
  have hΨ₀ : Ψ p₀ = q₀ := Prod.ext rfl (coulombMap_self x)
  have hmem : q₀ ∈ H.target := hΨ₀ ▸ hΨ.image_mem_toOpenPartialHomeomorph_target
  have hι : Continuous fun u : V ↦ ((u, 0) : V × T) := continuous_id.prodMk continuous_const
  refine ⟨(fun u : V ↦ ((u, 0) : V × T)) ⁻¹' H.target,
    hι.continuousAt.preimage_mem_nhds (H.open_target.mem_nhds hmem),
    fun u ↦ (H.symm (u, 0)).2, ?_, ?_, fun u hu ↦ ?_⟩
  · exact continuous_snd.comp_continuousOn
      (H.continuousOn_symm.comp hι.continuousOn fun _ hu ↦ hu)
  · have h : H.symm q₀ = p₀ := by
      rw [← hΨ₀]
      exact H.left_inv hΨ.mem_toOpenPartialHomeomorph_source
    exact congrArg Prod.snd h
  · -- `H` is `Ψ` as a function (`HasStrictFDerivAt.toOpenPartialHomeomorph_coe`).
    have h := H.right_inv hu
    have h₁ : (H.symm (u, 0)).1 = u := congrArg Prod.fst h
    have h₂ : coulombMap x (H.symm (u, 0)) = 0 := congrArg Prod.snd h
    rwa [show H.symm (u, 0) = (u, (H.symm (u, 0)).2) from Prod.ext h₁ rfl] at h₂

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
  have hdiff (a : Fin 4) : ⇑(inclusionLp h0W ((coordW j u - ξ) a)) =ᵐ[volume]
      fun z ↦ (((⇑y - ⇑x) z a : ℝ) : ℂ) := by
    filter_upwards [coeFn_inclusionLp_sub_ae_eq h0W (coeFn_inclusionLp_coordW y a)
      (coeFn_inclusionLp_coordW x a)] with z hz
    rw [Pi.sub_apply, hz]
    simp
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
  have hS : ⇑(inclusionLp h0W (phaseW j (sinSubSelf _ hsP F))) =ᵐ[volume]
      fun z ↦ ((Real.sin (continuousRep F z) - continuousRep F z : ℝ) : ℂ) := by
    simpa [phaseW, inclusionLp_inclusion] using coeFn_inclusionLp_sinSubSelf hsP F
  have hC : ⇑(inclusionLp h0W (phaseW j (cosSubOne _ hsP F))) =ᵐ[volume]
      fun z ↦ ((Real.cos (continuousRep F z) - 1 : ℝ) : ℂ) := by
    simpa [phaseW, inclusionLp_inclusion] using coeFn_inclusionLp_cosSubOne hsP F
  have hpair : ⇑(inclusionLp h0W (sectionPairing (f := f) (m := m) ξ (coordW j u - ξ)))
      =ᵐ[volume] fun z ↦ ((x z 2 * (y z 2 - x z 2) + x z 3 * (y z 3 - x z 3) : ℝ) : ℂ) := by
    filter_upwards [coeFn_inclusionLp_add_ae_eq h0W (coeFn_inclusionLp_fieldMul_coordW x 2
      (hdiff 2)) (coeFn_inclusionLp_fieldMul_coordW x 3 (hdiff 3))] with z hz
    -- `sectionPairing ξ v` is `x₂ v₂ + x₃ v₃` by definition.
    rw [show sectionPairing (f := f) (m := m) ξ (coordW j u - ξ) =
      fieldMulOrderPreservingCLM f m (by omega) ξ 2 ((coordW j u - ξ) 2) +
        fieldMulOrderPreservingCLM f m (by omega) ξ 3 ((coordW j u - ξ) 3) from rfl, hz]
    simp
  have h := coeFn_inclusionLp_sub_ae_eq h0W (coeFn_inclusionLp_add_ae_eq h0W
    (coeFn_inclusionLp_add_ae_eq h0W (coeFn_inclusionLp_add_ae_eq h0W
      (coeFn_inclusionLp_mulR hF hpair) (coeFn_inclusionLp_fieldMul_coordW x 2 (hY 2 hS)))
        (coeFn_inclusionLp_fieldMul_coordW x 3 (hY 3 hS)))
          (coeFn_inclusionLp_fieldMul_coordW x 2 (hY 3 hC)))
            (coeFn_inclusionLp_fieldMul_coordW x 3 (hY 2 hC))
  -- `h` is about the definition of `coulombNonlinear x (y, F)` unfolded.
  refine h.trans (Eventually.of_forall fun z ↦ ?_)
  push_cast
  ring

/-- **The Coulomb map computes the Coulomb defect.** For continuous fields `x, y` of `A_m^(j+2)`,
`j ≥ 1`, and a real phase `F` with continuous representative `f`, the `L²` function of
`coulombMap x (y, F)` is almost everywhere
`d₀* (y - x) - (p² + q²) f + sin f (p y₂ + q y₃) + (cos f - 1) (p y₃ - q y₂) + d₀* d₀ F`, where
`x = (b₁, b₂, p, q)` and the last term is the continuous representative of
`realGaugeLaplacian x F`. -/
private theorem coeFn_inclusionLp_coulombMap (hj : 1 ≤ j)
    (x y : SobolevFieldSpace f m ((j + 2 : ℕ) : ℝ))
    (F : realSubmodule ℂ (natCast_add_two_add_one_nonneg j)) :
    ⇑(inclusionLp (Nat.cast_nonneg (j + 1))
        (coulombMap x (y.realSubRef (Nat.cast_nonneg (j + 2)), F) : H^{((j + 1 : ℕ) : ℝ)}(ℂ)))
      =ᵐ[volume] fun z ↦ ((gaugeAdjoint x (⇑y - ⇑x) z -
        (x z 2 ^ 2 + x z 3 ^ 2) * continuousRep F z +
        Real.sin (continuousRep F z) * (x z 2 * y z 2 + x z 3 * y z 3) +
        (Real.cos (continuousRep F z) - 1) * (x z 2 * y z 3 - x z 3 * y z 2) +
        continuousRep (realGaugeLaplacian x F) z : ℝ) : ℂ) := by
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
    have hdiff (a : Fin 4) : ⇑(inclusionLp (natCast_succ_add_one_nonneg j) ((coordW j u - ξ) a))
        =ᵐ[volume] fun z ↦ (((⇑y - ⇑x) z a : ℝ) : ℂ) := by
      filter_upwards [coeFn_inclusionLp_sub_ae_eq (natCast_succ_add_one_nonneg j)
        (coeFn_inclusionLp_coordW y a) (coeFn_inclusionLp_coordW x a)] with z hz
      rw [Pi.sub_apply, hz]
      simp
    have h := coeFn_inclusionLp_sobolevGaugeAdjoint_ae_eq (f := f) (m := m) hj'
      (coeFn_inclusionLp_coordW x) hdiff (hc 0) (hc 1)
    rwa [add_sub_cancel] at h
  -- The nonlinear part, the real part and the gauge Laplacian.
  have hlin := coeFn_inclusionLp_add_ae_eq (Nat.cast_nonneg (j + 1)) hA
    ((inclusionLp_inclusion (lt_add_one ((j + 1 : ℕ) : ℝ)).le (Nat.cast_nonneg (j + 1))
      (coulombNonlinear x (u, F))).symm ▸ coeFn_inclusionLp_coulombNonlinear x y F)
  have hre := coeFn_inclusionLp_realPartCLM (h := (Nat.cast_nonneg (j + 1) : (0 : ℝ) ≤ _))
    (sobolevGaugeAdjoint f m hj' ξ (coordW j u - ξ) +
      inclusion (lt_add_one ((j + 1 : ℕ) : ℝ)).le (coulombNonlinear x (u, F)))
  have hsum := coeFn_inclusionLp_add_ae_eq (Nat.cast_nonneg (j + 1)) hre
    (coeFn_inclusionLp_ae_eq_continuousRep hd2 (realGaugeLaplacian x F))
  -- `hsum` is about the definition of `coulombMap x (y, F)` unfolded.
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
    contDiff_continuousRep (by rw [Complex.finrank_real_complex]; push_cast; linarith) F
  set φ := continuousRep F
  set G := realGaugeLaplacian x F
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
      (fun ψ hψ hc ↦ integral_mul_gaugeAdjoint_gaugeDirection_eq_of_realGaugeLaplacian_eq hj x
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

end CoulombMap

/-! ### Existence of the Coulomb gauge -/

namespace SobolevFieldSpace

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ} [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

variable (hs) in
/-- **Existence of the Coulomb gauge near a field.** Let `x` be a continuous field of `A_m^k`,
`k ≥ 3`. There are a neighbourhood `U` of `x` and a map `g` to the Sobolev gauge group `G_(k+1)`,
continuous on `U` with `g x = 1`, such that `g y · y` lies in the Coulomb slice of `x` for every
`y ∈ U`: `d₀* (g y · y - x) = 0`. -/
theorem exists_mem_nhds_continuousOn_forall_gaugeAdjoint_smul_sub_eq_zero (hk : 3 ≤ k)
    (x : SobolevFieldSpace f m k) :
    ∃ U ∈ 𝓝 x, ∃ g : SobolevFieldSpace f m k → SobolevTopologicalGaugeGroup hs,
      ContinuousOn g U ∧ g x = 1 ∧ ∀ y ∈ U, ∀ z, gaugeAdjoint x (⇑(g y • y) - ⇑x) z = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hj : 1 ≤ j := by omega
  have hs₀ : 1 < ((j + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨U, hU, Φ, hΦc, hΦ0, hΦ⟩ := exists_coulombPhase x
  have hc : Continuous (realSubRef (f := f) (m := m) (Nat.cast_nonneg (j + 2))) := by
    simpa using
      (realSubRefHomeomorph (f := f) (m := m) hs₀ (h := Nat.cast_nonneg (j + 2))).continuous
  refine ⟨realSubRef (Nat.cast_nonneg (j + 2)) ⁻¹' U, hc.continuousAt.preimage_mem_nhds hU,
    fun y ↦ expGauge hs (Φ (y.realSubRef (Nat.cast_nonneg (j + 2)))), ?_, ?_, fun y hy z ↦ ?_⟩
  · exact (continuous_expGauge hs).comp_continuousOn (hΦc.comp hc.continuousOn fun _ h ↦ h)
  · simp only [hΦ0]
    exact AddChar.map_zero_eq_one _
  · set F := Φ (y.realSubRef (Nat.cast_nonneg (j + 2)))
    have hφ : ContDiff ℝ 2 (continuousRep F) :=
      contDiff_continuousRep (by rw [Complex.finrank_real_complex]; push_cast; linarith) _
    have hact : ⇑(expGauge hs F • y) = phaseGauge y (continuousRep F) := by
      rw [coe_smul, toSubgroup_expGauge]
      exact gaugeTransform_exp (hφ.differentiable two_ne_zero) y
    rw [hact]
    exact gaugeAdjoint_phaseGauge_sub_eq_zero_of_coulombMap_eq_zero hj x y (hΦ _ hy) z

end SobolevFieldSpace

end TauCeti.Vortex
