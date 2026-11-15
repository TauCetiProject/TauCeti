/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EquationMap.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
public import TauCeti.Analysis.Sobolev.BesselPotential.ClosedGraph
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import TauCeti.Analysis.Distribution.TemperateGrowth
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.Schwartz
import TauCeti.Analysis.Sobolev.BesselPotential.SmoothMultiplier
import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution

/-!
# The plane vortex equation as a smooth map of Sobolev spaces

The framed degree-`m` plane vortex fields form the affine space
`A_m^(k+2) = x_m + H^(k+2)(ℂ; iT*ℂ ⊕ ℂ)` (`TauCeti.Vortex.framedFieldSpace`) about the smooth
reference field `x_m = TauCeti.Vortex.referenceField f m`. In the real coordinates
`x = (b₁, b₂, p, q)` of `TauCeti.Vortex.equation`, the equation defect of `x = x_m + y` expands
exactly as

`equation (x_m + y) = equation x_m + d₁ y + quadraticTerm y`

(`TauCeti.Vortex.equation_add_smul`), where `equation x_m` is smooth with compact support, the
linearization `d₁ = linearizedEquation x_m` combines first derivatives of `y` with products of
`y` and the bounded smooth coordinates of `x_m`, and `quadraticTerm y` is a quadratic polynomial
in the values of `y`. This file realizes the right side as a map between Bessel-potential spaces

`sobolevEquation f m k : (Fin 4 → H^(k+2)(ℂ)) → (Fin 3 → H^(k+1)(ℂ))`,

for every natural number `k`, and proves that it is smooth, with derivative the linearized
equation. The Sobolev fields are complex valued: the map is the complexification of the vortex
equation, given by the same polynomial differential expression, and on fields with real
coordinates it is the vortex equation itself
(`TauCeti.Vortex.coeFn_toLp_inclusion_sobolevEquation`).

* The constant term is the reference defect, a Schwartz function.
* The linear term `sobolevReferenceLinearization f m k` is the linearization at `x_m`, a bounded
  operator `H^(k+2) → H^(k+1)`. On tempered distributions it is a first-order differential
  operator with coefficients of bounded derivatives, which maps `H^(k+2)` into `H^(k+1)`
  (`TemperedDistribution.MemSobolev.lineDerivOp`,
  `TemperedDistribution.MemSobolev.smulLeftCLM_of_norm_iteratedFDeriv_le`). It is bounded by the
  closed graph theorem (`BesselPotentialSpace.continuous_of_continuous_toDistr`).
* The quadratic term is a bounded bilinear map `H^(k+2) × H^(k+2) → H^(k+2)` composed with the
  inclusion `H^(k+2) ⊆ H^(k+1)`, because `H^(k+2)(ℂ)` is an algebra
  (`BesselPotentialSpace.mulCLM`).

So `sobolevEquation f m k` is a polynomial of degree two in continuous multilinear maps: it is
complex analytic, in particular `C^∞` (`TauCeti.Vortex.contDiff_sobolevEquation`), and its
derivative at `Y` is `sobolevLinearizedEquation f m k Y`
(`TauCeti.Vortex.hasFDerivAt_sobolevEquation`),
which on real fields is the linearized equation at `x_m + y`
(`TauCeti.Vortex.coeFn_toLp_inclusion_sobolevLinearizedEquation`). Every field of
`A_m^(k+2)` has its Sobolev coordinates
(`TauCeti.Vortex.mem_sobolevFields_iff_exists_coeFn_toLp_inclusion`), and the
zeros of `sobolevEquation f m k` at those coordinates are exactly the `C¹` vortices
(`TauCeti.Vortex.sobolevEquation_eq_zero_iff`).

## Main definitions

* `TauCeti.Vortex.sobolevReferenceLinearization f m k`: the linearized vortex equation at the
  reference field, as a bounded operator `(Fin 4 → H^(k+2)(ℂ)) →L[ℂ] (Fin 3 → H^(k+1)(ℂ))`.
* `TauCeti.Vortex.sobolevEquation f m k`: the vortex equation in the Sobolev coordinates `y` of
  `x = x_m + y`.
* `TauCeti.Vortex.sobolevLinearizedEquation f m k Y`: its derivative at `Y`.

## Main results

* `TauCeti.Vortex.hasFDerivAt_sobolevEquation`, `TauCeti.Vortex.contDiff_sobolevEquation`: the
  equation map is smooth, with derivative the linearized equation.
* `TauCeti.Vortex.coeFn_toLp_inclusion_sobolevEquation`: on the Sobolev coordinates of a `C¹`
  field of `A_m^(k+2)`, the equation map is the vortex equation defect.
* `TauCeti.Vortex.coeFn_toLp_inclusion_sobolevLinearizedEquation`: likewise its derivative is the
  linearized equation.
* `TauCeti.Vortex.sobolevEquation_eq_zero_iff`: the zeros of the equation map are the vortices.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Module TemperedDistribution BesselPotentialSpace
open scoped ENNReal SchwartzMap LineDeriv BesselPotentialSpace ContDiff

/-! ### The reference coordinates as multipliers -/

/-- A coordinate of the reference field, as a complex multiplier. -/
private def referenceCoeff (f : ContDiffBump (0 : ℝ)) (m : ℕ) (b : Fin 4) (z : ℂ) : ℂ :=
  referenceField f m z b

private theorem contDiff_referenceCoeff (f : ContDiffBump (0 : ℝ)) (m : ℕ) (b : Fin 4) :
    ContDiff ℝ ∞ (referenceCoeff f m b) :=
  ofRealCLM.contDiff.comp (contDiff_euclidean.1 (contDiff_referenceField f m) b)

private theorem exists_norm_iteratedFDeriv_referenceCoeff_le (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (b : Fin 4) (n : ℕ) : ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (referenceCoeff f m b) z‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_referenceField_apply_le f m b n
  refine ⟨C, fun z ↦ (le_of_eq ?_).trans (hC z)⟩
  exact ofRealLI.norm_iteratedFDeriv_comp_left
    (contDiff_euclidean.1 (contDiff_referenceField f m) b).contDiffAt (by exact_mod_cast le_top)

private theorem hasTemperateGrowth_referenceCoeff (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (b : Fin 4) : (referenceCoeff f m b).HasTemperateGrowth :=
  .of_norm_iteratedFDeriv_le (contDiff_referenceCoeff f m b)
    (exists_norm_iteratedFDeriv_referenceCoeff_le f m b)

private theorem memLp_top_referenceCoeff (f : ContDiffBump (0 : ℝ)) (m : ℕ) (b : Fin 4) :
    MemLp (referenceCoeff f m b) ⊤ (volume : Measure ℂ) := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_referenceCoeff_le f m b 0
  exact memLp_top_of_bound (contDiff_referenceCoeff f m b).continuous.aestronglyMeasurable C
    (ae_of_all _ fun z ↦ by simpa using hC z)

/-! ### The linearization at the reference field -/

/-- The linearized vortex equation at the reference field, acting on tempered distributions. -/
private def distribLinearization (f : ContDiffBump (0 : ℝ)) (m : ℕ) :
    (Fin 4 → 𝓢'(ℂ, ℂ)) →L[ℂ] Fin 3 → 𝓢'(ℂ, ℂ) :=
  let d (v : ℂ) (b : Fin 4) : (Fin 4 → 𝓢'(ℂ, ℂ)) →L[ℂ] 𝓢'(ℂ, ℂ) :=
    (LineDeriv.lineDerivOpCLM ℂ 𝓢'(ℂ, ℂ) v).comp (ContinuousLinearMap.proj b)
  let c (a b : Fin 4) : (Fin 4 → 𝓢'(ℂ, ℂ)) →L[ℂ] 𝓢'(ℂ, ℂ) :=
    (smulLeftCLM ℂ (referenceCoeff f m a)).comp (ContinuousLinearMap.proj b)
  ContinuousLinearMap.pi ![d I 0 - d 1 1 + c 2 2 + c 3 3,
    d 1 2 - d I 3 - c 0 3 - c 3 0 - c 1 2 - c 2 1,
    d 1 3 + d I 2 + c 0 2 + c 2 0 - c 1 3 - c 3 1]

private theorem distribLinearization_apply_zero (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (u : Fin 4 → 𝓢'(ℂ, ℂ)) :
    distribLinearization f m u 0 = ∂_{I} (u 0) - ∂_{(1 : ℂ)} (u 1) +
      smulLeftCLM ℂ (referenceCoeff f m 2) (u 2) + smulLeftCLM ℂ (referenceCoeff f m 3) (u 3) :=
  (rfl)

private theorem distribLinearization_apply_one (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (u : Fin 4 → 𝓢'(ℂ, ℂ)) :
    distribLinearization f m u 1 = ∂_{(1 : ℂ)} (u 2) - ∂_{I} (u 3) -
      smulLeftCLM ℂ (referenceCoeff f m 0) (u 3) - smulLeftCLM ℂ (referenceCoeff f m 3) (u 0) -
      smulLeftCLM ℂ (referenceCoeff f m 1) (u 2) - smulLeftCLM ℂ (referenceCoeff f m 2) (u 1) :=
  (rfl)

private theorem distribLinearization_apply_two (f : ContDiffBump (0 : ℝ)) (m : ℕ)
    (u : Fin 4 → 𝓢'(ℂ, ℂ)) :
    distribLinearization f m u 2 = ∂_{(1 : ℂ)} (u 3) + ∂_{I} (u 2) +
      smulLeftCLM ℂ (referenceCoeff f m 0) (u 2) + smulLeftCLM ℂ (referenceCoeff f m 2) (u 0) -
      smulLeftCLM ℂ (referenceCoeff f m 1) (u 3) - smulLeftCLM ℂ (referenceCoeff f m 3) (u 1) :=
  (rfl)

/-- The linearization at the reference field maps `H^(k+2)` into `H^(k+1)`. -/
private theorem memSobolev_distribLinearization (f : ContDiffBump (0 : ℝ)) (m k : ℕ)
    {u : Fin 4 → 𝓢'(ℂ, ℂ)} (hu : ∀ b, MemSobolev ((k : ℝ) + 2) 2 (u b)) (i : Fin 3) :
    MemSobolev ((k : ℝ) + 1) 2 (distribLinearization f m u i) := by
  have hd (v : ℂ) (b : Fin 4) : MemSobolev ((k : ℝ) + 1) 2 (∂_{v} (u b)) := by
    convert (hu b).lineDerivOp (m := v) using 2
    ring
  have hc (a b : Fin 4) :
      MemSobolev ((k : ℝ) + 1) 2 (smulLeftCLM ℂ (referenceCoeff f m a) (u b)) := by
    have h := ((hu b).mono (s' := ((k + 1 : ℕ) : ℝ)) (by push_cast; linarith))
      |>.smulLeftCLM_of_norm_iteratedFDeriv_le (by norm_num) ENNReal.ofNat_ne_top
        (hasTemperateGrowth_referenceCoeff f m a)
        fun n _ ↦ exists_norm_iteratedFDeriv_referenceCoeff_le f m a n
    simpa using h
  rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl
  · rw [distribLinearization_apply_zero]
    exact (((hd _ _).sub (hd _ _)).add (hc _ _)).add (hc _ _)
  · rw [distribLinearization_apply_one]
    exact (((((hd _ _).sub (hd _ _)).sub (hc _ _)).sub (hc _ _)).sub (hc _ _)).sub (hc _ _)
  · rw [distribLinearization_apply_two]
    exact (((((hd _ _).add (hd _ _)).add (hc _ _)).add (hc _ _)).sub (hc _ _)).sub (hc _ _)

/-- A component of the linearization at the reference field, as a linear map
`H^(k+2) → H^(k+1)`. -/
private def referenceLinearizationAux (f : ContDiffBump (0 : ℝ)) (m k : ℕ) (i : Fin 3) :
    (Fin 4 → H^{(k : ℝ) + 2}(ℂ)) →ₗ[ℂ] H^{(k : ℝ) + 1}(ℂ) where
  toFun Y := (memSobolev_distribLinearization f m k
    (fun b ↦ (Y b).memSobolev_toDistr) i).toBesselPotentialSpace
  map_add' Y Y' := by
    ext1
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, Pi.add_apply, toDistr_add]
    exact congrFun (map_add (distribLinearization f m) (fun b ↦ (Y b).toDistr)
      fun b ↦ (Y' b).toDistr) i
  map_smul' c Y := by
    ext1
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, Pi.smul_apply, toDistr_smul,
      RingHom.id_apply]
    exact congrFun (map_smul (distribLinearization f m) c fun b ↦ (Y b).toDistr) i

private theorem toDistr_referenceLinearizationAux (f : ContDiffBump (0 : ℝ)) (m k : ℕ)
    (i : Fin 3) (Y : Fin 4 → H^{(k : ℝ) + 2}(ℂ)) :
    (referenceLinearizationAux f m k i Y).toDistr =
      distribLinearization f m (fun b ↦ (Y b).toDistr) i :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- **The linearized vortex equation at the reference field on the Sobolev scale.** For every
natural number `k`, the linearization `d₁ = linearizedEquation x_m` at the reference field is a
bounded operator `H^(k+2)(ℂ)⁴ → H^(k+1)(ℂ)³` on complex Sobolev fields. -/
def sobolevReferenceLinearization (f : ContDiffBump (0 : ℝ)) (m k : ℕ) :
    (Fin 4 → H^{(k : ℝ) + 2}(ℂ)) →L[ℂ] Fin 3 → H^{(k : ℝ) + 1}(ℂ) :=
  ContinuousLinearMap.pi fun i ↦
    ⟨referenceLinearizationAux f m k i, continuous_of_continuous_toDistr _ <| by
      simp_rw [toDistr_referenceLinearizationAux]
      exact (continuous_apply i).comp ((distribLinearization f m).continuous.comp
        (continuous_pi fun b ↦ continuous_toDistr.comp (continuous_apply b)))⟩

private theorem toDistr_sobolevReferenceLinearization (f : ContDiffBump (0 : ℝ)) (m k : ℕ)
    (Y : Fin 4 → H^{(k : ℝ) + 2}(ℂ)) (i : Fin 3) :
    (sobolevReferenceLinearization f m k Y i).toDistr =
      distribLinearization f m (fun b ↦ (Y b).toDistr) i :=
  toDistr_referenceLinearizationAux f m k i Y

/-! ### The quadratic term and the equation map -/

private theorem finrank_lt_two_mul_add_two (k : ℕ) :
    (finrank ℝ ℂ : ℝ) < 2 * ((k : ℝ) + 2) :=
  finrank_real_complex_lt_two_mul (by have := k.cast_nonneg (α := ℝ); linarith)

private theorem natCast_add_one_le_add_two (k : ℕ) : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by
  linarith

/-- The product of two coordinates of Sobolev fields, as a bounded bilinear map. -/
private def mulCoord (k : ℕ) (a b : Fin 4) :
    (Fin 4 → H^{(k : ℝ) + 2}(ℂ)) →L[ℂ] (Fin 4 → H^{(k : ℝ) + 2}(ℂ)) →L[ℂ]
      H^{(k : ℝ) + 2}(ℂ) :=
  (mulCLM (finrank_lt_two_mul_add_two k)).bilinearComp (ContinuousLinearMap.proj a)
    (ContinuousLinearMap.proj b)

/-- The bilinear form `B` with `B y y = quadraticTerm y`, on Sobolev fields: its components are
`(y₂ w₂ + y₃ w₃) / 2`, `-(y₀ w₃ + y₁ w₂)` and `y₀ w₂ - y₁ w₃`. -/
private def quadraticForm (k : ℕ) (i : Fin 3) :
    (Fin 4 → H^{(k : ℝ) + 2}(ℂ)) →L[ℂ] (Fin 4 → H^{(k : ℝ) + 2}(ℂ)) →L[ℂ]
      H^{(k : ℝ) + 2}(ℂ) :=
  ![(1 / 2 : ℂ) • (mulCoord k 2 2 + mulCoord k 3 3), -(mulCoord k 0 3 + mulCoord k 1 2),
    mulCoord k 0 2 - mulCoord k 1 3] i

/-- The reference defect `equation x_m`, a Schwartz function. -/
private def referenceDefect (f : ContDiffBump (0 : ℝ)) (m : ℕ) (i : Fin 3) : 𝓢(ℂ, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun z ↦ (equation (referenceField f m) z i : ℂ))
    (((hasCompactSupport_equation_referenceField f m).comp_left
      (g := fun v : EuclideanSpace ℝ (Fin 3) ↦ v i) rfl).comp_left (g := ofReal) ofReal_zero)
    (ofRealCLM.contDiff.comp (contDiff_euclidean.1 (contDiff_equation
      (contDiff_referenceField f m) ENat.coe_top_add_one.le) i))

/-- **The plane vortex equation map on the Sobolev scale.** For a natural number `k`, the vortex
equation of the field `x_m + y`, in the Sobolev coordinates `Y ∈ H^(k+2)(ℂ)⁴` of `y`:
`equation x_m + d₁ y + quadraticTerm y`, with values in `H^(k+1)(ℂ)³`. The coordinates are complex
valued; on real coordinates this is the vortex equation
(`TauCeti.Vortex.coeFn_toLp_inclusion_sobolevEquation`). -/
def sobolevEquation (f : ContDiffBump (0 : ℝ)) (m k : ℕ) (Y : Fin 4 → H^{(k : ℝ) + 2}(ℂ)) :
    Fin 3 → H^{(k : ℝ) + 1}(ℂ) := fun i ↦
  SchwartzMap.toBesselPotentialSpaceCLM _ 2 (referenceDefect f m i) +
    sobolevReferenceLinearization f m k Y i +
      inclusion (natCast_add_one_le_add_two k) (quadraticForm k i Y Y)

/-- **The linearized vortex equation on the Sobolev scale.** The derivative of
`TauCeti.Vortex.sobolevEquation f m k` at `Y`: the linearization at the reference field plus the
variation `W ↦ B Y W + B W Y` of the quadratic term. On real coordinates it is the linearized
equation at `x_m + y` (`TauCeti.Vortex.coeFn_toLp_inclusion_sobolevLinearizedEquation`). -/
def sobolevLinearizedEquation (f : ContDiffBump (0 : ℝ)) (m k : ℕ)
    (Y : Fin 4 → H^{(k : ℝ) + 2}(ℂ)) :
    (Fin 4 → H^{(k : ℝ) + 2}(ℂ)) →L[ℂ] Fin 3 → H^{(k : ℝ) + 1}(ℂ) :=
  sobolevReferenceLinearization f m k + ContinuousLinearMap.pi fun i ↦
    (inclusion (natCast_add_one_le_add_two k)).comp
      (quadraticForm k i Y + (quadraticForm k i).flip Y)

/-- The linearized equation at `Y` applied to `W`. -/
private theorem sobolevLinearizedEquation_apply (f : ContDiffBump (0 : ℝ)) (m k : ℕ)
    (Y W : Fin 4 → H^{(k : ℝ) + 2}(ℂ)) (i : Fin 3) :
    sobolevLinearizedEquation f m k Y W i = sobolevReferenceLinearization f m k W i +
      inclusion (by linarith) (quadraticForm k i Y W + quadraticForm k i W Y) :=
  (rfl)

/-- At the reference field the linearized equation is the linearization at the reference field. -/
@[simp]
theorem sobolevLinearizedEquation_zero (f : ContDiffBump (0 : ℝ)) (m k : ℕ) :
    sobolevLinearizedEquation f m k 0 = sobolevReferenceLinearization f m k := by
  ext W i : 2
  simp [sobolevLinearizedEquation_apply]

/-- **The vortex equation map is differentiable**, with derivative the linearized equation. -/
theorem hasFDerivAt_sobolevEquation (f : ContDiffBump (0 : ℝ)) (m k : ℕ)
    (Y : Fin 4 → H^{(k : ℝ) + 2}(ℂ)) :
    HasFDerivAt (sobolevEquation f m k) (sobolevLinearizedEquation f m k Y) Y := by
  refine hasFDerivAt_pi'.2 fun i ↦ ?_
  have hQ : HasFDerivAt (fun W ↦ inclusion (natCast_add_one_le_add_two k)
      (quadraticForm k i W W)) _ Y :=
    (inclusion (natCast_add_one_le_add_two k)).hasFDerivAt.comp Y
      ((quadraticForm k i).hasFDerivAt_of_bilinear (hasFDerivAt_id Y) (hasFDerivAt_id Y))
  refine (((hasFDerivAt_const (SchwartzMap.toBesselPotentialSpaceCLM ((k : ℝ) + 1) 2
    (referenceDefect f m i)) Y).add (((ContinuousLinearMap.proj i).comp
      (sobolevReferenceLinearization f m k)).hasFDerivAt)).add hQ).congr_fderiv ?_
  ext W : 1
  simp [sobolevLinearizedEquation_apply]

/-- The derivative of the vortex equation map is the linearized equation. -/
theorem fderiv_sobolevEquation (f : ContDiffBump (0 : ℝ)) (m k : ℕ)
    (Y : Fin 4 → H^{(k : ℝ) + 2}(ℂ)) :
    fderiv ℂ (sobolevEquation f m k) Y = sobolevLinearizedEquation f m k Y :=
  (hasFDerivAt_sobolevEquation f m k Y).fderiv

/-- **The vortex equation map is smooth**: it is a polynomial of degree two in bounded multilinear
maps, hence complex analytic. -/
theorem contDiff_sobolevEquation (f : ContDiffBump (0 : ℝ)) (m k : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℂ n (sobolevEquation f m k) := by
  refine contDiff_pi.2 fun i ↦ ?_
  exact (contDiff_const.add
    ((ContinuousLinearMap.proj i).comp (sobolevReferenceLinearization f m k)).contDiff).add
      ((inclusion (natCast_add_one_le_add_two k)).contDiff.comp
        ((quadraticForm k i).contDiff.clm_apply contDiff_id))

/-! ### Representation by functions -/

/-- The tempered distribution `t` is that of an `L²` function equal to `φ` almost everywhere. -/
private def IsRep (t : 𝓢'(ℂ, ℂ)) (φ : ℂ → ℂ) : Prop :=
  ∃ w : Lp ℂ 2 (volume : Measure ℂ), (w : ℂ → ℂ) =ᵐ[volume] φ ∧ (w : 𝓢'(ℂ, ℂ)) = t

private theorem IsRep.add {t t' : 𝓢'(ℂ, ℂ)} {φ φ' : ℂ → ℂ} (h : IsRep t φ) (h' : IsRep t' φ') :
    IsRep (t + t') (φ + φ') := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', rfl⟩ := h'
  exact ⟨w + w', (Lp.coeFn_add w w').trans (hw.add hw'), Lp.toTemperedDistribution_add _ _⟩

private theorem IsRep.sub {t t' : 𝓢'(ℂ, ℂ)} {φ φ' : ℂ → ℂ} (h : IsRep t φ) (h' : IsRep t' φ') :
    IsRep (t - t') (φ - φ') := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', rfl⟩ := h'
  exact ⟨w - w', (Lp.coeFn_sub w w').trans (hw.sub hw'), Lp.toTemperedDistribution_sub _ _⟩

private theorem IsRep.neg {t : 𝓢'(ℂ, ℂ)} {φ : ℂ → ℂ} (h : IsRep t φ) : IsRep (-t) (-φ) := by
  simpa using (IsRep.sub ⟨0, (Lp.coeFn_zero ..), by simp⟩ h : IsRep (0 - t) (0 - φ))

private theorem IsRep.smul {t : 𝓢'(ℂ, ℂ)} {φ : ℂ → ℂ} (h : IsRep t φ) (c : ℂ) :
    IsRep (c • t) (c • φ) := by
  obtain ⟨w, hw, rfl⟩ := h
  exact ⟨c • w, (Lp.coeFn_smul c w).trans (hw.const_smul c), Lp.toTemperedDistribution_smul _ _⟩

private theorem IsRep.congr {t : 𝓢'(ℂ, ℂ)} {φ ψ : ℂ → ℂ} (h : IsRep t φ) (hφψ : φ =ᵐ[volume] ψ) :
    IsRep t ψ :=
  let ⟨w, hw, hwt⟩ := h
  ⟨w, hw.trans hφψ, hwt⟩

private theorem isRep_of_coeFn_toLp_inclusion {s : ℝ} (hs : 0 ≤ s) {u : H^{s}(ℂ)}
    {φ : ℂ → ℂ} (h : (inclusion hs u).toLp =ᵐ[volume] φ) : IsRep u.toDistr φ :=
  ⟨_, h, toTemperedDistribution_toLp_inclusion hs u⟩

private theorem IsRep.coeFn_toLp_inclusion {s : ℝ} (hs : 0 ≤ s) {u : H^{s}(ℂ)} {φ : ℂ → ℂ}
    (h : IsRep u.toDistr φ) : (inclusion hs u).toLp =ᵐ[volume] φ := by
  obtain ⟨w, hw, hwu⟩ := h
  have : (inclusion hs u).toLp = w :=
    Lp.toTemperedDistribution_injective (by
      simp only [toTemperedDistribution_toLp_inclusion, hwu])
  rwa [this]

/-- Multiplication by a reference coordinate on represented distributions. -/
private theorem IsRep.smulLeft {t : 𝓢'(ℂ, ℂ)} {φ : ℂ → ℂ} (h : IsRep t φ)
    (f : ContDiffBump (0 : ℝ)) (m : ℕ) (b : Fin 4) :
    IsRep (smulLeftCLM ℂ (referenceCoeff f m b) t) fun z ↦ referenceCoeff f m b z * φ z := by
  obtain ⟨w, hw, rfl⟩ := h
  have hg := memLp_top_referenceCoeff f m b
  refine ⟨hg.toLp _ • w, ?_,
    Lp.toTemperedDistribution_smul_eq (hasTemperateGrowth_referenceCoeff f m b) hg w⟩
  filter_upwards [Lp.coeFn_lpSMul (r := 2) (hg.toLp _) w, hg.coeFn_toLp, hw] with z h₁ h₂ h₃
  simp only [h₁, Pi.smul_apply', h₂, h₃, smul_eq_mul]

/-- The distributional derivative of a represented `C¹` Sobolev function is represented by its
classical derivative. -/
private theorem IsRep.lineDerivOp {s : ℝ} (hs : 0 ≤ s) {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g)
    (hmem : g ∈ realSobolevFunctions ℂ (s + 1) 2) {t : 𝓢'(ℂ, ℂ)}
    (h : IsRep t fun z ↦ (g z : ℂ)) (v : ℂ) :
    IsRep (∂_{v} t) fun z ↦ (fderiv ℝ g z v : ℂ) := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨u', hu'f, -⟩ := mem_realSobolevFunctions.1
    (fderiv_apply_mem_realSobolevFunctions (by norm_num) ENNReal.ofNat_ne_top hs hg hmem v)
  set u : Lp ℝ 2 (volume : Measure ℂ) := reCLM.compLp w
  have huf : u =ᵐ[volume] g := by
    filter_upwards [reCLM.coeFn_compLp (p := 2) (μ := volume) w, hw] with z h₁ h₂
    simp [u, h₁, h₂]
  have hwu : w = ofRealCLM.compLp u := by
    refine Lp.ext ?_
    filter_upwards [ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u, huf, hw] with z h₁ h₂ h₃
    simp [h₁, h₂, h₃]
  refine ⟨ofRealCLM.compLp u', ?_, ?_⟩
  · filter_upwards [ofRealCLM.coeFn_compLp (p := 2) (μ := volume) u', hu'f] with z h₁ h₂
    simp [h₁, h₂]
  · rw [hwu, lineDerivOp_toTemperedDistribution_ofReal_eq_of_contDiff hg huf hu'f]

/-- Products of represented Sobolev functions are represented by the pointwise products. -/
private theorem IsRep.mulCLM {s : ℝ} (hs : (finrank ℝ ℂ : ℝ) < 2 * s) (h₀ : 0 ≤ s)
    {u v : H^{s}(ℂ)} {φ ψ : ℂ → ℂ} (hu : IsRep u.toDistr φ) (hv : IsRep v.toDistr ψ) :
    IsRep (mulCLM hs u v).toDistr (φ * ψ) :=
  isRep_of_coeFn_toLp_inclusion h₀ <| (coeFn_toLp_inclusion_mulCLM hs h₀ u v).trans <| by
    filter_upwards [hu.coeFn_toLp_inclusion h₀, hv.coeFn_toLp_inclusion h₀] with z h₁ h₂
    simp [h₁, h₂]

/-! ### The equation map on real fields -/

/-- The bilinear form with `bilinearTerm y y = quadraticTerm y`, pointwise. -/
private def bilinearTerm (y w : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : Fin 3 → ℝ :=
  ![(y z 2 * w z 2 + y z 3 * w z 3) / 2, -(y z 0 * w z 3 + y z 1 * w z 2),
    y z 0 * w z 2 - y z 1 * w z 3]

private theorem isRep_quadraticForm (k : ℕ) {Y W : Fin 4 → H^{(k : ℝ) + 2}(ℂ)}
    {y w : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hY : ∀ b, IsRep (Y b).toDistr fun z ↦ (y z b : ℂ))
    (hW : ∀ b, IsRep (W b).toDistr fun z ↦ (w z b : ℂ)) (i : Fin 3) :
    IsRep (quadraticForm k i Y W).toDistr fun z ↦ (bilinearTerm y w z i : ℂ) := by
  have hp (a b : Fin 4) := IsRep.mulCLM (finrank_lt_two_mul_add_two k) (by positivity) (hY a) (hW b)
  fin_cases i
  · refine (((hp 2 2).add (hp 3 3)).smul (1 / 2)).congr (.of_forall fun z ↦ ?_)
    simp [bilinearTerm]
    ring
  · refine ((hp 0 3).add (hp 1 2)).neg.congr (.of_forall fun z ↦ ?_)
    simp [bilinearTerm]
  · refine ((hp 0 2).sub (hp 1 3)).congr (.of_forall fun z ↦ ?_)
    simp [bilinearTerm]

private theorem isRep_sobolevReferenceLinearization (f : ContDiffBump (0 : ℝ)) (m k : ℕ)
    {W : Fin 4 → H^{(k : ℝ) + 2}(ℂ)} {w : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hw : w ∈ sobolevFields ((k : ℝ) + 2)) (hwc : ContDiff ℝ 1 w)
    (hW : ∀ b, IsRep (W b).toDistr fun z ↦ (w z b : ℂ)) (i : Fin 3) :
    IsRep (sobolevReferenceLinearization f m k W i).toDistr
      fun z ↦ (linearizedEquation (referenceField f m) w z i : ℂ) := by
  have hd (b : Fin 4) (v : ℂ) := (hW b).lineDerivOp (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
    (contDiff_euclidean.1 hwc b) (by convert mem_sobolevFields.1 hw b using 2; ring) v
  have hc (a b : Fin 4) := (hW b).smulLeft f m a
  rw [toDistr_sobolevReferenceLinearization]
  rcases (by decide : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2) i with rfl | rfl | rfl
  · rw [distribLinearization_apply_zero]
    refine ((((hd 0 I).sub (hd 1 1)).add (hc 2 2)).add (hc 3 3)).congr (.of_forall fun z ↦ ?_)
    simp [referenceCoeff]
  · rw [distribLinearization_apply_one]
    refine ((((((hd 2 1).sub (hd 3 I)).sub (hc 0 3)).sub (hc 3 0)).sub (hc 1 2)).sub
      (hc 2 1)).congr (.of_forall fun z ↦ ?_)
    simp [referenceCoeff]
    ring
  · rw [distribLinearization_apply_two]
    refine ((((((hd 3 1).add (hd 2 I)).add (hc 0 2)).add (hc 2 0)).sub (hc 1 3)).sub
      (hc 3 1)).congr (.of_forall fun z ↦ ?_)
    simp [referenceCoeff]
    ring

/-- **Sobolev coordinates of fields.** For `s ≥ 0`, a real field lies in `H^s` exactly when it
has complex Sobolev coordinates `Y ∈ H^s(ℂ)⁴` whose `L²` functions are its coordinates. -/
theorem mem_sobolevFields_iff_exists_coeFn_toLp_inclusion {s : ℝ} (hs : 0 ≤ s)
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} :
    y ∈ sobolevFields s ↔
      ∃ Y : Fin 4 → H^{s}(ℂ), ∀ b, (inclusion hs (Y b)).toLp =ᵐ[volume] fun z ↦ (y z b : ℂ) := by
  refine ⟨fun hy ↦ ?_, fun ⟨Y, hY⟩ ↦ mem_sobolevFields.2 fun b ↦
    mem_realSobolevFunctions_of_ae_eq_ofReal (memSobolev_toLp_inclusion hs (Y b)) (hY b)⟩
  choose u hu hmem using fun b ↦ mem_realSobolevFunctions.1 (mem_sobolevFields.1 hy b)
  refine ⟨fun b ↦ (hmem b).toBesselPotentialSpace, fun b ↦ ?_⟩
  rw [toLp_inclusion_toBesselPotentialSpace hs (hmem b) rfl]
  filter_upwards [ofRealCLM.coeFn_compLp (p := 2) (μ := volume) (u b), hu b] with z h₁ h₂
  simp [h₁, h₂]

/-- **The equation map on real fields is the vortex equation.** Let `x` be a `C¹` field and
`Y ∈ H^(k+2)(ℂ)⁴` the Sobolev coordinates of `x - x_m`, so that `x ∈ A_m^(k+2)`. Then the
components of `sobolevEquation f m k Y` are the components of the equation defect `equation x`. -/
theorem coeFn_toLp_inclusion_sobolevEquation {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hxc : ContDiff ℝ 1 x) {Y : Fin 4 → H^{(k : ℝ) + 2}(ℂ)}
    (hY : ∀ b, (inclusion (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2) (Y b)).toLp =ᵐ[volume]
      fun z ↦ ((x - referenceField f m) z b : ℂ)) (i : Fin 3) :
    (inclusion (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) (sobolevEquation f m k Y i)).toLp =ᵐ[volume]
      fun z ↦ (equation x z i : ℂ) := by
  set y := x - referenceField f m
  have hy : y ∈ sobolevFields ((k : ℝ) + 2) :=
    (mem_sobolevFields_iff_exists_coeFn_toLp_inclusion (by positivity)).2 ⟨Y, hY⟩
  have hyc : ContDiff ℝ 1 y := hxc.sub ((contDiff_referenceField f m).of_le (by simp))
  have hY' (b : Fin 4) := isRep_of_coeFn_toLp_inclusion _ (hY b)
  have hdef : IsRep (SchwartzMap.toBesselPotentialSpaceCLM ((k : ℝ) + 1) 2
      (referenceDefect f m i)).toDistr fun z ↦ (equation (referenceField f m) z i : ℂ) :=
    ⟨(referenceDefect f m i).toLp 2, (referenceDefect f m i).coeFn_toLp 2 volume, by
      rw [SchwartzMap.toDistr_toBesselPotentialSpaceCLM, Lp.toTemperedDistribution_toLp_eq]⟩
  refine IsRep.coeFn_toLp_inclusion _ ?_
  refine ((hdef.add (isRep_sobolevReferenceLinearization f m k hy hyc hY' i)).add
    (by simpa using isRep_quadraticForm k hY' hY' i)).congr (.of_forall fun z ↦ ?_)
  -- Expand the equation exactly about the reference field.
  have h := equation_add_smul (z := z)
    (fun j ↦ (contDiff_euclidean.1 (contDiff_referenceField f m) j).differentiable
      (by simp) z)
    (fun j ↦ (contDiff_euclidean.1 hyc j).differentiable one_ne_zero z) 1
  simp only [one_smul, one_pow] at h
  simp only [Pi.add_apply]
  have hxy : equation x z = equation (referenceField f m + y) z := by simp [y]
  rw [hxy, h]
  fin_cases i <;> simp [bilinearTerm, y] <;> ring

/-- **The linearized equation map on real fields.** Let `Y` be the Sobolev coordinates of
`x - x_m`, and let `W` be the Sobolev coordinates of a `C¹` variation `w`. Then the components of
`sobolevLinearizedEquation f m k Y W` are those of the linearized equation
`linearizedEquation x w`. -/
theorem coeFn_toLp_inclusion_sobolevLinearizedEquation {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} {Y : Fin 4 → H^{(k : ℝ) + 2}(ℂ)}
    (hY : ∀ b, (inclusion (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2) (Y b)).toLp =ᵐ[volume]
      fun z ↦ ((x - referenceField f m) z b : ℂ))
    {w : ℂ → EuclideanSpace ℝ (Fin 4)} (hwc : ContDiff ℝ 1 w) {W : Fin 4 → H^{(k : ℝ) + 2}(ℂ)}
    (hW : ∀ b, (inclusion (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2) (W b)).toLp =ᵐ[volume]
      fun z ↦ (w z b : ℂ))
    (i : Fin 3) :
    (inclusion (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
      (sobolevLinearizedEquation f m k Y W i)).toLp =ᵐ[volume]
      fun z ↦ (linearizedEquation x w z i : ℂ) := by
  have hY' (b : Fin 4) := isRep_of_coeFn_toLp_inclusion _ (hY b)
  have hW' (b : Fin 4) := isRep_of_coeFn_toLp_inclusion _ (hW b)
  have hw : w ∈ sobolevFields ((k : ℝ) + 2) :=
    (mem_sobolevFields_iff_exists_coeFn_toLp_inclusion (by positivity)).2 ⟨W, hW⟩
  refine IsRep.coeFn_toLp_inclusion _ ?_
  rw [sobolevLinearizedEquation_apply, toDistr_add, toDistr_inclusion, toDistr_add]
  refine ((isRep_sobolevReferenceLinearization f m k hw hwc hW' i).add
    ((isRep_quadraticForm k hY' hW' i).add (isRep_quadraticForm k hW' hY' i))).congr
      (.of_forall fun z ↦ ?_)
  fin_cases i <;> simp [bilinearTerm] <;> ring

/-- **The zeros of the equation map are the vortices.** Let `x` be a `C¹` field and `Y` the
Sobolev coordinates of `x - x_m`. Then `sobolevEquation f m k Y = 0` exactly when `x`
solves the vortex equations everywhere. -/
theorem sobolevEquation_eq_zero_iff {f : ContDiffBump (0 : ℝ)} {m k : ℕ}
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hxc : ContDiff ℝ 1 x) {Y : Fin 4 → H^{(k : ℝ) + 2}(ℂ)}
    (hY : ∀ b, (inclusion (by positivity : (0 : ℝ) ≤ (k : ℝ) + 2) (Y b)).toLp =ᵐ[volume]
      fun z ↦ ((x - referenceField f m) z b : ℂ)) :
    sobolevEquation f m k Y = 0 ↔ equation x = 0 := by
  have hrep := coeFn_toLp_inclusion_sobolevEquation hxc hY
  have hcont (i : Fin 3) : Continuous fun z ↦ (equation x z i : ℂ) :=
    continuous_ofReal.comp
      ((contDiff_euclidean.1 (contDiff_equation (m := 0) hxc (by simp))) i).continuous
  constructor
  · intro h
    ext z i
    have hae : (fun z ↦ (equation x z i : ℂ)) =ᵐ[volume] 0 := by
      refine (hrep i).symm.trans ?_
      rw [h, Pi.zero_apply, map_zero, toLp_zero]
      exact Lp.coeFn_zero ..
    simpa using congrFun ((hcont i).ae_eq_iff_eq volume continuous_zero |>.1 hae) z
  · intro h
    funext i
    refine toLp_inclusion_injective (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1) ?_
    refine Lp.ext ((hrep i).trans ?_)
    simp only [Pi.zero_apply, map_zero, toLp_zero]
    have h0 : (fun z ↦ (equation x z i : ℂ)) = 0 := funext fun z ↦ by simp [h]
    rw [h0]
    exact (Lp.coeFn_zero ..).symm

end TauCeti.Vortex
