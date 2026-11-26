/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import TauCeti.Analysis.PDE.Vortex.Divisor.JointSmooth
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import TauCeti.Analysis.PDE.Vortex.Divisor.Normalized
import TauCeti.Analysis.PDE.Vortex.FramedGauge.WindowBound

/-!
# Grafting a plane vortex into the exterior vacuum

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` represents the
connection `a = i (b₁ ds + b₂ dt)` and the section `α = 2 (p + i q)`. A cutoff `χ` interpolates
between two fields `x` and `y` by the graft `x + χ (y - x)`
(`AffineMap.lineMap (x z) (y z) (χ z)` at each point), equal to `y` where `χ = 1` and to `x` where
`χ = 0`. The vortex equation is quadratic and of first order, so its defect on the graft is exact:
with `v = y - x`,

`equation (x + χ v) = (1 - χ) equation x + χ equation y + σ(dχ) v + (χ² - χ) quadraticTerm v`

(`TauCeti.Vortex.equation_lineMap`). Here `σ = TauCeti.Vortex.linearizedEquationSymbol` is the
principal symbol of the linearized equation, the commutator of the linearized equation with
multiplication by a real function (`TauCeti.Vortex.linearizedEquation_fun_smul`). When `x` and
`y` both solve the equation, only the terms supported where `χ` is not locally constant remain:
the cutoff errors `σ(dχ) v` and `(χ² - χ) quadraticTerm v`, both controlled by `v`.

**The initial vortex graft.** For divisor coefficients `a ∈ ℂᵐ`, `m ≥ 1`, the normalized vortex
`y_a = TauCeti.Vortex.normalizedVortex a` has winding-`m` end, and the reference field
`x_ref = TauCeti.Vortex.referenceField f m` is the exterior vacuum `(-i m dθ, (z / |z|)ᵐ)` outside
a disc, where it solves the equation exactly. The graft
`TauCeti.Vortex.vortexGraft f χ a = x_ref + χ (y_a - x_ref)` replaces the vortex by this vacuum
where `χ` vanishes, and lies in every affine Sobolev space `A_m^s` when `χ` has compact support
(`TauCeti.Vortex.vortexGraft_mem_framedFieldSpace`). If `χ = 1` on the disc carrying the
reference cutoff, its equation defect is exactly the cutoff error
(`TauCeti.Vortex.equation_vortexGraft_eq`). Since `y_a - x_ref` decays like `exp (-c |z|)` for
every rate `c < 1 / 2`, uniformly over bounded windows of coefficients, so does every derivative
of the defect, with one constant for all cutoffs with bounded derivatives
(`TauCeti.Vortex.exists_norm_iteratedFDeriv_equation_vortexGraft_le_mul_exp_of_isBounded`).

For the dilated cutoff `z ↦ φ (z / R)` of a bump function `φ`, one on the closed ball of radius
`φ.rIn` and zero outside the ball of radius `φ.rOut`, the graft is the vortex on the disc of
radius `φ.rIn R` and the vacuum outside the disc of radius `φ.rOut R`, and it is an exact solution
on both (`TauCeti.Vortex.equation_vortexGraft_comp_smul_eventuallyEq_zero`). On the annulus
between them every derivative of its defect is `O(exp (-c φ.rIn R))`, uniformly over a bounded
window of coefficients
(`TauCeti.Vortex.exists_norm_iteratedFDeriv_equation_vortexGraft_comp_smul_le_mul_exp`), so the
defect is smaller than every power of `R`. This is the plane model of inserting a vortex into a
normal disc of radius `φ.rOut R`, measured in the coordinate in which the vortex has unit size.

## References

* C. H. Taubes, *Gr ⇒ SW: from pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter Metric Set Topology
open TauCeti.Polynomial
open scoped ContDiff

/-! ### The principal symbol of the linearized equation -/

/-- The principal symbol of the linearized vortex equation `d₁ = TauCeti.Vortex.linearizedEquation`,
as a bilinear map of a real covector `d` and a field value `v`: the terms of `d₁ (w v)` in the
derivative `d = dw` of a real function `w` (`TauCeti.Vortex.linearizedEquation_fun_smul`). These
are the last three rows of the symbol of the gauge-fixed operator
(`TauCeti.Vortex.gaugeFixedOperatorSymbol_apply_succ`). -/
def linearizedEquationSymbol :
    (ℂ →L[ℝ] ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap <|
    (LinearMap.toContinuousLinearMap :
        (EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) ≃ₗ[ℝ]
          (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 3))).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun (d : ℂ →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin 4)) ↦
        !₂[d I * v 0 - d 1 * v 1, d 1 * v 2 - d I * v 3, d 1 * v 3 + d I * v 2])
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp <;> ring)
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp <;> ring)
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp <;> ring)
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp <;> ring)

/-- The defining formula of `linearizedEquationSymbol`. -/
@[simp]
theorem linearizedEquationSymbol_apply (d : ℂ →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin 4)) :
    linearizedEquationSymbol d v =
      !₂[d I * v 0 - d 1 * v 1, d 1 * v 2 - d I * v 3, d 1 * v 3 + d I * v 2] :=
  (rfl)

/-- The last three rows of the symbol of the gauge-fixed operator `L_x = d₀* ⊕ d₁` are the symbol of
the linearized equation `d₁`, as the last three rows of `L_x` are
`TauCeti.Vortex.linearizedEquation`. -/
@[simp]
theorem gaugeFixedOperatorSymbol_apply_succ (d : ℂ →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin 4))
    (i : Fin 3) : gaugeFixedOperatorSymbol d v i.succ = linearizedEquationSymbol d v i := by
  fin_cases i <;> simp

/-- **The Leibniz rule of the linearized equation** for a real weight `w`, with its exact symbol
commutator: `d₁ (w y) = w d₁ y + σ(dw) y`. -/
theorem linearizedEquation_fun_smul (x : ℂ → EuclideanSpace ℝ (Fin 4))
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} {w : ℂ → ℝ} {z : ℂ}
    (hw : DifferentiableAt ℝ w z) (hy : DifferentiableAt ℝ y z) :
    linearizedEquation x (fun t ↦ w t • y t) z =
      w z • linearizedEquation x y z + linearizedEquationSymbol (fderiv ℝ w z) (y z) := by
  have hyi (i : Fin 4) : DifferentiableAt ℝ (fun t ↦ y t i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy
  have hd (i : Fin 4) (v : ℂ) :
      fderiv ℝ (fun t ↦ w t * y t i) z v =
        fderiv ℝ w z v * y z i + w z * fderiv ℝ (fun t ↦ y t i) z v := by
    rw [fderiv_fun_mul hw (hyi i)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  ext i
  fin_cases i <;>
    simp [linearizedEquation_apply_zero, linearizedEquation_apply_one,
      linearizedEquation_apply_two, hd] <;> ring

/-- The quadratic term is homogeneous of degree two under multiplication by a real function. -/
theorem quadraticTerm_fun_smul (y : ℂ → EuclideanSpace ℝ (Fin 4)) (w : ℂ → ℝ) (z : ℂ) :
    quadraticTerm (fun t ↦ w t • y t) z = w z ^ 2 • quadraticTerm y z := by
  ext i
  fin_cases i <;>
    simp [quadraticTerm_apply_zero, quadraticTerm_apply_one, quadraticTerm_apply_two] <;> ring

/-! ### The equation on a graft -/

/-- **The vortex defect of a graft.** For a cutoff `χ` and fields `x`, `y`, differentiable at
`z`, the graft `x + χ (y - x)` has defect
`(1 - χ) equation x + χ equation y + σ(dχ) (y - x) + (χ² - χ) quadraticTerm (y - x)` at `z`. -/
theorem equation_lineMap {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {χ : ℂ → ℝ} {z : ℂ}
    (hx : DifferentiableAt ℝ x z) (hy : DifferentiableAt ℝ y z) (hχ : DifferentiableAt ℝ χ z) :
    equation (fun t ↦ AffineMap.lineMap (x t) (y t) (χ t)) z =
      (1 - χ z) • equation x z + χ z • equation y z +
        linearizedEquationSymbol (fderiv ℝ χ z) (y z - x z) +
        (χ z ^ 2 - χ z) • quadraticTerm (y - x) z := by
  have hi {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : DifferentiableAt ℝ u z) (i : Fin 4) :
      DifferentiableAt ℝ (fun t ↦ u t i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hu
  have hv : DifferentiableAt ℝ (y - x) z := hy.sub hx
  have hχv : DifferentiableAt ℝ (fun t ↦ χ t • (y - x) t) z := hχ.smul hv
  have hG : (fun t ↦ AffineMap.lineMap (x t) (y t) (χ t)) =
      x + (1 : ℝ) • fun t ↦ χ t • (y - x) t := by
    ext1 t
    simp [AffineMap.lineMap_apply, add_comm]
  have hy' : y = x + (1 : ℝ) • (y - x) := by simp
  have hey : equation y z = equation x z + linearizedEquation x (y - x) z + quadraticTerm (y - x) z
      := by
    conv_lhs => rw [hy']
    simpa using equation_add_smul (hi hx) (hi hv) 1
  rw [hG, equation_add_smul (hi hx) (hi hχv), linearizedEquation_fun_smul x hχ hv,
    quadraticTerm_fun_smul, hey]
  simp only [Pi.sub_apply, one_smul, one_pow]
  module

/-! ### The initial vortex graft -/

variable {m : ℕ}

/-- **The initial vortex graft.** The normalized plane vortex `y_a` with divisor coefficients
`a ∈ ℂᵐ` (`TauCeti.Vortex.normalizedVortex`), cut off by `χ` into the reference field `x_ref`
(`TauCeti.Vortex.referenceField`), the exterior vacuum `(-i m dθ, (z / |z|)ᵐ)` of winding `m`
outside a disc: the field `x_ref + χ (y_a - x_ref)`. It is the vortex where `χ = 1`
(`TauCeti.Vortex.vortexGraft_eventuallyEq_normalizedVortex`) and the vacuum where `χ = 0`
(`TauCeti.Vortex.vortexGraft_eventuallyEq_referenceField`). -/
def vortexGraft (f : ContDiffBump (0 : ℝ)) (χ : ℂ → ℝ) (a : Fin m → ℂ) :
    ℂ → EuclideanSpace ℝ (Fin 4) :=
  fun z ↦ AffineMap.lineMap (referenceField f m z) (normalizedVortex a z) (χ z)

/-- The defining formula of `vortexGraft`. -/
theorem vortexGraft_def (f : ContDiffBump (0 : ℝ)) (χ : ℂ → ℝ) (a : Fin m → ℂ) :
    vortexGraft f χ a =
      fun z ↦ AffineMap.lineMap (referenceField f m z) (normalizedVortex a z) (χ z) :=
  (rfl)

/-- The graft at a point, as the reference field plus `χ` times the difference with the vortex. -/
theorem vortexGraft_apply (f : ContDiffBump (0 : ℝ)) (χ : ℂ → ℝ) (a : Fin m → ℂ) (z : ℂ) :
    vortexGraft f χ a z =
      referenceField f m z + χ z • (normalizedVortex a z - referenceField f m z) := by
  simp [vortexGraft_def, AffineMap.lineMap_apply, add_comm]

/-- Where the cutoff is one, the graft is the normalized vortex. -/
theorem vortexGraft_eventuallyEq_normalizedVortex (f : ContDiffBump (0 : ℝ)) {χ : ℂ → ℝ}
    (a : Fin m → ℂ) {z : ℂ} (h : χ =ᶠ[𝓝 z] 1) :
    vortexGraft f χ a =ᶠ[𝓝 z] normalizedVortex a :=
  h.mono fun w hw ↦ by simp [vortexGraft_def, hw]

/-- Where the cutoff is zero, the graft is the reference field. -/
theorem vortexGraft_eventuallyEq_referenceField (f : ContDiffBump (0 : ℝ)) {χ : ℂ → ℝ}
    (a : Fin m → ℂ) {z : ℂ} (h : χ =ᶠ[𝓝 z] 0) :
    vortexGraft f χ a =ᶠ[𝓝 z] referenceField f m :=
  h.mono fun w hw ↦ by simp [vortexGraft_def, hw]

/-- The graft is as smooth as the cutoff. -/
theorem contDiff_vortexGraft (f : ContDiffBump (0 : ℝ)) {χ : ℂ → ℝ} {n : ℕ∞}
    (hχ : ContDiff ℝ n χ) (a : Fin m → ℂ) : ContDiff ℝ n (vortexGraft f χ a) := by
  have hx : ContDiff ℝ n (referenceField f m) :=
    (contDiff_referenceField f m).of_le (mod_cast le_top)
  have hy : ContDiff ℝ n (normalizedVortex a) :=
    (contDiff_normalizedVortex a).of_le (mod_cast le_top)
  have h : vortexGraft f χ a = fun z ↦
      referenceField f m z + χ z • (normalizedVortex a z - referenceField f m z) :=
    funext (vortexGraft_apply f χ a)
  rw [h]
  exact hx.add (hχ.smul (hy.sub hx))

/-- **The graft lies in every `A_m^s`.** For a smooth compactly supported cutoff, the graft differs
from the reference field by the smooth compactly supported field `χ (y_a - x_ref)`. -/
theorem vortexGraft_mem_framedFieldSpace (f : ContDiffBump (0 : ℝ)) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcs : HasCompactSupport χ) (a : Fin m → ℂ) (s : ℝ) :
    vortexGraft f χ a ∈ framedFieldSpace f m s := by
  have h : vortexGraft f χ a - referenceField f m =
      fun z ↦ χ z • (normalizedVortex a z - referenceField f m z) := by
    ext1 z
    simp [vortexGraft_apply]
  rw [mem_framedFieldSpace, h]
  exact mem_sobolevFields_of_hasCompactSupport
    (hχ.smul ((contDiff_normalizedVortex a).sub (contDiff_referenceField f m)))
    (hcs.smul_right (f' := normalizedVortex a - referenceField f m)) s

/-- **The vortex defect of the graft.** Since the normalized vortex solves the equation, the defect
of the graft at `z` is `(1 - χ) equation x_ref + σ(dχ) v + (χ² - χ) quadraticTerm v` with
`v = y_a - x_ref`. -/
theorem equation_vortexGraft (hm : 0 < m) (f : ContDiffBump (0 : ℝ)) {χ : ℂ → ℝ}
    (a : Fin m → ℂ) {z : ℂ} (hχ : DifferentiableAt ℝ χ z) :
    equation (vortexGraft f χ a) z =
      (1 - χ z) • equation (referenceField f m) z +
        linearizedEquationSymbol (fderiv ℝ χ z) (normalizedVortex a z - referenceField f m z) +
        (χ z ^ 2 - χ z) • quadraticTerm (normalizedVortex a - referenceField f m) z := by
  rw [vortexGraft_def, equation_lineMap
    (((contDiff_referenceField f m).differentiable (by simp)) z)
    (((contDiff_normalizedVortex a).differentiable (by simp)) z) hχ,
    equation_normalizedVortex hm a z, smul_zero, add_zero]

/-- **The defect of the graft is the cutoff error.** If `χ` is differentiable and equal to one on
the disc where the reference field is not a vortex, the defect of the graft is
`σ(dχ) v + (χ² - χ) quadraticTerm v`, `v = y_a - x_ref`: it vanishes wherever `χ` is locally
constant with values in `{0, 1}`. -/
theorem equation_vortexGraft_eq (hm : 0 < m) (f : ContDiffBump (0 : ℝ)) {χ : ℂ → ℝ}
    (hχ : Differentiable ℝ χ) (h₁ : ∀ z, ‖z‖ ^ 2 ≤ f.rOut → χ z = 1) (a : Fin m → ℂ) :
    equation (vortexGraft f χ a) = fun z ↦
      linearizedEquationSymbol (fderiv ℝ χ z) (normalizedVortex a z - referenceField f m z) +
        (χ z ^ 2 - χ z) • quadraticTerm (normalizedVortex a - referenceField f m) z := by
  ext1 z
  rw [equation_vortexGraft hm f a (hχ z)]
  rcases le_or_gt (‖z‖ ^ 2) f.rOut with hz | hz
  · rw [h₁ z hz, sub_self, zero_smul, zero_add]
  · rw [equation_referenceField_eq_zero f m hz, smul_zero, zero_add]

/-! ### Uniform bounds for the cutoff error -/

/-- The polarization of `TauCeti.Vortex.quadraticTerm`, a bilinear map of two field values. -/
private def quadraticPairing :
    EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearMap.toContinuousLinearMap <|
    (LinearMap.toContinuousLinearMap :
        (EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) ≃ₗ[ℝ]
          (EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 3))).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun u v : EuclideanSpace ℝ (Fin 4) ↦
        !₂[(u 2 * v 2 + u 3 * v 3) / 2, -u 0 * v 3 - u 1 * v 2, u 0 * v 2 - u 1 * v 3])
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp <;> ring)
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp <;> ring)
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp <;> ring)
        (fun _ _ _ ↦ by ext i; fin_cases i <;> simp <;> ring)

private theorem quadraticTerm_eq_quadraticPairing (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    quadraticTerm y = fun z ↦ quadraticPairing (y z) (y z) := by
  ext z i
  fin_cases i <;>
    simp [quadraticPairing, quadraticTerm_apply_zero, quadraticTerm_apply_one,
      quadraticTerm_apply_two]
  ring

/-- The derivatives of order `i ≤ n` of `χ² - χ` at `z` are at most `2ⁿ B² + B` when those of `χ`
of order at most `n` are at most `B`. -/
private theorem norm_iteratedFDeriv_sq_sub_le {n i : ℕ} {B : ℝ} {χ : ℂ → ℝ} {z : ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hχB : ∀ j ≤ n, ‖iteratedFDeriv ℝ j χ z‖ ≤ B) (hi : i ≤ n) :
    ‖iteratedFDeriv ℝ i (fun z ↦ χ z ^ 2 - χ z) z‖ ≤ 2 ^ n * B * B + B := by
  have hsq : ‖iteratedFDeriv ℝ i (fun z ↦ χ z * χ z) z‖ ≤ 2 ^ n * B * B := by
    refine ((ContinuousLinearMap.mul ℝ ℝ).norm_iteratedFDeriv_le_of_bilinear_of_forall_le
      (hχ.of_le (mod_cast le_top)).contDiffAt (hχ.of_le (mod_cast le_top)).contDiffAt
      (fun j hj ↦ hχB j (by omega)) fun j hj ↦ hχB j (by omega)).trans ?_
    have hB : 0 ≤ B := (norm_nonneg _).trans (hχB 0 (Nat.zero_le _))
    have : (2 : ℝ) ^ i ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hi
    calc ‖ContinuousLinearMap.mul ℝ ℝ‖ * 2 ^ i * B * B ≤ 1 * 2 ^ n * B * B := by
          gcongr; exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
      _ = 2 ^ n * B * B := by ring
  simp_rw [sq]
  rw [fun_iteratedFDeriv_sub_apply ((hχ.mul hχ).of_le (mod_cast le_top)).contDiffAt
    (hχ.of_le (mod_cast le_top)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add hsq (hχB i hi))

/-- **The cutoff error is bounded by the field it cuts off.** Let `χ` be a smooth real function
whose derivatives of order at most `n + 1` are bounded by `B`, and `v` a smooth field whose
derivatives of order at most `n + 1` at `z` are bounded by `K w`, with `0 ≤ w ≤ 1`. Then the
`n`-th derivative of `σ(dχ) v + (χ² - χ) quadraticTerm v` at `z` is at most `C w`, with `C`
depending only on `n`, `B` and `K`. -/
private theorem norm_iteratedFDeriv_cutoffError_le (n : ℕ) {B : ℝ} {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχB : ∀ j ≤ n + 1, ∀ z, ‖iteratedFDeriv ℝ j χ z‖ ≤ B)
    {v : ℂ → EuclideanSpace ℝ (Fin 4)} (hv : ContDiff ℝ ∞ v) {z : ℂ} {K w : ℝ} (hw₀ : 0 ≤ w)
    (hw : w ≤ 1) (hvK : ∀ j ≤ n + 1, ‖iteratedFDeriv ℝ j v z‖ ≤ K * w) :
    ‖iteratedFDeriv ℝ n (fun z ↦ linearizedEquationSymbol (fderiv ℝ χ z) (v z) +
        (χ z ^ 2 - χ z) • quadraticTerm v z) z‖ ≤
      (‖linearizedEquationSymbol‖ * 2 ^ n * B * K +
        2 ^ n * (2 ^ n * B * B + B) * (‖quadraticPairing‖ * 2 ^ n * K ^ 2)) * w := by
  have hχ' : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right le_rfl
  have hχ₂ : ContDiff ℝ ∞ fun z ↦ χ z ^ 2 - χ z := (hχ.pow 2).sub hχ
  have hQ : ContDiff ℝ ∞ (quadraticTerm v) := by
    rw [quadraticTerm_eq_quadraticPairing]
    exact (quadraticPairing.contDiff.comp hv).clm_apply hv
  have hS : ContDiff ℝ ∞ fun z ↦ linearizedEquationSymbol (fderiv ℝ χ z) (v z) :=
    (linearizedEquationSymbol.contDiff.comp hχ').clm_apply hv
  have hT : ContDiff ℝ ∞ fun z ↦ (χ z ^ 2 - χ z) • quadraticTerm v z := hχ₂.smul hQ
  -- The symbol term, bilinear in `dχ` and `v`.
  have h₁ : ‖iteratedFDeriv ℝ n (fun z ↦ linearizedEquationSymbol (fderiv ℝ χ z) (v z)) z‖ ≤
      ‖linearizedEquationSymbol‖ * 2 ^ n * B * (K * w) :=
    linearizedEquationSymbol.norm_iteratedFDeriv_le_of_bilinear_of_forall_le
      (hχ'.of_le (mod_cast le_top)).contDiffAt (hv.of_le (mod_cast le_top)).contDiffAt
      (fun i hi ↦ by rw [norm_iteratedFDeriv_fderiv]; exact hχB (i + 1) (by omega) z)
      fun i hi ↦ hvK i (by omega)
  -- The quadratic term, bilinear in `v`, with `(K w)² ≤ K² w`.
  have hq (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (quadraticTerm v) z‖ ≤ ‖quadraticPairing‖ * 2 ^ n * K ^ 2 * w := by
    rw [quadraticTerm_eq_quadraticPairing]
    refine (quadraticPairing.norm_iteratedFDeriv_le_of_bilinear_of_forall_le
      (hv.of_le (mod_cast le_top)).contDiffAt (hv.of_le (mod_cast le_top)).contDiffAt
      (fun j hj ↦ hvK j (by omega)) fun j hj ↦ hvK j (by omega)).trans ?_
    have : (2 : ℝ) ^ i ≤ 2 ^ n := pow_le_pow_right₀ one_le_two hi
    have : K ^ 2 * (w * w) ≤ K ^ 2 * w := by gcongr; exact mul_le_of_le_one_right hw₀ hw
    calc ‖quadraticPairing‖ * 2 ^ i * (K * w) * (K * w) =
          ‖quadraticPairing‖ * 2 ^ i * (K ^ 2 * (w * w)) := by ring
      _ ≤ ‖quadraticPairing‖ * 2 ^ n * (K ^ 2 * w) := by gcongr
      _ = _ := by ring
  have hc (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun z ↦ χ z ^ 2 - χ z) z‖ ≤ 2 ^ n * B * B + B :=
    norm_iteratedFDeriv_sq_sub_le hχ (fun j hj ↦ hχB j (by omega) z) hi
  have h₂ : ‖iteratedFDeriv ℝ n (fun z ↦ (χ z ^ 2 - χ z) • quadraticTerm v z) z‖ ≤
      2 ^ n * (2 ^ n * B * B + B) * (‖quadraticPairing‖ * 2 ^ n * K ^ 2 * w) := by
    refine ((ContinuousLinearMap.lsmul ℝ ℝ).norm_iteratedFDeriv_le_of_bilinear_of_forall_le
      (hχ₂.of_le (mod_cast le_top)).contDiffAt (hQ.of_le (mod_cast le_top)).contDiffAt
      (fun i hi ↦ hc i hi) fun i hi ↦ hq i hi).trans ?_
    have hB : 0 ≤ 2 ^ n * B * B + B := (norm_nonneg _).trans (hc 0 (Nat.zero_le _))
    calc ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] _ →L[ℝ] EuclideanSpace ℝ (Fin 3))‖ * 2 ^ n *
          (2 ^ n * B * B + B) * (‖quadraticPairing‖ * 2 ^ n * K ^ 2 * w) ≤
          1 * 2 ^ n * (2 ^ n * B * B + B) * (‖quadraticPairing‖ * 2 ^ n * K ^ 2 * w) := by
          gcongr; exact ContinuousLinearMap.opNorm_lsmul_le
      _ = _ := by ring
  rw [fun_iteratedFDeriv_add_apply (hS.of_le (mod_cast le_top)).contDiffAt
    (hT.of_le (mod_cast le_top)).contDiffAt]
  refine (norm_add_le _ _).trans ((add_le_add h₁ h₂).trans_eq ?_)
  ring

/-- **Uniform exponential decay of the defect of the graft.** Let `m ≥ 1`, `S` a bounded set of
divisor coefficients, `n` an order, `c < 1 / 2` a rate and `B` a bound. There is `K ≥ 0` such that
for every smooth cutoff `χ` whose derivatives of order at most `n + 1` are bounded by `B` and which
is one on the disc `‖z‖² ≤ f.rOut` where the reference field is not a vortex, every `a ∈ S` and
every `z ∈ ℂ`, the `n`-th derivative of the vortex defect of the graft `x_ref + χ (y_a - x_ref)`
satisfies `‖Dⁿ equation (z)‖ ≤ K exp (-c |z|)`. -/
theorem exists_norm_iteratedFDeriv_equation_vortexGraft_le_mul_exp_of_isBounded (hm : 0 < m)
    (f : ContDiffBump (0 : ℝ)) {S : Set (Fin m → ℂ)} (hS : Bornology.IsBounded S) (n : ℕ)
    {c : ℝ} (hc : c < 1 / 2) (B : ℝ) :
    ∃ K, 0 ≤ K ∧ ∀ χ : ℂ → ℝ, ContDiff ℝ ∞ χ →
      (∀ j ≤ n + 1, ∀ z, ‖iteratedFDeriv ℝ j χ z‖ ≤ B) → (∀ z, ‖z‖ ^ 2 ≤ f.rOut → χ z = 1) →
      ∀ a ∈ S, ∀ z, ‖iteratedFDeriv ℝ n (equation (vortexGraft f χ a)) z‖ ≤
        K * Real.exp (-(c * ‖z‖)) := by
  -- Work with the nonnegative rate `c' = max c 0`, which gives the stronger bound.
  set c' := max c 0
  have hc' : c' < 1 / 2 := max_lt hc (by norm_num)
  -- One decay constant for `y_a - x_ref` serving every order at most `n + 1`.
  have hdecay (j : ℕ) : ∃ K, 0 ≤ K ∧ ∀ a ∈ S, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ j (normalizedVortex a - referenceField f m) z‖ ≤
        K * Real.exp (-(c' * ‖z‖)) := by
    simpa only [normalizedVortex_def] using
      exists_norm_iteratedFDeriv_gaugeTransform_sub_referenceField_le_mul_exp_of_isBounded hm f
        hS j (le_max_right c 0) hc'
  choose K hK₀ hK using hdecay
  set L := ∑ j ∈ Finset.range (n + 2), K j
  have hKL (j : ℕ) (hj : j ≤ n + 1) : K j ≤ L :=
    Finset.single_le_sum (f := K) (fun j _ ↦ hK₀ j) (Finset.mem_range.2 (by omega))
  have hL₀ : 0 ≤ L := Finset.sum_nonneg fun j _ ↦ hK₀ j
  set B' := max B 0
  refine ⟨‖linearizedEquationSymbol‖ * 2 ^ n * B' * L +
    2 ^ n * (2 ^ n * B' * B' + B') * (‖quadraticPairing‖ * 2 ^ n * L ^ 2), by positivity,
    fun χ hχ hχB h₁ a ha z ↦ ?_⟩
  rw [equation_vortexGraft_eq hm f (hχ.differentiable (by simp)) h₁ a]
  have hexp : Real.exp (-(c' * ‖z‖)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (le_max_right c 0) (norm_nonneg z)))
  refine (norm_iteratedFDeriv_cutoffError_le n hχ
    (B := B') (fun j hj z ↦ (hχB j hj z).trans (le_max_left B 0))
    ((contDiff_normalizedVortex a).sub (contDiff_referenceField f m)) (Real.exp_pos _).le
    hexp fun j hj ↦ (hK j a ha z).trans (by gcongr; exact hKL j hj)).trans ?_
  gcongr
  exact le_max_left c 0

/-! ### Dilated cutoffs -/

/-- `‖R⁻¹ • z‖ ≤ r` exactly when `‖z‖ ≤ r R`, for `R > 0`. -/
private theorem norm_inv_smul_le_iff {R r : ℝ} (hR : 0 < R) (z : ℂ) :
    ‖R⁻¹ • z‖ ≤ r ↔ ‖z‖ ≤ r * R := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR, inv_mul_le_iff₀ hR, mul_comm]

/-- **The graft with a dilated cutoff is an exact solution off an annulus.** Let `φ` be a bump
function on `ℂ`, one on the closed ball of radius `φ.rIn` and zero outside the ball of radius
`φ.rOut`, and `R > 0` with `f.rOut < (φ.rIn R)²`. For the cutoff `z ↦ φ (z / R)`, the graft is the
normalized vortex on the disc `‖z‖ < φ.rIn R` and the reference field outside the closed disc of
radius `φ.rOut R`, so near every point of either region its vortex defect vanishes. -/
theorem equation_vortexGraft_comp_smul_eventuallyEq_zero (hm : 0 < m) (f : ContDiffBump (0 : ℝ))
    (φ : ContDiffBump (0 : ℂ)) {R : ℝ} (hR : 0 < R) (hrOut : f.rOut < (φ.rIn * R) ^ 2)
    (a : Fin m → ℂ) {z : ℂ} (hz : ‖z‖ < φ.rIn * R ∨ φ.rOut * R < ‖z‖) :
    equation (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a) =ᶠ[𝓝 z] 0 := by
  rcases hz with hz | hz
  · have hU : IsOpen {w : ℂ | ‖w‖ < φ.rIn * R} := isOpen_lt continuous_norm continuous_const
    filter_upwards [hU.mem_nhds hz] with w hw
    have h₁ : (fun w ↦ φ (R⁻¹ • w)) =ᶠ[𝓝 w] 1 := by
      filter_upwards [hU.mem_nhds hw] with u hu
      exact φ.one_of_mem_closedBall (by
        rw [mem_closedBall, dist_zero_right, norm_inv_smul_le_iff hR]; exact hu.le)
    rw [Pi.zero_apply, equation_congr_nhds (vortexGraft_eventuallyEq_normalizedVortex f a h₁),
      equation_normalizedVortex hm a w]
  · have hU : IsOpen {w : ℂ | φ.rOut * R < ‖w‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hU.mem_nhds hz] with w hw
    have h₀ : (fun w ↦ φ (R⁻¹ • w)) =ᶠ[𝓝 w] 0 := by
      filter_upwards [hU.mem_nhds hw] with u hu
      refine φ.zero_of_le_dist ?_
      rw [dist_zero_right]
      by_contra h
      exact (((norm_inv_smul_le_iff hR u).1 (not_le.1 h).le).trans_lt hu).false
    have hw' : f.rOut < ‖w‖ ^ 2 := by
      have : φ.rIn * R < ‖w‖ :=
        (mul_lt_mul_of_pos_right φ.rIn_lt_rOut hR).trans hw
      exact hrOut.trans (pow_lt_pow_left₀ this (mul_pos φ.rIn_pos hR).le two_ne_zero)
    rw [Pi.zero_apply, equation_congr_nhds (vortexGraft_eventuallyEq_referenceField f a h₀),
      equation_referenceField_eq_zero f m hw']

/-- **The error of the initial vortex graft is exponentially small.** Let `m ≥ 1`, `S` a bounded
set of divisor coefficients, `φ` a bump function on `ℂ`, one on the closed ball of radius
`φ.rIn`, `n` an order and `c < 1 / 2` a rate. There is `K` such that for every `R > 0` with
`f.rOut < (φ.rIn R)²`, every `a ∈ S` and every `z ∈ ℂ`, the `n`-th derivative of the vortex
defect of the graft of `y_a` with the dilated cutoff `z ↦ φ (z / R)` satisfies
`‖Dⁿ equation (z)‖ ≤ K exp (-c φ.rIn R)`. The defect vanishes off the annulus
`φ.rIn R ≤ ‖z‖ ≤ φ.rOut R` (`TauCeti.Vortex.equation_vortexGraft_comp_smul_eventuallyEq_zero`). -/
theorem exists_norm_iteratedFDeriv_equation_vortexGraft_comp_smul_le_mul_exp (hm : 0 < m)
    (f : ContDiffBump (0 : ℝ)) (φ : ContDiffBump (0 : ℂ)) {S : Set (Fin m → ℂ)}
    (hS : Bornology.IsBounded S) (n : ℕ) {c : ℝ} (hc : c < 1 / 2) :
    ∃ K, ∀ R, 0 < R → f.rOut < (φ.rIn * R) ^ 2 → ∀ a ∈ S, ∀ z,
      ‖iteratedFDeriv ℝ n (equation (vortexGraft f (fun w ↦ φ (R⁻¹ • w)) a)) z‖ ≤
        K * Real.exp (-(c * (φ.rIn * R))) := by
  obtain ⟨C, -, hC⟩ := φ.hasCompactSupport.exists_bound_iteratedFDeriv_of_contDiff
    (n := n + 1) (𝕜 := ℝ) φ.contDiff
  -- The admissible dilations are bounded below, so `R⁻¹ ≤ M` with `M ≥ 1`.
  set M := max 1 (φ.rIn / √f.rOut)
  have hM : 1 ≤ M := le_max_left _ _
  -- Work with the nonnegative rate `max c 0`, which gives the stronger bound.
  obtain ⟨K, hK₀, hK⟩ := exists_norm_iteratedFDeriv_equation_vortexGraft_le_mul_exp_of_isBounded
    hm f hS n (max_lt hc (by norm_num : (0 : ℝ) < 1 / 2)) (M ^ (n + 1) * C)
  refine ⟨K, fun R hR₀ hrOut a ha z ↦ ?_⟩
  rcases lt_or_ge ‖z‖ (φ.rIn * R) with hz | hz
  · -- Inside the disc where the cutoff is one, the defect vanishes near `z`.
    rw [((equation_vortexGraft_comp_smul_eventuallyEq_zero hm f φ hR₀ hrOut a
      (Or.inl hz)).iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply,
      norm_zero]
    positivity
  · -- On and outside the inner circle, the window-uniform bound applies.
    have hRM : R⁻¹ ≤ M := by
      have hs : 0 < √f.rOut := Real.sqrt_pos.2 f.rOut_pos
      have : √f.rOut < φ.rIn * R := (Real.sqrt_lt' (mul_pos φ.rIn_pos hR₀)).2 hrOut
      refine le_max_of_le_right ?_
      rw [le_div_iff₀ hs, inv_mul_le_iff₀ hR₀]
      linarith
    have hχ : ContDiff ℝ ∞ fun w ↦ φ (R⁻¹ • w) := φ.contDiff.comp (contDiff_const_smul _)
    have hχB (j : ℕ) (hj : j ≤ n + 1) (w : ℂ) :
        ‖iteratedFDeriv ℝ j (fun w ↦ φ (R⁻¹ • w)) w‖ ≤ M ^ (n + 1) * C := by
      rw [iteratedFDeriv_comp_const_smul R⁻¹ (φ.contDiff (n := j)), norm_smul, norm_pow,
        Real.norm_eq_abs, abs_inv, abs_of_pos hR₀]
      exact mul_le_mul ((pow_le_pow_left₀ (by positivity) hRM j).trans (pow_le_pow_right₀ hM hj))
        (hC j hj _) (norm_nonneg _) (by positivity)
    have h₁ (w : ℂ) (hw : ‖w‖ ^ 2 ≤ f.rOut) : φ (R⁻¹ • w) = 1 := by
      refine φ.one_of_mem_closedBall ?_
      rw [mem_closedBall, dist_zero_right, norm_inv_smul_le_iff hR₀]
      by_contra h
      exact (hw.trans_lt hrOut).not_ge
        (pow_le_pow_left₀ (mul_pos φ.rIn_pos hR₀).le (le_of_not_ge h) 2)
    refine (hK _ hχ hχB h₁ a ha z).trans ?_
    have hc' : c * (φ.rIn * R) ≤ max c 0 * ‖z‖ :=
      (mul_le_mul_of_nonneg_right (le_max_left c 0) (mul_pos φ.rIn_pos hR₀).le).trans
        (mul_le_mul_of_nonneg_left hz (le_max_right c 0))
    gcongr

end TauCeti.Vortex
