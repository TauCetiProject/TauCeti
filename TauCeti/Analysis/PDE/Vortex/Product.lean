/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ZeroMultiplicity
public import TauCeti.Analysis.PDE.Vortex.Decay
public import TauCeti.Analysis.PDE.Vortex.Symmetry
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Products of plane vortex fields and the separation estimate

Two fields `x` and `y` of the plane vortex equation, with connections `a_x`, `a_y` and sections
`α_x`, `α_y`, have a **product field** `x ⊗ y` (`TauCeti.Vortex.productField`) with connection
`a_x + a_y` and section `α_x α_y`. It is the field of the tensor product of the two Higgs lines:
its section has the sum of the two zero divisors
(`TauCeti.Vortex.isZeroMultiplicity_sectionValue_productField`) and the end framing of degree
`m + n` when `x` and `y` are framed in degrees `m` and `n`
(`TauCeti.Vortex.tendsto_sectionValue_productField`). The vacuum field is its unit, and it is
commutative, associative, and translation and rotation equivariant.

The covariant derivative obeys the Leibniz rule
`∇(α_x α_y) = (∇α_x) α_y + α_x ∇α_y` (`TauCeti.Vortex.covariantDerivative_productField`). Hence
the three defects of the vortex equation for the product are computed exactly from those of the
factors (`TauCeti.Vortex.equation_productField_apply_zero`,
`TauCeti.Vortex.equation_productField_one_add_two_mul_I`):

* the `∂bar` defect is `∂bar_{a_x} α_x · α_y + α_x · ∂bar_{a_y} α_y`, so it vanishes when each
  section is holomorphic for its own connection, that is, when `∂bar_{a_x} α_x = 0` and
  `∂bar_{a_y} α_y = 0`;
* the curvature defect is the sum of the two curvature defects plus
  `(1 - |α_x|²) (1 - |α_y|²) / 8`, because the curvatures add while
  `1 - |α_x α_y|² = (1 - |α_x|²) + (1 - |α_y|²) - (1 - |α_x|²) (1 - |α_y|²)`.

So the product of two vortices satisfies every equation except the curvature equation, whose
defect is exactly `(1 - |α_x|²) (1 - |α_y|²) / 8`
(`TauCeti.Vortex.equation_productField_of_equation_eq_zero`). The modulus defects
`1 - |α_x|²` and `1 - |α_y|²` decay at the rate `exp (-c |z|)` for every `c < 1 / 2`
(`TauCeti.Vortex.exists_nonneg_one_sub_normSq_le_mul_exp`).
When the second vortex is moved away by the translation `z ↦ z + a`, the two defect factors are
concentrated near points at distance `|a|`, and since `|z| + |z + a| ≥ |a|` their product is
exponentially small in the separation: for every rate `c < 1 / 2` there are `K` and `δ > 0` with

`|E(z)| ≤ K exp (-c |a|) exp (-δ |z|)`

for the defect `E` of `x ⊗ (y ∘ (· + a))`
(`TauCeti.Vortex.exists_norm_equation_productField_translateField_le`), and every positive power
of `|E|` is integrable with `∫ |E|ᵏ ≤ K exp (-k c |a|)`
(`TauCeti.Vortex.exists_integrable_and_integral_norm_equation_productField_translateField_pow_le`).
The product of two well-separated vortices is therefore an approximate vortex, whose zero divisor
is the union of the two divisors and whose error is exponentially small in their separation in
every `Lᵏ` norm with `k ≥ 1`. This is the approximate solution from which a vortex with a
separated divisor is obtained by a right inverse of the linearized equation; that correction step
is not done here.

## Main definitions

* `TauCeti.Vortex.productField x y`: the field with connection `a_x + a_y` and section
  `α_x α_y`.

## Main results

* `TauCeti.Vortex.sectionValue_productField`: the section of `x ⊗ y` is `α_x α_y`.
* `TauCeti.Vortex.covariantDerivative_productField`: the Leibniz rule.
* `TauCeti.Vortex.equation_productField_apply_zero`,
  `TauCeti.Vortex.equation_productField_one_add_two_mul_I`: the defects of `x ⊗ y`.
* `TauCeti.Vortex.equation_productField_of_equation_eq_zero`: the defect of a product of
  vortices.
* `TauCeti.Vortex.tendsto_sectionValue_productField`,
  `TauCeti.Vortex.isZeroMultiplicity_sectionValue_productField`: framings multiply and zero
  divisors add.
* `TauCeti.Vortex.exists_norm_equation_productField_translateField_le`,
  `TauCeti.Vortex.exists_integrable_and_integral_norm_equation_productField_translateField_pow_le`:
  the separation estimate.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory
open scoped Topology

variable {x y w : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}

/-! ### The product field -/

/-- **The product of two vortex fields**: the field with connection `a_x + a_y` and section
`α_x α_y`, the field of the tensor product of the two Higgs lines. In the real coordinates
`x = (b₁, b₂, p, q)` with `α = 2 (p + i q)`, its section coordinates are half the real and
imaginary parts of `α_x α_y`. -/
def productField (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[x z 0 + y z 0, x z 1 + y z 1, (sectionValue x z * sectionValue y z).re / 2,
    (sectionValue x z * sectionValue y z).im / 2]

@[simp]
theorem productField_apply_zero (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    productField x y z 0 = x z 0 + y z 0 := (rfl)

@[simp]
theorem productField_apply_one (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    productField x y z 1 = x z 1 + y z 1 := (rfl)

@[simp]
theorem productField_apply_two (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    productField x y z 2 = (sectionValue x z * sectionValue y z).re / 2 := (rfl)

@[simp]
theorem productField_apply_three (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    productField x y z 3 = (sectionValue x z * sectionValue y z).im / 2 := (rfl)

/-- The section of the product field is the product of the sections. -/
@[simp]
theorem sectionValue_productField (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue (productField x y) z = sectionValue x z * sectionValue y z := by
  rw [sectionValue_apply, productField_apply_two, productField_apply_three]
  apply Complex.ext <;> simp <;> ring

/-- The product of fields is commutative. -/
theorem productField_comm (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    productField x y = productField y x :=
  funext fun _ ↦ apply_eq_of_sectionValue_eq (by simp [add_comm]) (by simp [add_comm])
    (by simp [mul_comm])

/-- The product of fields is associative. -/
theorem productField_assoc (x y w : ℂ → EuclideanSpace ℝ (Fin 4)) :
    productField (productField x y) w = productField x (productField y w) :=
  funext fun _ ↦ apply_eq_of_sectionValue_eq (by simp [add_assoc]) (by simp [add_assoc])
    (by simp [mul_assoc])

/-- The vacuum field is a unit for the product of fields. -/
@[simp]
theorem productField_vacuumField (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    productField x vacuumField = x :=
  funext fun _ ↦ apply_eq_of_sectionValue_eq (by simp [vacuumField_apply])
    (by simp [vacuumField_apply]) (by simp)

/-- The vacuum field is a unit for the product of fields. -/
@[simp]
theorem vacuumField_productField (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    productField vacuumField x = x := by
  rw [productField_comm, productField_vacuumField]

/-- Translations commute with the product of fields. -/
@[simp]
theorem translateField_productField (a : ℂ) (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    translateField a (productField x y) = productField (translateField a x) (translateField a y) :=
  funext fun _ ↦ apply_eq_of_sectionValue_eq (by simp) (by simp) (by simp)

/-- Rotations commute with the product of fields. -/
@[simp]
theorem rotateField_productField (u : Circle) (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    rotateField u (productField x y) = productField (rotateField u x) (rotateField u y) :=
  funext fun _ ↦ apply_eq_of_sectionValue_eq (by simp; ring) (by simp; ring)
    (by simp [sectionValue_rotateField])

/-! ### Regularity -/

/-- The product of two `Cⁿ` fields is a `Cⁿ` field. -/
theorem contDiff_productField {n : WithTop ℕ∞} (hx : ContDiff ℝ n x) (hy : ContDiff ℝ n y) :
    ContDiff ℝ n (productField x y) := by
  have hxi (i : Fin 4) : ContDiff ℝ n fun w ↦ x w i := (contDiff_piLp 2).1 hx i
  have hyi (i : Fin 4) : ContDiff ℝ n fun w ↦ y w i := (contDiff_piLp 2).1 hy i
  have hs : ContDiff ℝ n fun w ↦ sectionValue x w * sectionValue y w :=
    (contDiff_sectionValue (hxi 2) (hxi 3)).mul (contDiff_sectionValue (hyi 2) (hyi 3))
  refine (contDiff_piLp 2).2 fun i ↦ ?_
  fin_cases i
  · exact (hxi 0).add (hyi 0)
  · exact (hxi 1).add (hyi 1)
  · exact (reCLM.contDiff.comp hs).div_const 2
  · exact (imCLM.contDiff.comp hs).div_const 2

/-- The first section coordinate of the product field, half the real part of `α_x α_y`, is
differentiable where both sections are. -/
theorem differentiableAt_productField_apply_two (hx : DifferentiableAt ℝ (sectionValue x) z)
    (hy : DifferentiableAt ℝ (sectionValue y) z) :
    DifferentiableAt ℝ (fun w ↦ productField x y w 2) z := by
  simpa [div_eq_mul_inv] using (reCLM.differentiableAt.comp z (hx.mul hy)).mul_const (2⁻¹ : ℝ)

/-- The second section coordinate of the product field, half the imaginary part of `α_x α_y`, is
differentiable where both sections are. -/
theorem differentiableAt_productField_apply_three (hx : DifferentiableAt ℝ (sectionValue x) z)
    (hy : DifferentiableAt ℝ (sectionValue y) z) :
    DifferentiableAt ℝ (fun w ↦ productField x y w 3) z := by
  simpa [div_eq_mul_inv] using (imCLM.differentiableAt.comp z (hx.mul hy)).mul_const (2⁻¹ : ℝ)

/-- The product of two fields differentiable at a point is differentiable there. -/
theorem differentiableAt_productField (hx : DifferentiableAt ℝ x z)
    (hy : DifferentiableAt ℝ y z) : DifferentiableAt ℝ (productField x y) z := by
  have hxi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hx
  have hyi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy
  have hsx := differentiableAt_sectionValue_of_differentiableAt hx
  have hsy := differentiableAt_sectionValue_of_differentiableAt hy
  refine (differentiableAt_piLp 2).2 fun i ↦ ?_
  fin_cases i
  · exact (hxi 0).add (hyi 0)
  · exact (hxi 1).add (hyi 1)
  · exact differentiableAt_productField_apply_two hsx hsy
  · exact differentiableAt_productField_apply_three hsx hsy

/-! ### The Leibniz rule and the vortex defects of a product -/

/-- **The Leibniz rule**: the covariant derivative of the product section for the sum connection
is `∇(α_x α_y) = (∇α_x) α_y + α_x ∇α_y`. -/
theorem covariantDerivative_productField (hx : DifferentiableAt ℝ (sectionValue x) z)
    (hy : DifferentiableAt ℝ (sectionValue y) z) (v : ℂ) :
    covariantDerivative (productField x y) z v =
      covariantDerivative x z v * sectionValue y z +
        sectionValue x z * covariantDerivative y z v := by
  have hs : sectionValue (productField x y) = fun w ↦ sectionValue x w * sectionValue y w :=
    funext (sectionValue_productField x y)
  rw [covariantDerivative_apply, hs, fderiv_fun_mul hx hy, covariantDerivative_apply,
    covariantDerivative_apply]
  simp only [productField_apply_zero, productField_apply_one, add_apply,
    smul_apply, smul_eq_mul, ofReal_add, ofReal_mul]
  ring

/-- The curvatures of the factors add: `F_{a_x + a_y} = F_{a_x} + F_{a_y}`. -/
theorem curvature_productField (hx₀ : DifferentiableAt ℝ (fun w ↦ x w 0) z)
    (hx₁ : DifferentiableAt ℝ (fun w ↦ x w 1) z) (hy₀ : DifferentiableAt ℝ (fun w ↦ y w 0) z)
    (hy₁ : DifferentiableAt ℝ (fun w ↦ y w 1) z) :
    curvature (productField x y) z = curvature x z + curvature y z := by
  simp only [curvature_apply, productField_apply_zero, productField_apply_one,
    fderiv_fun_add hx₀ hy₀, fderiv_fun_add hx₁ hy₁, add_apply]
  ring

/-- **The curvature defect of a product.** It is the sum of the curvature defects of the factors
plus `(1 - |α_x|²) (1 - |α_y|²) / 8`. -/
theorem equation_productField_apply_zero (hx₀ : DifferentiableAt ℝ (fun w ↦ x w 0) z)
    (hx₁ : DifferentiableAt ℝ (fun w ↦ x w 1) z) (hy₀ : DifferentiableAt ℝ (fun w ↦ y w 0) z)
    (hy₁ : DifferentiableAt ℝ (fun w ↦ y w 1) z) :
    equation (productField x y) z 0 = equation x z 0 + equation y z 0 +
      (1 - ‖sectionValue x z‖ ^ 2) * (1 - ‖sectionValue y z‖ ^ 2) / 8 := by
  have hcurv := curvature_productField hx₀ hx₁ hy₀ hy₁
  have hn := sq_norm_sectionValue (productField x y) z
  rw [sectionValue_productField, norm_mul, mul_pow] at hn
  simp only [curvature_apply] at hcurv
  simp only [equation_apply_zero, ← sq_norm_sectionValue] at hn ⊢
  rw [← hn]
  linear_combination -hcurv

/-- **The `∂bar` defect of a product.** Writing `E = E₁ + i E₂` for the complex `∂bar` defect
`∂bar_a α` of a field, the defect of `x ⊗ y` is `E_x α_y + α_x E_y`. -/
theorem equation_productField_one_add_two_mul_I (hx₂ : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hx₃ : DifferentiableAt ℝ (fun w ↦ x w 3) z) (hy₂ : DifferentiableAt ℝ (fun w ↦ y w 2) z)
    (hy₃ : DifferentiableAt ℝ (fun w ↦ y w 3) z) :
    (equation (productField x y) z 1 : ℂ) + equation (productField x y) z 2 * I =
      ((equation x z 1 : ℂ) + equation x z 2 * I) * sectionValue y z +
        sectionValue x z * ((equation y z 1 : ℂ) + equation y z 2 * I) := by
  have hx := differentiableAt_sectionValue hx₂ hx₃
  have hy := differentiableAt_sectionValue hy₂ hy₃
  have h := covariantDerivative_one_add_I_mul_covariantDerivative_I
    (differentiableAt_productField_apply_two hx hy)
    (differentiableAt_productField_apply_three hx hy)
  have h₁ := covariantDerivative_one_add_I_mul_covariantDerivative_I hx₂ hx₃
  have h₂ := covariantDerivative_one_add_I_mul_covariantDerivative_I hy₂ hy₃
  rw [covariantDerivative_productField hx hy, covariantDerivative_productField hx hy] at h
  linear_combination (1 / 2 : ℂ) * (-h + sectionValue y z * h₁ + sectionValue x z * h₂)

/-- **The defect of a product of vortices.** If `x` and `y` solve the vortex equation at `z`,
then `x ⊗ y` solves its `∂bar` equation there, and its curvature defect is
`(1 - |α_x|²) (1 - |α_y|²) / 8`. -/
theorem equation_productField_of_equation_eq_zero (hx : DifferentiableAt ℝ x z)
    (hy : DifferentiableAt ℝ y z) (hxz : equation x z = 0) (hyz : equation y z = 0) :
    equation (productField x y) z =
      !₂[(1 - ‖sectionValue x z‖ ^ 2) * (1 - ‖sectionValue y z‖ ^ 2) / 8, 0, 0] := by
  have hxi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hx
  have hyi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hy
  have h₀ := equation_productField_apply_zero (hxi 0) (hxi 1) (hyi 0) (hyi 1)
  have h₁₂ := equation_productField_one_add_two_mul_I (hxi 2) (hxi 3) (hyi 2) (hyi 3)
  have hx' (i : Fin 3) : equation x z i = 0 := by simp [hxz]
  have hy' (i : Fin 3) : equation y z i = 0 := by simp [hyz]
  simp only [hx', hy', ofReal_zero, zero_mul, add_zero, zero_add, mul_zero] at h₀ h₁₂
  obtain ⟨h₁, h₂⟩ := Complex.ext_iff.1 h₁₂
  simp at h₁ h₂
  ext i
  fin_cases i
  · simpa using h₀
  · simpa using h₁
  · simpa using h₂

/-- The norm of the defect of a product of vortices is `|(1 - |α_x|²) (1 - |α_y|²)| / 8`. -/
theorem norm_equation_productField_of_equation_eq_zero (hx : DifferentiableAt ℝ x z)
    (hy : DifferentiableAt ℝ y z) (hxz : equation x z = 0) (hyz : equation y z = 0) :
    ‖equation (productField x y) z‖ =
      |(1 - ‖sectionValue x z‖ ^ 2) * (1 - ‖sectionValue y z‖ ^ 2)| / 8 := by
  rw [equation_productField_of_equation_eq_zero hx hy hxz hyz, EuclideanSpace.norm_eq,
    Fin.sum_univ_three]
  simp [Real.sqrt_sq_eq_abs, abs_div]

/-! ### Zero divisors and end framings -/

/-- **Zero divisors add.** If `n` and `n'` are the zero multiplicities of the sections of `x` and
`y`, then `n + n'` is that of the section of `x ⊗ y`. -/
theorem isZeroMultiplicity_sectionValue_productField {n n' : ℂ → ℕ}
    (hx : IsZeroMultiplicity (sectionValue x) n) (hy : IsZeroMultiplicity (sectionValue y) n') :
    IsZeroMultiplicity (sectionValue (productField x y)) (n + n') := by
  simpa only [← sectionValue_productField] using hx.mul hy

/-- **End framings multiply.** If the sections of `x` and `y` have end framings
`α(z) (z / |z|)⁻ᵐ → c` and `α(z) (z / |z|)⁻ⁿ → d`, then the section of `x ⊗ y` has the end framing
of degree `m + n` with limit `c d`. -/
theorem tendsto_sectionValue_productField {m n : ℕ} {c d : ℂ}
    (hx : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 c))
    (hy : Tendsto (fun z ↦ sectionValue y z * ((z / (‖z‖ : ℂ)) ^ n)⁻¹) (cocompact ℂ) (𝓝 d)) :
    Tendsto (fun z ↦ sectionValue (productField x y) z * ((z / (‖z‖ : ℂ)) ^ (m + n))⁻¹)
      (cocompact ℂ) (𝓝 (c * d)) := by
  refine (hx.mul hy).congr fun z ↦ ?_
  rw [sectionValue_productField, pow_add, mul_inv]
  ring

/-! ### The separation estimate -/

/-- **The separation estimate.** Let `x` and `y` be vortices on the plane with `|α| → 1` at
infinity, and move `y` by the translation `z ↦ z + a`. For every rate `c < 1 / 2` there are
constants `K` and `δ > 0`, independent of `a`, such that the defect of the product field
`x ⊗ (y ∘ (· + a))` satisfies

`|E(z)| ≤ K exp (-c |a|) exp (-δ |z|)`.

The defect is the curvature defect `(1 - |α_x(z)|²) (1 - |α_y(z + a)|²) / 8`, and the two factors
decay away from the two clusters of zeros, which are a distance comparable to `|a|` apart. -/
theorem exists_norm_equation_productField_translateField_le (hx : ContDiff ℝ 2 x)
    (hxsol : ∀ z, equation x z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy : ContDiff ℝ 2 y) (hysol : ∀ z, equation y z = 0)
    (hylim : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) :
    ∃ K δ, 0 < δ ∧ ∀ a z, ‖equation (productField x (translateField a y)) z‖ ≤
      K * Real.exp (-(c * ‖a‖)) * Real.exp (-(δ * ‖z‖)) := by
  -- Work with a nonnegative rate `c₀ ≥ c` and a slightly faster decay rate `c' < 1 / 2`.
  set c₀ := max c 0
  set c' := (c₀ + 1 / 2) / 2 with hc'
  have hc₀ : c₀ < 1 / 2 := max_lt hc (by norm_num)
  have hc₀c' : c₀ < c' := by linarith
  have hc'2 : c' < 1 / 2 := by linarith
  obtain ⟨Kx, hKx, hx'⟩ := exists_nonneg_one_sub_normSq_le_mul_exp ((contDiff_piLp 2).1 hx 2)
    ((contDiff_piLp 2).1 hx 3) hxsol hxlim hc'2
  obtain ⟨Ky, hKy, hy'⟩ := exists_nonneg_one_sub_normSq_le_mul_exp ((contDiff_piLp 2).1 hy 2)
    ((contDiff_piLp 2).1 hy 3) hysol hylim hc'2
  refine ⟨Kx * Ky / 8, c' - c₀, by linarith, fun a z ↦ ?_⟩
  have hdx : DifferentiableAt ℝ x z := (hx.differentiable (by norm_num)).differentiableAt
  have hya : ContDiff ℝ 2 (translateField a y) := contDiff_translateField a hy
  have hdy : DifferentiableAt ℝ (translateField a y) z :=
    (hya.differentiable (by norm_num)).differentiableAt
  rw [norm_equation_productField_of_equation_eq_zero hdx hdy (hxsol z)
    (by rw [equation_translateField]; exact hysol _), sectionValue_translateField,
    sq_norm_sectionValue, sq_norm_sectionValue]
  obtain ⟨h₁, h₁'⟩ := hx' z
  obtain ⟨h₂, h₂'⟩ := hy' (z + a)
  rw [abs_of_nonneg (mul_nonneg h₁ h₂)]
  have hexp := exp_neg_mul_norm_mul_exp_neg_mul_norm_add_le (le_max_right c 0) hc₀c'.le a z
  have hca : Real.exp (-(c₀ * ‖a‖)) ≤ Real.exp (-(c * ‖a‖)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg a)))
  calc (1 - 4 * (x z 2 ^ 2 + x z 3 ^ 2)) * (1 - 4 * (y (z + a) 2 ^ 2 + y (z + a) 3 ^ 2)) / 8
      ≤ Kx * Real.exp (-(c' * ‖z‖)) * (Ky * Real.exp (-(c' * ‖z + a‖))) / 8 := by
        gcongr
    _ = Kx * Ky / 8 * (Real.exp (-(c' * ‖z‖)) * Real.exp (-(c' * ‖z + a‖))) := by ring
    _ ≤ Kx * Ky / 8 * (Real.exp (-(c * ‖a‖)) * Real.exp (-((c' - c₀) * ‖z‖))) :=
        mul_le_mul_of_nonneg_left (hexp.trans (mul_le_mul_of_nonneg_right hca (Real.exp_pos _).le))
          (by positivity)
    _ = _ := by ring

/-- **The separation estimate in `Lᵏ`.** For vortices `x` and `y` with `|α| → 1` at infinity, a
rate `c < 1 / 2` and a positive power `k`, every power `|E|ᵏ` of the defect of
`x ⊗ (y ∘ (· + a))` is integrable for every additive Haar measure, with
`∫ |E|ᵏ ≤ K exp (-c |a|) ^ k` for a constant `K` independent of the translation `a`. -/
theorem exists_integrable_and_integral_norm_equation_productField_translateField_pow_le
    (μ : Measure ℂ) [μ.IsAddHaarMeasure] (hx : ContDiff ℝ 2 x) (hxsol : ∀ z, equation x z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy : ContDiff ℝ 2 y) (hysol : ∀ z, equation y z = 0)
    (hylim : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {c : ℝ}
    (hc : c < 1 / 2) {k : ℕ} (hk : k ≠ 0) :
    ∃ K, ∀ a, Integrable (fun z ↦ ‖equation (productField x (translateField a y)) z‖ ^ k) μ ∧
      ∫ z, ‖equation (productField x (translateField a y)) z‖ ^ k ∂μ ≤
        K * Real.exp (-(c * ‖a‖)) ^ k := by
  obtain ⟨K, δ, hδ, hK⟩ :=
    exists_norm_equation_productField_translateField_le hx hxsol hxlim hy hysol hylim hc
  have hkδ : 0 < (k : ℝ) * δ := mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)) hδ
  have hint : Integrable (fun z : ℂ ↦ Real.exp (-((k * δ) * ‖z‖))) μ :=
    integrable_exp_neg_mul_norm μ hkδ
  refine ⟨K ^ k * ∫ z, Real.exp (-((k * δ) * ‖z‖)) ∂μ, fun a ↦ ?_⟩
  -- The pointwise bound, raised to the power `k`.
  have hbound (z : ℂ) : ‖equation (productField x (translateField a y)) z‖ ^ k ≤
      K ^ k * Real.exp (-(c * ‖a‖)) ^ k * Real.exp (-((k * δ) * ‖z‖)) := by
    have hexp : Real.exp (-((k * δ) * ‖z‖)) = Real.exp (-(δ * ‖z‖)) ^ k := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp, ← mul_pow, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hK a z) k
  have hya : ContDiff ℝ 2 (translateField a y) := contDiff_translateField a hy
  have hcont : Continuous fun z ↦ ‖equation (productField x (translateField a y)) z‖ ^ k :=
    ((contDiff_equation (contDiff_productField hx hya) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
      ).continuous.norm).pow k
  have hdom : Integrable (fun z ↦
      K ^ k * Real.exp (-(c * ‖a‖)) ^ k * Real.exp (-((k * δ) * ‖z‖))) μ :=
    hint.const_mul _
  have hint' : Integrable (fun z ↦ ‖equation (productField x (translateField a y)) z‖ ^ k) μ :=
    hdom.mono' hcont.aestronglyMeasurable (.of_forall fun z ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hbound z)
  refine ⟨hint', (integral_mono hint' hdom hbound).trans_eq ?_⟩
  rw [integral_const_mul]
  ring

end TauCeti.Vortex
