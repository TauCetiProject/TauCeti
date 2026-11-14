/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence
public import TauCeti.Analysis.PDE.Vortex.Flux
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Plane vortices with split divisors

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has connection
`a = i (b₁ ds + b₂ dt)` and section `α = 2 (p + i q)` (`TauCeti.Vortex.sectionValue`). This file
compares a plane vortex whose zero divisor splits as `D₁ + D₂` with the vortices of the two
clusters `D₁` and `D₂`.

**The product field.** The tensor product of two fields `x` and `y` is the field
`TauCeti.Vortex.mulField x y` with connection `a_x + a_y` and section `α_x α_y`. It satisfies the
holomorphicity rows `∂bar_a α = 0` whenever `x` and `y` do, and its zero divisor is the sum of
theirs (`TauCeti.Vortex.isZeroMultiplicity_sectionValue_mulField`). So if `x`, `y₁`, `y₂` are
vortices with divisors `D₁ + D₂`, `D₁`, `D₂`, the sections are related by `α_x = h α_{y₁} α_{y₂}`
for a nowhere-vanishing factor `h`, as regular as the fields
(`TauCeti.Vortex.exists_contDiff_sectionValue_eq_mul_mul_of_add`); for `C²` fields `h` is `C²`.

**The pointwise comparison.** Write `s = |α|²`. Off the zeros, the scalar equations
`Δ log s = (s - 1) / 4` of the three vortices give, for `w = log |h|²`,

`4 Δ w = s_x - s₁ - s₂ + 1 = |h|² s₁ s₂ - s₁ - s₂ + 1`,

and by continuity this holds everywhere. Where `w > 0`, that is `|h| > 1`, the right side is at
least `s₁ s₂ - s₁ - s₂ + 1 = (1 - s₁) (1 - s₂) ≥ 0`, because `s₁, s₂ ≤ 1`. Since `w → 0` at
infinity, the weak maximum principle gives `w ≤ 0`, that is

`|α_x| ≤ |α_{y₁}| |α_{y₂}|`

(`TauCeti.Vortex.norm_sectionValue_le_mul_of_add`). In particular adding zeros decreases the
modulus of a vortex: a vortex with divisor `D₁ + D₂` satisfies `|α_x| ≤ |α_{y₁}|` for every
vortex `y₁` with divisor `D₁` (`TauCeti.Vortex.norm_sectionValue_le_of_add`).

**The overlap identity.** The flux identity `∫ (1 - s) = 16 π deg D`
(`TauCeti.Vortex.integral_one_sub_normSq_eq_mul_card`) is additive in the divisor, so
`∫ (s₁ s₂ - s_x) = ∫ (1 - s₁) (1 - s₂)`. With the pointwise comparison this is an identity for
the `L¹` distance between `s_x` and the product `s₁ s₂`:

`∫ |s_x - s₁ s₂| = ∫ (1 - s₁) (1 - s₂)`

(`TauCeti.Vortex.integral_abs_sq_norm_sectionValue_sub_mul_eq`). The right side is the overlap of
the two defects `1 - s₁` and `1 - s₂`, each concentrated near its own cluster and decaying
exponentially away from it (`TauCeti.Vortex.exists_one_sub_normSq_le_mul_exp`). When the
clusters are far apart the overlap is small, and `|α_x|²` is close in `L¹` to the product
`|α_{y₁}|² |α_{y₂}|²`: if the second cluster is translated by `-a`, the `L¹` distance tends to
zero as `a → ∞`
(`TauCeti.Vortex.tendsto_integral_abs_sq_norm_sectionValue_sub_mul`).

## Main definitions

* `TauCeti.Vortex.mulField x y`: the tensor product field, with connection `a_x + a_y` and section
  `α_x α_y`.

## Main results

* `TauCeti.Vortex.sectionValue_mulField`: the section of the product field is `α_x α_y`.
* `TauCeti.Vortex.contDiff_mulField`, `TauCeti.Vortex.differentiable_mulField`: the product field
  is as regular as its factors.
* `TauCeti.Vortex.equation_mulField_apply_one_eq_zero_and_apply_two_eq_zero`: the product field
  satisfies the holomorphicity rows when both factors do.
* `TauCeti.Vortex.isZeroMultiplicity_sectionValue_mulField`: the zero multiplicities of the
  product field are the sums of those of the factors.
* `TauCeti.Vortex.exists_contDiff_sectionValue_eq_mul_mul_of_add`: `α_x = h α_{y₁} α_{y₂}` with
  `h` of class `C^k` and nowhere zero, for `C^k` solutions of the holomorphicity rows with
  zero multiplicities `m₁ + m₂`, `m₁` and `m₂`.
* `TauCeti.Vortex.norm_sectionValue_le_mul_of_add`: `|α_x| ≤ |α_{y₁}| |α_{y₂}|` for vortices with
  divisors `D₁ + D₂`, `D₁` and `D₂`.
* `TauCeti.Vortex.norm_sectionValue_le_of_add`: `|α_x| ≤ |α_{y₁}|` for vortices with divisors
  `D₁ + D₂` and `D₁`.
* `TauCeti.Vortex.integrable_one_sub_sq_norm_sectionValue_mul_one_sub`,
  `TauCeti.Vortex.integrable_sq_norm_sectionValue_sub_mul`: the overlap `(1 - s₁) (1 - s₂)` and
  the comparison error `s_x - s₁ s₂` are integrable.
* `TauCeti.Vortex.integral_abs_sq_norm_sectionValue_sub_mul_eq`:
  `∫ |s_x - s₁ s₂| = ∫ (1 - s₁) (1 - s₂)`.
* `TauCeti.Vortex.tendsto_integral_abs_sq_norm_sectionValue_sub_mul`: the `L¹` distance between
  `|α_x|²` and `|α_{y₁}|² |α_{y₂}|²` tends to zero as the two clusters separate.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

open Complex Filter Topology InnerProductSpace Laplacian MeasureTheory

namespace TauCeti.Vortex

/-! ### The product field -/

/-- **The tensor product of two fields.** Its connection is the sum `a_x + a_y` of the
connections and its section is the product `α_x α_y` of the sections
(`TauCeti.Vortex.sectionValue_mulField`). -/
def mulField (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) : EuclideanSpace ℝ (Fin 4) :=
  !₂[x z 0 + y z 0, x z 1 + y z 1, (sectionValue x z * sectionValue y z).re / 2,
    (sectionValue x z * sectionValue y z).im / 2]

section MulField

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

@[simp]
theorem mulField_apply_zero (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    mulField x y z 0 = x z 0 + y z 0 := (rfl)

@[simp]
theorem mulField_apply_one (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    mulField x y z 1 = x z 1 + y z 1 := (rfl)

@[simp]
theorem mulField_apply_two (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    mulField x y z 2 = (sectionValue x z * sectionValue y z).re / 2 := (rfl)

@[simp]
theorem mulField_apply_three (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    mulField x y z 3 = (sectionValue x z * sectionValue y z).im / 2 := (rfl)

/-- The section of the product field is the product of the sections. -/
@[simp]
theorem sectionValue_mulField (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    sectionValue (mulField x y) z = sectionValue x z * sectionValue y z := by
  rw [sectionValue_apply, mulField_apply_two, mulField_apply_three]
  apply Complex.ext <;> simp <;> ring

/-- The section coordinates of the product field are differentiable where those of the factors
are. -/
theorem differentiableAt_mulField_apply_two {z : ℂ}
    (hxp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hxq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hyp : DifferentiableAt ℝ (fun w ↦ y w 2) z) (hyq : DifferentiableAt ℝ (fun w ↦ y w 3) z) :
    DifferentiableAt ℝ (fun w ↦ mulField x y w 2) z := by
  have h : DifferentiableAt ℝ (fun w ↦ (sectionValue x w * sectionValue y w).re) z :=
    reCLM.differentiableAt.comp z ((differentiableAt_sectionValue hxp hxq).mul
      (differentiableAt_sectionValue hyp hyq))
  have h₂ : DifferentiableAt ℝ (fun w ↦ (sectionValue x w * sectionValue y w).re / 2) z :=
    h.mul_const (2⁻¹ : ℝ) |>.congr_of_eventuallyEq (.of_forall fun _ ↦ div_eq_mul_inv _ _)
  exact h₂.congr_of_eventuallyEq (.of_forall fun w ↦ mulField_apply_two x y w)

/-- The section coordinates of the product field are differentiable where those of the factors
are. -/
theorem differentiableAt_mulField_apply_three {z : ℂ}
    (hxp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hxq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hyp : DifferentiableAt ℝ (fun w ↦ y w 2) z) (hyq : DifferentiableAt ℝ (fun w ↦ y w 3) z) :
    DifferentiableAt ℝ (fun w ↦ mulField x y w 3) z := by
  have h : DifferentiableAt ℝ (fun w ↦ (sectionValue x w * sectionValue y w).im) z :=
    imCLM.differentiableAt.comp z ((differentiableAt_sectionValue hxp hxq).mul
      (differentiableAt_sectionValue hyp hyq))
  have h₂ : DifferentiableAt ℝ (fun w ↦ (sectionValue x w * sectionValue y w).im / 2) z :=
    h.mul_const (2⁻¹ : ℝ) |>.congr_of_eventuallyEq (.of_forall fun _ ↦ div_eq_mul_inv _ _)
  exact h₂.congr_of_eventuallyEq (.of_forall fun w ↦ mulField_apply_three x y w)

/-- The product field is differentiable when both factors are. -/
theorem differentiable_mulField (hx : Differentiable ℝ x) (hy : Differentiable ℝ y) :
    Differentiable ℝ (mulField x y) := by
  have hc {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : Differentiable ℝ u) (i : Fin 4) :
      Differentiable ℝ fun w ↦ u w i :=
    (differentiable_piLp 2).1 hu i
  have h₀ : Differentiable ℝ fun w ↦ mulField x y w 0 := by
    simpa only [mulField_apply_zero] using (hc hx 0).fun_add (hc hy 0)
  have h₁ : Differentiable ℝ fun w ↦ mulField x y w 1 := by
    simpa only [mulField_apply_one] using (hc hx 1).fun_add (hc hy 1)
  have h₂ : Differentiable ℝ fun w ↦ mulField x y w 2 := fun w ↦
    differentiableAt_mulField_apply_two (hc hx 2 w) (hc hx 3 w) (hc hy 2 w) (hc hy 3 w)
  have h₃ : Differentiable ℝ fun w ↦ mulField x y w 3 := fun w ↦
    differentiableAt_mulField_apply_three (hc hx 2 w) (hc hx 3 w) (hc hy 2 w) (hc hy 3 w)
  -- `fin_cases` writes the index as `⟨i, _⟩`, which is the numeral `i` up to `rfl`.
  refine (differentiable_piLp 2).2 fun i ↦ ?_
  fin_cases i <;> assumption

/-- The product field is `C^n` when both factors are. -/
theorem contDiff_mulField {n : WithTop ℕ∞} (hx : ContDiff ℝ n x) (hy : ContDiff ℝ n y) :
    ContDiff ℝ n (mulField x y) := by
  have hc {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : ContDiff ℝ n u) (i : Fin 4) :
      ContDiff ℝ n fun w ↦ u w i :=
    (contDiff_piLp 2).1 hu i
  have hs : ContDiff ℝ n fun w ↦ sectionValue x w * sectionValue y w :=
    (contDiff_sectionValue (hc hx 2) (hc hx 3)).mul (contDiff_sectionValue (hc hy 2) (hc hy 3))
  have h₀ : ContDiff ℝ n fun w ↦ mulField x y w 0 := by
    simpa only [mulField_apply_zero] using (hc hx 0).add (hc hy 0)
  have h₁ : ContDiff ℝ n fun w ↦ mulField x y w 1 := by
    simpa only [mulField_apply_one] using (hc hx 1).add (hc hy 1)
  have h₂ : ContDiff ℝ n fun w ↦ mulField x y w 2 := by
    simpa only [mulField_apply_two, Function.comp_apply, reCLM_apply] using
      (reCLM.contDiff.comp hs).div_const (2 : ℝ)
  have h₃ : ContDiff ℝ n fun w ↦ mulField x y w 3 := by
    simpa only [mulField_apply_three, Function.comp_apply, imCLM_apply] using
      (imCLM.contDiff.comp hs).div_const (2 : ℝ)
  -- `fin_cases` writes the index as `⟨i, _⟩`, which is the numeral `i` up to `rfl`.
  refine (contDiff_piLp 2).2 fun i ↦ ?_
  fin_cases i <;> assumption

/-- **The product of two holomorphic fields is holomorphic.** If `x` and `y` satisfy the
holomorphicity rows `∂bar_a α = 0` of the vortex equation at `z`, so does their tensor product
`mulField x y`, by the Leibniz rule for `∂bar`. -/
theorem equation_mulField_apply_one_eq_zero_and_apply_two_eq_zero {z : ℂ}
    (hxp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hxq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hyp : DifferentiableAt ℝ (fun w ↦ y w 2) z) (hyq : DifferentiableAt ℝ (fun w ↦ y w 3) z)
    (hx : equation x z 1 = 0 ∧ equation x z 2 = 0)
    (hy : equation y z 1 = 0 ∧ equation y z 2 = 0) :
    equation (mulField x y) z 1 = 0 ∧ equation (mulField x y) z 2 = 0 := by
  refine (conjWirtingerDeriv_apply_one_section_eq_mul_iff
    (differentiableAt_mulField_apply_two hxp hxq hyp hyq)
    (differentiableAt_mulField_apply_three hxp hxq hyp hyq)).1 ?_
  have hsec : sectionValue (mulField x y) = fun w ↦ sectionValue x w * sectionValue y w :=
    funext (sectionValue_mulField x y)
  rw [hsec, conjWirtingerDeriv_fun_mul (differentiableAt_sectionValue hxp hxq)
    (differentiableAt_sectionValue hyp hyq), add_apply, smul_apply, smul_apply, smul_eq_mul,
    smul_eq_mul,
    conjWirtingerDeriv_apply_one_section_eq_mul hxp hxq hx.1 hx.2,
    conjWirtingerDeriv_apply_one_section_eq_mul hyp hyq hy.1 hy.2, mulField_apply_zero,
    mulField_apply_one]
  push_cast
  ring

/-- **The zero divisor of the product field.** The zero multiplicities of the section of
`mulField x y` are the sums of those of `x` and `y`. -/
theorem isZeroMultiplicity_sectionValue_mulField {m₁ m₂ : ℂ → ℕ}
    (h₁ : IsZeroMultiplicity (sectionValue x) m₁) (h₂ : IsZeroMultiplicity (sectionValue y) m₂) :
    IsZeroMultiplicity (sectionValue (mulField x y)) (m₁ + m₂) := by
  rw [show sectionValue (mulField x y) = fun w ↦ sectionValue x w * sectionValue y w from
    funext (sectionValue_mulField x y)]
  exact h₁.mul h₂

end MulField

/-! ### The pointwise comparison -/

section Comparison

variable {x y₁ y₂ : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- A component of a `C²` field is `C²`. -/
private theorem contDiff_apply {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : ContDiff ℝ 2 u)
    (i : Fin 4) : ContDiff ℝ 2 fun w ↦ u w i :=
  (contDiff_piLp 2).1 hu i

/-- A component of a `C²` field is differentiable. -/
private theorem differentiable_apply {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : ContDiff ℝ 2 u)
    (i : Fin 4) : Differentiable ℝ fun w ↦ u w i :=
  (contDiff_apply hu i).differentiable two_ne_zero

/-- The section `α` of a `C²` field is continuous. -/
private theorem continuous_sectionValue {u : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ContDiff ℝ 2 u) : Continuous (sectionValue u) :=
  (contDiff_sectionValue (contDiff_apply hu 2) (contDiff_apply hu 3)).continuous

/-- The squared modulus `|α|²` of a `C²` field is continuous. -/
private theorem continuous_sq_norm_sectionValue {u : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ContDiff ℝ 2 u) : Continuous fun z ↦ ‖sectionValue u z‖ ^ 2 :=
  (continuous_sectionValue hu).norm.pow 2

/-- The logarithm of `|α|² = 4 (p² + q²)` is `C²` where the section does not vanish. -/
private theorem contDiffAt_log_normSq {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : ContDiff ℝ 2 u)
    {z : ℂ} (hz : sectionValue u z ≠ 0) :
    ContDiffAt ℝ 2 (fun w ↦ Real.log (4 * (u w 2 ^ 2 + u w 3 ^ 2))) z :=
  (contDiff_normSq (contDiff_apply hu 2) (contDiff_apply hu 3)).contDiffAt.log <| by
    rw [← sq_norm_sectionValue]
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hz)

/-- The scalar equation of a vortex in terms of `|α|²`: `Δ log |α|² = (|α|² - 1) / 4` at a point
where the section does not vanish. -/
private theorem laplacian_log_normSq_eq {u : ℂ → EuclideanSpace ℝ (Fin 4)} (hu : ContDiff ℝ 2 u)
    (hsol : ∀ z, equation u z = 0) {z : ℂ} (hz : sectionValue u z ≠ 0) :
    Δ (fun w ↦ Real.log (4 * (u w 2 ^ 2 + u w 3 ^ 2))) z = (‖sectionValue u z‖ ^ 2 - 1) / 4 := by
  rw [laplacian_log_normSq_of_equation_eq_zero (contDiff_apply hu 2).contDiffAt
    (contDiff_apply hu 3).contDiffAt (by rwa [Ne, ← sectionValue_eq_zero_iff])
    (.of_forall hsol), sq_norm_sectionValue]

/-- **The scalar equation of the ratio.** If `α_x = h α_{y₁} α_{y₂}` for vortices `x`, `y₁`, `y₂`
and a nowhere-vanishing `C²` factor `h`, then off the zeros of `α_{y₁} α_{y₂}`,
`Δ log |h|² = (|α_x|² - |α_{y₁}|² - |α_{y₂}|² + 1) / 4`. -/
private theorem laplacian_log_norm_sq_eq_of_mul {h : ℂ → ℂ} {z : ℂ}
    (hx : ContDiff ℝ 2 x) (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂)
    (hxsol : ∀ z, equation x z = 0) (hy₁sol : ∀ z, equation y₁ z = 0)
    (hy₂sol : ∀ z, equation y₂ z = 0) (hh : ContDiff ℝ 2 h) (hh₀ : ∀ z, h z ≠ 0)
    (hα : ∀ z, sectionValue x z = h z * (sectionValue y₁ z * sectionValue y₂ z))
    (hz : sectionValue y₁ z * sectionValue y₂ z ≠ 0) :
    Δ (fun w ↦ Real.log (‖h w‖ ^ 2)) z =
      (‖sectionValue x z‖ ^ 2 - ‖sectionValue y₁ z‖ ^ 2 - ‖sectionValue y₂ z‖ ^ 2 + 1) / 4 := by
  have hz₁ : sectionValue y₁ z ≠ 0 := left_ne_zero_of_mul hz
  have hz₂ : sectionValue y₂ z ≠ 0 := right_ne_zero_of_mul hz
  have hzx : sectionValue x z ≠ 0 := by rw [hα z]; exact mul_ne_zero (hh₀ z) hz
  have hw : ContDiffAt ℝ 2 (fun w ↦ Real.log (‖h w‖ ^ 2)) z :=
    (hh.contDiffAt.norm_sq ℝ).log (pow_ne_zero 2 (norm_ne_zero_iff.2 (hh₀ z)))
  -- Near `z`, `log |α_x|² = log |h|² + log |α_{y₁}|² + log |α_{y₂}|²`.
  have hev : (fun w ↦ Real.log (4 * (x w 2 ^ 2 + x w 3 ^ 2))) =ᶠ[𝓝 z]
      ((fun w ↦ Real.log (‖h w‖ ^ 2)) + fun w ↦ Real.log (4 * (y₁ w 2 ^ 2 + y₁ w 3 ^ 2))) +
        fun w ↦ Real.log (4 * (y₂ w 2 ^ 2 + y₂ w 3 ^ 2)) := by
    filter_upwards [(continuous_sectionValue hy₁).continuousAt.eventually_ne hz₁,
      (continuous_sectionValue hy₂).continuousAt.eventually_ne hz₂] with w hw₁ hw₂
    have hn (c : ℂ) (hc : c ≠ 0) : ‖c‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hc)
    simp only [Pi.add_apply, ← sq_norm_sectionValue, hα w, norm_mul, mul_pow]
    rw [Real.log_mul (hn _ (hh₀ w)) (mul_ne_zero (hn _ hw₁) (hn _ hw₂)),
      Real.log_mul (hn _ hw₁) (hn _ hw₂), add_assoc]
  have hΔ := (laplacian_congr_nhds hev).eq_of_nhds
  have hA : ContDiffAt ℝ 2 ((fun w ↦ Real.log (‖h w‖ ^ 2)) +
      fun w ↦ Real.log (4 * (y₁ w 2 ^ 2 + y₁ w 3 ^ 2))) z :=
    hw.add (contDiffAt_log_normSq hy₁ hz₁)
  rw [hA.laplacian_add (contDiffAt_log_normSq hy₂ hz₂),
    hw.laplacian_add (contDiffAt_log_normSq hy₁ hz₁), laplacian_log_normSq_eq hx hxsol hzx,
    laplacian_log_normSq_eq hy₁ hy₁sol hz₁, laplacian_log_normSq_eq hy₂ hy₂sol hz₂] at hΔ
  linarith

/-- A vortex with `|α| → 1` at infinity has `|α|² ≤ 1`. -/
private theorem norm_sectionValue_sq_le_one {u : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ContDiff ℝ 2 u) (hsol : ∀ z, equation u z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (u z 2 ^ 2 + u z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) (z : ℂ) :
    ‖sectionValue u z‖ ^ 2 ≤ 1 := by
  rw [sq_norm_sectionValue]
  exact normSq_le_one_of_tendsto (contDiff_apply hu 2) (contDiff_apply hu 3) hsol hlim z

/-- **The maximum principle for the ratio.** If `α_x = h α_{y₁} α_{y₂}` for vortices `x`, `y₁`, `y₂`
with `|α| → 1` at infinity and a nowhere-vanishing `C²` factor `h`, and the zeros of
`α_{y₁} α_{y₂}` have empty interior, then `|h| ≤ 1`. -/
private theorem norm_le_one_of_sectionValue_eq_mul {h : ℂ → ℂ}
    (hx : ContDiff ℝ 2 x) (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂)
    (hxsol : ∀ z, equation x z = 0) (hy₁sol : ∀ z, equation y₁ z = 0)
    (hy₂sol : ∀ z, equation y₂ z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₁lim : Tendsto (fun z ↦ 4 * (y₁ z 2 ^ 2 + y₁ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₂lim : Tendsto (fun z ↦ 4 * (y₂ z 2 ^ 2 + y₂ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hh : ContDiff ℝ 2 h) (hh₀ : ∀ z, h z ≠ 0)
    (hα : ∀ z, sectionValue x z = h z * (sectionValue y₁ z * sectionValue y₂ z))
    (hdense : Dense {z | sectionValue y₁ z * sectionValue y₂ z ≠ 0}) (z : ℂ) :
    ‖h z‖ ≤ 1 := by
  have hw : ContDiff ℝ 2 fun z ↦ Real.log (‖h z‖ ^ 2) :=
    (hh.norm_sq ℝ).log fun z ↦ pow_ne_zero 2 (norm_ne_zero_iff.2 (hh₀ z))
  -- The scalar equation for `w = log |h|²` holds off the zeros of `α_{y₁} α_{y₂}`, hence
  -- everywhere.
  have hΔ : Δ (fun z ↦ Real.log (‖h z‖ ^ 2)) = fun z ↦
      (‖h z‖ ^ 2 * (‖sectionValue y₁ z‖ ^ 2 * ‖sectionValue y₂ z‖ ^ 2) -
        ‖sectionValue y₁ z‖ ^ 2 - ‖sectionValue y₂ z‖ ^ 2 + 1) / 4 :=
    hw.continuous_laplacian.ext_on hdense
      (((((hh.continuous.norm.pow 2).mul ((continuous_sq_norm_sectionValue hy₁).mul
        (continuous_sq_norm_sectionValue hy₂))).sub (continuous_sq_norm_sectionValue hy₁)).sub
        (continuous_sq_norm_sectionValue hy₂)).add continuous_const |>.div_const 4)
      fun z hz ↦ by
        rw [laplacian_log_norm_sq_eq_of_mul hx hy₁ hy₂ hxsol hy₁sol hy₂sol hh hh₀ hα hz, hα z,
          norm_mul, norm_mul, mul_pow, mul_pow]
  -- Where `|h| > 1`, the right side is at least `(1 - |α_{y₁}|²) (1 - |α_{y₂}|²) ≥ 0`.
  have hpos (z : ℂ) (hz : 0 < Real.log (‖h z‖ ^ 2)) : 0 ≤ Δ (fun z ↦ Real.log (‖h z‖ ^ 2)) z := by
    have h₁ : 1 < ‖h z‖ ^ 2 := by
      rwa [Real.log_pos_iff (by positivity)] at hz
    have hs₁ := norm_sectionValue_sq_le_one hy₁ hy₁sol hy₁lim z
    have hs₂ := norm_sectionValue_sq_le_one hy₂ hy₂sol hy₂lim z
    have hs : 0 ≤ ‖sectionValue y₁ z‖ ^ 2 * ‖sectionValue y₂ z‖ ^ 2 := by positivity
    rw [hΔ]
    nlinarith [mul_nonneg (sub_nonneg.2 hs₁) (sub_nonneg.2 hs₂)]
  -- At infinity `|h|² = |α_x|² / (|α_{y₁}|² |α_{y₂}|²) → 1`, so `w → 0`.
  have hlim : Tendsto (fun z ↦ Real.log (‖h z‖ ^ 2)) (cocompact ℂ) (𝓝 0) := by
    simp_rw [← sq_norm_sectionValue] at hxlim hy₁lim hy₂lim
    have hdiv := hxlim.div (hy₁lim.mul hy₂lim) (by norm_num)
    rw [mul_one, div_one] at hdiv
    have hnorm : Tendsto (fun z ↦ ‖h z‖ ^ 2) (cocompact ℂ) (𝓝 1) := by
      refine hdiv.congr' ?_
      filter_upwards [(hy₁lim.mul hy₂lim).eventually_ne (by norm_num : (1 : ℝ) * 1 ≠ 0)] with z hz
      rw [Pi.div_apply, div_eq_iff hz, hα z, norm_mul, norm_mul, mul_pow, mul_pow]
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hnorm
    rwa [Real.log_one] at hlog
  have hw₀ := nonpos_of_tendsto_cocompact_of_laplacian_nonneg hw hpos hlim z
  rw [Real.log_nonpos_iff (by positivity)] at hw₀
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hw₀

/-- **The zeros of a vortex with divisor `D₁ + D₂` against the two clusters.** Let `x`, `y₁`, `y₂`
be fields on the plane with `C^k` connection and differentiable section components (`1 ≤ k`),
solving the holomorphicity rows, with zero multiplicities `m₁ + m₂`, `m₁` and `m₂`. Then
`α_x = h α_{y₁} α_{y₂}` for a nowhere-vanishing `C^k` function `h`. -/
theorem exists_contDiff_sectionValue_eq_mul_mul_of_add {k : ℕ∞} (hk : 1 ≤ k) {m₁ m₂ : ℂ → ℕ}
    (hxb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hxb₂ : ContDiff ℝ k (fun w ↦ x w 1))
    (hxp : Differentiable ℝ (fun w ↦ x w 2)) (hxq : Differentiable ℝ (fun w ↦ x w 3))
    (hxhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hy₁b₁ : ContDiff ℝ k (fun w ↦ y₁ w 0)) (hy₁b₂ : ContDiff ℝ k (fun w ↦ y₁ w 1))
    (hy₁p : Differentiable ℝ (fun w ↦ y₁ w 2)) (hy₁q : Differentiable ℝ (fun w ↦ y₁ w 3))
    (hy₁hol : ∀ w, equation y₁ w 1 = 0 ∧ equation y₁ w 2 = 0)
    (hy₂b₁ : ContDiff ℝ k (fun w ↦ y₂ w 0)) (hy₂b₂ : ContDiff ℝ k (fun w ↦ y₂ w 1))
    (hy₂p : Differentiable ℝ (fun w ↦ y₂ w 2)) (hy₂q : Differentiable ℝ (fun w ↦ y₂ w 3))
    (hy₂hol : ∀ w, equation y₂ w 1 = 0 ∧ equation y₂ w 2 = 0)
    (hm : IsZeroMultiplicity (sectionValue x) (m₁ + m₂))
    (hm₁ : IsZeroMultiplicity (sectionValue y₁) m₁)
    (hm₂ : IsZeroMultiplicity (sectionValue y₂) m₂) :
    ∃ h : ℂ → ℂ, ContDiff ℝ k h ∧ (∀ z, h z ≠ 0) ∧
      ∀ z, sectionValue x z = h z * (sectionValue y₁ z * sectionValue y₂ z) := by
  -- The connection components of the product field are the sums of those of the factors.
  have hb₁ : ContDiff ℝ k fun w ↦ mulField y₁ y₂ w 0 := by
    simpa only [mulField_apply_zero] using hy₁b₁.add hy₂b₁
  have hb₂ : ContDiff ℝ k fun w ↦ mulField y₁ y₂ w 1 := by
    simpa only [mulField_apply_one] using hy₁b₂.add hy₂b₂
  obtain ⟨h, hh, hh₀, hα⟩ := exists_contDiff_sectionValue_eq_mul hk hxb₁ hxb₂ hxp hxq hxhol hb₁ hb₂
    (fun w ↦ differentiableAt_mulField_apply_two (hy₁p w) (hy₁q w) (hy₂p w) (hy₂q w))
    (fun w ↦ differentiableAt_mulField_apply_three (hy₁p w) (hy₁q w) (hy₂p w) (hy₂q w))
    (fun w ↦ equation_mulField_apply_one_eq_zero_and_apply_two_eq_zero (hy₁p w) (hy₁q w)
      (hy₂p w) (hy₂q w) (hy₁hol w) (hy₂hol w))
    (isZeroMultiplicity_iff.1 hm)
    (isZeroMultiplicity_iff.1 (isZeroMultiplicity_sectionValue_mulField hm₁ hm₂))
  exact ⟨h, hh, hh₀, fun z ↦ by rw [hα z, sectionValue_mulField]⟩

/-- **A vortex is dominated by the vortices of its clusters.** Let `x`, `y₁`, `y₂` be `C²`
vortices on the plane with `|α| → 1` at infinity and zero divisors `D₁ + D₂`, `D₁` and `D₂`.
Then `|α_x| ≤ |α_{y₁}| |α_{y₂}|` everywhere. -/
theorem norm_sectionValue_le_mul_of_add {D₁ D₂ : Multiset ℂ}
    (hx : ContDiff ℝ 2 x) (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂)
    (hxsol : ∀ z, equation x z = 0) (hy₁sol : ∀ z, equation y₁ z = 0)
    (hy₂sol : ∀ z, equation y₂ z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₁lim : Tendsto (fun z ↦ 4 * (y₁ z 2 ^ 2 + y₁ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₂lim : Tendsto (fun z ↦ 4 * (y₂ z 2 ^ 2 + y₂ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) (Multiset.count · (D₁ + D₂)))
    (hD₁ : IsZeroMultiplicity (sectionValue y₁) (Multiset.count · D₁))
    (hD₂ : IsZeroMultiplicity (sectionValue y₂) (Multiset.count · D₂)) (z : ℂ) :
    ‖sectionValue x z‖ ≤ ‖sectionValue y₁ z‖ * ‖sectionValue y₂ z‖ := by
  have hhol (u : ℂ → EuclideanSpace ℝ (Fin 4)) (hsol : ∀ z, equation u z = 0) (w : ℂ) :
      equation u w 1 = 0 ∧ equation u w 2 = 0 := by
    simp [hsol w]
  have hcount : (Multiset.count · (D₁ + D₂)) = (Multiset.count · D₁) + (Multiset.count · D₂) :=
    funext fun z ↦ Multiset.count_add z D₁ D₂
  obtain ⟨h, hh, hh₀, hα⟩ := exists_contDiff_sectionValue_eq_mul_mul_of_add (k := 2) (by norm_num)
    (contDiff_apply hx 0) (contDiff_apply hx 1) (differentiable_apply hx 2)
    (differentiable_apply hx 3) (hhol x hxsol) (contDiff_apply hy₁ 0) (contDiff_apply hy₁ 1)
    (differentiable_apply hy₁ 2) (differentiable_apply hy₁ 3) (hhol y₁ hy₁sol)
    (contDiff_apply hy₂ 0) (contDiff_apply hy₂ 1) (differentiable_apply hy₂ 2)
    (differentiable_apply hy₂ 3) (hhol y₂ hy₂sol) (hcount ▸ hD) hD₁ hD₂
  -- The zeros of `α_{y₁} α_{y₂}` lie in the finite set `D₁ + D₂`, so they have empty interior.
  have hsub : {z | sectionValue y₁ z * sectionValue y₂ z = 0} ⊆ ↑(D₁ + D₂).toFinset := by
    intro z hz
    rw [Set.mem_ofPred_eq, ← (hD₁.mul hD₂).pos_iff, Pi.add_apply, ← Multiset.count_add,
      Multiset.count_pos] at hz
    simpa using hz
  have hdense : Dense {z | sectionValue y₁ z * sectionValue y₂ z ≠ 0} :=
    ((D₁ + D₂).toFinset.finite_toSet.subset hsub).countable.dense_compl ℝ
  rw [hα z, norm_mul, ← norm_mul (sectionValue y₁ z)]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_le_one_of_sectionValue_eq_mul hx hy₁ hy₂
    hxsol hy₁sol hy₂sol hxlim hy₁lim hy₂lim hh hh₀ hα hdense z)

/-- **Adding zeros decreases the modulus of a vortex.** Let `x` and `y` be `C²` vortices on the
plane with `|α| → 1` at infinity and zero divisors `D₁ + D₂` and `D₁`. Then `|α_x| ≤ |α_y|`
everywhere. -/
theorem norm_sectionValue_le_of_add {y : ℂ → EuclideanSpace ℝ (Fin 4)} {D₁ D₂ : Multiset ℂ}
    (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y)
    (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hylim : Tendsto (fun z ↦ 4 * (y z 2 ^ 2 + y z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) (Multiset.count · (D₁ + D₂)))
    (hD₁ : IsZeroMultiplicity (sectionValue y) (Multiset.count · D₁)) (z : ℂ) :
    ‖sectionValue x z‖ ≤ ‖sectionValue y z‖ := by
  -- A vortex with divisor `D₂` exists by Taubes's existence theorem.
  obtain ⟨y₂, hy₂, hy₂sol, hy₂fr, hD₂⟩ :=
    exists_contDiff_equation_eq_zero_isZeroMultiplicity (⟨D₂, rfl⟩ : Sym ℂ (Multiset.card D₂))
  have hy₂lim := tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hy₂fr
  have hy₂' : ContDiff ℝ 2 y₂ := hy₂.of_le (by simp)
  have h₂ : ‖sectionValue y₂ z‖ ≤ 1 :=
    (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
      (norm_sectionValue_sq_le_one hy₂' hy₂sol hy₂lim z)
  calc ‖sectionValue x z‖ ≤ ‖sectionValue y z‖ * ‖sectionValue y₂ z‖ :=
        norm_sectionValue_le_mul_of_add hx hy hy₂' hxsol hysol hy₂sol hxlim hylim hy₂lim hD hD₁
          hD₂ z
    _ ≤ ‖sectionValue y z‖ := mul_le_of_le_one_right (norm_nonneg _) h₂

end Comparison

/-! ### The overlap identity -/

section Overlap

variable {x y₁ y₂ : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The flux identity `∫ (1 - |α|²) = 16 π deg D` in terms of `|α|`. -/
private theorem integral_one_sub_norm_sectionValue_sq {u : ℂ → EuclideanSpace ℝ (Fin 4)}
    {D : Multiset ℂ} (hu : ContDiff ℝ 2 u) (hsol : ∀ z, equation u z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (u z 2 ^ 2 + u z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue u) (Multiset.count · D)) :
    ∫ z, (1 - ‖sectionValue u z‖ ^ 2) = 16 * Real.pi * Multiset.card D := by
  simpa only [sq_norm_sectionValue] using integral_one_sub_normSq_eq_mul_card
    (contDiff_apply hu 0) (contDiff_apply hu 1) (contDiff_apply hu 2) (contDiff_apply hu 3) hsol
    hlim hD

/-- The defect `1 - |α|²` of a vortex with `|α| → 1` at infinity is integrable. -/
private theorem integrable_one_sub_norm_sectionValue_sq {u : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hu : ContDiff ℝ 2 u) (hsol : ∀ z, equation u z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (u z 2 ^ 2 + u z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Integrable fun z ↦ 1 - ‖sectionValue u z‖ ^ 2 := by
  simpa only [sq_norm_sectionValue] using integrable_one_sub_normSq (μ := volume)
    (contDiff_apply hu 2) (contDiff_apply hu 3) hsol hlim

/-- The overlap `(1 - |α_{y₁}|²) (1 - |α_{y₂}|²)` of the defects of two vortices with `|α| → 1` at
infinity is integrable. -/
theorem integrable_one_sub_sq_norm_sectionValue_mul_one_sub (hy₁ : ContDiff ℝ 2 y₁)
    (hy₂ : ContDiff ℝ 2 y₂)
    (hy₁sol : ∀ z, equation y₁ z = 0) (hy₂sol : ∀ z, equation y₂ z = 0)
    (hy₁lim : Tendsto (fun z ↦ 4 * (y₁ z 2 ^ 2 + y₁ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₂lim : Tendsto (fun z ↦ 4 * (y₂ z 2 ^ 2 + y₂ z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Integrable fun z ↦ (1 - ‖sectionValue y₁ z‖ ^ 2) * (1 - ‖sectionValue y₂ z‖ ^ 2) := by
  refine (integrable_one_sub_norm_sectionValue_sq hy₁ hy₁sol hy₁lim).mul_bdd (c := 1)
    (continuous_const.sub (continuous_sq_norm_sectionValue hy₂)).aestronglyMeasurable
    (.of_forall fun z ↦ ?_)
  have h₂ := norm_sectionValue_sq_le_one hy₂ hy₂sol hy₂lim z
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [sq_nonneg ‖sectionValue y₂ z‖]

/-- The comparison error `|α_x|² - |α_{y₁}|² |α_{y₂}|²` of three vortices with `|α| → 1` at
infinity is integrable: it is a combination of the three defects and the overlap. -/
theorem integrable_sq_norm_sectionValue_sub_mul
    (hx : ContDiff ℝ 2 x) (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂)
    (hxsol : ∀ z, equation x z = 0) (hy₁sol : ∀ z, equation y₁ z = 0)
    (hy₂sol : ∀ z, equation y₂ z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₁lim : Tendsto (fun z ↦ 4 * (y₁ z 2 ^ 2 + y₁ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₂lim : Tendsto (fun z ↦ 4 * (y₂ z 2 ^ 2 + y₂ z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Integrable fun z ↦
      ‖sectionValue x z‖ ^ 2 - ‖sectionValue y₁ z‖ ^ 2 * ‖sectionValue y₂ z‖ ^ 2 := by
  refine ((((integrable_one_sub_norm_sectionValue_sq hy₁ hy₁sol hy₁lim).add
    (integrable_one_sub_norm_sectionValue_sq hy₂ hy₂sol hy₂lim)).sub
    (integrable_one_sub_norm_sectionValue_sq hx hxsol hxlim)).sub
    (integrable_one_sub_sq_norm_sectionValue_mul_one_sub hy₁ hy₂ hy₁sol hy₂sol hy₁lim
      hy₂lim)).congr (.of_forall fun z ↦ ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- **The overlap identity.** Let `x`, `y₁`, `y₂` be `C²` vortices on the plane with `|α| → 1` at
infinity and zero divisors `D₁ + D₂`, `D₁` and `D₂`. The `L¹` distance between `|α_x|²` and the
product `|α_{y₁}|² |α_{y₂}|²` is the overlap of the defects of `y₁` and `y₂`:

`∫ | |α_x|² - |α_{y₁}|² |α_{y₂}|² | = ∫ (1 - |α_{y₁}|²) (1 - |α_{y₂}|²)`. -/
theorem integral_abs_sq_norm_sectionValue_sub_mul_eq {D₁ D₂ : Multiset ℂ}
    (hx : ContDiff ℝ 2 x) (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂)
    (hxsol : ∀ z, equation x z = 0) (hy₁sol : ∀ z, equation y₁ z = 0)
    (hy₂sol : ∀ z, equation y₂ z = 0)
    (hxlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₁lim : Tendsto (fun z ↦ 4 * (y₁ z 2 ^ 2 + y₁ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₂lim : Tendsto (fun z ↦ 4 * (y₂ z 2 ^ 2 + y₂ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) (Multiset.count · (D₁ + D₂)))
    (hD₁ : IsZeroMultiplicity (sectionValue y₁) (Multiset.count · D₁))
    (hD₂ : IsZeroMultiplicity (sectionValue y₂) (Multiset.count · D₂)) :
    ∫ z, |‖sectionValue x z‖ ^ 2 - ‖sectionValue y₁ z‖ ^ 2 * ‖sectionValue y₂ z‖ ^ 2| =
      ∫ z, (1 - ‖sectionValue y₁ z‖ ^ 2) * (1 - ‖sectionValue y₂ z‖ ^ 2) := by
  -- Pointwise, `|α_x|² ≤ |α_{y₁}|² |α_{y₂}|²`, so the absolute value is a sum of the three
  -- defects and the overlap.
  have hpt (z : ℂ) :
      |‖sectionValue x z‖ ^ 2 - ‖sectionValue y₁ z‖ ^ 2 * ‖sectionValue y₂ z‖ ^ 2| =
        (1 - ‖sectionValue x z‖ ^ 2) - (1 - ‖sectionValue y₁ z‖ ^ 2) -
          (1 - ‖sectionValue y₂ z‖ ^ 2) +
          (1 - ‖sectionValue y₁ z‖ ^ 2) * (1 - ‖sectionValue y₂ z‖ ^ 2) := by
    have hle := pow_le_pow_left₀ (norm_nonneg _) (norm_sectionValue_le_mul_of_add hx hy₁ hy₂
      hxsol hy₁sol hy₂sol hxlim hy₁lim hy₂lim hD hD₁ hD₂ z) 2
    rw [mul_pow] at hle
    rw [abs_of_nonpos (sub_nonpos.2 hle)]
    ring
  have hix := integrable_one_sub_norm_sectionValue_sq hx hxsol hxlim
  have hi₁ := integrable_one_sub_norm_sectionValue_sq hy₁ hy₁sol hy₁lim
  have hi₂ := integrable_one_sub_norm_sectionValue_sq hy₂ hy₂sol hy₂lim
  have hi₃ : Integrable fun z ↦
      (1 - ‖sectionValue x z‖ ^ 2) - (1 - ‖sectionValue y₁ z‖ ^ 2) -
        (1 - ‖sectionValue y₂ z‖ ^ 2) :=
    (hix.sub hi₁).sub hi₂
  have hi₄ : Integrable fun z ↦ (1 - ‖sectionValue x z‖ ^ 2) - (1 - ‖sectionValue y₁ z‖ ^ 2) :=
    hix.sub hi₁
  rw [funext hpt, integral_add hi₃
      (integrable_one_sub_sq_norm_sectionValue_mul_one_sub hy₁ hy₂ hy₁sol hy₂sol hy₁lim hy₂lim),
    integral_sub hi₄ hi₂, integral_sub hix hi₁,
    integral_one_sub_norm_sectionValue_sq hx hxsol hxlim hD,
    integral_one_sub_norm_sectionValue_sq hy₁ hy₁sol hy₁lim hD₁,
    integral_one_sub_norm_sectionValue_sq hy₂ hy₂sol hy₂lim hD₂, Multiset.card_add]
  push_cast
  ring

/-- The overlap of the defect of `y₁` with the defect of the translate `z ↦ y₂ (z + a)` tends to
zero as `a → ∞`, by dominated convergence: it is bounded by the integrable defect of `y₁`, and
tends to zero pointwise because `|α_{y₂}| → 1` at infinity. -/
private theorem tendsto_integral_one_sub_mul_one_sub_comp_add (hy₁ : ContDiff ℝ 2 y₁)
    (hy₂ : ContDiff ℝ 2 y₂) (hy₁sol : ∀ z, equation y₁ z = 0) (hy₂sol : ∀ z, equation y₂ z = 0)
    (hy₁lim : Tendsto (fun z ↦ 4 * (y₁ z 2 ^ 2 + y₁ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₂lim : Tendsto (fun z ↦ 4 * (y₂ z 2 ^ 2 + y₂ z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    Tendsto (fun a ↦ ∫ z, (1 - ‖sectionValue y₁ z‖ ^ 2) * (1 - ‖sectionValue y₂ (z + a)‖ ^ 2))
      (cocompact ℂ) (𝓝 0) := by
  have : (cocompact ℂ).IsCountablyGenerated := by
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
    infer_instance
  have hc₁ := continuous_sq_norm_sectionValue hy₁
  have hc₂ := continuous_sq_norm_sectionValue hy₂
  have hlim₂ : Tendsto (fun z ↦ ‖sectionValue y₂ z‖ ^ 2) (cocompact ℂ) (𝓝 1) := by
    simpa only [sq_norm_sectionValue] using hy₂lim
  have hbound (a z : ℂ) : ‖(1 - ‖sectionValue y₁ z‖ ^ 2) * (1 - ‖sectionValue y₂ (z + a)‖ ^ 2)‖ ≤
      1 - ‖sectionValue y₁ z‖ ^ 2 := by
    have h₁ := norm_sectionValue_sq_le_one hy₁ hy₁sol hy₁lim z
    have h₂ := norm_sectionValue_sq_le_one hy₂ hy₂sol hy₂lim (z + a)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂))]
    exact mul_le_of_le_one_right (sub_nonneg.2 h₁)
      (by nlinarith [sq_nonneg ‖sectionValue y₂ (z + a)‖])
  have hpt (z : ℂ) : Tendsto (fun a ↦
      (1 - ‖sectionValue y₁ z‖ ^ 2) * (1 - ‖sectionValue y₂ (z + a)‖ ^ 2)) (cocompact ℂ) (𝓝 0) := by
    have h₂ : Tendsto (fun a ↦ ‖sectionValue y₂ (z + a)‖ ^ 2) (cocompact ℂ) (𝓝 1) :=
      hlim₂.comp (Homeomorph.addLeft z).isClosedEmbedding.tendsto_cocompact
    have h := (tendsto_const_nhds (x := 1 - ‖sectionValue y₁ z‖ ^ 2)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub h₂)
    rwa [sub_self, mul_zero] at h
  simpa using tendsto_integral_filter_of_dominated_convergence (l := cocompact ℂ) (μ := volume)
    (f := fun _ ↦ (0 : ℝ)) (fun z ↦ 1 - ‖sectionValue y₁ z‖ ^ 2)
    (.of_forall fun a ↦ ((continuous_const.sub hc₁).mul
      (continuous_const.sub (hc₂.comp (continuous_id.add continuous_const)))).aestronglyMeasurable)
    (.of_forall fun a ↦ .of_forall (hbound a))
    (integrable_one_sub_norm_sectionValue_sq hy₁ hy₁sol hy₁lim) (.of_forall hpt)

/-- **Separated clusters.** Let `y₁` and `y₂` be `C²` vortices on the plane with `|α| → 1` at
infinity and zero divisors `D₁` and `D₂`, and for each `a ∈ ℂ` let `x a` be a `C²` vortex with
`|α| → 1` at infinity whose zero divisor is `D₁` together with the translate `D₂ - a`. As the
second cluster moves off to infinity, `|α_{x a}|²` approaches `|α_{y₁}|² |α_{y₂}(· + a)|²` in
`L¹`:

`∫ | |α_{x a}(z)|² - |α_{y₁}(z)|² |α_{y₂}(z + a)|² | → 0`  as `a → ∞`. -/
theorem tendsto_integral_abs_sq_norm_sectionValue_sub_mul {D₁ D₂ : Multiset ℂ}
    {x : ℂ → ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ∀ a, ContDiff ℝ 2 (x a)) (hy₁ : ContDiff ℝ 2 y₁) (hy₂ : ContDiff ℝ 2 y₂)
    (hxsol : ∀ a z, equation (x a) z = 0) (hy₁sol : ∀ z, equation y₁ z = 0)
    (hy₂sol : ∀ z, equation y₂ z = 0)
    (hxlim : ∀ a, Tendsto (fun z ↦ 4 * (x a z 2 ^ 2 + x a z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₁lim : Tendsto (fun z ↦ 4 * (y₁ z 2 ^ 2 + y₁ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hy₂lim : Tendsto (fun z ↦ 4 * (y₂ z 2 ^ 2 + y₂ z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hD : ∀ a, IsZeroMultiplicity (sectionValue (x a))
      (Multiset.count · (D₁ + D₂.map (· - a))))
    (hD₁ : IsZeroMultiplicity (sectionValue y₁) (Multiset.count · D₁))
    (hD₂ : IsZeroMultiplicity (sectionValue y₂) (Multiset.count · D₂)) :
    Tendsto (fun a ↦ ∫ z, |‖sectionValue (x a) z‖ ^ 2 -
      ‖sectionValue y₁ z‖ ^ 2 * ‖sectionValue y₂ (z + a)‖ ^ 2|) (cocompact ℂ) (𝓝 0) := by
  -- The translate `z ↦ y₂ (z + a)` is a vortex with divisor `D₂ - a`, so the overlap identity
  -- applies to it.
  have hover (a : ℂ) : ∫ z, |‖sectionValue (x a) z‖ ^ 2 -
      ‖sectionValue y₁ z‖ ^ 2 * ‖sectionValue y₂ (z + a)‖ ^ 2| =
        ∫ z, (1 - ‖sectionValue y₁ z‖ ^ 2) * (1 - ‖sectionValue y₂ (z + a)‖ ^ 2) := by
    simpa only [sectionValue_translateField] using
      integral_abs_sq_norm_sectionValue_sub_mul_eq (hx a) hy₁ (contDiff_translateField hy₂ a)
        (hxsol a) hy₁sol (fun z ↦ by rw [equation_translateField]; exact hy₂sol _) (hxlim a)
        hy₁lim (tendsto_comp_translateField (f := fun v ↦ 4 * (v 2 ^ 2 + v 3 ^ 2)) hy₂lim a)
        (hD a) hD₁ (isZeroMultiplicity_sectionValue_translateField hD₂ a)
  simp_rw [hover]
  exact tendsto_integral_one_sub_mul_one_sub_comp_add hy₁ hy₂ hy₁sol hy₂sol hy₁lim hy₂lim

end Overlap

end TauCeti.Vortex
