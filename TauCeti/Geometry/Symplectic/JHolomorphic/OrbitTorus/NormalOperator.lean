/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.ODE.DysonSeries
public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.MeasureTheory.Integral.Rectangle

/-!
# The kernel of the model normal operator of an orbit torus

Let `γ` be a closed orbit of period `d` of the suspension flow of a surface diffeomorphism, and
let `C = S¹ × γ` be the corresponding orbit torus in `S¹ × Y_φ`, with coordinates `s ∈ ℝ / ℤ`
along the circle factor and `t ∈ ℝ / dℤ` along `γ`. In a unitary trivialization of its normal
bundle the normal operator of `C` is independent of `s`:

`D u = ∂s u + A u`,  `A u = J₀ ∂t u + S(t) u`,

with `J₀` an orthogonal complex structure on the fibre `V` and `S(t)` a `d`-periodic path of
symmetric operators. The asymptotic operator `A` is formally self-adjoint, and the twisted
versions of `D` act on maps `u : ℝ × ℝ → V` with `u (s + 1, t) = ε₁ u (s, t)` and
`u (s, t + d) = ε₂ u (s, t)` for signs `ε₁, ε₂`, which are the four real sign characters of the
torus. This file computes the kernels of these four operators.

The integrated form of `D* D = -∂s² + A²` is the energy identity
(`TauCeti.setIntegral_norm_sq_orbitTorusOperator`): over the fundamental rectangle,

`∫ ‖D u‖² = ∫ (‖∂s u‖² + ‖A u‖²)`.

The cross term `2 ⟪∂s u, A u⟫` is a sum of an `s`-derivative and a `t`-derivative of quantities
that are periodic because `ε₁² = ε₂² = 1`, so it integrates to zero. Consequently every kernel
element is independent of `s`. For the two characters twisted along the circle factor
(`ε₁ = -1`) this forces `u = 0`
(`TauCeti.eq_zero_of_orbitTorusOperator_eq_zero_of_antiperiodic`). For the two characters
untwisted along the circle factor (`ε₁ = 1`), a kernel element is a solution of the loop equation
`w' = J₀ S(t) w`, hence `u (s, t) = Ψ(t) (u 0)` with `Ψ` the propagator of that equation, and its
value at the origin lies in the `ε₂`-eigenspace of the return map `Ψ(d)`, nonzero exactly when
`u` is. Conversely every such eigenvector produces a nonzero kernel element. In finite dimension
the kernel is therefore nonzero exactly when `det (ε₂ - Ψ(d)) = 0`
(`TauCeti.exists_ne_zero_orbitTorusOperator_eq_zero_iff_det_eq_zero`): the untwisted operator
is degenerate exactly when `det (1 - Ψ(d)) = 0`, and the operator twisted along `γ` exactly when
`det (1 + Ψ(d)) = 0`. In the geometric application `Ψ(d)` is the linearized return map of the
orbit, written in the chosen trivialization.

These are statements about the model operator in a fixed trivialization. Identifying the normal
operator of an actual orbit torus with this model, and the determinant signs of the four twisted
operators, are separate.

## Main results

* `TauCeti.orbitTorusOperator`: the operator `D u = ∂s u + (J₀ ∂t u + S(t) u)`.
* `TauCeti.setIntegral_norm_sq_orbitTorusOperator`: the energy identity on the fundamental
  rectangle.
* `TauCeti.fderiv_apply_stdComplexLineReal_eq_zero_of_orbitTorusOperator_eq_zero`: kernel
  elements are independent of `s`.
* `TauCeti.eq_zero_of_orbitTorusOperator_eq_zero_of_antiperiodic`: the operators twisted along
  the circle factor have no kernel.
* `TauCeti.apply_eq_dysonSeriesLeft_apply_of_orbitTorusOperator_eq_zero`,
  `TauCeti.dysonSeriesLeft_apply_eq_smul_of_orbitTorusOperator_eq_zero` and
  `TauCeti.orbitTorusOperator_dysonSeriesLeft_apply_eq_zero`: the kernel of the operators
  untwisted along the circle factor is described by the propagator and the return map.
* `TauCeti.exists_ne_zero_orbitTorusOperator_eq_zero_iff_det_eq_zero`: such a kernel is nonzero
  exactly when `det (ε₂ - Ψ(d)) = 0`.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*,
  Algebraic & Geometric Topology 5 (2005), 301--354.
* D. Salamon, *Lectures on Floer homology*, in Symplectic Geometry and Topology,
  IAS/Park City Math. Ser. 7 (1999), Section 2, for the operator `∂s + A` with `A` self-adjoint.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace TauCeti

section Operator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J₀ : V →L[ℝ] V} {S : ℝ → V →L[ℝ] V} {u : ℝ × ℝ → V} {ε₁ ε₂ d : ℝ}

/-- The model normal operator `D u = ∂s u + (J₀ ∂t u + S(t) u)` of an orbit torus, acting on maps
`u : ℝ × ℝ → V` with `s` the first and `t` the second coordinate. Here `∂s u` and `∂t u` are the
derivatives of `u` in the directions `(1, 0)` and `(0, 1)`. -/
def orbitTorusOperator (J₀ : V →L[ℝ] V) (S : ℝ → V →L[ℝ] V) (u : ℝ × ℝ → V) (z : ℝ × ℝ) : V :=
  fderiv ℝ u z stdComplexLineReal + (J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z))

/-- Unfolding `orbitTorusOperator` at a point. -/
theorem orbitTorusOperator_apply (z : ℝ × ℝ) :
    orbitTorusOperator J₀ S u z =
      fderiv ℝ u z stdComplexLineReal + (J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z)) :=
  (rfl)

/-- The orbit-torus operator vanishes on the zero map. -/
@[simp]
theorem orbitTorusOperator_zero : orbitTorusOperator J₀ S (0 : ℝ × ℝ → V) = 0 := by
  funext z
  simp [orbitTorusOperator_apply]

/-- The orbit-torus operator is additive on maps differentiable at the point. -/
theorem orbitTorusOperator_add {v : ℝ × ℝ → V} {z : ℝ × ℝ} (hu : DifferentiableAt ℝ u z)
    (hv : DifferentiableAt ℝ v z) :
    orbitTorusOperator J₀ S (u + v) z =
      orbitTorusOperator J₀ S u z + orbitTorusOperator J₀ S v z := by
  simp only [orbitTorusOperator_apply, fderiv_add hu hv, add_apply, map_add,
    Pi.add_apply]
  abel

/-- The orbit-torus operator commutes with multiplication by a real scalar. -/
@[simp]
theorem orbitTorusOperator_smul (c : ℝ) :
    orbitTorusOperator J₀ S (c • u) = c • orbitTorusOperator J₀ S u := by
  funext z
  simp only [orbitTorusOperator_apply, fderiv_const_smul_field, Pi.smul_apply,
    smul_apply, map_smul, smul_add]

/-- The cross term `⟪∂s u, J₀ ∂t u + S(t) u⟫` of `‖D u‖²` integrates to zero over the fundamental
rectangle: it is half of `∂s ⟪u, S u + J₀ ∂t u⟫ - ∂t ⟪u, J₀ ∂s u⟫`, and both potentials are
periodic because the twists square to one. -/
private theorem setIntegral_inner_fderiv_eq_zero
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hScont : Continuous S) (hu : ContDiff ℝ 2 u) (hε₁ : ε₁ ^ 2 = 1) (hε₂ : ε₂ ^ 2 = 1)
    (hs : ∀ s t, u (s + 1, t) = ε₁ • u (s, t)) (ht : ∀ s t, u (s, t + d) = ε₂ • u (s, t)) :
    ∫ z in Icc (0 : ℝ) 1 ×ˢ Icc 0 d,
      ⟪fderiv ℝ u z stdComplexLineReal, J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z)⟫ =
      0 := by
  set e₁ := stdComplexLineReal
  set e₂ := stdComplexLineImag
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hdu1 : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero
  have hddu : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) le_rfl).continuous_fderiv one_ne_zero
  have hus (s t : ℝ) : HasDerivAt (fun s => u (s, t)) (fderiv ℝ u (s, t) e₁) s :=
    (hu1 _).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_prodMk_left s t)
  have hut (s t : ℝ) : HasDerivAt (fun t => u (s, t)) (fderiv ℝ u (s, t) e₂) t :=
    (hu1 _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_prodMk_right s t)
  have hs' (s t : ℝ) : fderiv ℝ u (s + 1, t) = ε₁ • fderiv ℝ u (s, t) := by
    simpa using fderiv_add_eq_smul (c := ((1 : ℝ), (0 : ℝ)))
      (fun ⟨a, b⟩ => by simpa using hs a b) (s, t)
  have ht' (s t : ℝ) : fderiv ℝ u (s, t + d) = ε₂ • fderiv ℝ u (s, t) := by
    simpa using fderiv_add_eq_smul (c := ((0 : ℝ), d)) (fun ⟨a, b⟩ => by simpa using ht a b) (s, t)
  -- `φ₁` is the `s`-derivative of `⟪u, S u⟫ + ⟪u, J₀ ∂t u⟫`.
  let φ₁ : ℝ × ℝ → ℝ := fun z =>
    (⟪u z, S z.2 (fderiv ℝ u z e₁)⟫ + ⟪fderiv ℝ u z e₁, S z.2 (u z)⟫) +
      (⟪u z, J₀ (fderiv ℝ (fderiv ℝ u) z e₁ e₂)⟫ + ⟪fderiv ℝ u z e₁, J₀ (fderiv ℝ u z e₂)⟫)
  -- `φ₂` is the `t`-derivative of `⟪u, J₀ ∂s u⟫`.
  let φ₂ : ℝ × ℝ → ℝ := fun z =>
    ⟪u z, J₀ (fderiv ℝ (fderiv ℝ u) z e₂ e₁)⟫ + ⟪fderiv ℝ u z e₂, J₀ (fderiv ℝ u z e₁)⟫
  have hu0 := hu.continuous
  have hφ₁ : Continuous φ₁ := by fun_prop
  have hφ₂ : Continuous φ₂ := by fun_prop
  have h₁ : ∫ z in Icc (0 : ℝ) 1 ×ˢ Icc 0 d, φ₁ z = 0 := by
    refine setIntegral_rect_eq_zero_of_hasDerivAt_fst hφ₁
      (Φ := fun z => ⟪u z, S z.2 (u z)⟫ + ⟪u z, J₀ (fderiv ℝ u z e₂)⟫)
      (fun s t => ((hus s t).inner ℝ ((S t).hasFDerivAt.comp_hasDerivAt s (hus s t))).add
        ((hus s t).inner ℝ (J₀.hasFDerivAt.comp_hasDerivAt s
          (hasDerivAt_fderiv_apply_fst (hdu1 _) e₂)))) fun t => ?_
    have h0 := hs 0 t
    have h0' := hs' 0 t
    rw [zero_add] at h0 h0'
    simp only [h0, h0', map_smul, smul_apply, real_inner_smul_left,
      real_inner_smul_right]
    linear_combination (⟪u (0, t), S t (u (0, t))⟫ + ⟪u (0, t), J₀ (fderiv ℝ u (0, t) e₂)⟫) * hε₁
  have h₂ : ∫ z in Icc (0 : ℝ) 1 ×ˢ Icc 0 d, φ₂ z = 0 := by
    refine setIntegral_rect_eq_zero_of_hasDerivAt_snd hφ₂
      (Φ := fun z => ⟪u z, J₀ (fderiv ℝ u z e₁)⟫)
      (fun s t => (hut s t).inner ℝ (J₀.hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_fderiv_apply_snd (hdu1 _) e₁))) fun s => ?_
    have h0 := ht s 0
    have h0' := ht' s 0
    rw [zero_add] at h0 h0'
    simp only [h0, h0', map_smul, smul_apply, real_inner_smul_left,
      real_inner_smul_right]
    linear_combination ⟪u (s, 0), J₀ (fderiv ℝ u (s, 0) e₁)⟫ * hε₂
  have hpt : (fun z : ℝ × ℝ => ⟪fderiv ℝ u z e₁, J₀ (fderiv ℝ u z e₂) + S z.2 (u z)⟫) =
      fun z => (φ₁ z - φ₂ z) / 2 := by
    funext z
    have k₁ : ⟪u z, S z.2 (fderiv ℝ u z e₁)⟫ = ⟪fderiv ℝ u z e₁, S z.2 (u z)⟫ := by
      rw [← hS, real_inner_comm]
    have k₂ : ⟪fderiv ℝ u z e₂, J₀ (fderiv ℝ u z e₁)⟫ =
        -⟪fderiv ℝ u z e₁, J₀ (fderiv ℝ u z e₂)⟫ := by
      rw [← hJ₀, real_inner_comm]
    have k₃ : fderiv ℝ (fderiv ℝ u) z e₁ e₂ = fderiv ℝ (fderiv ℝ u) z e₂ e₁ :=
      hu.contDiffAt.isSymmSndFDerivAt (by simp) e₁ e₂
    simp only [φ₁, φ₂, inner_add_right, k₁, k₂, k₃]
    ring
  have hR : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc 0 d) := isCompact_Icc.prod isCompact_Icc
  rw [hpt, integral_div, integral_sub (hφ₁.continuousOn.integrableOn_compact hR)
    (hφ₂.continuousOn.integrableOn_compact hR), h₁, h₂, sub_self, zero_div]

/-- **The energy identity for the orbit-torus operator.** For a `C²` map `u` which is twisted
periodic with signs `ε₁` in `s` and `ε₂` in `t`, with `J₀` skew-adjoint and `S` symmetric, the
`L²` norm of `D u = ∂s u + A u` over the fundamental rectangle `[0, 1] × [0, d]` splits as
`‖∂s u‖² + ‖A u‖²`, where `A u = J₀ ∂t u + S(t) u`. This is the integrated form of
`D* D = -∂s² + A²`. -/
theorem setIntegral_norm_sq_orbitTorusOperator
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hScont : Continuous S) (hu : ContDiff ℝ 2 u) (hε₁ : ε₁ ^ 2 = 1) (hε₂ : ε₂ ^ 2 = 1)
    (hs : ∀ s t, u (s + 1, t) = ε₁ • u (s, t)) (ht : ∀ s t, u (s, t + d) = ε₂ • u (s, t)) :
    ∫ z in Icc (0 : ℝ) 1 ×ˢ Icc 0 d, ‖orbitTorusOperator J₀ S u z‖ ^ 2 =
      ∫ z in Icc (0 : ℝ) 1 ×ˢ Icc 0 d, (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
        ‖J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z)‖ ^ 2) := by
  have hR : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc 0 d) := isCompact_Icc.prod isCompact_Icc
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hu0 := hu.continuous
  have hpt : (fun z => ‖orbitTorusOperator J₀ S u z‖ ^ 2) = fun z =>
      (‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
        ‖J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z)‖ ^ 2) +
      2 * ⟪fderiv ℝ u z stdComplexLineReal,
        J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z)⟫ := by
    funext z
    rw [orbitTorusOperator_apply, norm_add_sq_real]
    ring
  have h₁ : Continuous fun z : ℝ × ℝ => ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
      ‖J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z)‖ ^ 2 := by fun_prop
  have h₂ : Continuous fun z : ℝ × ℝ => 2 * ⟪fderiv ℝ u z stdComplexLineReal,
      J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z)⟫ := by fun_prop
  rw [hpt, integral_add (h₁.continuousOn.integrableOn_compact hR)
    (h₂.continuousOn.integrableOn_compact hR), integral_const_mul,
    setIntegral_inner_fderiv_eq_zero hJ₀ hS hScont hu hε₁ hε₂ hs ht, mul_zero, add_zero]

/-- **Elements of the kernel are independent of `s`.** If a twisted periodic `C²` map, with
twists squaring to one and period `d > 0` in `t`, solves `D u = 0`, then `∂s u = 0`
everywhere. -/
theorem fderiv_apply_stdComplexLineReal_eq_zero_of_orbitTorusOperator_eq_zero (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hScont : Continuous S) (hu : ContDiff ℝ 2 u) (hε₁ : ε₁ ^ 2 = 1) (hε₂ : ε₂ ^ 2 = 1)
    (hs : ∀ s t, u (s + 1, t) = ε₁ • u (s, t)) (ht : ∀ s t, u (s, t + d) = ε₂ • u (s, t))
    (hD : ∀ z, orbitTorusOperator J₀ S u z = 0) (z : ℝ × ℝ) :
    fderiv ℝ u z stdComplexLineReal = 0 := by
  have hdu : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hu0 := hu.continuous
  have hf : Continuous fun z : ℝ × ℝ => ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 +
      ‖J₀ (fderiv ℝ u z stdComplexLineImag) + S z.2 (u z)‖ ^ 2 := by fun_prop
  have hzero := eqOn_zero_of_setIntegral_rect_eq_zero zero_lt_one hd hf
      (fun z => by positivity) <| by
    rw [← setIntegral_norm_sq_orbitTorusOperator hJ₀ hS hScont hu hε₁ hε₂ hs ht]
    simp [hD]
  -- `‖∂s u‖` is periodic in both variables, so it suffices to look at the rectangle.
  have habs₁ : |ε₁| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg ε₁) two_ne_zero).1
    (by rw [sq_abs, hε₁])
  have habs₂ : |ε₂| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg ε₂) two_ne_zero).1
    (by rw [sq_abs, hε₂])
  set g : ℝ × ℝ → ℝ := fun z => ‖fderiv ℝ u z stdComplexLineReal‖
  have hg₁ (t : ℝ) : Function.Periodic (fun s => g (s, t)) 1 := fun s => by
    have := fderiv_add_eq_smul (c := ((1 : ℝ), (0 : ℝ))) (fun ⟨a, b⟩ => by simpa using hs a b)
      (s, t)
    simp only [Prod.mk_add_mk, add_zero] at this
    simp [g, this, norm_smul, habs₁]
  have hg₂ (s : ℝ) : Function.Periodic (fun t => g (s, t)) d := fun t => by
    have := fderiv_add_eq_smul (c := ((0 : ℝ), d)) (fun ⟨a, b⟩ => by simpa using ht a b) (s, t)
    simp only [Prod.mk_add_mk, add_zero] at this
    simp [g, this, norm_smul, habs₂]
  obtain ⟨s, t⟩ := z
  obtain ⟨s₀, hs₀, h₁⟩ := (hg₁ t).exists_mem_Ico₀ one_pos s
  obtain ⟨t₀, ht₀, h₂⟩ := (hg₂ s₀).exists_mem_Ico₀ hd t
  have h₀ := @hzero (s₀, t₀) ⟨Ico_subset_Icc_self hs₀, Ico_subset_Icc_self ht₀⟩
  have hg0 : g (s₀, t₀) = 0 := by
    have h₃ : 0 ≤ ‖J₀ (fderiv ℝ u (s₀, t₀) stdComplexLineImag) + S t₀ (u (s₀, t₀))‖ ^ 2 := by
      positivity
    have h₄ : 0 ≤ g (s₀, t₀) := norm_nonneg _
    simp only [Pi.zero_apply] at h₀
    nlinarith
  have hz : g (s, t) = 0 := by rw [h₁, h₂, hg0]
  simpa [g] using hz

/-- **Twisting along the circle factor kills the kernel.** A `C²` solution of `D u = 0` which is
antiperiodic in `s`, and twisted periodic in `t` with period `d > 0` and a sign `ε₂`, vanishes. -/
theorem eq_zero_of_orbitTorusOperator_eq_zero_of_antiperiodic (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫)
    (hScont : Continuous S) (hu : ContDiff ℝ 2 u) (hε₂ : ε₂ ^ 2 = 1)
    (hs : ∀ s t, u (s + 1, t) = -u (s, t)) (ht : ∀ s t, u (s, t + d) = ε₂ • u (s, t))
    (hD : ∀ z, orbitTorusOperator J₀ S u z = 0) : u = 0 := by
  have h0 := fderiv_apply_stdComplexLineReal_eq_zero_of_orbitTorusOperator_eq_zero (ε₁ := -1)
    hd hJ₀ hS hScont hu (by norm_num) hε₂ (fun s t => by rw [hs, neg_one_smul]) ht hD
  have hc := apply_eq_apply_zero_of_fderiv_fst_eq_zero (hu.differentiable (by norm_num)) h0
  funext ⟨s, t⟩
  have h1 := hs 0 t
  rw [zero_add, hc] at h1
  rw [Pi.zero_apply, hc]
  have h2 : (2 : ℝ) • u (0, t) = 0 := by rw [two_smul]; nth_rw 1 [h1]; exact neg_add_cancel _
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

section Complete

variable [CompleteSpace V]

/-- **The kernel without circle twist is given by the propagator.** If `J₀² = -1`, a `C²`
solution of `D u = 0` which is periodic in `s` is `u (s, t) = Ψ(t) (u 0)`, where
`Ψ = dysonSeriesLeft (J₀ ∘ S)` is the propagator of the loop equation `w' = J₀ S(t) w`. -/
theorem apply_eq_dysonSeriesLeft_apply_of_orbitTorusOperator_eq_zero (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫) (hScont : Continuous S) (hu : ContDiff ℝ 2 u)
    (hε₂ : ε₂ ^ 2 = 1) (hs : ∀ s t, u (s + 1, t) = u (s, t))
    (ht : ∀ s t, u (s, t + d) = ε₂ • u (s, t)) (hD : ∀ z, orbitTorusOperator J₀ S u z = 0)
    (z : ℝ × ℝ) : u z = dysonSeriesLeft (fun t => J₀ ∘L S t) z.2 (u 0) := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have h0 := fderiv_apply_stdComplexLineReal_eq_zero_of_orbitTorusOperator_eq_zero (ε₁ := 1)
    hd hJ₀ hS hScont hu (one_pow 2) hε₂ (fun s t => by rw [hs, one_smul]) ht hD
  have hc := apply_eq_apply_zero_of_fderiv_fst_eq_zero hu1 h0
  -- On the line `s = 0`, the equation `J₀ ∂t u + S u = 0` reads `∂t u = J₀ S u`.
  have hw (t : ℝ) : HasDerivAt (fun t => u (0, t)) ((J₀ ∘L S t) (u (0, t))) t := by
    have hl : HasDerivAt (fun t => u (0, t)) (fderiv ℝ u (0, t) stdComplexLineImag) t :=
      (hu1 _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_prodMk_right 0 t)
    have hz := hD (0, t)
    rw [orbitTorusOperator_apply, h0, zero_add, add_eq_zero_iff_eq_neg] at hz
    have hb : fderiv ℝ u (0, t) stdComplexLineImag = J₀ (S t (u (0, t))) := by
      have h2 := congrArg J₀ hz
      rwa [hJ₀sq, map_neg, neg_inj] at h2
    simpa [Function.comp_def, hb] using hl
  obtain ⟨s, t⟩ := z
  rw [hc, eq_dysonSeriesLeft_apply (continuous_const.clm_comp hScont) hw t]
  rfl

/-- **Return condition.** For a `C²` solution of `D u = 0` periodic in `s` and twisted by `ε₂`
in `t`, the value `u 0` lies in the `ε₂`-eigenspace of the return map `Ψ(d)`, that is,
`Ψ(d) (u 0) = ε₂ • u 0`. -/
theorem dysonSeriesLeft_apply_eq_smul_of_orbitTorusOperator_eq_zero (hd : 0 < d)
    (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫) (hScont : Continuous S) (hu : ContDiff ℝ 2 u)
    (hε₂ : ε₂ ^ 2 = 1) (hs : ∀ s t, u (s + 1, t) = u (s, t))
    (ht : ∀ s t, u (s, t + d) = ε₂ • u (s, t)) (hD : ∀ z, orbitTorusOperator J₀ S u z = 0) :
    dysonSeriesLeft (fun t => J₀ ∘L S t) d (u 0) = ε₂ • u 0 := by
  have h := apply_eq_dysonSeriesLeft_apply_of_orbitTorusOperator_eq_zero hd hJ₀ hJ₀sq hS hScont
    hu hε₂ hs ht hD (0, d)
  have h' := ht 0 0
  rw [zero_add] at h'
  rw [← h, h']
  rfl

/-- The propagator `Ψ` of the loop equation `w' = J₀ S(t) w`, applied to a vector `v` and
extended constantly in `s`, solves `D u = 0`. -/
theorem orbitTorusOperator_dysonSeriesLeft_apply_eq_zero (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hScont : Continuous S) (v : V) (z : ℝ × ℝ) :
    orbitTorusOperator J₀ S (fun z => dysonSeriesLeft (fun t => J₀ ∘L S t) z.2 v) z = 0 := by
  have hg := hasDerivAt_dysonSeriesLeft_apply
    ((continuous_const (y := J₀)).clm_comp hScont) v z.2
  have hf : HasFDerivAt (fun z : ℝ × ℝ => dysonSeriesLeft (fun t => J₀ ∘L S t) z.2 v) _ z :=
    (hasDerivAt_iff_hasFDerivAt.1 hg).comp z hasFDerivAt_snd
  rw [orbitTorusOperator_apply, hf.fderiv]
  simp [stdComplexLineReal, stdComplexLineImag, hJ₀sq]

end Complete

/-- **Nondegeneracy of the untwisted circle direction.** Let `V` be finite-dimensional, `J₀` an
orthogonal complex structure, and `S` a `C¹` path of symmetric operators with period `d > 0`.
The operator `D = ∂s + J₀ ∂t + S(t)` has a nonzero `C²` kernel element which is periodic in `s`
and twisted by the sign `ε₂` in `t` exactly when `det (ε₂ - Ψ(d)) = 0`, where `Ψ(d)` is the
return map of the loop equation `w' = J₀ S(t) w`. For `ε₂ = 1` this is `det (1 - Ψ(d)) = 0`, and
for `ε₂ = -1` it is `det (-1 - Ψ(d)) = 0`, equivalently `det (1 + Ψ(d)) = 0`. -/
theorem exists_ne_zero_orbitTorusOperator_eq_zero_iff_det_eq_zero [FiniteDimensional ℝ V]
    (hd : 0 < d) (hJ₀ : ∀ x y, ⟪J₀ x, y⟫ = -⟪x, J₀ y⟫) (hJ₀sq : ∀ x, J₀ (J₀ x) = -x)
    (hS : ∀ t x y, ⟪S t x, y⟫ = ⟪x, S t y⟫) (hS1 : ContDiff ℝ 1 S)
    (hper : Function.Periodic S d) (hε₂ : ε₂ ^ 2 = 1) :
    (∃ u : ℝ × ℝ → V, ContDiff ℝ 2 u ∧ u ≠ 0 ∧ (∀ s t, u (s + 1, t) = u (s, t)) ∧
      (∀ s t, u (s, t + d) = ε₂ • u (s, t)) ∧ ∀ z, orbitTorusOperator J₀ S u z = 0) ↔
      LinearMap.det
        ((ε₂ • 1 - dysonSeriesLeft (fun t => J₀ ∘L S t) d : V →L[ℝ] V) : V →ₗ[ℝ] V) = 0 := by
  set Ψ := dysonSeriesLeft (fun t => J₀ ∘L S t)
  have hScont := hS1.continuous
  have hM : Continuous fun t => J₀ ∘L S t := (continuous_const (y := J₀)).clm_comp hScont
  rw [LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨u, hu, hne, hs, ht, hD⟩
    refine ⟨u 0, ?_, fun h0 => hne ?_⟩
    · simp [Ψ, dysonSeriesLeft_apply_eq_smul_of_orbitTorusOperator_eq_zero hd hJ₀ hJ₀sq hS
        hScont hu hε₂ hs ht hD]
    · funext z
      rw [apply_eq_dysonSeriesLeft_apply_of_orbitTorusOperator_eq_zero hd hJ₀ hJ₀sq hS hScont hu
        hε₂ hs ht hD z, h0, map_zero, Pi.zero_apply]
  · rintro ⟨v, hv, hne⟩
    have hΨv : Ψ d v = ε₂ • v := by
      have h0 : (ε₂ • 1 - Ψ d) v = 0 := hv
      rw [sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] at h0
      exact h0.symm
    have hΨ : ContDiff ℝ 2 Ψ := (contDiff_dysonSeriesLeft (n := 1)
      ((contDiff_const (c := J₀)).clm_comp (by simpa using hS1))).of_le (by norm_num)
    have hMper : Function.Periodic (fun t => J₀ ∘L S t) d := fun t => by simp only [hper t]
    refine ⟨fun z => Ψ z.2 v, (hΨ.clm_apply contDiff_const).comp contDiff_snd, fun h => hne ?_,
      fun _ _ => rfl, fun s t => ?_, orbitTorusOperator_dysonSeriesLeft_apply_eq_zero hJ₀sq
        hScont v⟩
    · simpa [Ψ] using congrFun h (0, 0)
    · have hadd : Ψ (t + d) = Ψ t * Ψ d := dysonSeriesLeft_add_of_periodic hM hMper t
      dsimp only
      rw [hadd, mul_apply_eq_comp, hΨv, map_smul]

end Operator

end TauCeti
