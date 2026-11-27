/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.SmallHamiltonian
public import TauCeti.Geometry.Symplectic.Hamiltonian.Hessian
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.IntervalIntegral.Slice
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The linearized Floer operator along a time-independent cylinder

Let `(V, ω)` be a symplectic vector space whose inner product is the metric `g = ω(·, J ·)` of a
constant compatible almost complex structure `J`, and let `H : V → ℝ` be an autonomous
Hamiltonian. A map `(s, t) ↦ γ(s)` solves the Floer equation of `K = H dt` exactly when
`γ' = J X_H(γ)`, that is, when `γ` is a gradient line of `H`
(`TauCeti.SymplecticForm.Invariant.isComplexLinearMap_perturbedFDeriv_comp_fst_iff`). Conversely,
if `H` is `C³` with `‖dX_H‖ ≤ a < 2π` and `‖d²X_H‖ ≤ c`, then a `C³` Floer cylinder `u` of period
one in `t` with `‖du‖ ≤ M`, where `c M < 2 (2π - a)²`, is of this form
(`TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`). This file studies the
linearized Floer operator along such a time-independent cylinder `u(s, t) = γ(s)`,

`D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)`

(`TauCeti.SymplecticForm.floerLinearization_const_eq`), and compares it with the linearization
`ζ ↦ ζ' - J dX_H(γ) ζ` of the ordinary differential equation `γ' = J X_H(γ)` of the gradient lines,
the Morse operator along `γ`. The coefficients of `D` do not depend on `t`, so `D` preserves the
splitting of a map `ξ` of period one in `t` into its slice average and the rest.

* **The zero Fourier mode.** For a `C¹` map `ξ` of period one in `t`, the slice average of `D ξ`
  is the Morse operator applied to the slice average `ξbar(s) = ∫₀¹ ξ(s, t) dt`:
  `∫₀¹ D ξ(s, t) dt = ξbar'(s) - J dX_H(γ(s)) ξbar(s)`
  (`TauCeti.SymplecticForm.intervalIntegral_floerLinearization_comp_fst`).
* **Maps that do not depend on `t`.** On the map `(s, t) ↦ ζ(s)` of a curve, `D` is the Morse
  operator: `D ζ = ζ' - J dX_H(γ) ζ` (`TauCeti.SymplecticForm.floerLinearization_comp_fst`, along
  any map). So on the mean-zero part,
  `D (ξ - ξbar) = D ξ - (ξbar' - J dX_H(γ) ξbar)`
  (`TauCeti.SymplecticForm.floerLinearization_sub_intervalIntegral`).

  These two statements hold more generally for Hamiltonians `H_s` depending on `s`, as for
  continuation data `K = H_s dt`, with `dX_{H_s}(γ(s))` in place of `dX_H(γ(s))`.
* **The kernel.** Let `H` be `C³` with `‖dX_H‖ ≤ a < 2π` and `‖d²X_H‖ ≤ c`, and let `γ` be `C¹`
  with `‖γ'‖ ≤ M`, where `c M < 2 (2π - a)²`. Let `ξ` be a `C²` map of period one in `t` whose
  mean-zero part `ξ - ξbar` is bounded; `ξ` itself may grow as `s → ±∞`, and a bound on `∂t ξ` or
  on `ξ` suffices. If `D ξ = 0`, then `ξ` does not depend on `t`
  (`TauCeti.SymplecticForm.eq_comp_fst_of_floerLinearization_eq_zero`): for each `r`, the
  difference `ξ(s, t + r) - ξ(s, t)` is again a bounded solution of `D η = 0` of period one in `t`
  whose slices have mean zero, since the coefficients of `D` do not depend on `t`, and it vanishes
  by the slice-energy argument with Wirtinger's inequality
  (`TauCeti.SymplecticForm.eq_zero_of_floerLinearization_eq_zero`). So the remaining modes carry no
  kernel: `D ξ = 0` exactly when `ξ` does not depend on `t` and `ζ(s) = ξ(s, 0)` solves the
  linearized gradient equation `ζ' = d(∇H)(γ) ζ`, where `J dX_H = d(∇H)` is the Hessian operator
  of `H` (`TauCeti.SymplecticForm.forall_floerLinearization_eq_zero_iff`). For bounded `ξ` this
  reads `ζ' = J dX_H(γ) ζ`
  (`TauCeti.SymplecticForm.forall_floerLinearization_comp_fst_eq_zero_iff`).
* **The adjoint equation.** Under the same hypotheses, a bounded `C²` map `η` of period one in `t`
  solves the formal adjoint equation `-∂s η + J (∂t η - dX_H(γ(s)) η) = 0` exactly when it does not
  depend on `t` and `ζ(s) = η(s, 0)` solves `ζ' = -J dX_H(γ) ζ`
  (`TauCeti.SymplecticForm.forall_neg_fderiv_add_eq_zero_iff`). The reflection `s ↦ -s` turns
  the adjoint equation along `γ` into the equation `D η = 0` along `s ↦ γ(-s)`.

So the bounded kernels of `D` and of its formal adjoint along a time-independent cylinder are
those of the Morse operator `∂s - J dX_H(γ)` and of its adjoint `-∂s - J dX_H(γ)`, embedded as
functions of `s` alone: the nonzero Fourier modes contribute nothing, because a loop `ζ` of mean
zero has `‖ζ'‖ ≥ 2π ‖ζ‖` in `L²` by Wirtinger's inequality. These are statements about classical
solutions; the Sobolev realization of `D`, its Fredholm index and the transversality of the
cylinder are not treated here.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the linearized operator at
  time-independent solutions of a small Hamiltonian.
-/

public section

open Real Set Filter Topology MeasureTheory ContinuousLinearMap
open scoped RealInnerProductSpace

namespace TauCeti.SymplecticForm

section ZeroMode

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : ℝ → V → ℝ}

/-- **The zero Fourier mode of the linearized operator is the Morse operator.** Along a
time-independent cylinder `u(s, t) = γ(s)` and for Hamiltonians `H_s` depending on `s` alone, the
slice average of the linearized Floer operator `D ξ = ∂s ξ + J (∂t ξ - dX_{H_s}(γ(s)) ξ)` applied
to a `C¹` map `ξ` of period one in `t` is the operator `ζ ↦ ζ' - J dX_{H_s}(γ) ζ` applied to the
slice average `ξbar(s) = ∫₀¹ ξ(s, t) dt`. -/
theorem intervalIntegral_floerLinearization_comp_fst (γ : ℝ → V) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (s : ℝ) :
    ∫ t in (0 : ℝ)..1, ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) ξ (s, t) =
      deriv (fun s ↦ ∫ t in (0 : ℝ)..1, ξ (s, t)) s -
        J (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s) (∫ t in (0 : ℝ)..1, ξ (s, t))) := by
  set Jc : V →L[ℝ] V := J.toLinearMap.toContinuousLinearMap
  set L : V →L[ℝ] V := Jc ∘L fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)
  have hξs : Continuous fun t ↦ fderiv ℝ ξ (s, t) (1, 0) :=
    continuous_fderiv_apply_slice_right hξ s (1, 0)
  have hξt : Continuous fun t ↦ fderiv ℝ ξ (s, t) (0, 1) :=
    continuous_fderiv_apply_slice_right hξ s (0, 1)
  have hξc : Continuous fun t ↦ ξ (s, t) := hξ.continuous.comp (.prodMk_right s)
  -- Pointwise, the integrand is `∂s ξ + J ∂t ξ - L ξ` for the constant operator `L = J dX_H(γ s)`.
  have hpt : ∀ t, ω.floerLinearization (fun _ _ ↦ Jc) (fun _ _ ↦ 0) (fun z ↦ H z.1)
      (fun z ↦ γ z.1) ξ (s, t) =
        fderiv ℝ ξ (s, t) (1, 0) + Jc (fderiv ℝ ξ (s, t) (0, 1)) - L (ξ (s, t)) := fun t ↦ by
    rw [floerLinearization_const_eq, map_sub]
    simp only [Jc, L, coe_comp, Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
    abel
  -- The `s`-derivative of the slice average is the slice average of `∂s ξ`.
  have hderiv := (hasDerivAt_intervalIntegral_of_contDiffOn isOpen_univ hξ.contDiffOn
    (x₀ := s) (a := 0) (b := 1) (subset_univ _)).2.deriv
  -- The `t`-derivative integrates to zero over a period.
  have hJt : ∫ t in (0 : ℝ)..1, Jc (fderiv ℝ ξ (s, t) (0, 1)) = 0 := by
    rw [Jc.intervalIntegral_comp_comm (hξt.intervalIntegrable 0 1),
      integral_fderiv_apply_zero_one_eq_zero hξ hper s, map_zero]
  have i₁ : IntervalIntegrable (fun t ↦ fderiv ℝ ξ (s, t) (1, 0)) volume 0 1 :=
    hξs.intervalIntegrable 0 1
  have i₂ : IntervalIntegrable (fun t ↦ Jc (fderiv ℝ ξ (s, t) (0, 1))) volume 0 1 :=
    (Jc.continuous.comp hξt).intervalIntegrable 0 1
  have i₁₂ : IntervalIntegrable
      (fun t ↦ fderiv ℝ ξ (s, t) (1, 0) + Jc (fderiv ℝ ξ (s, t) (0, 1))) volume 0 1 :=
    i₁.add i₂
  have i₃ : IntervalIntegrable (fun t ↦ L (ξ (s, t))) volume 0 1 :=
    (L.continuous.comp hξc).intervalIntegrable 0 1
  rw [intervalIntegral.integral_congr fun t _ ↦ hpt t, intervalIntegral.integral_sub i₁₂ i₃,
    intervalIntegral.integral_add i₁ i₂, hJt, add_zero,
    L.intervalIntegral_comp_comm (hξc.intervalIntegrable 0 1), hderiv]
  simp only [L, Jc, coe_comp, Function.comp_apply, LinearMap.coe_toContinuousLinearMap']

/-- **The linearized operator on the mean-zero part.** Along a time-independent cylinder
`u(s, t) = γ(s)` and for Hamiltonians `H_s` depending on `s` alone, the linearized Floer operator
`D` of the mean-zero part `ξ - ξbar` of a `C¹` map `ξ` is `D ξ` minus the Morse operator
`ξbar' - J dX_{H_s}(γ) ξbar` of the slice average `ξbar(s) = ∫₀¹ ξ(s, t) dt`. -/
theorem floerLinearization_sub_intervalIntegral (γ : ℝ → V) {ξ : ℝ × ℝ → V}
    (hξ : ContDiff ℝ 1 ξ) (z : ℝ × ℝ) :
    ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun z ↦ H z.1) (fun z ↦ γ z.1) (fun z ↦ ξ z - ∫ t in (0 : ℝ)..1, ξ (z.1, t)) z =
      ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun z ↦ H z.1) (fun z ↦ γ z.1) ξ z -
        (deriv (fun s ↦ ∫ t in (0 : ℝ)..1, ξ (s, t)) z.1 -
          J (fderiv ℝ (ω.hamiltonianVectorField (H z.1)) (γ z.1)
            (∫ t in (0 : ℝ)..1, ξ (z.1, t)))) := by
  have hbar : DifferentiableAt ℝ (fun s ↦ ∫ t in (0 : ℝ)..1, ξ (s, t)) z.1 :=
    (hξ.parametric_intervalIntegral (μ := volume)).differentiable one_ne_zero z.1
  rw [← floerLinearization_comp_fst ω J (fun z ↦ H z.1) (fun z ↦ γ z.1)
    (fun s ↦ ∫ t in (0 : ℝ)..1, ξ (s, t))]
  exact floerLinearization_sub ω _ _ _ _ ξ _ z (hξ.differentiable one_ne_zero z)
    (hbar.comp z differentiableAt_fst)

end ZeroMode

section Kernel

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {γ : ℝ → V} {a c M B : ℝ}

/-- **Kernel elements along a time-independent cylinder are time-independent.** Let the inner
product of `V` be the metric `ω(·, J ·)` of a constant compatible almost complex structure `J`,
let `H` be a `C³` autonomous Hamiltonian with `‖dX_H‖ ≤ a < 2π` and `‖d²X_H‖ ≤ c`, and let `γ` be
a `C¹` curve with `‖γ'‖ ≤ M`, where `c M < 2 (2π - a)²`. Let `ξ` be a `C²` map of period one in
`t` whose mean-zero part `ξ(s, t) - ∫₀¹ ξ(s, r) dr` is bounded, for instance a bounded map or a map
with bounded `∂t ξ`. If `ξ` lies in the kernel of the linearized Floer operator
`D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)` along `(s, t) ↦ γ(s)`, then it does not depend on `t`. -/
theorem eq_comp_fst_of_floerLinearization_eq_zero (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hγ : ContDiff ℝ 1 γ) (hM : ∀ s, ‖deriv γ s‖ ≤ M) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hD : ∀ z, ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) ξ z = 0)
    (hB : ∀ z, ‖ξ z - ∫ t in (0 : ℝ)..1, ξ (z.1, t)‖ ≤ B) (s t : ℝ) :
    ξ (s, t) = ξ (s, 0) := by
  -- The cylinder `(s, t) ↦ γ(s)` has `‖du‖ ≤ M`.
  have hu (z : ℝ × ℝ) : ‖fderiv ℝ (fun z : ℝ × ℝ ↦ γ z.1) z‖ ≤ M :=
    (norm_fderiv_comp_fst_le γ z).trans (norm_deriv_eq_norm_fderiv (f := γ) ▸ hM z.1)
  -- For every shift `r`, the difference `η(z) = ξ(z + (0, r)) - ξ(z)` vanishes.
  have hshift (r : ℝ) : (fun z ↦ ξ (z + (0, r))) - ξ = 0 := by
    have hξr : ContDiff ℝ 2 fun z : ℝ × ℝ ↦ ξ (z + (0, r)) :=
      hξ.comp (contDiff_id.add contDiff_const)
    refine eq_zero_of_floerLinearization_eq_zero (u := fun z ↦ γ z.1) (B := B + B) hg hH ha hc
      ha2π hcM (hγ.comp contDiff_fst) hu (hξr.sub hξ) (fun s t ↦ ?_) (fun s ↦ ?_) (fun z ↦ ?_)
      fun z ↦ ?_
    · simp only [Pi.sub_apply, Prod.mk_add_mk, add_zero, add_right_comm t 1 r, hper]
    -- The slices of `η` have mean zero, by periodicity of `t ↦ ξ(s, t)`.
    · have hcont : Continuous fun t ↦ ξ (s, t) := hξ.continuous.comp (.prodMk_right s)
      have hcont' : Continuous fun t ↦ ξ (s, t + r) :=
        hcont.comp (continuous_id.add continuous_const)
      have hperiodic : Function.Periodic (fun t ↦ ξ (s, t)) 1 := hper s
      simp only [Pi.sub_apply, Prod.mk_add_mk, add_zero]
      rw [intervalIntegral.integral_sub (hcont'.intervalIntegrable 0 1)
          (hcont.intervalIntegrable 0 1), sub_eq_zero,
        intervalIntegral.integral_comp_add_right (fun t ↦ ξ (s, t)), zero_add, add_comm 1 r,
        hperiodic.intervalIntegral_add_eq r 0, zero_add]
    -- `η` is in the kernel, since the coefficients of `D` do not depend on `t`.
    · have h := floerLinearization_comp_add_right ω (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) ξ (0, r) z
      simp only [Prod.fst_add, add_zero] at h
      rw [floerLinearization_sub ω _ _ _ _ _ _ z (hξr.differentiable two_ne_zero z)
        (hξ.differentiable two_ne_zero z), h, hD, hD, sub_self]
    -- `η` is bounded, since the mean-zero part of `ξ` is.
    · have h := hB (z + (0, r))
      simp only [Prod.fst_add, add_zero] at h
      rw [Pi.sub_apply, ← sub_sub_sub_cancel_right _ _ (∫ t in (0 : ℝ)..1, ξ (z.1, t))]
      exact (norm_sub_le _ _).trans (add_le_add h (hB z))
  simpa [sub_eq_zero] using congrFun (hshift t) (s, 0)

/-- **The kernel of the linearized operator along a gradient line.** Under the hypotheses of
`TauCeti.SymplecticForm.eq_comp_fst_of_floerLinearization_eq_zero`, a `C²` map `ξ` of period one
in `t` with bounded mean-zero part lies in the kernel of the linearized Floer operator along
`(s, t) ↦ γ(s)` exactly when it does not depend on `t` and `ζ(s) = ξ(s, 0)` solves the linearized
gradient equation `ζ' = d(∇H)(γ) ζ`, written with the Hessian operator
`TauCeti.hessianOperator H = d(∇H)`. These are the solutions that describe the kernel of the
linearized Morse operator `ζ ↦ ζ' - d(∇H)(γ) ζ` of a gradient line `γ`. -/
theorem forall_floerLinearization_eq_zero_iff (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hγ : ContDiff ℝ 1 γ) (hM : ∀ s, ‖deriv γ s‖ ≤ M) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hB : ∀ z, ‖ξ z - ∫ t in (0 : ℝ)..1, ξ (z.1, t)‖ ≤ B) :
    (∀ z, ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ ↦ H) (fun z ↦ γ z.1) ξ z = 0) ↔
      (∀ s t, ξ (s, t) = ξ (s, 0)) ∧
        ∀ s, HasDerivAt (fun s ↦ ξ (s, 0)) (hessianOperator H (γ s) (ξ (s, 0))) s := by
  have hζ : Differentiable ℝ fun s ↦ ξ (s, 0) :=
    (hξ.differentiable two_ne_zero).comp (differentiable_id.prodMk (differentiable_const 0))
  -- On a map that does not depend on `t`, `D` is the Morse operator `ζ' - d(∇H)(γ) ζ`.
  have hDζ (z : ℝ × ℝ) : ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ z.1) (fun z ↦ ξ (z.1, 0)) z =
        deriv (fun s ↦ ξ (s, 0)) z.1 - hessianOperator H (γ z.1) (ξ (z.1, 0)) := by
    rw [← apply_fderiv_hamiltonianVectorField_eq_hessianOperator hg]
    exact floerLinearization_comp_fst ω J (fun _ ↦ H) _ (fun s ↦ ξ (s, 0)) z
  constructor
  · intro hD
    have ht := eq_comp_fst_of_floerLinearization_eq_zero hg hH ha hc ha2π hcM hγ hM hξ hper hD hB
    refine ⟨ht, fun s ↦ ?_⟩
    have h := hD (s, 0)
    rw [show ξ = fun z ↦ ξ (z.1, 0) from funext fun z ↦ ht z.1 z.2, hDζ, sub_eq_zero] at h
    exact (hζ s).hasDerivAt.congr_deriv h
  · rintro ⟨ht, hd⟩ z
    rw [show ξ = fun z ↦ ξ (z.1, 0) from funext fun z ↦ ht z.1 z.2, hDζ, (hd z.1).deriv, sub_self]

/-- **The bounded kernel of the linearized operator along a time-independent cylinder.** Let the
inner product of `V` be the metric `ω(·, J ·)` of a constant compatible almost complex structure
`J`, let `H` be a `C³` autonomous Hamiltonian with `‖dX_H‖ ≤ a < 2π` and `‖d²X_H‖ ≤ c`, and let `γ`
be a `C¹` curve with `‖γ'‖ ≤ M`, where `c M < 2 (2π - a)²`. A bounded `C²` map `ξ` of period one in
`t` lies in the kernel of the linearized Floer operator `D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)`
along `(s, t) ↦ γ(s)` exactly when it does not depend on `t` and `ζ(s) = ξ(s, 0)` solves the
linearized gradient equation `ζ' = J dX_H(γ) ζ`. This is the case of bounded `ξ` of
`TauCeti.SymplecticForm.forall_floerLinearization_eq_zero_iff`. -/
theorem forall_floerLinearization_comp_fst_eq_zero_iff (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hγ : ContDiff ℝ 1 γ) (hM : ∀ s, ‖deriv γ s‖ ≤ M) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hB : ∀ z, ‖ξ z‖ ≤ B) :
    (∀ z, ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun _ ↦ H) (fun z ↦ γ z.1) ξ z = 0) ↔
      (∀ s t, ξ (s, t) = ξ (s, 0)) ∧
        ∀ s, HasDerivAt (fun s ↦ ξ (s, 0))
          (J (fderiv ℝ (ω.hamiltonianVectorField H) (γ s) (ξ (s, 0)))) s := by
  -- The mean-zero part of a map bounded by `B` is bounded by `B + B`.
  have hB' (z : ℝ × ℝ) : ‖ξ z - ∫ t in (0 : ℝ)..1, ξ (z.1, t)‖ ≤ B + B :=
    (norm_sub_le _ _).trans (add_le_add (hB z) (by
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := 1) (f := fun t ↦ ξ (z.1, t)) fun t _ ↦ hB (z.1, t)))
  rw [forall_floerLinearization_eq_zero_iff hg hH ha hc ha2π hcM hγ hM hξ hper hB']
  simp only [apply_fderiv_hamiltonianVectorField_eq_hessianOperator hg]

/-- **The adjoint equation along a time-independent cylinder.** Under the hypotheses of
`TauCeti.SymplecticForm.forall_floerLinearization_comp_fst_eq_zero_iff`, a bounded `C²` map `η`
of period one in `t` solves the formal adjoint equation
`-∂s η + J (∂t η - dX_H(γ(s)) η) = 0` of the linearized Floer operator along `(s, t) ↦ γ(s)`
exactly when it does not depend on `t` and `ζ(s) = η(s, 0)` solves `ζ' = -J dX_H(γ) ζ`. -/
theorem forall_neg_fderiv_add_eq_zero_iff (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hγ : ContDiff ℝ 1 γ) (hM : ∀ s, ‖deriv γ s‖ ≤ M) {η : ℝ × ℝ → V} (hη : ContDiff ℝ 2 η)
    (hper : ∀ s t, η (s, t + 1) = η (s, t)) (hB : ∀ z, ‖η z‖ ≤ B) :
    (∀ z, -fderiv ℝ η z (1, 0) +
        J (fderiv ℝ η z (0, 1) - fderiv ℝ (ω.hamiltonianVectorField H) (γ z.1) (η z)) = 0) ↔
      (∀ s t, η (s, t) = η (s, 0)) ∧
        ∀ s, HasDerivAt (fun s ↦ η (s, 0))
          (-J (fderiv ℝ (ω.hamiltonianVectorField H) (γ s) (η (s, 0)))) s := by
  -- Reflect `s ↦ -s`: `ρ (s, t) = (-s, t)`, `η̂ = η ∘ ρ` and `γ̂ (s) = γ (-s)`.
  set ρ : ℝ × ℝ →L[ℝ] ℝ × ℝ := (-fst ℝ ℝ ℝ).prod (snd ℝ ℝ ℝ)
  have hρ (z : ℝ × ℝ) : ρ z = (-z.1, z.2) := by
    simp only [ρ, ContinuousLinearMap.prod_apply, _root_.neg_apply, coe_fst', coe_snd']
  have hρ₁ : ρ (1, 0) = -(1, 0) := by simp only [hρ, Prod.neg_mk, neg_zero]
  have hρ₂ : ρ (0, 1) = (0, 1) := by simp only [hρ, neg_zero]
  set γ' : ℝ → V := fun s ↦ γ (-s)
  have hγ' : ContDiff ℝ 1 γ' := hγ.comp contDiff_neg
  have hM' (s : ℝ) : ‖deriv γ' s‖ ≤ M := by
    rw [deriv_comp_neg, norm_neg]
    exact hM _
  have hη' : ContDiff ℝ 2 (η ∘ ρ) := hη.comp ρ.contDiff
  have hper' (s t : ℝ) : (η ∘ ρ) (s, t + 1) = (η ∘ ρ) (s, t) := by
    simp only [Function.comp_apply, hρ, hper]
  have hB' (z : ℝ × ℝ) : ‖(η ∘ ρ) z‖ ≤ B := hB _
  -- The linearized operator along `γ̂` at `z` is the adjoint expression along `γ` at `ρ z`.
  have hD (z : ℝ × ℝ) : ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ ↦ H) (fun z ↦ γ' z.1) (η ∘ ρ) z =
        -fderiv ℝ η (ρ z) (1, 0) + J (fderiv ℝ η (ρ z) (0, 1) -
          fderiv ℝ (ω.hamiltonianVectorField H) (γ (ρ z).1) (η (ρ z))) := by
    have hd : HasFDerivAt (η ∘ ρ) ((fderiv ℝ η (ρ z)).comp ρ) z :=
      ((hη.differentiable (by norm_num)) (ρ z)).hasFDerivAt.comp z ρ.hasFDerivAt
    have hγρ : γ' z.1 = γ (ρ z).1 := by simp only [γ', hρ]
    simp only [floerLinearization_const_eq, hd.fderiv, coe_comp, Function.comp_apply, hρ₁, hρ₂,
      map_neg, hγρ]
  -- Reflecting `s ↦ -s` negates the derivative of a curve.
  have hrefl (ζ f : ℝ → V) (h : ∀ s, HasDerivAt ζ (f s) s) (s : ℝ) :
      HasDerivAt (fun s ↦ ζ (-s)) (-f (-s)) s := by
    rw [← neg_one_smul ℝ (f (-s))]
    exact (h (-s)).scomp s (hasDerivAt_neg' (x := s))
  have hiff := forall_floerLinearization_comp_fst_eq_zero_iff hg hH ha hc ha2π hcM hγ' hM' hη'
    hper' hB'
  simp only [hD] at hiff
  simp only [Function.comp_apply, hρ, γ'] at hiff
  constructor
  · intro h
    obtain ⟨ht, hd⟩ := hiff.1 fun z ↦ h (-z.1, z.2)
    refine ⟨fun s t ↦ by simpa only [neg_neg] using ht (-s) t, fun s ↦ ?_⟩
    simpa only [neg_neg] using hrefl _ _ hd s
  · rintro ⟨ht, hd⟩
    have key := hiff.2 ⟨fun s t ↦ ht (-s) t, fun s ↦ by simpa only [neg_neg] using hrefl _ _ hd s⟩
    intro z
    simpa only [neg_neg, Prod.mk.eta] using key (-z.1, z.2)

end Kernel

end TauCeti.SymplecticForm
