/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Inhomogeneous
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import TauCeti.Analysis.InnerProductSpace.GelfandTriple
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.ODE.Caratheodory
import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
import TauCeti.MeasureTheory.Function.StronglyMeasurable.FiniteDimensional
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Galerkin approximations of linear parabolic equations

Let `ι : V →L[ℝ] H` map a real seminormed space into a real inner product space, as for a Gelfand
triple `V ↪ H ↪ V*` (`ContinuousLinearMap.gelfandDual`), and consider the abstract linear parabolic
equation

`u' + A(t) u = f`, `u(a) = u₀`

on `(a, b)`, where `A(t) : V →L[ℝ] V*` and `f(t) ∈ V*`.

The **Galerkin method** solves this equation on an increasing sequence of finite-dimensional
subspaces `V_m ⊆ V`, with `A(t)` and `f(t)` restricted to `V_m`, and passes to the limit. This file
proves that each Galerkin approximation exists, in two settings. No symmetry or coercivity of `A`
is needed for either.

### Autonomous operator, continuous forcing

For a bounded operator `A : V → V*`, a finite-dimensional real normed space `F` and a
continuous linear map `e : F → V` whose composite with `ι` is injective, the Galerkin equation is

`⟪ι(e c'(t)), ι(e v)⟫ + A(e c(t))(e v) = f(t)(e v)` for every `v : F`.

For continuous `f : ℝ → V*`, this equation has a unique global `C¹` solution for any initial
coordinate vector (`TauCeti.PDE.existsUnique_galerkinSolution`). Injectivity into the pivot space
makes the finite-dimensional Gram operator `F → F*` invertible, so no inner product on the
coordinate space is needed. Mathlib's `ContinuousLinearMap.bilinearComp` restricts the forms.

### Measurable coefficients

Here the time derivative `u'` is the weak derivative of `t ↦ ι.gelfandDual (ι (u t))` in `V*`, as
in `TauCeti.HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual`, and the equation is
solvable when `V` is finite-dimensional and `ι` is injective
(`TauCeti.exists_hasWeakLineDerivOn_gelfandDual_of_finiteDimensional`). Only measurability of
`t ↦ A t v w`, essential boundedness of `‖A t‖` and integrability of `f` are assumed; continuity
in time is not needed.

In finite dimension, `G = ι.gelfandDual ∘ ι : V → V*`, the Gram operator `v ↦ ⟪ι v, ι ·⟫`, is
invertible, and the equation is the linear ordinary differential equation
`x' = G⁻¹ (f(t) - A(t) x)` in `V`. Its coefficients are only measurable in time, so it is solved in
Carathéodory's sense (`TauCeti.exists_continuousOn_eq_forall_mem_Icc_eq_picard`), and the integral
equation it gives makes `G x` weakly differentiable with derivative `f - A x`.

When `f ∈ L²(a, b; V*)` and `A(t)` satisfies Gårding's inequality on `V`, it also does on each
`V_m` with the same constants, so the energy estimate
`TauCeti.HasWeakLineDerivOn.norm_sq_add_mul_integral_le_of_gelfandDual`, applied on `V_m`, bounds
the Galerkin approximations in terms of their initial values in `H` and of `∫ ‖f‖²`, uniformly in
`m`.

## Main declarations

* `TauCeti.PDE.existsUnique_galerkinSolution`: the autonomous Galerkin equation with continuous
  forcing has a unique global `C¹` solution.
* `TauCeti.exists_hasWeakLineDerivOn_gelfandDual_of_finiteDimensional`: the abstract linear
  parabolic equation with measurable coefficients is solvable on a finite-dimensional space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.2, Theorem 1.
* E. Zeidler, *Nonlinear Functional Analysis and its Applications II/A*, Chapter 23.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti.PDE

variable {V H F : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Existence and uniqueness of Galerkin approximations.** For a bounded autonomous energy
operator, continuous forcing and a finite-dimensional trial map injective into the pivot space,
the projected parabolic equation has a unique global `C¹` solution with prescribed value at
any time `t₀`. The coordinate space needs only a norm, with no chosen inner product. -/
theorem existsUnique_galerkinSolution (ι : V →L[ℝ] H) (A : V →L[ℝ] StrongDual ℝ V)
    (e : F →L[ℝ] V) (he : Function.Injective (ι.comp e)) {f : ℝ → StrongDual ℝ V}
    (hf : Continuous f) (x : F) (t₀ : ℝ) :
    ∃! c : ℝ → F, c t₀ = x ∧ ContDiff ℝ 1 c ∧ ∀ t v,
      ⟪ι (e (deriv c t)), ι (e v)⟫_ℝ + A (e (c t)) (e v) = f t (e v) := by
  have := FiniteDimensional.complete ℝ F
  -- The Gram map into the coordinate dual is invertible, independently of the energy form.
  let j := ι.comp e
  obtain ⟨Q, hQ⟩ := ContinuousLinearMap.isInvertible_of_injective
    (j.gelfandDual_comp_injective he)
  replace hQ : ∀ z v, Q z v = ⟪ι (e z), ι (e v)⟫_ℝ := by
    intro z v
    simpa [j] using congr($hQ z v)
  let D := A.bilinearComp e e
  let R : StrongDual ℝ V →L[ℝ] StrongDual ℝ F := (ContinuousLinearMap.compL ℝ F V ℝ).flip e
  let B : F →L[ℝ] F := -(Q.symm.toContinuousLinearMap.comp D)
  let g : ℝ → F := fun t ↦ Q.symm (R (f t))
  have hg : Continuous g := Q.symm.continuous.comp (R.continuous.comp hf)
  have hEq (z d : F) (t : ℝ) :
      (∀ v, ⟪ι (e d), ι (e v)⟫_ℝ + A (e z) (e v) = f t (e v)) ↔
        d = B z + g t := by
    constructor
    · intro h
      have hmass : Q d = R (f t) - D z := by
        ext v
        simpa [hQ, R, D] using eq_sub_of_add_eq (h v)
      have := congrArg Q.symm hmass
      simpa [B, g, map_sub, sub_eq_add_neg, add_comm] using this
    · rintro rfl
      have hmass : Q (B z + g t) = R (f t) - D z := by
        simp [B, g, sub_eq_add_neg, add_comm]
      intro v
      have hv := congr($hmass v)
      simpa [hQ, R, D, inner_add_left] using (eq_sub_iff_add_eq).1 hv
  -- Solve the reduced ODE, then transfer both its equation and its uniqueness back.
  obtain ⟨c, hc, huniq⟩ := B.existsUnique_hasDerivAt_add hg x t₀
  have hderiv : deriv c = fun t ↦ B (c t) + g t := by
    funext t
    exact (hc.2 t).deriv
  have hc1 : ContDiff ℝ 1 c := contDiff_one_iff_deriv.2
    ⟨fun t ↦ (hc.2 t).differentiableAt,
      hderiv ▸ (B.continuous.comp
        (continuous_iff_continuousAt.2 fun t ↦ (hc.2 t).continuousAt)).add hg⟩
  refine ⟨c, ⟨hc.1, hc1, fun t ↦ (hEq _ _ t).2 ((hc.2 t).deriv)⟩, ?_⟩
  intro d hd
  apply huniq d
  refine ⟨hd.1, fun t ↦ ?_⟩
  rw [← (hEq (d t) (deriv d t) t).1 (hd.2.2 t)]
  exact (hd.2.1.differentiable one_ne_zero t).hasDerivAt

end TauCeti.PDE

end

section Measurable

open MeasureTheory Set Function Filter

namespace TauCeti

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {ι : V →L[ℝ] H}
  {A : ℝ → V →L[ℝ] StrongDual ℝ V} {f : ℝ → StrongDual ℝ V} {a b K : ℝ}

/-- **Galerkin approximations exist.** Let `V` be finite-dimensional and `ι : V →L[ℝ] H` injective.
Let `t ↦ A t v w` be almost everywhere strongly measurable on `(a, b)` for all `v, w`, with
`‖A t‖ ≤ K` almost everywhere there, and let `f` be integrable on `(a, b)`. Then for every
`u₀ : V` there is `u`, continuous on `[a, b]` with `u a = u₀`, such that
`t ↦ ι.gelfandDual (ι (u t))` has weak derivative `f - A u` on `(a, b)`: `u` solves
`u' + A(t) u = f`, `u(a) = u₀`. -/
theorem exists_hasWeakLineDerivOn_gelfandDual_of_finiteDimensional (hι : Injective ι)
    (hA : ∀ v w, AEStronglyMeasurable (fun t ↦ A t v w) (volume.restrict (Ioo a b)))
    (hK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖A t‖ ≤ K) (hf : IntegrableOn f (Ioo a b)) (u₀ : V) :
    ∃ u : ℝ → V, ContinuousOn u (Icc a b) ∧ u a = u₀ ∧
      HasWeakLineDerivOn volume ⟨Ioo a b, isOpen_Ioo⟩ (fun t ↦ ι.gelfandDual (ι (u t)))
        (fun t ↦ f t - A t (u t)) 1 := by
  have := FiniteDimensional.complete ℝ V
  -- The Gram operator `G = ι.gelfandDual ∘ ι` is an isomorphism `V ≃L[ℝ] V*`.
  obtain ⟨G, hG⟩ := ContinuousLinearMap.isInvertible_of_injective (ι.gelfandDual_comp_injective hι)
  replace hG : ∀ v, G v = ι.gelfandDual (ι v) := fun v ↦ congr($hG v)
  set Ginv : StrongDual ℝ V →L[ℝ] V := (G.symm : StrongDual ℝ V →L[ℝ] V)
  -- The equation is `x' = M(t) x + F(t)` with `M(t) = -G⁻¹ A(t)` and `F(t) = G⁻¹ f(t)`.
  set M : ℝ → V →L[ℝ] V := fun t ↦ -(Ginv.comp (A t))
  set F : ℝ → V := fun t ↦ Ginv (f t)
  have hM : AEStronglyMeasurable M (volume.restrict (Ioo a b)) :=
    ((ContinuousLinearMap.compL ℝ V (StrongDual ℝ V) V Ginv).continuous.comp_aestronglyMeasurable
      (aestronglyMeasurable_clm_apply_iff.2 fun v ↦
        aestronglyMeasurable_clm_apply_iff.2 (hA v))).neg
  have hMK : ∀ᵐ t ∂volume.restrict (Ioo a b), ‖M t‖ ≤ ‖Ginv‖ * K := by
    filter_upwards [hK] with t ht
    rw [norm_neg]
    exact (Ginv.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
  have hF : IntegrableOn F (Ioo a b) := Ginv.integrable_comp hf
  obtain ⟨x, hx, hxa, hxeq⟩ := exists_continuousOn_eq_forall_mem_Icc_eq_picard hM hMK hF u₀
  refine ⟨x, hx, hxa, ?_⟩
  -- `x` is `u₀` plus the primitive of `M x + F` on `(a, b)`, so it has weak derivative `M x + F`.
  have hxg := ((hasWeakLineDerivOn_const (μ := volume) (Ω := ⟨Ioo a b, isOpen_Ioo⟩) (v := 1)
    u₀).add (hasWeakLineDerivOn_intervalIntegral_left
      (integrableOn_clm_apply_add hM hMK hF hx))).congr_ae
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht ↦
      (hxeq t (Ioo_subset_Icc_self ht)).symm)) |>.congr_ae_deriv (EventuallyEq.of_eq (zero_add _))
  -- Applying `G` gives the weak derivative `G (M x + F) = f - A x` of `G x`.
  convert hxg.clm_comp (G : V →L[ℝ] StrongDual ℝ V) using 1
  · ext t
    simp [hG]
  · ext t
    simp [M, F, Ginv, neg_add_eq_sub]

end TauCeti

end Measurable
