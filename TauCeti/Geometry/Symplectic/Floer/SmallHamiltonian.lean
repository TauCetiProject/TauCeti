/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Convex.BddAbove
import TauCeti.Analysis.Fourier.Wirtinger
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Floer cylinders of small autonomous Hamiltonians are time-independent

Let `(V, ω)` be a symplectic vector space whose inner product is the metric `g = ω(·, J ·)` of a
constant compatible almost complex structure `J`, and let `H : V → ℝ` be an autonomous
Hamiltonian. For the cylindrical perturbation `K = H dt` the Floer equation reads
`∂s u + J (∂t u - X_H(u)) = 0`. Its solutions that do not depend on `t` are the gradient lines of
`H` (`TauCeti.Geometry.Symplectic.Floer.TimeIndependent`). This file proves the converse for
`C²`-small Hamiltonians: every solution of period one in `t` with bounded derivative is
independent of `t`, and so is a gradient line. This is the analytic step behind the
identification of the Floer cylinders of a small Morse Hamiltonian with its gradient trajectories.

The smallness is quantitative. If `‖dX_H‖ ≤ a < 2π` and `‖d²X_H‖ ≤ c` everywhere, `u` is `C³`,
and `‖du‖ ≤ M` with `c M < 2 (2π - a)²`, then `u(s, t) = u(s, 0)`
(`TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`), and
`γ(s) = u(s, 0)` solves `γ' = ∇H(γ)`
(`TauCeti.SymplecticForm.hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv`). No finite
energy, limits at the ends or nondegeneracy are assumed.

**The argument.** Differentiating the Floer equation in `t`, the derivative `ξ = ∂t u` solves
the linearized equation `∂s ξ = -J ∂t ξ + S ξ` with `S = J dX_H(u)`. Since `J X_H` is the
gradient of `H`, the operator `S` is the Hessian of `H` along `u`, so it is symmetric, and `J` is
skew-adjoint. Each slice `t ↦ ξ(s, t)` is the derivative of a loop, so it has mean zero. The
slice energy `f(s) = ∫₀¹ ‖ξ(s, t)‖² dt` then satisfies

`f'' = 4 ∫₀¹ ‖∂s ξ‖² + 2 ∫₀¹ ⟪ξ, (∂s S) ξ⟫`,

after an integration by parts in `t` whose boundary terms cancel by periodicity. Wirtinger's
inequality on the mean-zero slices (`TauCeti.integral_norm_sub_average_sq_le`, with its sharp
constant `2π`) bounds `∫₀¹ ‖∂s ξ‖² = ∫₀¹ ‖∂t ξ - dX_H(u) ξ‖²` below by `(2π - a)² f`, and
`‖∂s S‖ ≤ c M`. Hence `f'' ≥ (4 (2π - a)² - 2 c M) f` with a positive constant. A nonnegative
bounded function with `f'' ≥ κ f`, `κ > 0`, is convex and bounded, hence zero
(`TauCeti.eq_zero_of_hasDerivAt_of_mul_le_of_bddAbove`). So `ξ = 0`.

The constant structure `J` covers flat targets. On a torus `V / Λ` with a flat compatible
structure, a Floer cylinder whose loops are contractible lifts to a solution on `V` of period one
in `t`, for the lifted `Λ`-periodic Hamiltonian. Domain- or target-dependent structures, for which
the linearized operator acquires derivatives of `J`, and the bound on `du` in terms of `H` are not
treated here.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360.
-/

public section

open Real Set Filter Topology MeasureTheory
open scoped Gradient RealInnerProductSpace

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {u : ℝ × ℝ → V}

section Pointwise

omit [FiniteDimensional ℝ V] in
/-- When the inner product is the metric `ω(·, J ·)`, pairing with `J p` is `ω(p, ·)`. -/
private theorem inner_apply_left (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (p w : V) :
    ⟪J p, w⟫ = ω p w := by
  have h : ω w (-p) = -ω w p := map_neg (ω.toBilinForm w) p
  rw [real_inner_comm, ← hg, J.apply_apply, h, ω.neg_eq]

omit [FiniteDimensional ℝ V] in
/-- When the inner product is the metric `ω(·, J ·)`, `J` is skew-adjoint. -/
private theorem inner_apply_left_eq_neg (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (p w : V) :
    ⟪J p, w⟫ = -⟪p, J w⟫ := by
  rw [inner_apply_left hg, real_inner_comm, inner_apply_left hg, ω.neg_eq]

/-- When the inner product is the metric `ω(·, J ·)`, the operator `J ∘ dX_H(x)` is symmetric: it
is the Hessian of `H` at `x`, since `J X_H` is the gradient of `H`. -/
private theorem inner_apply_fderiv_hamiltonianVectorField_comm
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {x : V} (hH : ContDiffAt ℝ 2 H x) (v w : V) :
    ⟪J (fderiv ℝ (ω.hamiltonianVectorField H) x v), w⟫ =
      ⟪v, J (fderiv ℝ (ω.hamiltonianVectorField H) x w)⟫ := by
  have h := ω.apply_fderiv_hamiltonianVectorField_add hH v w
  have hneg := ω.neg_eq v (fderiv ℝ (ω.hamiltonianVectorField H) x w)
  rw [inner_apply_left hg, real_inner_comm, inner_apply_left hg]
  linarith

end Pointwise

section Derivatives

/-- The Floer equation of `K = H dt`, solved for `∂s u`. -/
private theorem fderiv_apply_real_eq {z : ℝ × ℝ}
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    fderiv ℝ u z (1, 0) = -J (fderiv ℝ u z (0, 1)) + J (ω.hamiltonianVectorField H (u z)) := by
  rw [ω.isComplexLinearMap_perturbedFDeriv_iff] at hfl
  simp only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero, stdComplexLineReal_eq,
    stdComplexLineImag_eq, map_sub] at hfl
  linear_combination (norm := module) hfl

/-- **The linearized equation of `∂t u`.** For a solution `u` of the Floer equation of `K = H dt`,
the derivative `ξ = ∂t u` solves `∂s ξ + J ∂t ξ - J dX_H(u) ξ = 0`. -/
private theorem fderiv_imag_apply_real (hH : ContDiff ℝ 2 H) (hu : ContDiff ℝ 2 u)
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V)) (z : ℝ × ℝ) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z (1, 0) =
      -J (fderiv ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z (0, 1)) +
        J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (fderiv ℝ u z (0, 1))) := by
  have hfun : (fun y ↦ fderiv ℝ u y (1, 0)) =
      fun y ↦ -J (fderiv ℝ u y (0, 1)) + J (ω.hamiltonianVectorField H (u y)) :=
    funext fun y ↦ fderiv_apply_real_eq (hfl y)
  rw [fderiv_fderiv_apply_comm hu.contDiffAt
    (by norm_num [minSmoothness_of_isRCLikeNormedField]), hfun]
  set Jc : V →L[ℝ] V := J.toLinearMap.toContinuousLinearMap
  have hξ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero z
  have hX : DifferentiableAt ℝ (ω.hamiltonianVectorField H) (u z) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) hH).differentiable one_ne_zero _
  have h : HasFDerivAt
      (fun y ↦ -J (fderiv ℝ u y (0, 1)) + J (ω.hamiltonianVectorField H (u y)))
      (-(Jc.comp (fderiv ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z)) +
        Jc.comp ((fderiv ℝ (ω.hamiltonianVectorField H) (u z)).comp (fderiv ℝ u z))) z :=
    (Jc.hasFDerivAt.comp z hξ.hasFDerivAt).neg.add
      (Jc.hasFDerivAt.comp z (hX.hasFDerivAt.comp z
        ((hu.differentiable (by norm_num)) z).hasFDerivAt))
  rw [h.fderiv]
  simp [Jc]

/-- **The equation of `∂s ξ`.** If `ξ` solves `∂s ξ = -J ∂t ξ + J dX_H(u) ξ`, then `η = ∂s ξ`
solves `∂s η = -J ∂t η + J (d²X_H(u)(∂s u) ξ) + J dX_H(u) η`. -/
private theorem fderiv_real_apply_real (hH : ContDiff ℝ 3 H) (hu : Differentiable ℝ u)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ)
    (hξeq : ∀ z, fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (z : ℝ × ℝ) :
    fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) z (1, 0) =
      -J (fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) z (0, 1)) +
        J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) (u z) (fderiv ℝ u z (1, 0)) (ξ z)) +
        J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (fderiv ℝ ξ z (1, 0))) := by
  rw [fderiv_fderiv_apply_comm hξ.contDiffAt
    (by norm_num [minSmoothness_of_isRCLikeNormedField]) (1, 0) (0, 1)]
  conv_lhs => rw [funext hξeq]
  set Jc : V →L[ℝ] V := J.toLinearMap.toContinuousLinearMap
  set dX := fderiv ℝ (ω.hamiltonianVectorField H)
  have hdξ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ ξ y (0, 1)) z :=
    ((hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero z
  have hdX : DifferentiableAt ℝ dX (u z) :=
    ((ω.contDiff_hamiltonianVectorField (n := 2) hH).fderiv_right (m := 1)
      (by norm_num)).differentiable one_ne_zero _
  have h : HasFDerivAt
      (fun y ↦ -J (fderiv ℝ ξ y (0, 1)) + J (dX (u y) (ξ y)))
      (-(Jc.comp (fderiv ℝ (fun y ↦ fderiv ℝ ξ y (0, 1)) z)) +
        Jc.comp ((dX (u z)).comp (fderiv ℝ ξ z) +
          ((fderiv ℝ dX (u z)).comp (fderiv ℝ u z)).flip (ξ z))) z :=
    (Jc.hasFDerivAt.comp z hdξ.hasFDerivAt).neg.add
      (Jc.hasFDerivAt.comp z ((hdX.hasFDerivAt.comp z (hu z).hasFDerivAt).clm_apply
        ((hξ.differentiable (by norm_num)) z).hasFDerivAt))
  rw [h.fderiv]
  simp only [add_apply, neg_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, Jc, LinearMap.coe_toContinuousLinearMap', map_add]
  abel

end Derivatives

section Periodic

omit [FiniteDimensional ℝ V] in
/-- The map `t ↦ ∂ ξ(s, t) v` is continuous for a `C¹` map `ξ`. -/
private theorem continuous_fderiv_slice {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {ξ : ℝ × ℝ → W} (hξ : ContDiff ℝ 1 ξ) (s : ℝ) (v : ℝ × ℝ) :
    Continuous fun t ↦ fderiv ℝ ξ (s, t) v :=
  ((hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
    (continuous_const.prodMk continuous_id)

/-- The `t`-derivative of a `C¹` function of period one in `t` integrates to zero over a
period. -/
private theorem integral_fderiv_apply_imag_eq_zero {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W] {F : ℝ × ℝ → W} (hF : ContDiff ℝ 1 F)
    (hper : ∀ s t, F (s, t + 1) = F (s, t)) (s : ℝ) :
    ∫ t in (0 : ℝ)..1, fderiv ℝ F (s, t) (0, 1) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_slice_right (hF.differentiable one_ne_zero (s, t)))
    ((continuous_fderiv_slice hF s (0, 1)).intervalIntegrable _ _)]
  simpa using congrArg (· - F (s, 0)) (hper s 0)

end Periodic

section Slice

variable {ξ : ℝ × ℝ → V}

/-- **Wirtinger's inequality on a slice.** If `ξ` is `C¹`, of period one in `t`, and every slice
`t ↦ ξ(s, t)` has mean zero, then `∫₀¹ ‖ξ(s, t)‖² dt ≤ (2π)⁻² ∫₀¹ ‖∂t ξ(s, t)‖² dt`. -/
private theorem integral_norm_sq_slice_le (hξ : ContDiff ℝ 1 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0)
    (s : ℝ) :
    ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      (1 / (2 * π)) ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (0, 1)‖ ^ 2 := by
  have hac : AbsolutelyContinuousOnInterval (fun t ↦ ξ (s, t)) 0 1 :=
    (hξ.comp (contDiff_const.prodMk contDiff_id)).contDiffOn.absolutelyContinuousOnInterval
  have hL2 : MemLp (fun t ↦ fderiv ℝ ξ (s, t) (0, 1)) 2 (volume.restrict (Ioc 0 1)) :=
    (continuous_fderiv_slice hξ s (0, 1)).continuousOn.memLp_restrict_of_subset_isCompact
      isCompact_Icc measurableSet_Ioc Ioc_subset_Icc_self 2
  have hW := integral_norm_sub_average_sq_le zero_lt_one hac
    (Eventually.of_forall fun t _ ↦ hasDerivAt_slice_right (hξ.differentiable one_ne_zero _))
    (by simpa using (hper s 0).symm) hL2
  rw [interval_average_eq, hmean s, smul_zero] at hW
  simpa using hW

omit [FiniteDimensional ℝ V] in
/-- A pointwise form of the reverse triangle inequality in `L²`: if `‖q‖ ≤ a r` with
`0 ≤ a ≤ 2π`, then `(1 - a / 2π) ‖p‖² - (2π - a) a r² ≤ ‖p - q‖²`. -/
private theorem sub_mul_norm_sq_le_norm_sub_sq {a r : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 2 * π)
    {p q : V} (hq : ‖q‖ ≤ a * r) :
    (1 - a / (2 * π)) * ‖p‖ ^ 2 - (2 * π - a) * a * r ^ 2 ≤ ‖p - q‖ ^ 2 := by
  have hπ : 0 < 2 * π := by positivity
  have hpq : ⟪p, q⟫ ≤ ‖p‖ * ‖q‖ := real_inner_le_norm p q
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  rw [norm_sub_sq_real]
  rcases ha0.eq_or_lt with rfl | ha0'
  · have : ‖q‖ = 0 := le_antisymm (by simpa using hq) hq0
    rw [this] at hpq ⊢
    norm_num at hpq ⊢
    linarith
  -- After multiplying by `2π a`, the difference is at least `(a ‖p‖ - 2π ‖q‖)²`.
  have hq2 : ‖q‖ ^ 2 ≤ (a * r) ^ 2 := pow_le_pow_left₀ hq0 hq 2
  have hX : 0 ≤ 2 * π * a *
      (a / (2 * π) * ‖p‖ ^ 2 - 2 * (‖p‖ * ‖q‖) + ‖q‖ ^ 2 + (2 * π - a) * a * r ^ 2) := by
    have he : 2 * π * a *
        (a / (2 * π) * ‖p‖ ^ 2 - 2 * (‖p‖ * ‖q‖) + ‖q‖ ^ 2 + (2 * π - a) * a * r ^ 2) =
        (a * ‖p‖ - 2 * π * ‖q‖) ^ 2 + 2 * π * (2 * π - a) * ((a * r) ^ 2 - ‖q‖ ^ 2) := by
      field_simp
      ring
    rw [he]
    have : 0 ≤ 2 * π * (2 * π - a) := mul_nonneg hπ.le (by linarith)
    nlinarith [sq_nonneg (a * ‖p‖ - 2 * π * ‖q‖)]
  have hX' := (mul_nonneg_iff_of_pos_left (by positivity : 0 < 2 * π * a)).1 hX
  have hsplit : (1 - a / (2 * π)) * ‖p‖ ^ 2 = ‖p‖ ^ 2 - a / (2 * π) * ‖p‖ ^ 2 := by ring
  rw [hsplit]
  nlinarith

/-- **The lower bound for `∂s ξ`.** If `ξ` solves `∂s ξ = -J ∂t ξ + J dX_H(u) ξ`, with `ξ` of
period one in `t` and mean zero on every slice, and `‖dX_H‖ ≤ a ≤ 2π`, then
`(2π - a)² ∫₀¹ ‖ξ(s, t)‖² dt ≤ ∫₀¹ ‖∂s ξ(s, t)‖² dt`. -/
private theorem mul_integral_norm_sq_slice_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a : ℝ}
    (ha0 : 0 ≤ a) (ha2π : a ≤ 2 * π)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a) (hξ : ContDiff ℝ 1 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0)
    (hξeq : ∀ z, fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (s : ℝ) :
    (2 * π - a) ^ 2 * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2 := by
  have hJ : ∀ v, ‖J v‖ = ‖v‖ := ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner fun v ↦ hg v v
  -- Pointwise, `∂s ξ = -J (∂t ξ - dX_H(u) ξ)` with `‖dX_H(u) ξ‖ ≤ a ‖ξ‖`.
  have hpt (t : ℝ) : (1 - a / (2 * π)) * ‖fderiv ℝ ξ (s, t) (0, 1)‖ ^ 2 -
      (2 * π - a) * a * ‖ξ (s, t)‖ ^ 2 ≤ ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2 := by
    have he : fderiv ℝ ξ (s, t) (1, 0) = -J (fderiv ℝ ξ (s, t) (0, 1) -
        fderiv ℝ (ω.hamiltonianVectorField H) (u (s, t)) (ξ (s, t))) := by
      rw [hξeq, map_sub]
      abel
    rw [he, norm_neg, hJ]
    exact sub_mul_norm_sq_le_norm_sub_sq ha0 ha2π
      (((fderiv ℝ (ω.hamiltonianVectorField H) (u (s, t))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (ha _) (norm_nonneg _)))
  have hcξ : Continuous fun t ↦ ξ (s, t) :=
    hξ.continuous.comp (continuous_const.prodMk continuous_id)
  have hc₁ :=
    ((continuous_fderiv_slice hξ s (0, 1)).norm.pow 2).intervalIntegrable (μ := volume) 0 1
  have hc₂ :=
    ((continuous_fderiv_slice hξ s (1, 0)).norm.pow 2).intervalIntegrable (μ := volume) 0 1
  have hc₀ := (hcξ.norm.pow 2).intervalIntegrable (μ := volume) 0 1
  have hint := intervalIntegral.integral_mono_on zero_le_one
    ((hc₁.const_mul _).sub (hc₀.const_mul _)) hc₂ fun t _ ↦ hpt t
  rw [intervalIntegral.integral_sub (hc₁.const_mul _) (hc₀.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  simp only [Pi.pow_apply] at hint
  -- Wirtinger: `(2π)² ∫ ‖ξ‖² ≤ ∫ ‖∂t ξ‖²`.
  have hπ : 0 < 2 * π := by positivity
  have hW : (2 * π) ^ 2 * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (0, 1)‖ ^ 2 := by
    have h := integral_norm_sq_slice_le hξ hper hmean s
    rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h
    linarith
  have hcoef : 0 ≤ 1 - a / (2 * π) := by
    rw [sub_nonneg, div_le_one hπ]
    exact ha2π
  have hmul := mul_le_mul_of_nonneg_left hW hcoef
  have hid : (1 - a / (2 * π)) * (2 * π) ^ 2 = (2 * π - a) * (2 * π) := by
    field_simp
  rw [← mul_assoc, hid] at hmul
  linarith

/-- **The bound for the curvature of `dX_H` along `u`.** If `‖d²X_H‖ ≤ c` and `‖du‖ ≤ M`, then
`-c M ∫₀¹ ‖ξ‖² ≤ ∫₀¹ ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫`. -/
private theorem neg_mul_integral_norm_sq_slice_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {c M : ℝ}
    (hH : ContDiff ℝ 3 H)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (hu : ContDiff ℝ 1 u) (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) (hξ : ContDiff ℝ 1 ξ) (s : ℝ) :
    -(c * M) * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ⟪ξ (s, t), J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
        (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ := by
  set Jc : V →L[ℝ] V := J.toLinearMap.toContinuousLinearMap
  have hJ : ∀ v, ‖J v‖ = ‖v‖ := ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner fun v ↦ hg v v
  have hc0 : 0 ≤ c :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) 0)).trans (hc 0)
  have hsl : Continuous fun t : ℝ ↦ ((s, t) : ℝ × ℝ) := continuous_const.prodMk continuous_id
  have hcξ : Continuous fun t ↦ ξ (s, t) := hξ.continuous.comp hsl
  have hd2X : Continuous (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))) :=
    ((ω.contDiff_hamiltonianVectorField (n := 2) hH).fderiv_right (m := 1)
      (by norm_num)).continuous_fderiv one_ne_zero
  have hcont : Continuous fun t ↦ ⟪ξ (s, t), Jc (fderiv ℝ (fderiv ℝ
      (ω.hamiltonianVectorField H)) (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ :=
    hcξ.inner (Jc.continuous.comp (((hd2X.comp (hu.continuous.comp hsl)).clm_apply
      ((continuous_fderiv_slice hu s (1, 0)))).clm_apply hcξ))
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one
    (((hcξ.norm.pow 2).intervalIntegrable (μ := volume) 0 1).const_mul _)
    (hcont.intervalIntegrable 0 1) fun t _ ↦ ?_
  set L := fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) (u (s, t))
  have hus : ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ M :=
    ((fderiv ℝ u (s, t)).le_opNorm _).trans (by simpa using hM (s, t))
  have hLξ : ‖L (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t))‖ ≤ c * M * ‖ξ (s, t)‖ :=
    ((L _).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((L.le_opNorm _).trans
      (mul_le_mul (hc _) hus (norm_nonneg _) hc0)) (norm_nonneg _))
  have hin := neg_le_of_abs_le (abs_real_inner_le_norm (ξ (s, t))
    (J (L (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))))
  rw [hJ] at hin
  nlinarith [mul_le_mul_of_nonneg_left hLξ (norm_nonneg (ξ (s, t)))]

/-- **The second variation of the slice energy.** If `ξ` solves `∂s ξ = -J ∂t ξ + J dX_H(u) ξ`
and has period one in `t`, then, with `η = ∂s ξ`,
`∫₀¹ (⟪ξ, ∂s η⟫ + ‖η‖²) = 2 ∫₀¹ ‖η‖² + ∫₀¹ ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫`. The difference of the
integrands is the `t`-derivative of `⟪J ξ, η⟫`, which integrates to zero over a period; this is
where the symmetry of `J dX_H(u)` and the skew-adjointness of `J` enter. -/
private theorem integral_inner_fderiv_slice_eq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t))
    (hξeq : ∀ z, fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (s : ℝ) :
    ∫ t in (0 : ℝ)..1, (⟪ξ (s, t), fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) (s, t) (1, 0)⟫ +
        ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2) =
      2 * (∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2) +
        ∫ t in (0 : ℝ)..1, ⟪ξ (s, t), J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
          (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ := by
  set Jc : V →L[ℝ] V := J.toLinearMap.toContinuousLinearMap
  set η : ℝ × ℝ → V := fun y ↦ fderiv ℝ ξ y (1, 0)
  have hη : ContDiff ℝ 1 η := (hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hJξ : ContDiff ℝ 1 fun y ↦ J (ξ y) := Jc.contDiff.comp (hξ.of_le (by norm_num))
  -- The boundary term `⟪J ξ, η⟫` has period one in `t`, so its `t`-derivative integrates to zero.
  have hB : ContDiff ℝ 1 fun y ↦ ⟪J (ξ y), η y⟫ := hJξ.inner ℝ hη
  have hBper : ∀ s t, ⟪J (ξ (s, t + 1)), η (s, t + 1)⟫ = ⟪J (ξ (s, t)), η (s, t)⟫ :=
    fun s t ↦ by
      have hpξ : Function.Periodic ξ ((0 : ℝ), (1 : ℝ)) := fun ⟨p, q⟩ ↦ by simpa using hper p q
      have hd : fderiv ℝ ξ (s, t + 1) = fderiv ℝ ξ (s, t) := by simpa using hpξ.fderiv (s, t)
      simp only [η, hper, hd]
  have hB0 := integral_fderiv_apply_imag_eq_zero hB hBper s
  -- Pointwise, the integrands differ by the `t`-derivative of `⟪J ξ, η⟫`.
  have hpt (z : ℝ × ℝ) : ⟪ξ z, fderiv ℝ η z (1, 0)⟫ + ‖η z‖ ^ 2 =
      2 * ‖η z‖ ^ 2 + ⟪ξ z, J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) (u z)
        (fderiv ℝ u z (1, 0)) (ξ z))⟫ + fderiv ℝ (fun y ↦ ⟪J (ξ y), η y⟫) z (0, 1) := by
    have hdJξ : fderiv ℝ (fun y ↦ J (ξ y)) z (0, 1) = J (fderiv ℝ ξ z (0, 1)) := by
      have h : HasFDerivAt (fun y ↦ J (ξ y)) (Jc.comp (fderiv ℝ ξ z)) z :=
        Jc.hasFDerivAt.comp z ((hξ.differentiable (by norm_num)) z).hasFDerivAt
      rw [h.fderiv]
      simp [Jc]
    rw [fderiv_inner_apply ℝ (hJξ.differentiable one_ne_zero z) (hη.differentiable one_ne_zero z),
      hdJξ,
      fderiv_real_apply_real hH (hu.differentiable one_ne_zero) hξ hξeq z]
    have hsym := inner_apply_fderiv_hamiltonianVectorField_comm hg (hH.contDiffAt.of_le
      (by norm_num) : ContDiffAt ℝ 2 H (u z)) (ξ z) (η z)
    have hskew := inner_apply_left_eq_neg hg (ξ z) (fderiv ℝ η z (0, 1))
    have hηeq : η z = -J (fderiv ℝ ξ z (0, 1)) +
        J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)) := hξeq z
    have hnorm : ‖η z‖ ^ 2 = ⟪-J (fderiv ℝ ξ z (0, 1)) +
        J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)), η z⟫ := by
      rw [← hηeq, real_inner_self_eq_norm_sq]
    simp only [inner_add_right, inner_add_left, inner_neg_left, inner_neg_right] at hnorm ⊢
    linarith
  have hsl : Continuous fun t : ℝ ↦ ((s, t) : ℝ × ℝ) := continuous_const.prodMk continuous_id
  have hd2X : Continuous (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))) :=
    ((ω.contDiff_hamiltonianVectorField (n := 2) hH).fderiv_right (m := 1)
      (by norm_num)).continuous_fderiv one_ne_zero
  have hcξ : Continuous fun t ↦ ξ (s, t) := hξ.continuous.comp hsl
  have hA₁ : Continuous fun t ↦ ‖η (s, t)‖ ^ 2 := (hη.continuous.comp hsl).norm.pow 2
  have hA₂ : Continuous fun t ↦ ⟪ξ (s, t), J (fderiv ℝ (fderiv ℝ
      (ω.hamiltonianVectorField H)) (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ :=
    hcξ.inner (Jc.continuous.comp (((hd2X.comp (hu.continuous.comp hsl)).clm_apply
      (continuous_fderiv_slice hu s (1, 0))).clm_apply hcξ))
  have hdB : Continuous fun t ↦ fderiv ℝ (fun y ↦ ⟪J (ξ y), η y⟫) (s, t) (0, 1) :=
    continuous_fderiv_slice hB s (0, 1)
  rw [intervalIntegral.integral_congr fun t _ ↦ hpt (s, t),
    intervalIntegral.integral_add (((hA₁.intervalIntegrable (μ := volume) 0 1).const_mul 2).add
      (hA₂.intervalIntegrable 0 1)) (hdB.intervalIntegrable 0 1), hB0, add_zero,
    intervalIntegral.integral_add ((hA₁.intervalIntegrable 0 1).const_mul 2)
      (hA₂.intervalIntegrable 0 1), intervalIntegral.integral_const_mul]

omit [FiniteDimensional ℝ V] in
/-- The slice energy `s ↦ ∫₀¹ ‖ξ(s, t)‖² dt` has derivative `∫₀¹ 2 ⟪ξ, ∂s ξ⟫ dt`. -/
private theorem hasDerivAt_integral_norm_sq_slice (hξ : ContDiff ℝ 1 ξ) (s : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2)
      (∫ t in (0 : ℝ)..1, 2 * ⟪ξ (s, t), fderiv ℝ ξ (s, t) (1, 0)⟫) s := by
  have h := (TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn (G := fun z ↦ ‖ξ z‖ ^ 2)
    isOpen_univ (hξ.norm_sq ℝ).contDiffOn (x₀ := s) (a := 0) (b := 1) (subset_univ _)).2
  refine h.congr_deriv (intervalIntegral.integral_congr fun t _ ↦ ?_)
  rw [(((hξ.differentiable one_ne_zero) (s, t)).hasFDerivAt.norm_sq).fderiv]
  simp

omit [FiniteDimensional ℝ V] in
/-- The derivative `s ↦ ∫₀¹ 2 ⟪ξ, ∂s ξ⟫ dt` of the slice energy has derivative
`∫₀¹ 2 (⟪ξ, ∂s² ξ⟫ + ‖∂s ξ‖²) dt`. -/
private theorem hasDerivAt_integral_inner_slice (hξ : ContDiff ℝ 2 ξ) (s : ℝ) :
    HasDerivAt (fun s ↦ ∫ t in (0 : ℝ)..1, 2 * ⟪ξ (s, t), fderiv ℝ ξ (s, t) (1, 0)⟫)
      (∫ t in (0 : ℝ)..1, 2 * (⟪ξ (s, t), fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) (s, t) (1, 0)⟫ +
        ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2)) s := by
  have hη : ContDiff ℝ 1 fun y ↦ fderiv ℝ ξ y (1, 0) :=
    (hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le (by norm_num)
  have h := (TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn
    (G := fun z ↦ 2 * ⟪ξ z, fderiv ℝ ξ z (1, 0)⟫) isOpen_univ
    (contDiff_const.mul (hξ1.inner ℝ hη)).contDiffOn (x₀ := s) (a := 0) (b := 1)
    (subset_univ _)).2
  refine h.congr_deriv (intervalIntegral.integral_congr fun t _ ↦ ?_)
  rw [fderiv_const_mul ((hξ1.inner ℝ hη).differentiable one_ne_zero (s, t)),
    smul_apply, fderiv_inner_apply ℝ (hξ1.differentiable one_ne_zero (s, t))
      (hη.differentiable one_ne_zero (s, t)), real_inner_self_eq_norm_sq, smul_eq_mul]

/-- **Bounded solutions of the linearized equation with mean-zero slices vanish.** Let `ξ` be a
bounded `C²` solution of `∂s ξ = -J ∂t ξ + J dX_H(u) ξ`, of period one in `t`, whose slices
`t ↦ ξ(s, t)` have mean zero. If `‖dX_H‖ ≤ a < 2π`, `‖d²X_H‖ ≤ c`, `‖du‖ ≤ M` and
`c M < 2 (2π - a)²`, then `ξ = 0`. -/
private theorem eq_zero_of_fderiv_apply_real_eq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a c M B : ℝ}
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hu : ContDiff ℝ 1 u) (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0)
    (hξeq : ∀ z, fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (hB : ∀ z, ‖ξ z‖ ≤ B) (z : ℝ × ℝ) : ξ z = 0 := by
  have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le (by norm_num)
  have ha0 : 0 ≤ a := (norm_nonneg (fderiv ℝ (ω.hamiltonianVectorField H) 0)).trans (ha 0)
  have hsl (s : ℝ) : Continuous fun t : ℝ ↦ ((s, t) : ℝ × ℝ) :=
    continuous_const.prodMk continuous_id
  -- The slice energy `f` satisfies `f'' ≥ κ f` with `κ = 4 (2π - a)² - 2 c M > 0`.
  set f : ℝ → ℝ := fun s ↦ ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 with hf_def
  have hle (s : ℝ) : (4 * (2 * π - a) ^ 2 - 2 * (c * M)) * f s ≤
      ∫ t in (0 : ℝ)..1, 2 * (⟪ξ (s, t), fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) (s, t) (1, 0)⟫ +
        ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul,
      integral_inner_fderiv_slice_eq hg hH hu hξ hper hξeq s]
    have h₁ := mul_integral_norm_sq_slice_le hg ha0 ha2π.le ha hξ1 hper hmean hξeq s
    have h₂ := neg_mul_integral_norm_sq_slice_le hg hH hc hu hM hξ1 s
    simp only [hf_def]
    linarith
  have hf0 (s : ℝ) : 0 ≤ f s :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ ↦ sq_nonneg _
  have hcont (s : ℝ) : Continuous fun t ↦ ‖ξ (s, t)‖ ^ 2 :=
    (hξ.continuous.comp (hsl s)).norm.pow 2
  have hfb : BddAbove (range f) := ⟨B ^ 2, by
    rintro _ ⟨s, rfl⟩
    have h := intervalIntegral.integral_mono_on (g := fun _ ↦ B ^ 2) zero_le_one
      ((hcont s).intervalIntegrable (μ := volume) 0 1) intervalIntegrable_const
      fun t _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hB (s, t)) 2
    simpa using h⟩
  have hfz := eq_zero_of_hasDerivAt_of_mul_le_of_bddAbove (by nlinarith)
    (hasDerivAt_integral_norm_sq_slice hξ1) (hasDerivAt_integral_inner_slice hξ) hle hf0 hfb
  -- A continuous slice with vanishing `L²` norm vanishes on `(0, 1]`, hence everywhere.
  obtain ⟨s, t⟩ := z
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (Eventually.of_forall fun t ↦ sq_nonneg ‖ξ (s, t)‖)
    ((hcont s).intervalIntegrable (μ := volume) 0 1)).1 (hfz s)
  have hIoc := Measure.eqOn_Ioc_of_ae_eq volume hae (hcont s).continuousOn continuousOn_const
  have hpers : Function.Periodic (fun t ↦ ξ (s, t)) 1 := hper s
  obtain ⟨t', ht', hξt⟩ := hpers.exists_mem_Ioc zero_lt_one t 0
  rw [zero_add] at ht'
  simpa [hξt] using hIoc ht'

end Slice


section Main

variable {a c M : ℝ}

/-- **Floer cylinders of a small autonomous Hamiltonian are time-independent.** Let the inner
product of `V` be the metric `ω(·, J ·)` of a constant compatible almost complex structure `J`,
and let `H` be a `C³` autonomous Hamiltonian with `‖dX_H‖ ≤ a < 2π` and `‖d²X_H‖ ≤ c`. Let `u` be
a `C³` solution of the Floer equation `∂s u + J (∂t u - X_H(u)) = 0` of `K = H dt`, of period one
in `t`, with `‖du‖ ≤ M`. If `c M < 2 (2π - a)²`, then `u` does not depend on `t`:
`u(s, t) = u(s, 0)`. -/
theorem eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hu : ContDiff ℝ 3 u) (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) :
    u = fun z ↦ u (z.1, 0) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  -- `ξ = ∂t u` is a bounded solution of the linearized equation with mean-zero slices.
  set ξ : ℝ × ℝ → V := fun y ↦ fderiv ℝ u y (0, 1)
  have hξ : ContDiff ℝ 2 ξ := (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hξper (s t : ℝ) : ξ (s, t + 1) = ξ (s, t) := by
    have hpu : Function.Periodic u ((0 : ℝ), (1 : ℝ)) := fun ⟨p, q⟩ ↦ by simpa using hper p q
    have hd : fderiv ℝ u (s, t + 1) = fderiv ℝ u (s, t) := by simpa using hpu.fderiv (s, t)
    simp only [ξ, hd]
  have hB (z : ℝ × ℝ) : ‖ξ z‖ ≤ M :=
    ((fderiv ℝ u z).le_opNorm _).trans (by simpa using hM z)
  have hzero := eq_zero_of_fderiv_apply_real_eq hg hH ha hc ha2π hcM hu1 hM hξ hξper
    (integral_fderiv_apply_imag_eq_zero hu1 hper)
    (fderiv_imag_apply_real (hH.of_le (by norm_num)) (hu.of_le (by norm_num)) hfl) hB
  -- So every slice `t ↦ u(s, t)` has vanishing derivative.
  funext ⟨s, t⟩
  have hd (t : ℝ) : HasDerivAt (fun t ↦ u (s, t)) 0 t := by
    simpa [ξ, hzero (s, t)] using hasDerivAt_slice_right (hu1.differentiable one_ne_zero (s, t))
  exact is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) t 0

/-- **Floer cylinders of a small autonomous Hamiltonian are gradient lines.** Under the hypotheses
of `TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`, the curve
`γ(s) = u(s, 0)` is an upward gradient line of `H`, `γ' = ∇H(γ)`, for the metric `ω(·, J ·)`, and
`u(s, t) = γ(s)`. -/
theorem hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hH : ContDiff ℝ 3 H)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hu : ContDiff ℝ 3 u) (hper : ∀ s t, u (s, t + 1) = u (s, t))
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) (s : ℝ) :
    HasDerivAt (fun s ↦ u (s, 0)) (∇ H (u (s, 0))) s := by
  have hmain := eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv hg hH ha hc ha2π hcM hu hper
    hfl hM
  have hγ : Differentiable ℝ fun s ↦ u (s, 0) :=
    (hu.differentiable (by norm_num)).comp (differentiable_id.prodMk (differentiable_const 0))
  have h := hfl (s, 0)
  rw [hmain] at h
  have hgrad := (Invariant.isComplexLinearMap_perturbedFDeriv_comp_fst_iff
    (ω.invariant_of_apply_apply_eq_inner hg) (γ := fun s ↦ u (s, 0)) (z := (s, 0)) (hγ s)).1 h
  have hd : deriv (fun s ↦ u (s, 0)) s = ∇ H (u (s, 0)) := ext_inner_right ℝ fun w ↦ by
    rw [inner_gradient_left, ← hg, ← associatedBilinForm_apply]
    exact hgrad w
  exact hd ▸ (hγ s).hasDerivAt

end Main

end TauCeti.SymplecticForm
