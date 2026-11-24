/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization.Basic
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Submodule
import TauCeti.Analysis.Calculus.IntervalIntegral.Slice
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Convex.BddAbove
import TauCeti.Analysis.Fourier.MixedWirtinger
import TauCeti.Analysis.Fourier.Wirtinger
import TauCeti.Analysis.InnerProductSpace.CompleteSquare
import TauCeti.Geometry.Symplectic.CompatibleMetric

/-!
# Floer cylinders and strips of small autonomous Hamiltonians are time-independent

Let `(V, ω)` be a symplectic vector space whose inner product is the metric `g = ω(·, J ·)` of a
constant compatible almost complex structure `J`, and let `H : V → ℝ` be an autonomous
Hamiltonian. For the cylindrical perturbation `K = H dt` the Floer equation reads
`∂s u + J (∂t u - X_H(u)) = 0`. Its solutions that do not depend on `t` are the gradient lines of
`H` (`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Basic`). This file proves a converse,
both for cylinders and for strips: a solution whose derivative is small relative to the
Hamiltonian is independent of `t`, and so is a gradient line. This is the analytic step behind
the identification of the Floer cylinders of a small Morse Hamiltonian, and of the Floer strips
between a Lagrangian and its image under a small Hamiltonian, with gradient trajectories.

The smallness condition couples `H` and the solution. Let `H` be `C³` with `‖dX_H‖ ≤ a` and
`‖d²X_H‖ ≤ c` everywhere, and let `u` be `C³` with `‖du‖ ≤ M`.

* **Cylinders.** If `u` has period one in `t`, `a < 2π` and `c M < 2 (2π - a)²`, then
  `u(s, t) = u(s, 0)`
  (`TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`), and
  `γ(s) = u(s, 0)` solves `γ' = ∇H(γ)`
  (`TauCeti.SymplecticForm.hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv`).
* **Strips.** Let `L` be an isotropic subspace, for instance a Lagrangian one, along which the
  gradient of `H` is tangent to `L`. If `u` solves the Floer equation on the strip `ℝ × [0, 1]`
  with boundary values `u(s, 0), u(s, 1) ∈ L`, `a < π` and `c M < 2 (π - a)²`, then
  `u(s, t) = u(s, 0)` on the strip
  (`TauCeti.SymplecticForm.eqOn_comp_fst_of_isComplexLinearMap_perturbedFDeriv_of_isIsotropic`),
  and `γ(s) = u(s, 0)` is again a gradient line in `L`
  (`SymplecticForm.hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv_of_isIsotropic`).
  In the cotangent model `V × V` with the zero section `L = V × {0}` and `H(q, p) = h(q)`, the
  gradient `(∇h(q), 0)` is tangent to `L`. This is the setting of Floer's comparison of the Floer
  complex of the zero section and its image under the time-one flow of `X_H`, the graph of `-dh`,
  with the Morse complex of `h`.

No finite energy, limits at the ends or nondegeneracy are assumed.

**The argument.** Differentiating the Floer equation in `t`, the derivative `ξ = ∂t u` solves
the linearized equation `∂s ξ = -J ∂t ξ + S ξ` with `S = J dX_H(u)`. Since `J X_H` is the
gradient of `H`, the operator `S` is the Hessian of `H` along `u`, so it is symmetric, and `J` is
skew-adjoint. The slice energy `f(s) = ∫₀¹ ‖ξ(s, t)‖² dt` then satisfies

`f'' = 4 ∫₀¹ ‖∂s ξ‖² + 2 ∫₀¹ ⟪ξ, (∂s S) ξ⟫ + 2 [⟪J ξ, ∂s ξ⟫]₀¹`,

after an integration by parts in `t`. For a cylinder the boundary term cancels by periodicity, and
each slice `t ↦ ξ(s, t)` is the derivative of a loop, so it has mean zero and Wirtinger's
inequality for loops (`TauCeti.integral_norm_sq_le_of_integral_eq_zero`) bounds `∫₀¹ ‖∂t ξ‖²`
below by `(2π)² f(s)`. For a strip the Floer equation puts `J ξ` and `J ∂s ξ` in `L` on the
boundary, so the boundary term vanishes because `L` is isotropic. The boundary values of `ξ` lie
in `Lᗮ` and the integral of each slice is `u(s, 1) - u(s, 0) ∈ L`, so the Poincaré inequality with
mixed boundary conditions
(`TauCeti.mul_integral_norm_sq_le_integral_norm_sq_of_mem_of_integral_mem_orthogonal`) bounds
`∫₀¹ ‖∂t ξ‖²` below by `π² f(s)`. Writing `C` for `2π`, respectively `π`, this bounds
`∫₀¹ ‖∂s ξ‖² = ∫₀¹ ‖∂t ξ - dX_H(u) ξ‖²` below by `(C - a)² f`, and `‖∂s S‖ ≤ c M`. Hence
`f'' ≥ (4 (C - a)² - 2 c M) f` with a positive constant. A nonnegative bounded function with
`f'' ≥ κ f`, `κ > 0`, is convex and bounded, hence zero
(`TauCeti.eq_zero_of_hasDerivAt_of_mul_le_of_bddAbove`). So `ξ = 0`. This step only uses that `ξ`
is a bounded solution of the linearized equation along `u` whose slices satisfy the Wirtinger-type
bound `C² ∫₀¹ ‖ξ‖² ≤ ∫₀¹ ‖∂t ξ‖²` and whose boundary term `⟪J ξ, ∂s ξ⟫` takes equal values at
`t = 0` and `t = 1`.

**The linearized operator.** That step is a statement about the linearized Floer operator
`D_u ξ = ∂s ξ + J (∂t ξ - dX_H(u) ξ)` of `K = H dt` (`TauCeti.SymplecticForm.floerLinearization`).
If `H` is `C³` with `‖dX_H‖ ≤ a < 2π` and `‖d²X_H‖ ≤ c`, and `u` is a `C¹` map with `‖du‖ ≤ M`,
where `c M < 2 (2π - a)²`, then a bounded `C²` section `ξ` of period one in `t` whose slices have
mean zero and with `D_u ξ = 0` everywhere vanishes
(`TauCeti.SymplecticForm.eq_zero_of_floerLinearization_eq_zero`). Its consequences for the kernel of
`D_u` along a time-independent cylinder are in
`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Linearization`.

The constant structure `J` covers flat targets. On a torus `V / Λ` with a flat compatible
structure, a Floer cylinder whose loops are contractible lifts to a solution on `V` of period one
in `t`, for the lifted `Λ`-periodic Hamiltonian. Domain- or target-dependent structures, for which
the linearized operator acquires derivatives of `J`, are not treated here. For a small multiple `εH`
of `H` and cylinders of finite energy in a compact set, the bound on `du` holds uniformly, so that
these cylinders are time-independent
(`TauCeti.Geometry.Symplectic.Floer.TimeIndependent.SmallMultiple`).

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

section Derivatives

/-- Applying the constant structure `J` commutes with differentiation. -/
private theorem hasFDerivAt_apply {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : W → V} {f' : W →L[ℝ] V} {z : W} (hf : HasFDerivAt f f' z) :
    HasFDerivAt (fun y ↦ J (f y)) (J.toLinearMap.toContinuousLinearMap.comp f') z :=
  J.toLinearMap.toContinuousLinearMap.hasFDerivAt.comp z hf

/-- The Floer equation of `K = H dt`, solved for `∂s u`. -/
private theorem fderiv_apply_real_eq {z : ℝ × ℝ}
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V)) :
    fderiv ℝ u z (1, 0) = -J (fderiv ℝ u z (0, 1)) + J (ω.hamiltonianVectorField H (u z)) := by
  rw [ω.isComplexLinearMap_perturbedFDeriv_iff] at hfl
  simp only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero, stdComplexLineReal_eq,
    stdComplexLineImag_eq, map_sub] at hfl
  linear_combination (norm := module) hfl

/-- **The linearized equation of `∂t u`.** If `u` solves the Floer equation of `K = H dt` near
`z`, the derivative `ξ = ∂t u` solves `∂s ξ + J ∂t ξ - J dX_H(u) ξ = 0` at `z`. -/
private theorem fderiv_imag_apply_real (hH : ContDiff ℝ 2 H) (hu : ContDiff ℝ 2 u) {z : ℝ × ℝ}
    (hfl : ∀ᶠ y in 𝓝 z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u y : ℝ × ℝ →ₗ[ℝ] V)) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z (1, 0) =
      -J (fderiv ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z (0, 1)) +
        J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (fderiv ℝ u z (0, 1))) := by
  have hfun : (fun y ↦ fderiv ℝ u y (1, 0)) =ᶠ[𝓝 z]
      fun y ↦ -J (fderiv ℝ u y (0, 1)) + J (ω.hamiltonianVectorField H (u y)) :=
    hfl.mono fun y hy ↦ fderiv_apply_real_eq hy
  rw [fderiv_fderiv_apply_comm hu.contDiffAt
    (by norm_num [minSmoothness_of_isRCLikeNormedField]), hfun.fderiv_eq]
  have hξ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y (0, 1)) z :=
    ((hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero z
  have hX : DifferentiableAt ℝ (ω.hamiltonianVectorField H) (u z) :=
    (ω.contDiff_hamiltonianVectorField (n := 1) hH).differentiable one_ne_zero _
  have h : HasFDerivAt
      (fun y ↦ -J (fderiv ℝ u y (0, 1)) + J (ω.hamiltonianVectorField H (u y)))
      (_ : ℝ × ℝ →L[ℝ] V) z :=
    (hasFDerivAt_apply hξ.hasFDerivAt).neg.add (hasFDerivAt_apply
      (hX.hasFDerivAt.comp z ((hu.differentiable (by norm_num)) z).hasFDerivAt))
  rw [h.fderiv]
  simp

/-- **The equation of `∂s ξ`.** If `ξ` solves `∂s ξ = -J ∂t ξ + J dX_H(u) ξ` near `z`, then
`η = ∂s ξ` solves `∂s η = -J ∂t η + J (d²X_H(u)(∂s u) ξ) + J dX_H(u) η` at `z`. -/
private theorem fderiv_real_apply_real (hH : ContDiff ℝ 3 H) (hu : Differentiable ℝ u)
    {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 2 ξ) {z : ℝ × ℝ}
    (hξeq : ∀ᶠ y in 𝓝 z, fderiv ℝ ξ y (1, 0) =
      -J (fderiv ℝ ξ y (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u y) (ξ y))) :
    fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) z (1, 0) =
      -J (fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) z (0, 1)) +
        J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) (u z) (fderiv ℝ u z (1, 0)) (ξ z)) +
        J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (fderiv ℝ ξ z (1, 0))) := by
  set dX := fderiv ℝ (ω.hamiltonianVectorField H)
  have hfun : (fun y ↦ fderiv ℝ ξ y (1, 0)) =ᶠ[𝓝 z]
      fun y ↦ -J (fderiv ℝ ξ y (0, 1)) + J (dX (u y) (ξ y)) := hξeq
  rw [fderiv_fderiv_apply_comm hξ.contDiffAt
    (by norm_num [minSmoothness_of_isRCLikeNormedField]) (1, 0) (0, 1), hfun.fderiv_eq]
  have hdξ : DifferentiableAt ℝ (fun y ↦ fderiv ℝ ξ y (0, 1)) z :=
    ((hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero z
  have hdX : DifferentiableAt ℝ dX (u z) :=
    ((ω.contDiff_hamiltonianVectorField (n := 2) hH).fderiv_right (m := 1)
      (by norm_num)).differentiable one_ne_zero _
  have h : HasFDerivAt (fun y ↦ -J (fderiv ℝ ξ y (0, 1)) + J (dX (u y) (ξ y)))
      (_ : ℝ × ℝ →L[ℝ] V) z :=
    (hasFDerivAt_apply hdξ.hasFDerivAt).neg.add
      (hasFDerivAt_apply ((hdX.hasFDerivAt.comp z (hu z).hasFDerivAt).clm_apply
        ((hξ.differentiable (by norm_num)) z).hasFDerivAt))
  rw [h.fderiv]
  simp only [add_apply, neg_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply, LinearMap.coe_toContinuousLinearMap', map_add]
  abel

end Derivatives

section Slice

variable {ξ : ℝ × ℝ → V}

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A property of the points of the open strip `ℝ × (0, 1)` holds near each of them. -/
private theorem eventually_nhds_of_mem_Ioo {P : ℝ × ℝ → Prop}
    (hP : ∀ y : ℝ × ℝ, y.2 ∈ Ioo (0 : ℝ) 1 → P y) {z : ℝ × ℝ} (hz : z.2 ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ y in 𝓝 z, P y :=
  Filter.mem_of_superset ((isOpen_Ioo.preimage continuous_snd).mem_nhds hz) fun y hy ↦ hP y hy

/-- **The lower bound for `∂s ξ`.** Let the slice `t ↦ ξ(s, t)` satisfy the Wirtinger-type bound
`C² ∫₀¹ ‖ξ‖² ≤ ∫₀¹ ‖∂t ξ‖²` with `0 < C`, and let `ξ` solve `∂s ξ = -J ∂t ξ + J dX_H(u) ξ` on it
for `0 < t < 1`. If `‖dX_H‖ ≤ a ≤ C`, then `(C - a)² ∫₀¹ ‖ξ(s, t)‖² dt ≤ ∫₀¹ ‖∂s ξ(s, t)‖² dt`. -/
private theorem mul_integral_norm_sq_slice_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a C : ℝ}
    (ha0 : 0 ≤ a) (hC : 0 < C) (haC : a ≤ C)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a) (hξ : ContDiff ℝ 1 ξ) {s : ℝ}
    (hW : C ^ 2 * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (0, 1)‖ ^ 2)
    (hξeq : ∀ t ∈ Ioo (0 : ℝ) 1, fderiv ℝ ξ (s, t) (1, 0) = -J (fderiv ℝ ξ (s, t) (0, 1)) +
      J (fderiv ℝ (ω.hamiltonianVectorField H) (u (s, t)) (ξ (s, t)))) :
    (C - a) ^ 2 * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2 := by
  -- Pointwise, `∂s ξ = -J (∂t ξ - dX_H(u) ξ)` with `‖dX_H(u) ξ‖ ≤ a ‖ξ‖`.
  have hpt (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : (1 - a / C) * ‖fderiv ℝ ξ (s, t) (0, 1)‖ ^ 2 -
      (C - a) * a * ‖ξ (s, t)‖ ^ 2 ≤ ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2 := by
    have he : fderiv ℝ ξ (s, t) (1, 0) = -J (fderiv ℝ ξ (s, t) (0, 1) -
        fderiv ℝ (ω.hamiltonianVectorField H) (u (s, t)) (ξ (s, t))) := by
      rw [hξeq t ht, map_sub]
      abel
    rw [he, norm_neg, ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner fun v ↦ hg v v]
    exact one_sub_div_mul_norm_sq_sub_le_norm_sub_sq ha0 haC
      (((fderiv ℝ (ω.hamiltonianVectorField H) (u (s, t))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (ha _) (norm_nonneg _)))
  have hc₁ := ((continuous_fderiv_apply_slice_right hξ s (0, 1)).norm.pow 2).intervalIntegrable
    (μ := volume) 0 1
  have hc₂ := ((continuous_fderiv_apply_slice_right hξ s (1, 0)).norm.pow 2).intervalIntegrable
    (μ := volume) 0 1
  have hcξ : Continuous fun t ↦ ξ (s, t) := hξ.continuous.comp (.prodMk_right s)
  have hc₀ := (hcξ.norm.pow 2).intervalIntegrable (μ := volume) 0 1
  have hint := intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one
    ((hc₁.const_mul _).sub (hc₀.const_mul _)) hc₂ hpt
  rw [intervalIntegral.integral_sub (hc₁.const_mul _) (hc₀.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hint
  simp only [Pi.pow_apply] at hint
  have hcoef : 0 ≤ 1 - a / C := by
    rw [sub_nonneg, div_le_one hC]
    exact haC
  have hmul := mul_le_mul_of_nonneg_left hW hcoef
  have hid : (1 - a / C) * C ^ 2 = (C - a) * C := by
    field_simp
  rw [← mul_assoc, hid] at hmul
  linarith

/-- The integrand `t ↦ ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫` of the curvature term is continuous. -/
private theorem continuous_inner_apply_fderiv_fderiv_hamiltonianVectorField (hH : ContDiff ℝ 3 H)
    (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 1 ξ) (s : ℝ) :
    Continuous fun t ↦ ⟪ξ (s, t), J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
      (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ := by
  have hd2X : Continuous (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))) :=
    ((ω.contDiff_hamiltonianVectorField (n := 2) hH).fderiv_right (m := 1)
      (by norm_num)).continuous_fderiv one_ne_zero
  have hcξ : Continuous fun t ↦ ξ (s, t) := hξ.continuous.comp (.prodMk_right s)
  exact hcξ.inner (J.toLinearMap.toContinuousLinearMap.continuous.comp
    (((hd2X.comp (hu.continuous.comp (.prodMk_right s))).clm_apply
      (continuous_fderiv_apply_slice_right hu s (1, 0))).clm_apply hcξ))

/-- **The bound for the curvature of `dX_H` along `u`.** If `‖d²X_H‖ ≤ c` and `‖du‖ ≤ M` on the
slice `{s} × [0, 1]`, then `-c M ∫₀¹ ‖ξ‖² ≤ ∫₀¹ ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫`. -/
private theorem neg_mul_integral_norm_sq_slice_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {c M : ℝ}
    (hH : ContDiff ℝ 3 H)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (hu : ContDiff ℝ 1 u) {s : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ u (s, t)‖ ≤ M)
    (hξ : ContDiff ℝ 1 ξ) :
    -(c * M) * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ⟪ξ (s, t), J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
        (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ := by
  have hc0 : 0 ≤ c :=
    (norm_nonneg (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) 0)).trans (hc 0)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on zero_le_one
    ((((hξ.continuous.comp (.prodMk_right s)).norm.pow 2).intervalIntegrable
      (μ := volume) 0 1).const_mul _)
    ((continuous_inner_apply_fderiv_fderiv_hamiltonianVectorField hH hu hξ s).intervalIntegrable
      0 1) fun t ht ↦ ?_
  set L := fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) (u (s, t))
  have hus : ‖fderiv ℝ u (s, t) (1, 0)‖ ≤ M :=
    ((fderiv ℝ u (s, t)).le_opNorm _).trans (by simpa using hM t ht)
  have hLξ : ‖L (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t))‖ ≤ c * M * ‖ξ (s, t)‖ :=
    ((L _).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((L.le_opNorm _).trans
      (mul_le_mul (hc _) hus (norm_nonneg _) hc0)) (norm_nonneg _))
  have hin := neg_le_of_abs_le (abs_real_inner_le_norm (ξ (s, t))
    (J (L (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))))
  rw [ω.norm_apply_eq_norm_of_apply_apply_self_eq_inner fun v ↦ hg v v] at hin
  nlinarith [mul_le_mul_of_nonneg_left hLξ (norm_nonneg (ξ (s, t)))]

/-- **The pointwise identity behind the second variation of the slice energy.** If `ξ` solves
`∂s ξ = -J ∂t ξ + J dX_H(u) ξ` near `z`, then, with `η = ∂s ξ`,
`⟪ξ, ∂s η⟫ + ‖η‖² = 2 ‖η‖² + ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫ + ∂t ⟪J ξ, η⟫` at `z`. This is where the
symmetry of `J dX_H(u)` and the skew-adjointness of `J` enter. -/
private theorem inner_fderiv_real_real_add_norm_sq_eq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (hu : Differentiable ℝ u) (hξ : ContDiff ℝ 2 ξ) {z : ℝ × ℝ}
    (hξeq : ∀ᶠ y in 𝓝 z, fderiv ℝ ξ y (1, 0) =
      -J (fderiv ℝ ξ y (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u y) (ξ y))) :
    ⟪ξ z, fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) z (1, 0)⟫ + ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 =
      2 * ‖fderiv ℝ ξ z (1, 0)‖ ^ 2 + ⟪ξ z, J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
        (u z) (fderiv ℝ u z (1, 0)) (ξ z))⟫ +
        fderiv ℝ (fun y ↦ ⟪J (ξ y), fderiv ℝ ξ y (1, 0)⟫) z (0, 1) := by
  set η : ℝ × ℝ → V := fun y ↦ fderiv ℝ ξ y (1, 0)
  have hη : ContDiff ℝ 1 η := (hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hdξ : DifferentiableAt ℝ ξ z := (hξ.differentiable (by norm_num)) z
  have hdJξ : HasFDerivAt (fun y ↦ J (ξ y)) (_ : ℝ × ℝ →L[ℝ] V) z :=
    hasFDerivAt_apply hdξ.hasFDerivAt
  rw [fderiv_inner_apply ℝ hdJξ.differentiableAt (hη.differentiable one_ne_zero z),
    hdJξ.fderiv, fderiv_real_apply_real hH hu hξ hξeq]
  have hsym : ⟪J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)), η z⟫ =
      ⟪ξ z, J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (η z))⟫ := by
    have h := (ω.invariant_of_apply_apply_eq_inner hg)
      |>.associatedBilinForm_apply_fderiv_hamiltonianVectorField_comm (x := u z)
        (hH.contDiffAt.of_le (by norm_num)) (ξ z) (η z)
    simpa only [associatedBilinForm_apply, hg] using h
  have hskew := inner_apply_left_eq_neg_of_apply_apply_eq_inner hg (ξ z) (fderiv ℝ η z (0, 1))
  have hηeq : η z = -J (fderiv ℝ ξ z (0, 1)) +
      J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)) := hξeq.self_of_nhds
  have hnorm : ‖η z‖ ^ 2 = ⟪-J (fderiv ℝ ξ z (0, 1)) +
      J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)), η z⟫ := by
    rw [← hηeq, real_inner_self_eq_norm_sq]
  simp only [inner_add_right, inner_add_left, inner_neg_left, inner_neg_right,
    ContinuousLinearMap.coe_comp, Function.comp_apply, LinearMap.coe_toContinuousLinearMap']
    at hnorm ⊢
  linarith

/-- **The second variation of the slice energy.** If `ξ` solves `∂s ξ = -J ∂t ξ + J dX_H(u) ξ` on
the open strip `ℝ × (0, 1)`, then, with `η = ∂s ξ`,
`∫₀¹ (⟪ξ, ∂s η⟫ + ‖η‖²) = 2 ∫₀¹ ‖η‖² + ∫₀¹ ⟪ξ, J (d²X_H(u)(∂s u) ξ)⟫ + [⟪J ξ, η⟫]₀¹`. The
difference of the integrands is the `t`-derivative of `⟪J ξ, η⟫`. -/
private theorem integral_inner_fderiv_slice_eq (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (hu : ContDiff ℝ 1 u) (hξ : ContDiff ℝ 2 ξ)
    (hξeq : ∀ z : ℝ × ℝ, z.2 ∈ Ioo (0 : ℝ) 1 → fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (s : ℝ) :
    ∫ t in (0 : ℝ)..1, (⟪ξ (s, t), fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) (s, t) (1, 0)⟫ +
        ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2) =
      2 * (∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2) +
        (∫ t in (0 : ℝ)..1, ⟪ξ (s, t), J (fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H))
          (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫) +
        (⟪J (ξ (s, 1)), fderiv ℝ ξ (s, 1) (1, 0)⟫ - ⟪J (ξ (s, 0)), fderiv ℝ ξ (s, 0) (1, 0)⟫) := by
  set η : ℝ × ℝ → V := fun y ↦ fderiv ℝ ξ y (1, 0)
  have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le (by norm_num)
  have hη : ContDiff ℝ 1 η := (hξ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  -- The `t`-derivative of the boundary term `⟪J ξ, η⟫` integrates to its increment.
  have hB : ContDiff ℝ 1 fun y ↦ ⟪J (ξ y), η y⟫ :=
    (J.toLinearMap.toContinuousLinearMap.contDiff.comp hξ1).inner ℝ hη
  have hB0 : ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y ↦ ⟪J (ξ y), η y⟫) (s, t) (0, 1) =
      ⟪J (ξ (s, 1)), η (s, 1)⟫ - ⟪J (ξ (s, 0)), η (s, 0)⟫ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_slice_right (hB.differentiable one_ne_zero (s, t)))
      ((continuous_fderiv_apply_slice_right hB s (0, 1)).intervalIntegrable _ _)
  have hA₁ : Continuous fun t ↦ ‖η (s, t)‖ ^ 2 :=
    (hη.continuous.comp (.prodMk_right s)).norm.pow 2
  have hA₂ := continuous_inner_apply_fderiv_fderiv_hamiltonianVectorField hH hu hξ1 s
    (ω := ω) (J := J)
  -- Away from `t = 1`, the integrands agree on the open strip.
  have hcongr : ∫ t in (0 : ℝ)..1, (⟪ξ (s, t), fderiv ℝ η (s, t) (1, 0)⟫ + ‖η (s, t)‖ ^ 2) =
      ∫ t in (0 : ℝ)..1, (2 * ‖η (s, t)‖ ^ 2 + ⟪ξ (s, t), J (fderiv ℝ
        (fderiv ℝ (ω.hamiltonianVectorField H)) (u (s, t)) (fderiv ℝ u (s, t) (1, 0)) (ξ (s, t)))⟫ +
          fderiv ℝ (fun y ↦ ⟪J (ξ y), η y⟫) (s, t) (0, 1)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    exact inner_fderiv_real_real_add_norm_sq_eq hg hH (hu.differentiable one_ne_zero) hξ
      (eventually_nhds_of_mem_Ioo hξeq (z := (s, t)) ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩)
  rw [hcongr, intervalIntegral.integral_add (((hA₁.intervalIntegrable (μ := volume) 0 1).const_mul
      2).add (hA₂.intervalIntegrable 0 1))
      ((continuous_fderiv_apply_slice_right hB s (0, 1)).intervalIntegrable 0 1), hB0,
    intervalIntegral.integral_add ((hA₁.intervalIntegrable 0 1).const_mul 2)
      (hA₂.intervalIntegrable 0 1), intervalIntegral.integral_const_mul]

/-- **Bounded solutions of the linearized equation vanish.** Let `ξ` be a `C²` solution of
`∂s ξ = -J ∂t ξ + J dX_H(u) ξ` on the open strip `ℝ × (0, 1)`, bounded by `B` on the closed
strip. Suppose that its slices satisfy the Wirtinger-type bound `C² ∫₀¹ ‖ξ‖² ≤ ∫₀¹ ‖∂t ξ‖²` and
that the boundary term `⟪J ξ, ∂s ξ⟫` takes the same value at `t = 0` and at `t = 1`. If
`‖dX_H‖ ≤ a < C`, `‖d²X_H‖ ≤ c`, `‖du‖ ≤ M` on the closed strip and `c M < 2 (C - a)²`, then `ξ`
vanishes on the closed strip. -/
private theorem eq_zero_of_fderiv_apply_real_eq_of_mul_integral_le
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {a c M B C : ℝ} (hH : ContDiff ℝ 3 H)
    (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (haC : a < C) (hcM : c * M < 2 * (C - a) ^ 2)
    (hu : ContDiff ℝ 1 u) (hM : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ u (s, t)‖ ≤ M)
    (hξ : ContDiff ℝ 2 ξ)
    (hW : ∀ s, C ^ 2 * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (0, 1)‖ ^ 2)
    (hbd : ∀ s, ⟪J (ξ (s, 1)), fderiv ℝ ξ (s, 1) (1, 0)⟫ =
      ⟪J (ξ (s, 0)), fderiv ℝ ξ (s, 0) (1, 0)⟫)
    (hξeq : ∀ z : ℝ × ℝ, z.2 ∈ Ioo (0 : ℝ) 1 → fderiv ℝ ξ z (1, 0) =
      -J (fderiv ℝ ξ z (0, 1)) + J (fderiv ℝ (ω.hamiltonianVectorField H) (u z) (ξ z)))
    (hB : ∀ s, ∀ t ∈ Icc (0 : ℝ) 1, ‖ξ (s, t)‖ ≤ B) (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ξ (s, t) = 0 := by
  have hξ1 : ContDiff ℝ 1 ξ := hξ.of_le (by norm_num)
  have ha0 : 0 ≤ a := (norm_nonneg (fderiv ℝ (ω.hamiltonianVectorField H) 0)).trans (ha 0)
  -- The slice energy `f` satisfies `f'' ≥ κ f` with `κ = 4 (C - a)² - 2 c M > 0`.
  set f : ℝ → ℝ := fun s ↦ ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 with hf_def
  have hle (s : ℝ) : (4 * (C - a) ^ 2 - 2 * (c * M)) * f s ≤
      ∫ t in (0 : ℝ)..1, 2 * (⟪ξ (s, t), fderiv ℝ (fun y ↦ fderiv ℝ ξ y (1, 0)) (s, t) (1, 0)⟫ +
        ‖fderiv ℝ ξ (s, t) (1, 0)‖ ^ 2) := by
    rw [intervalIntegral.integral_const_mul,
      integral_inner_fderiv_slice_eq hg hH hu hξ hξeq s, hbd s, sub_self, add_zero]
    have h₁ := mul_integral_norm_sq_slice_le hg ha0 (ha0.trans_lt haC) haC.le ha hξ1 (hW s)
      fun t ht ↦ hξeq (s, t) ht
    have h₂ := neg_mul_integral_norm_sq_slice_le hg hH hc hu (hM s) hξ1
    simp only [hf_def]
    linarith
  have hf0 (s : ℝ) : 0 ≤ f s :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ ↦ sq_nonneg _
  have hcont (s : ℝ) : Continuous fun t ↦ ‖ξ (s, t)‖ ^ 2 :=
    (hξ.continuous.comp (.prodMk_right s)).norm.pow 2
  have hfb : BddAbove (range f) := ⟨B ^ 2, by
    rintro _ ⟨s, rfl⟩
    have h := intervalIntegral.integral_mono_on (g := fun _ ↦ B ^ 2) zero_le_one
      ((hcont s).intervalIntegrable (μ := volume) 0 1) intervalIntegrable_const
      fun t ht ↦ pow_le_pow_left₀ (norm_nonneg _) (hB s t ht) 2
    simpa using h⟩
  have hfz := eq_zero_of_hasDerivAt_of_mul_le_of_bddAbove (by nlinarith)
    (hasDerivAt_intervalIntegral_norm_sq hξ1 0 1)
    (hasDerivAt_intervalIntegral_two_mul_inner_fderiv hξ 0 1) hle hf0 hfb
  -- A continuous slice with vanishing `L²` norm vanishes on `[0, 1]`.
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
    (Eventually.of_forall fun t ↦ sq_nonneg ‖ξ (s, t)‖)
    ((hcont s).intervalIntegrable (μ := volume) 0 1)).1 (hfz s)
  have hIcc := Measure.eqOn_Icc_of_ae_eq volume zero_ne_one (g := fun _ ↦ (0 : ℝ))
    (by rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae) (hcont s).continuousOn
    continuousOn_const
  simpa using hIcc ht

/-- **Wirtinger's inequality on the slices of a cylinder.** If `ξ` has period one in `t` and mean
zero on every slice, then `(2π)² ∫₀¹ ‖ξ(s, t)‖² dt ≤ ∫₀¹ ‖∂t ξ(s, t)‖² dt`. -/
private theorem mul_integral_norm_sq_slice_le_of_periodic (hξ : ContDiff ℝ 1 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0)
    (s : ℝ) :
    (2 * π) ^ 2 * ∫ t in (0 : ℝ)..1, ‖ξ (s, t)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ ξ (s, t) (0, 1)‖ ^ 2 := by
  have h := integral_norm_sq_le_of_integral_eq_zero zero_lt_one
    (fun t ↦ hasDerivAt_slice_right (hξ.differentiable one_ne_zero (s, t)))
    (continuous_fderiv_apply_slice_right hξ s (0, 1)) (by simpa using (hper s 0).symm) (hmean s)
  rw [sub_zero, div_pow, one_pow, div_mul_eq_mul_div, one_mul,
    le_div_iff₀ (by positivity)] at h
  linarith

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
  -- The boundary term has period one.
  have hbd (s : ℝ) : ⟪J (ξ (s, 1)), fderiv ℝ ξ (s, 1) (1, 0)⟫ =
      ⟪J (ξ (s, 0)), fderiv ℝ ξ (s, 0) (1, 0)⟫ := by
    have h := fderiv_add_snd_of_periodic_snd (𝕜 := ℝ) hper s 0
    rw [zero_add] at h
    rw [h, show ξ (s, 1) = ξ (s, 0) by simpa using hper s 0]
  have hzero := eq_zero_of_fderiv_apply_real_eq_of_mul_integral_le hg hH ha hc ha2π hcM hu
    (fun s t _ ↦ hM (s, t)) hξ
    (mul_integral_norm_sq_slice_le_of_periodic (hξ.of_le (by norm_num)) hper hmean) hbd
    (fun z _ ↦ hξeq z) fun s t _ ↦ hB (s, t)
  -- By periodicity, `ξ` vanishes everywhere.
  obtain ⟨s, t⟩ := z
  obtain ⟨t', ht', hξt⟩ :=
    (show Function.Periodic (fun t ↦ ξ (s, t)) 1 from hper s).exists_mem_Ioc zero_lt_one t 0
  rw [zero_add] at ht'
  simpa [hξt] using hzero s (Ioc_subset_Icc_self ht')

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
    simp only [ξ, fderiv_add_snd_of_periodic_snd hper]
  have hB (z : ℝ × ℝ) : ‖ξ z‖ ≤ M :=
    ((fderiv ℝ u z).le_opNorm _).trans (by simpa using hM z)
  have hzero := eq_zero_of_fderiv_apply_real_eq hg hH ha hc ha2π hcM hu1 hM hξ hξper
    (integral_fderiv_apply_zero_one_eq_zero hu1 hper)
    (fun z ↦ fderiv_imag_apply_real (hH.of_le (by norm_num)) (hu.of_le (by norm_num))
      (Eventually.of_forall hfl)) hB
  -- So every slice `t ↦ u(s, t)` has vanishing derivative.
  funext ⟨s, t⟩
  have hd (t : ℝ) : HasDerivAt (fun t ↦ u (s, t)) 0 t := by
    simpa [ξ, hzero (s, t)] using hasDerivAt_slice_right (hu1.differentiable one_ne_zero (s, t))
  exact is_const_of_deriv_eq_zero (fun t ↦ (hd t).differentiableAt) (fun t ↦ (hd t).deriv) t 0

/-- **Floer cylinders of a small autonomous Hamiltonian are gradient lines.** Under the hypotheses
of `TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`, the curve
`γ(s) = u(s, 0)` is an upward gradient line of `H`, `γ' = ∇H(γ)`, for the metric `ω(·, J ·)`. That
`u(s, t) = γ(s)` is `TauCeti.SymplecticForm.eq_comp_fst_of_isComplexLinearMap_perturbedFDeriv`. -/
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
  have hd := (isComplexLinearMap_perturbedFDeriv_comp_fst_iff (γ := fun s ↦ u (s, 0))
    (z := (s, 0)) (hγ s)).1 h
  rw [apply_hamiltonianVectorField_eq_gradient hg] at hd
  exact hd ▸ (hγ s).hasDerivAt

end Main

section Linearization

/-! ### The linearized operator -/

variable {a c M B : ℝ} {ξ : ℝ × ℝ → V}

/-- **Bounded kernel elements with mean-zero slices vanish.** Let the inner product of `V` be the
metric `ω(·, J ·)` of a constant compatible almost complex structure `J`, let `H` be a `C³`
autonomous Hamiltonian with `‖dX_H‖ ≤ a < 2π` and `‖d²X_H‖ ≤ c`, and let `u` be a `C¹` map with
`‖du‖ ≤ M`, where `c M < 2 (2π - a)²`. If a bounded `C²` section `ξ` of period one in `t`, whose
slices `t ↦ ξ(s, t)` have mean zero, is in the kernel of the linearized Floer operator
`D_u ξ = ∂s ξ + J (∂t ξ - dX_H(u) ξ)` of `K = H dt`, then `ξ = 0`. -/
theorem eq_zero_of_floerLinearization_eq_zero (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hH : ContDiff ℝ 3 H) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (ha2π : a < 2 * π) (hcM : c * M < 2 * (2 * π - a) ^ 2)
    (hu : ContDiff ℝ 1 u) (hM : ∀ z, ‖fderiv ℝ u z‖ ≤ M) (hξ : ContDiff ℝ 2 ξ)
    (hper : ∀ s t, ξ (s, t + 1) = ξ (s, t)) (hmean : ∀ s, ∫ t in (0 : ℝ)..1, ξ (s, t) = 0)
    (hD : ∀ z, ω.floerLinearization (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ ↦ H) u ξ z = 0)
    (hB : ∀ z, ‖ξ z‖ ≤ B) : ξ = 0 :=
  funext <| eq_zero_of_fderiv_apply_real_eq hg hH ha hc ha2π hcM hu hM hξ hper hmean
    (fun z ↦ (floerLinearization_const_eq_zero_iff ω J H).1 (hD z)) hB

end Linearization

section Strip

variable {L : Submodule ℝ V} {a c M : ℝ}

/-- **The boundary condition of `∂t u`.** Let `u` map the line `ℝ × {t}` into `L`, along which
the gradient of `H` is tangent to `L`. If `u` solves the Floer equation of `K = H dt` at `(s, t)`,
then `J ∂t u(s, t) ∈ L`. -/
private theorem apply_fderiv_apply_mem (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hHL : ∀ x ∈ L, ∇ H x ∈ L) (hu : Differentiable ℝ u) {s t : ℝ} (hut : ∀ s, u (s, t) ∈ L)
    (hfl : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u (s, t) : ℝ × ℝ →ₗ[ℝ] V)) :
    J (fderiv ℝ u (s, t) (0, 1)) ∈ L := by
  have he := fderiv_apply_real_eq hfl
  rw [apply_hamiltonianVectorField_eq_gradient hg] at he
  have hJ : J (fderiv ℝ u (s, t) (0, 1)) = ∇ H (u (s, t)) - fderiv ℝ u (s, t) (1, 0) := by
    rw [he]
    abel
  rw [hJ]
  simpa using L.sub_mem (hHL _ (hut s))
    ((hasDerivAt_slice_left (hu (s, t))).hasFDerivAt.apply_mem_of_eventually_sub_mem
      L.isClosed_of_finiteDimensional (.of_forall fun y ↦ L.sub_mem (hut y) (hut s)) 1)

/-- **The boundary term of a strip vanishes.** If `J ξ(s, t) ∈ L` for every `s`, for an isotropic
subspace `L`, then `⟪J ξ, ∂s ξ⟫ = 0` at `(s, t)`. -/
private theorem inner_apply_fderiv_eq_zero (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL : ω.IsIsotropic L) {ξ : ℝ × ℝ → V} (hξ : Differentiable ℝ ξ) {t : ℝ}
    (hξt : ∀ s, J (ξ (s, t)) ∈ L) (s : ℝ) : ⟪J (ξ (s, t)), fderiv ℝ ξ (s, t) (1, 0)⟫ = 0 := by
  have hη : J (fderiv ℝ ξ (s, t) (1, 0)) ∈ L := by
    simpa using (hasFDerivAt_apply (J := J) (hasDerivAt_slice_left (hξ (s, t))).hasFDerivAt
      ).apply_mem_of_eventually_sub_mem L.isClosed_of_finiteDimensional
        (.of_forall fun y ↦ L.sub_mem (hξt y) (hξt s)) 1
  rw [← hg]
  exact isIsotropic_iff.1 hL _ (hξt s) _ hη

/-- **The Poincaré inequality on the slices of a strip.** Let `u` be `C²` with boundary values
`u(s, 0), u(s, 1)` in an isotropic subspace `L`, and let `ξ = ∂t u` satisfy `J ξ(s, 0) ∈ L` and
`J ξ(s, 1) ∈ L`. Then `π² ∫₀¹ ‖ξ(s, t)‖² dt ≤ ∫₀¹ ‖∂t ξ(s, t)‖² dt`. -/
private theorem mul_integral_norm_sq_slice_le_of_isIsotropic (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (hL : ω.IsIsotropic L) (hu : ContDiff ℝ 2 u) (hu0 : ∀ s, u (s, 0) ∈ L)
    (hu1 : ∀ s, u (s, 1) ∈ L) (s : ℝ) (h0 : J (fderiv ℝ u (s, 0) (0, 1)) ∈ L)
    (h1 : J (fderiv ℝ u (s, 1) (0, 1)) ∈ L) :
    π ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u (s, t) (0, 1)‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ (fun y ↦ fderiv ℝ u y (0, 1)) (s, t) (0, 1)‖ ^ 2 := by
  set ξ : ℝ × ℝ → V := fun y ↦ fderiv ℝ u y (0, 1)
  have hξ : ContDiff ℝ 1 ξ := (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  -- The boundary values of `ξ` are orthogonal to `L`, since `J ξ ∈ L` and `L` is isotropic.
  have hperp {t : ℝ} (ht : J (ξ (s, t)) ∈ L) : ξ (s, t) ∈ Lᗮ :=
    (Submodule.mem_orthogonal _ _).2 fun ℓ hℓ ↦ by
      rw [← hg]
      exact isIsotropic_iff.1 hL ℓ hℓ _ ht
  -- The integral of the slice is `u(s, 1) - u(s, 0) ∈ L`.
  have hint : ∫ t in (0 : ℝ)..1, ξ (s, t) ∈ Lᗮᗮ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_slice_right ((hu.differentiable (by norm_num)) (s, t)))
      ((hξ.continuous.comp (.prodMk_right s)).intervalIntegrable _ _)]
    exact L.le_orthogonal_orthogonal (L.sub_mem (hu1 s) (hu0 s))
  have h := mul_integral_norm_sq_le_integral_norm_sq_of_mem_of_integral_mem_orthogonal
    zero_lt_one
    (fun t _ ↦ (hasDerivAt_slice_right (hξ.differentiable one_ne_zero (s, t))).hasDerivWithinAt)
    (continuous_fderiv_apply_slice_right hξ s (0, 1)).continuousOn (hperp h0) (hperp h1) hint
  simpa using h

/-- **Floer strips of a small autonomous Hamiltonian are time-independent.** Let the inner
product of `V` be the metric `ω(·, J ·)` of a constant compatible almost complex structure `J`,
let `L` be an isotropic subspace, for instance a Lagrangian one, and let `H` be a `C³` autonomous
Hamiltonian whose gradient is tangent to `L` along `L`, with `‖dX_H‖ ≤ a < π` and
`‖d²X_H‖ ≤ c`. Let `u` be a `C³` map which on the strip `ℝ × [0, 1]` solves the Floer equation
`∂s u + J (∂t u - X_H(u)) = 0` of `K = H dt`, with `‖du‖ ≤ M` and boundary values
`u(s, 0), u(s, 1) ∈ L`. If `c M < 2 (π - a)²`, then `u` does not depend on `t` on the strip:
`u(s, t) = u(s, 0)`. -/
theorem eqOn_comp_fst_of_isComplexLinearMap_perturbedFDeriv_of_isIsotropic
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hL : ω.IsIsotropic L) (hH : ContDiff ℝ 3 H)
    (hHL : ∀ x ∈ L, ∇ H x ∈ L) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (haπ : a < π) (hcM : c * M < 2 * (π - a) ^ 2) (hu : ContDiff ℝ 3 u)
    (hu0 : ∀ s, u (s, 0) ∈ L) (hu1 : ∀ s, u (s, 1) ∈ L)
    (hfl : ∀ z : ℝ × ℝ, z.2 ∈ Icc (0 : ℝ) 1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hM : ∀ z : ℝ × ℝ, z.2 ∈ Icc (0 : ℝ) 1 → ‖fderiv ℝ u z‖ ≤ M) :
    EqOn u (fun z ↦ u (z.1, 0)) {z | z.2 ∈ Icc (0 : ℝ) 1} := by
  have hu₁ : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hud : Differentiable ℝ u := hu₁.differentiable one_ne_zero
  -- `ξ = ∂t u` is a bounded solution of the linearized equation on the strip, and `J ξ ∈ L` on
  -- the boundary.
  set ξ : ℝ × ℝ → V := fun y ↦ fderiv ℝ u y (0, 1)
  have hξ : ContDiff ℝ 2 ξ := (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hJξ₀ (s : ℝ) : J (ξ (s, 0)) ∈ L :=
    apply_fderiv_apply_mem hg hHL hud hu0 (hfl (s, 0) ⟨le_rfl, zero_le_one⟩)
  have hJξ₁ (s : ℝ) : J (ξ (s, 1)) ∈ L :=
    apply_fderiv_apply_mem hg hHL hud hu1 (hfl (s, 1) ⟨zero_le_one, le_rfl⟩)
  have hξd : Differentiable ℝ ξ := hξ.differentiable (by norm_num)
  have hzero := eq_zero_of_fderiv_apply_real_eq_of_mul_integral_le hg hH ha hc haπ hcM hu₁
    (fun s t ht ↦ hM (s, t) ht) hξ
    (fun s ↦ mul_integral_norm_sq_slice_le_of_isIsotropic hg hL (hu.of_le (by norm_num)) hu0
      hu1 s (hJξ₀ s) (hJξ₁ s))
    (fun s ↦ by rw [inner_apply_fderiv_eq_zero hg hL hξd hJξ₁,
      inner_apply_fderiv_eq_zero hg hL hξd hJξ₀])
    (fun z hz ↦ fderiv_imag_apply_real (hH.of_le (by norm_num)) (hu.of_le (by norm_num))
      (eventually_nhds_of_mem_Ioo (fun y hy ↦ hfl y (Ioo_subset_Icc_self hy)) hz))
    fun s t ht ↦ ((fderiv ℝ u (s, t)).le_opNorm _).trans (by simpa using hM (s, t) ht)
  -- So every slice `t ↦ u(s, t)` has vanishing derivative on `[0, 1]`.
  rintro ⟨s, t⟩ ht
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (f := fun t ↦ u (s, t)) (f' := fun t ↦ ξ (s, t))
    (fun τ _ ↦ hasDerivAt_slice_right (hud (s, τ)))
    ((hξ.continuous.comp (.prodMk_right s)).intervalIntegrable _ _)
  have h0 : ∫ τ in (0 : ℝ)..t, ξ (s, τ) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : V)) fun τ hτ ↦ ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le ht.1] at hτ
    exact hzero s ⟨hτ.1, hτ.2.trans ht.2⟩
  rw [h0, eq_comm, sub_eq_zero] at h
  exact h

/-- **Floer strips of a small autonomous Hamiltonian are gradient lines.** Under the hypotheses of
`TauCeti.SymplecticForm.eqOn_comp_fst_of_isComplexLinearMap_perturbedFDeriv_of_isIsotropic`, the
boundary curve `γ(s) = u(s, 0)`, which lies in `L`, is an upward gradient line of `H`,
`γ' = ∇H(γ)`, for the metric `ω(·, J ·)`. -/
theorem hasDerivAt_gradient_of_isComplexLinearMap_perturbedFDeriv_of_isIsotropic
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) (hL : ω.IsIsotropic L) (hH : ContDiff ℝ 3 H)
    (hHL : ∀ x ∈ L, ∇ H x ∈ L) (ha : ∀ x, ‖fderiv ℝ (ω.hamiltonianVectorField H) x‖ ≤ a)
    (hc : ∀ x, ‖fderiv ℝ (fderiv ℝ (ω.hamiltonianVectorField H)) x‖ ≤ c)
    (haπ : a < π) (hcM : c * M < 2 * (π - a) ^ 2) (hu : ContDiff ℝ 3 u)
    (hu0 : ∀ s, u (s, 0) ∈ L) (hu1 : ∀ s, u (s, 1) ∈ L)
    (hfl : ∀ z : ℝ × ℝ, z.2 ∈ Icc (0 : ℝ) 1 →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hM : ∀ z : ℝ × ℝ, z.2 ∈ Icc (0 : ℝ) 1 → ‖fderiv ℝ u z‖ ≤ M) (s : ℝ) :
    HasDerivAt (fun s ↦ u (s, 0)) (∇ H (u (s, 0))) s := by
  have hmain := eqOn_comp_fst_of_isComplexLinearMap_perturbedFDeriv_of_isIsotropic hg hL hH hHL
    ha hc haπ hcM hu hu0 hu1 hfl hM
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  -- `u` is constant along `t ↦ u(s, t)` on `[0, 1]`, so `∂t u(s, 0) = 0`.
  have hξ₀ : fderiv ℝ u (s, 0) (0, 1) = 0 := by
    have h₁ : HasDerivWithinAt (fun t ↦ u (s, t)) (fderiv ℝ u (s, 0) (0, 1)) (Icc 0 1) 0 :=
      (hasDerivAt_slice_right (hud (s, 0))).hasDerivWithinAt
    have h₂ : HasDerivWithinAt (fun t ↦ u (s, t)) 0 (Icc 0 1) 0 :=
      (hasDerivWithinAt_const 0 (Icc (0 : ℝ) 1) (u (s, 0))).congr
        (fun t ht ↦ hmain (x := (s, t)) ht) rfl
    exact (uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩).eq_deriv _ h₁ h₂
  have he := fderiv_apply_real_eq (hfl (s, 0) ⟨le_rfl, zero_le_one⟩)
  rw [hξ₀, map_zero, neg_zero, zero_add, apply_hamiltonianVectorField_eq_gradient hg] at he
  exact he ▸ hasDerivAt_slice_left (hud (s, 0))

end Strip

end TauCeti.SymplecticForm
