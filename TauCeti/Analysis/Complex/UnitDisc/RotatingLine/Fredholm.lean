/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Boundary
public import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Isomorphism
public import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Pi
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Holder
import TauCeti.Analysis.Complex.Wirtinger.Holomorphic
import TauCeti.Analysis.Fredholm.Criteria
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.Holder.Normed

/-!
# The Cauchy–Riemann operator with rotating-line boundary values is Fredholm

Let `D` be the open unit disc, `0 < α < 1` and `k` an integer. On the closed subspace `X_k` of
`C^{1,α}(D)` of the functions whose continuous extension to the closed disc takes boundary values
on the rotating lines `e^{ikθ/2} ℝ` (`TauCeti.rotatingLineSubspace`), the Cauchy–Riemann operator

`∂/∂(conj z) : X_k → C^{0,α}(D)` (`TauCeti.rotatingLineConjWirtingerDerivL`)

is the Hölder realization of the Cauchy–Riemann operator on the disc with a boundary loop of
Maslov index `k`. This file proves that for `k ≥ -1` it is a Fredholm operator of index `k + 1`,
which is `n χ(D) + μ` for rank `n = 1`, Euler characteristic `χ(D) = 1` and Maslov index `μ = k`,
as the Riemann–Roch formula for discs predicts.

* **Surjectivity.** For `k ≥ -1` every `α`-Hölder forcing is `∂u/∂(conj z)` for some `u ∈ X_k`
  (`TauCeti.rotatingLineConjWirtingerDerivL_surjective`), by the solution of the inhomogeneous
  problem with Hölder forcing
  (`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_holderOnWith`).
* **The kernel.** The values on the closed disc identify the kernel with the space
  `TauCeti.unitDiscCauchyRiemannKernel k` of holomorphic solutions continuous up to the boundary
  (`TauCeti.rotatingLineConjWirtingerDerivKerEquiv`), which are the conjugate-reciprocal
  polynomials of degree at most `k`, of real dimension `(k + 1).toNat`
  (`TauCeti.finrank_ker_rotatingLineConjWirtingerDerivL`).
* **Fredholm property and index.** A surjective operator between Banach spaces with
  finite-dimensional kernel is Fredholm (`TauCeti.isFredholm_rotatingLineConjWirtingerDerivL`), of
  index the dimension of its kernel (`TauCeti.index_rotatingLineConjWirtingerDerivL`). For
  constant real boundary values, `k = 0`, this is index `1`, the real constants; for the
  normalization `k = 3` of the real-boundary disc problem it is index `4`, the four real
  coefficients of the cubics `a₀ + a₁ z + conj a₁ z² + conj a₀ z³`.

**Evaluation at a boundary point.** For real boundary values, `k = 0`, the kernel consists of
the real constants, and the real part of the value at the boundary point `1` reads them off. So
the operator `u ↦ (∂u/∂(conj z), Re u(1))` is a Banach isomorphism `X_0 ≃L[ℝ] C^{0,α}(D) × ℝ`
(`TauCeti.rotatingLineZeroEvalEquiv`). This is the linearization at a constant disc of the
Cauchy–Riemann equation for discs with boundary on a totally real curve, combined with evaluation
at a boundary marked point; on the boundary the values of `u ∈ X_0` are real, so `Re u(1)` is the
value `u(1)` itself (`TauCeti.ofReal_re_closureExtend_of_mem_rotatingLineSubspace_zero`).

The same holds in every rank: for a finite type `ι`, the operator `u ↦ (∂u/∂(conj z), Re u(1))`
is a Banach isomorphism from the maps `u ∈ C^{1,α}(D, ι → ℂ)` with boundary values in `ℝ^ι`
(`TauCeti.rotatingLinePiSubspace ι 0 α`) onto `C^{0,α}(D, ι → ℂ) × ℝ^ι`
(`TauCeti.rotatingLinePiZeroEvalEquiv`), coordinate by coordinate. This is the linearization at a
constant disc `u ≡ x` of the Cauchy–Riemann equation for discs in `ℂⁿ` with boundary on a
Lagrangian or totally real submanifold `L` with `T_x L = ℝⁿ`, together with evaluation at the
boundary marked point `1`: the kernel of `∂/∂(conj z)` is the constant maps with values in
`T_x L`, and evaluation at `1` identifies it with `T_x L`.

## Main definitions

* `TauCeti.rotatingLineConjWirtingerDerivL k α`: the operator `∂/∂(conj z) : X_k → C^{0,α}(D)`.
* `TauCeti.rotatingLineConjWirtingerDerivKerEquiv`: its kernel is the space of holomorphic
  solutions `TauCeti.unitDiscCauchyRiemannKernel k`, by the values on the closed disc.
* `TauCeti.rotatingLineZeroEvalEquiv`: the isomorphism `u ↦ (∂u/∂(conj z), Re u(1))` from `X_0`
  onto `C^{0,α}(D) × ℝ`.
* `TauCeti.rotatingLinePiZeroEvalEquiv`: the same isomorphism for maps `D → ℂ^ι` with boundary
  values in `ℝ^ι`, onto `C^{0,α}(D, ι → ℂ) × ℝ^ι`.

## Main results

* `TauCeti.rotatingLineConjWirtingerDerivL_surjective`: surjectivity for `k ≥ -1`.
* `TauCeti.finrank_ker_rotatingLineConjWirtingerDerivL`: the kernel has dimension
  `(k + 1).toNat`.
* `TauCeti.isFredholm_rotatingLineConjWirtingerDerivL`: the operator is Fredholm for `k ≥ -1`.
* `TauCeti.index_rotatingLineConjWirtingerDerivL`: its index is `k + 1`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (Theorem C.1.10, the Riemann–Roch theorem for
  discs, and Theorem C.4.1, its proof in rank one with boundary values on `e^{ikθ/2} ℝ`).
-/

public section

noncomputable section

namespace TauCeti

open Complex Metric Module Polynomial Set Filter Topology CkHolderSpaceOn
open scoped ComplexConjugate NNReal

variable {k : ℤ} {α : ℝ≥0}

/-! ### The operator -/

variable (k α) in
/-- The Cauchy–Riemann operator `u ↦ ∂u/∂(conj z)` on the closed subspace `X_k` of `C^{1,α}(D)`
of the functions with boundary values on the rotating lines `e^{ikθ/2} ℝ`, with values in
`C^{0,α}(D)`, for the open unit disc `D`. -/
def rotatingLineConjWirtingerDerivL :
    rotatingLineSubspace k α →L[ℝ] HolderSpace α (unitBallOpens ℂ) ℂ :=
  conjWirtingerDerivL α (unitBallOpens ℂ) ℂ ∘L (rotatingLineSubspace k α).subtypeL

/-- The operator `TauCeti.rotatingLineConjWirtingerDerivL` is the Cauchy–Riemann operator of
`C^{1,α}(D)` on the elements of `X_k`. -/
@[simp]
theorem rotatingLineConjWirtingerDerivL_apply (u : rotatingLineSubspace k α) :
    rotatingLineConjWirtingerDerivL k α u = conjWirtingerDerivL α (unitBallOpens ℂ) ℂ u :=
  (rfl)

/-- An element of `X_k` lies in the kernel of the Cauchy–Riemann operator on `X_k` exactly when
its Cauchy–Riemann derivative vanishes. -/
theorem mem_ker_rotatingLineConjWirtingerDerivL_iff {u : rotatingLineSubspace k α} :
    u ∈ (rotatingLineConjWirtingerDerivL k α).ker ↔
      conjWirtingerDerivL α (unitBallOpens ℂ) ℂ u = 0 :=
  LinearMap.mem_ker

/-- **Surjectivity for Maslov index at least `-1`.** For `k ≥ -1` and `0 < α < 1`, every
`α`-Hölder forcing on the open unit disc is `∂u/∂(conj z)` for some `u ∈ C^{1,α}(D)` with boundary
values on the rotating lines `e^{ikθ/2} ℝ`. -/
theorem rotatingLineConjWirtingerDerivL_surjective (hk : -1 ≤ k) (hα0 : 0 < α) (hα1 : α < 1) :
    Function.Surjective (rotatingLineConjWirtingerDerivL k α) := by
  intro f
  -- The forcing, extended to the closed disc as an `α`-Hölder function.
  obtain ⟨G, hGg, hG⟩ := f.exists_holderOnWith_closure hα0
  rw [closure_unitBallOpens] at hG
  obtain ⟨u, ⟨K, huH⟩, hud, ⟨u', K', hu'H, hu'⟩, hubar, hub⟩ :=
    exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_of_holderOnWith hk hα0 hα1 hG
  obtain ⟨U, hUk, hUe⟩ := exists_mem_rotatingLineSubspace_eventuallyEq hα0 huH hud hu'H hu' hub
  refine ⟨⟨U, hUk⟩, HolderSpace.ext fun z ↦ ?_⟩
  have hz := mem_unitBallOpens_iff_mem_ball.1 z.property
  rw [rotatingLineConjWirtingerDerivL_apply, conjWirtingerDerivL_apply U z (hUe z hz),
    hubar z hz, hGg]

/-! ### The kernel -/

variable (k α) in
/-- The values on the closed unit disc of the elements of `X_k`, as a real-linear map. -/
private def closedDiscValuesₗ : rotatingLineSubspace k α →ₗ[ℝ] (closedBall (0 : ℂ) 1 → ℂ) :=
  LinearMap.pi fun z ↦ (closureEvalL (k := 0) (convex_unitBallOpens ℂ)
    (by rw [closure_unitBallOpens]; exact z.property)).toLinearMap ∘ₗ
      (rotatingLineSubspace k α).subtype

private theorem closedDiscValuesₗ_apply (u : rotatingLineSubspace k α)
    (z : closedBall (0 : ℂ) 1) :
    closedDiscValuesₗ k α u z = (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend z := by
  simp [closedDiscValuesₗ, closureEvalL_apply]

/-- A conjugate-reciprocal polynomial of degree at most `k` gives an element of the kernel of the
Cauchy–Riemann operator on `X_k` whose continuous extension to the closed disc is the
polynomial. -/
private theorem exists_mem_ker_closureExtend_eq (hα0 : 0 < α) (hα1 : α ≤ 1) {p : Polynomial ℂ}
    (hp : p ∈ conjReciprocalPolynomials k) :
    ∃ u ∈ (rotatingLineConjWirtingerDerivL k α).ker,
      ∀ z ∈ closedBall (0 : ℂ) 1,
        (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend z = p.eval z := by
  have hpc : ContDiff ℂ 2 fun z : ℂ ↦ p.eval z := (Polynomial.differentiable p).contDiff
  have hpr : ContDiff ℝ 2 fun z : ℂ ↦ p.eval z := hpc.restrict_scalars ℝ
  obtain ⟨K, hpH⟩ := (hpr.of_le (by norm_num)).contDiffOn.exists_holderOnWith
    (convex_closedBall (0 : ℂ) 1) (isCompact_closedBall 0 1) hα1
  obtain ⟨K', hp'H⟩ := (hpr.fderiv_right (m := 1) le_rfl).contDiffOn.exists_holderOnWith
    (convex_closedBall (0 : ℂ) 1) (isCompact_closedBall 0 1) hα1
  obtain ⟨U, hUk, hUe⟩ := exists_mem_rotatingLineSubspace_eventuallyEq hα0 hpH
    (hpr.differentiable (by norm_num)).differentiableOn hp'H (fun _ _ ↦ rfl)
    fun w hw ↦ eval_eq_zpow_mul_conj_eval hp (by simpa using hw)
  refine ⟨⟨U, hUk⟩, mem_ker_rotatingLineConjWirtingerDerivL_iff.2 (HolderSpace.ext fun z ↦ ?_),
    fun z hz ↦ ?_⟩
  · have hz := mem_unitBallOpens_iff_mem_ball.1 z.property
    rw [conjWirtingerDerivL_apply U z (hUe z hz),
      ((Polynomial.differentiable p).differentiableAt).conjWirtingerDeriv_eq_zero]
    simp
  · refine U.closureExtend_eq_of_continuousWithinAt (fun x ↦ ?_)
      (closure_unitBallOpens ℂ ▸ hz) (Polynomial.continuous p).continuousWithinAt
    have hx := mem_unitBallOpens_iff_mem_ball.1 x.property
    rw [← U.extend_apply_of_mem x.property, (hUe _ hx).eq_of_nhds]

variable (k α) in
/-- **The kernel is the space of holomorphic solutions.** For `0 < α ≤ 1`, the values on the
closed unit disc identify the kernel of the Cauchy–Riemann operator on `X_k` with the space
`TauCeti.unitDiscCauchyRiemannKernel k` of functions holomorphic on the open disc, continuous on
its closure, with boundary values on the rotating lines `e^{ikθ/2} ℝ`. -/
def rotatingLineConjWirtingerDerivKerEquiv (hα0 : 0 < α) (hα1 : α ≤ 1) :
    (rotatingLineConjWirtingerDerivL k α).ker ≃ₗ[ℝ] unitDiscCauchyRiemannKernel k :=
  LinearEquiv.ofBijective
    ((closedDiscValuesₗ k α ∘ₗ ((rotatingLineConjWirtingerDerivL k α).ker).subtype
      ).codRestrict _ fun u ↦
        mem_unitDiscCauchyRiemannKernel_iff.2 ⟨_, coe_unitBallOpens ℂ ▸
          diffContOnCl_closureExtend_of_conjWirtingerDerivL_eq_zero (convex_unitBallOpens ℂ)
            (mem_ker_rotatingLineConjWirtingerDerivL_iff.1 u.property),
          mem_rotatingLineSubspace_iff.1 u.val.property,
          funext fun z ↦ (closedDiscValuesₗ_apply _ z).symm⟩)
    ⟨fun u v huv ↦ by
      -- Elements of `C^{1,α}(D)` are determined by their values on the open disc.
      refine Subtype.ext (Subtype.ext (CkHolderSpaceOn.ext fun x ↦ ?_))
      have h := congr_fun (congr_arg Subtype.val huv)
        ⟨x, ball_subset_closedBall (mem_unitBallOpens_iff_mem_ball.1 x.property)⟩
      simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        closedDiscValuesₗ_apply] at h
      rwa [closureExtend_apply, closureExtend_apply] at h,
    fun g ↦ by
      obtain ⟨p, hp, hpg⟩ := mem_unitDiscCauchyRiemannKernel_iff_exists_eval.1 g.property
      obtain ⟨u, hu, hue⟩ := exists_mem_ker_closureExtend_eq hα0 hα1 hp
      refine ⟨⟨u, hu⟩, Subtype.ext (funext fun z ↦ ?_)⟩
      simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        closedDiscValuesₗ_apply]
      rw [hue z z.property, ← hpg]⟩

/-- The isomorphism `TauCeti.rotatingLineConjWirtingerDerivKerEquiv` sends an element of the
kernel to the values of its continuous extension on the closed disc. -/
@[simp]
theorem rotatingLineConjWirtingerDerivKerEquiv_apply (hα0 : 0 < α) (hα1 : α ≤ 1)
    (u : (rotatingLineConjWirtingerDerivL k α).ker) (z : closedBall (0 : ℂ) 1) :
    (rotatingLineConjWirtingerDerivKerEquiv k α hα0 hα1 u : closedBall (0 : ℂ) 1 → ℂ) z =
      ((u : rotatingLineSubspace k α) : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend z :=
  closedDiscValuesₗ_apply _ z

/-- The kernel of the Cauchy–Riemann operator on `X_k` is finite-dimensional. -/
theorem finiteDimensional_ker_rotatingLineConjWirtingerDerivL (hα0 : 0 < α) (hα1 : α ≤ 1) :
    FiniteDimensional ℝ ((rotatingLineConjWirtingerDerivL k α).ker) :=
  (rotatingLineConjWirtingerDerivKerEquiv k α hα0 hα1).symm.finiteDimensional

/-- **The dimension of the kernel.** For `0 < α ≤ 1`, the kernel of the Cauchy–Riemann operator on
`X_k` has real dimension `k + 1` when `k ≥ -1`, and `0` when `k < 0`. -/
theorem finrank_ker_rotatingLineConjWirtingerDerivL (hα0 : 0 < α) (hα1 : α ≤ 1) :
    finrank ℝ ((rotatingLineConjWirtingerDerivL k α).ker) = (k + 1).toNat :=
  (rotatingLineConjWirtingerDerivKerEquiv k α hα0 hα1).finrank_eq.trans
    (finrank_unitDiscCauchyRiemannKernel k)

/-! ### Fredholm property and index -/

/-- **The Cauchy–Riemann operator with rotating-line boundary values is Fredholm.** For `k ≥ -1`
and `0 < α < 1`, the operator `∂/∂(conj z) : X_k → C^{0,α}(D)` is a Fredholm operator. -/
theorem isFredholm_rotatingLineConjWirtingerDerivL (hk : -1 ≤ k) (hα0 : 0 < α) (hα1 : α < 1) :
    (rotatingLineConjWirtingerDerivL k α).IsFredholm :=
  have := finiteDimensional_ker_rotatingLineConjWirtingerDerivL (k := k) hα0 hα1.le
  .of_surjective (rotatingLineConjWirtingerDerivL_surjective hk hα0 hα1)

/-- **The Riemann–Roch formula on the disc in rank one.** For `k ≥ -1` and `0 < α < 1`, the
Fredholm index of `∂/∂(conj z) : X_k → C^{0,α}(D)` is `k + 1 = χ(D) + μ`, for the Maslov index
`μ = k` of the boundary loop of lines `e^{ikθ/2} ℝ`. -/
theorem index_rotatingLineConjWirtingerDerivL (hk : -1 ≤ k) (hα0 : 0 < α) (hα1 : α < 1) :
    (rotatingLineConjWirtingerDerivL k α).index = k + 1 := by
  rw [ContinuousLinearMap.index_of_surjective _
      (rotatingLineConjWirtingerDerivL_surjective hk hα0 hα1),
    finrank_ker_rotatingLineConjWirtingerDerivL hα0 hα1.le]
  exact Int.toNat_of_nonneg (by omega)

/-! ### Real boundary values and evaluation at a boundary point -/

/-- For real boundary values, `k = 0`, the continuous extension of an element of `X_0` is real at
every point of the unit circle. -/
theorem ofReal_re_closureExtend_of_mem_rotatingLineSubspace_zero
    {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ} (hu : u ∈ rotatingLineSubspace 0 α) {w : ℂ}
    (hw : w ∈ sphere (0 : ℂ) 1) : ((u.closureExtend w).re : ℂ) = u.closureExtend w := by
  have h := mem_rotatingLineSubspace_iff.1 hu w hw
  rw [zpow_zero, one_mul] at h
  exact conj_eq_iff_re.1 h.symm

variable (α) in
/-- The operator `u ↦ (∂u/∂(conj z), Re u(1))` on `X_0`, before it is shown to be an
isomorphism. -/
private def rotatingLineZeroEvalL :
    rotatingLineSubspace 0 α →L[ℝ] HolderSpace α (unitBallOpens ℂ) ℂ × ℝ :=
  (rotatingLineConjWirtingerDerivL 0 α).prod
    (reCLM ∘L closureEvalL (k := 0) (convex_unitBallOpens ℂ)
      (mem_closure_unitBallOpens.2 norm_one.le) ∘L
      (rotatingLineSubspace 0 α).subtypeL)

private theorem rotatingLineZeroEvalL_apply (u : rotatingLineSubspace 0 α) :
    rotatingLineZeroEvalL α u = (rotatingLineConjWirtingerDerivL 0 α u,
      ((u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1).re) := by
  simp [rotatingLineZeroEvalL, closureEvalL_apply]

/-- An element of the kernel of the Cauchy–Riemann operator on `X_0` is a real constant on the
closed disc, the real part of its value at `1`. -/
private theorem closureExtend_eq_re_closureExtend_one (hα0 : 0 < α) (hα1 : α ≤ 1)
    {u : rotatingLineSubspace 0 α} (hu : u ∈ (rotatingLineConjWirtingerDerivL 0 α).ker)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend z =
      (((u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1).re : ℂ) := by
  obtain ⟨r, hr⟩ := mem_unitDiscCauchyRiemannKernel_zero_iff.1
    (rotatingLineConjWirtingerDerivKerEquiv 0 α hα0 hα1 ⟨u, hu⟩).property
  have hv (w : closedBall (0 : ℂ) 1) :
      (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend w = r := by
    rw [← rotatingLineConjWirtingerDerivKerEquiv_apply hα0 hα1 ⟨u, hu⟩ w, hr]
  rw [hv ⟨z, hz⟩, hv ⟨1, by simp⟩, ofReal_re]

/-- The real constants lie in the kernel of the Cauchy–Riemann operator on `X_0`, with the
prescribed value at `1`. -/
private theorem exists_mem_ker_closureExtend_one_eq (hα0 : 0 < α) (hα1 : α ≤ 1) (r : ℝ) :
    ∃ u ∈ (rotatingLineConjWirtingerDerivL 0 α).ker,
      (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1 = r := by
  obtain ⟨u, hu, hue⟩ := exists_mem_ker_closureExtend_eq (k := 0) hα0 hα1
    (p := C (r : ℂ)) (mem_conjReciprocalPolynomials_iff.2 ⟨fun n hn ↦ coeff_C_of_ne_zero (by omega),
      fun i j hij ↦ by
        obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
        simp⟩)
  exact ⟨u, hu, by rw [hue 1 (by simp), eval_C]⟩

/-- **Real boundary values with a boundary marked point.** For `0 < α < 1`, the operator
`u ↦ (∂u/∂(conj z), Re u(1))` is a Banach isomorphism from the elements of `C^{1,α}(D)` with real
boundary values onto `C^{0,α}(D) × ℝ`. The kernel of `∂/∂(conj z)` on these functions is the
real constants, and the value at the boundary point `1` reads them off. -/
def rotatingLineZeroEvalEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    rotatingLineSubspace 0 α ≃L[ℝ] HolderSpace α (unitBallOpens ℂ) ℂ × ℝ :=
  ContinuousLinearEquiv.ofBijective (rotatingLineZeroEvalL α)
    (LinearMap.ker_eq_bot.2 fun u v huv ↦ by
      rw [ContinuousLinearMap.coe_coe, rotatingLineZeroEvalL_apply, rotatingLineZeroEvalL_apply,
        Prod.mk.injEq] at huv
      -- `u - v` lies in the kernel of `∂/∂(conj z)`, so it is the real constant `Re (u - v)(1)`.
      have hk : u - v ∈ (rotatingLineConjWirtingerDerivL 0 α).ker := by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, huv.1, sub_self]
      have h1 : ((u - v : rotatingLineSubspace 0 α) :
          CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1 =
            (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1 -
              (v : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1 := by
        simpa only [closureEvalL_apply, Submodule.coe_sub] using
          map_sub (closureEvalL (k := 0) (convex_unitBallOpens ℂ)
            (mem_closure_unitBallOpens.2 norm_one.le))
            (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ) v
      rw [← sub_eq_zero]
      refine Subtype.ext (CkHolderSpaceOn.ext fun x ↦ ?_)
      have hx := closureExtend_eq_re_closureExtend_one hα0 hα1.le hk
        (ball_subset_closedBall (mem_unitBallOpens_iff_mem_ball.1 x.property))
      rw [closureExtend_apply, h1, sub_re, huv.2, sub_self, ofReal_zero] at hx
      simpa using hx)
    (LinearMap.range_eq_top.2 fun y ↦ by
      obtain ⟨f, c⟩ := y
      obtain ⟨u, rfl⟩ := rotatingLineConjWirtingerDerivL_surjective (k := 0) (by norm_num) hα0 hα1 f
      -- Correct the value at `1` by a real constant, which lies in the kernel.
      obtain ⟨v, hv, hv1⟩ := exists_mem_ker_closureExtend_one_eq hα0 hα1.le
        (c - ((u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1).re)
      have h1 : ((u + v : rotatingLineSubspace 0 α) :
          CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1 =
            (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1 +
              (v : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1 :=
        closureExtend_add (convex_unitBallOpens ℂ) _ _ (mem_closure_unitBallOpens.2 norm_one.le)
      have hv0 : rotatingLineConjWirtingerDerivL 0 α v = 0 := hv
      refine ⟨u + v, ?_⟩
      rw [ContinuousLinearMap.coe_coe, rotatingLineZeroEvalL_apply, map_add, hv0, add_zero, h1,
        add_re, hv1, ofReal_re, add_sub_cancel])

/-- The isomorphism `TauCeti.rotatingLineZeroEvalEquiv` is `u ↦ (∂u/∂(conj z), Re u(1))`. -/
@[simp]
theorem rotatingLineZeroEvalEquiv_apply (hα0 : 0 < α) (hα1 : α < 1)
    (u : rotatingLineSubspace 0 α) :
    rotatingLineZeroEvalEquiv hα0 hα1 u = (rotatingLineConjWirtingerDerivL 0 α u,
      ((u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ).closureExtend 1).re) :=
  rotatingLineZeroEvalL_apply u

/-! ### Real boundary values in `ℂ^ι` -/

section Pi

variable {ι : Type*} [Fintype ι]

/-- The `i`-th coordinate projection `ℂ^ι → ℂ`, as a real-linear map. -/
private abbrev piProjₗ (i : ι) : (ι → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).restrictScalars ℝ

variable (ι α) in
/-- The operator `u ↦ (∂u/∂(conj z), (Re u(1)ᵢ)ᵢ)` on the maps `D → ℂ^ι` with boundary values in
`ℝ^ι`, before it is shown to be an isomorphism. -/
private def rotatingLinePiZeroEvalL :
    rotatingLinePiSubspace ι 0 α →L[ℝ] HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℝ) :=
  (conjWirtingerDerivL α (unitBallOpens ℂ) (ι → ℂ) ∘L
      (rotatingLinePiSubspace ι 0 α).subtypeL).prod
    (ContinuousLinearMap.pi fun i ↦ reCLM ∘L piProjₗ i ∘L
      closureEvalL (k := 0) (convex_unitBallOpens ℂ)
        (mem_closure_unitBallOpens.2 norm_one.le) ∘L
        (rotatingLinePiSubspace ι 0 α).subtypeL)

private theorem rotatingLinePiZeroEvalL_apply (u : rotatingLinePiSubspace ι 0 α) :
    rotatingLinePiZeroEvalL α ι u = (conjWirtingerDerivL α (unitBallOpens ℂ) (ι → ℂ) u,
      fun i ↦ ((u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)).closureExtend 1 i).re) := by
  simp [rotatingLinePiZeroEvalL, closureEvalL_apply]

/-- The `i`-th coordinate of a map `D → ℂ^ι` with boundary values in `ℝ^ι`, a function with real
boundary values. -/
private def rotatingLinePiZeroCoord (i : ι) (u : rotatingLinePiSubspace ι 0 α) :
    rotatingLineSubspace 0 α :=
  ⟨compLeftL (piProjₗ i) u, mem_rotatingLinePiSubspace_iff_forall_compLeftL_mem.1 u.property i⟩

/-- The operator `u ↦ (∂u/∂(conj z), Re u(1))` acts coordinatewise. -/
private theorem rotatingLineZeroEvalEquiv_rotatingLinePiZeroCoord (hα0 : 0 < α) (hα1 : α < 1)
    (i : ι) (u : rotatingLinePiSubspace ι 0 α) :
    rotatingLineZeroEvalEquiv hα0 hα1 (rotatingLinePiZeroCoord i u) =
      (HolderSpace.compLeftL (piProjₗ i) (rotatingLinePiZeroEvalL α ι u).1,
        (rotatingLinePiZeroEvalL α ι u).2 i) := by
  rw [rotatingLineZeroEvalEquiv_apply, rotatingLinePiZeroEvalL_apply,
    rotatingLineConjWirtingerDerivL_apply, rotatingLinePiZeroCoord]
  simp only [conjWirtingerDerivL_compLeftL (ContinuousLinearMap.proj (R := ℂ)
    (φ := fun _ : ι ↦ ℂ) i), closureExtend_compLeftL (convex_unitBallOpens ℂ) _ _
      (mem_closure_unitBallOpens.2 norm_one.le), piProjₗ, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.proj_apply]

variable (ι) in
/-- **Real boundary values in `ℂ^ι` with a boundary marked point.** For `0 < α < 1` and a finite
type `ι`, the operator `u ↦ (∂u/∂(conj z), Re u(1))` is a Banach isomorphism from the maps
`u ∈ C^{1,α}(D, ι → ℂ)` with boundary values in `ℝ^ι` onto `C^{0,α}(D, ι → ℂ) × ℝ^ι`. This is the
linearization of the Cauchy–Riemann equation at a constant disc with boundary on a totally real
submanifold `L` of `ℂ^ι` with `T_x L = ℝ^ι`, combined with evaluation at the boundary marked
point `1`: its kernel is the constant maps with values in `T_x L`, and evaluation identifies them
with `T_x L`. -/
def rotatingLinePiZeroEvalEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    rotatingLinePiSubspace ι 0 α ≃L[ℝ] HolderSpace α (unitBallOpens ℂ) (ι → ℂ) × (ι → ℝ) :=
  ContinuousLinearEquiv.ofBijective (rotatingLinePiZeroEvalL α ι)
    (LinearMap.ker_eq_bot.2 fun u v huv ↦ by
      rw [ContinuousLinearMap.coe_coe] at huv
      -- Each coordinate is determined by the rank-one isomorphism.
      have h (i : ι) : rotatingLinePiZeroCoord i u = rotatingLinePiZeroCoord i v :=
        (rotatingLineZeroEvalEquiv hα0 hα1).injective (by
          rw [rotatingLineZeroEvalEquiv_rotatingLinePiZeroCoord,
            rotatingLineZeroEvalEquiv_rotatingLinePiZeroCoord, huv])
      refine Subtype.ext (CkHolderSpaceOn.ext fun z ↦ funext fun i ↦ ?_)
      simpa [rotatingLinePiZeroCoord] using
        congr_arg (fun w : rotatingLineSubspace 0 α ↦
          (w : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ) z) (h i))
    (LinearMap.range_eq_top.2 fun y ↦ by
      obtain ⟨f, c⟩ := y
      -- Solve the rank-one problem in each coordinate and assemble the coordinates.
      set v : ι → rotatingLineSubspace 0 α := fun i ↦
        (rotatingLineZeroEvalEquiv hα0 hα1).symm (HolderSpace.compLeftL (piProjₗ i) f, c i)
      obtain ⟨u, hmem, hu⟩ :=
        exists_mem_rotatingLinePiSubspace_compLeftL_eq (fun i ↦ (v i).val) fun i ↦ (v i).property
      refine ⟨⟨u, hmem⟩, ?_⟩
      rw [ContinuousLinearMap.coe_coe]
      have hc (i : ι) := rotatingLineZeroEvalEquiv_rotatingLinePiZeroCoord hα0 hα1 i ⟨u, hmem⟩
      have hv (i : ι) : rotatingLinePiZeroCoord i ⟨u, hmem⟩ = v i := Subtype.ext (hu i)
      simp only [hv, v, ContinuousLinearEquiv.apply_symm_apply, Prod.mk.injEq] at hc
      refine Prod.ext (HolderSpace.ext fun z ↦ funext fun i ↦ ?_) (funext fun i ↦ (hc i).2.symm)
      simpa [HolderSpace.compLeftL_apply] using congr_arg (· z) (hc i).1.symm)

/-- The isomorphism `TauCeti.rotatingLinePiZeroEvalEquiv` is `u ↦ (∂u/∂(conj z), Re u(1))`. -/
@[simp]
theorem rotatingLinePiZeroEvalEquiv_apply (hα0 : 0 < α) (hα1 : α < 1)
    (u : rotatingLinePiSubspace ι 0 α) :
    rotatingLinePiZeroEvalEquiv ι hα0 hα1 u = (conjWirtingerDerivL α (unitBallOpens ℂ) (ι → ℂ) u,
      fun i ↦ ((u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) (ι → ℂ)).closureExtend 1 i).re) :=
  rotatingLinePiZeroEvalL_apply u

end Pi

end TauCeti
