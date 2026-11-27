/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField
public import TauCeti.Geometry.Manifold.DifferentialForm.Flow
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

/-!
# Forms invariant under a Lie group action

Let a Lie group `G` act smoothly on the left on a finite-dimensional Hausdorff manifold `M` without
boundary. The fundamental vector field `ξ_M` of an element `ξ` of the Lie algebra of `G` is
complete, and its flow is the action of the one-parameter subgroup `t ↦ exp(t ξ)`
(`TauCeti.globalFlow_fundamentalVectorField`). Consequently, a differential form `α` on `M` which
is invariant under every element of `G`, `g^* α = α`, is annihilated by the Lie derivative along
every fundamental vector field:

`L_{ξ_M} α = 0` (`TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`).

This is the infinitesimal form of invariance. For instance, it turns an action preserving a
primitive `λ` of a symplectic form `ω = -dλ` into the moment map identity
`d (λ(ξ_M)) = ι_{ξ_M} ω`, through Cartan's formula `L_{ξ_M} λ = ι_{ξ_M} dλ + d (λ(ξ_M))`.

## Main results

* `TauCeti.isCompleteVectorField_fundamentalVectorField`: fundamental vector fields are complete.
* `TauCeti.globalFlow_fundamentalVectorField`: the flow of `ξ_M` is `(t, x) ↦ exp(t ξ) • x`.
* `TauCeti.mlieDerivForm_fundamentalVectorField_eq_zero`: invariant forms have vanishing Lie
  derivative along fundamental vector fields.
* `TauCeti.mextDerivₗ_apply_fundamentalVectorField_eq_zero`: the exterior derivative of an
  invariant one-form pairing fundamental vector fields with constants vanishes on them.
* `TauCeti.SmoothForm.apply_smul_eq_apply_mfderiv_of_mpullback_inv_smul_eq`: pointwise form of the
  invariance of a one-form under a group element.
* `TauCeti.SmoothForm.eval₂_mfderiv_smul_of_mpullback_smul_eq`: pointwise form of the invariance
  of a two-form under the action.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 20 (infinitesimal
  generators) and Proposition 12.36 (Lie derivatives of forms along flows).
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace TauCeti

section Pointwise

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Pointwise invariance of a one-form.** If a one-form `α` is invariant under `g⁻¹`, its value
at `g • x` on a tangent vector `w` is its value at `x` on the image of `w` under the differential
of `y ↦ g⁻¹ • y`: `α_{g x}(w) = α_x(d(g⁻¹)_{g x} w)`. -/
theorem SmoothForm.apply_smul_eq_apply_mfderiv_of_mpullback_inv_smul_eq {g : G}
    {α : SmoothForm I M F 1}
    (hα : SmoothForm.mpullback (fun y : M ↦ g⁻¹ • y) (contMDiff_const_smul g⁻¹) α = α) (x : M)
    (w : TangentSpace I (g • x)) :
    α.val (g • x) ![w] = α.val x ![mfderiv I I (fun y : M ↦ g⁻¹ • y) (g • x) w] := by
  -- The differential lands in the tangent space at `g⁻¹ • g • x`, which is only definitionally
  -- that at `x`, so the base points are identified on the form itself rather than by `rw`.
  rw [← congrArg (fun φ : SmoothForm I M F 1 ↦ φ.val (g • x) ![w]) hα,
    SmoothForm.mpullback_apply_one]
  exact congrArg (fun A : E [⋀^Fin 1]→L[ℝ] F ↦ A _)
    (show α.val (g⁻¹ • g • x) = α.val x by rw [inv_smul_smul])

end Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  [T2Space G] [BoundarylessManifold I G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [T2Space M] [IsManifold I' ∞ M]
  [MulAction G M] [ContMDiffSMul I I' ∞ G M]

omit [CompleteSpace E] [LieGroup I (minSmoothness ℝ 3) G] [T2Space G] [BoundarylessManifold I G]
  [FiniteDimensional ℝ E'] [I'.Boundaryless] [T2Space M] in
/-- **Pointwise invariance of a two-form.** If `(g • ·)^* σ = σ` for every `g`, then `σ` is
preserved by the differentials of the action:
`σ_{a • x}(d(a • ·) u, d(a • ·) v) = σ_x(u, v)`. -/
theorem SmoothForm.eval₂_mfderiv_smul_of_mpullback_smul_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {σ : SmoothForm I' M F 2}
    (hG : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (a : G) (x : M) (u v : TangentSpace I' x) :
    σ.eval₂ (a • x) (mfderiv I' I' (a • ·) x u) (mfderiv I' I' (a • ·) x v) = σ.eval₂ x u v := by
  rw [← SmoothForm.eval₂_mpullback _ (ContMDiffSMul.contMDiff_const_smul (I := I) a), hG a]

omit [CompleteSpace E] [T2Space G] [BoundarylessManifold I G] [FiniteDimensional ℝ E']
  [I'.Boundaryless] [T2Space M] in
/-- The fundamental vector field of a smooth action is a `C²` section of the tangent bundle. -/
private theorem contMDiff_two_fundamentalVectorField (ξ : GroupLieAlgebra I G) :
    ContMDiff I' I'.tangent 2
      (fun x ↦ (⟨x, fundamentalVectorField I' ξ x⟩ : TangentBundle I' M)) :=
  contMDiff_fundamentalVectorField (m := 2) (n := ∞) (by simp) ξ

omit [FiniteDimensional ℝ E'] in
/-- **Fundamental vector fields are complete**: the integral curve of `ξ_M` through `x` is
`t ↦ exp(t ξ) • x`, defined for all times. -/
theorem isCompleteVectorField_fundamentalVectorField (ξ : GroupLieAlgebra I G) :
    IsCompleteVectorField (fundamentalVectorField I' (M := M) ξ) :=
  (isCompleteVectorField_iff_exists_isMIntegralCurve
    ((contMDiff_two_fundamentalVectorField ξ).of_le one_le_two)).2 fun x ↦
      ⟨_, by simp, isMIntegralCurve_mulInvariantExp_smul_smul ξ x⟩

omit [FiniteDimensional ℝ E'] in
/-- **The flow of a fundamental vector field** is the action of the one-parameter subgroup
generated by `ξ`: `ψ_t(x) = exp(t ξ) • x`. -/
theorem globalFlow_fundamentalVectorField [FiniteDimensional ℝ E'] (ξ : GroupLieAlgebra I G)
    (hv : ContMDiff I' I'.tangent 1
      (fun x ↦ (⟨x, fundamentalVectorField I' ξ x⟩ : TangentBundle I' M)))
    (hc : IsCompleteVectorField (fundamentalVectorField I' (M := M) ξ)) (t : ℝ) (x : M) :
    globalFlow (fundamentalVectorField I' ξ) hv hc t x = mulInvariantExp (t • ξ) • x := by
  simpa using globalFlow_eq_of_isMIntegralCurve hv hc
    (isMIntegralCurve_mulInvariantExp_smul_smul ξ x) t

/-- **Invariant forms are infinitesimally invariant.** If a smooth form `α` is invariant under the
action of every element of `G`, then its Lie derivative along every fundamental vector field
vanishes: `L_{ξ_M} α = 0`. -/
theorem mlieDerivForm_fundamentalVectorField_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} {α : SmoothForm I' M F k}
    (hα : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) α = α)
    (ξ : GroupLieAlgebra I G) :
    mlieDerivForm (fundamentalVectorField I' ξ) α.val = 0 := by
  funext x
  have hZ := contMDiff_two_fundamentalVectorField (I' := I') (M := M) ξ
  have hc := isCompleteVectorField_fundamentalVectorField (I' := I') (M := M) ξ
  -- Along the flow `ψ_t = exp(t ξ) • ·` the pulled-back form is constant, equal to `α`.
  have hconst : (fun s ↦ mpullback I' I' (globalFlow _ (hZ.of_le one_le_two) hc s) α.val x) =
      fun _ ↦ α.val x := by
    funext s
    have hψ : globalFlow _ (hZ.of_le one_le_two) hc s = fun y : M ↦ mulInvariantExp (s • ξ) • y :=
      funext (globalFlow_fundamentalVectorField ξ _ hc s)
    rw [hψ, ← SmoothForm.coe_mpullback _ (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') _),
      hα]
  have h := hasDerivAt_mpullback_globalFlow_zero hc (hZ.of_le one_le_two) x (α.mdifferentiable x)
  rw [hconst] at h
  exact h.unique (hasDerivAt_const 0 _)

/-- **Horizontality of the exterior derivative.** If a one-form `α` is invariant under the action
of every element of `G` and pairs every fundamental vector field with a constant `c(ξ)`, its
exterior derivative vanishes on every fundamental vector field: `dα(ξ_M, v) = 0`. -/
theorem mextDerivₗ_apply_fundamentalVectorField_eq_zero {α : SmoothForm I' M ℝ 1}
    {c : Module.Dual ℝ (GroupLieAlgebra I G)}
    (hinv : ∀ g : G, SmoothForm.mpullback (fun x : M ↦ g • x)
      (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := I') g) α = α)
    (hα : ∀ x ξ, α.val x ![fundamentalVectorField I' ξ x] = c ξ) (ξ : GroupLieAlgebra I G) (x : M)
    (v : TangentSpace I' x) :
    (mextDerivₗ I' 1 α).val x ![fundamentalVectorField I' ξ x, v] = 0 := by
  have hX : MDifferentiableAt I' I'.tangent
      (fun y ↦ (⟨y, fundamentalVectorField I' ξ y⟩ : TangentBundle I' M)) x :=
    ((contMDiff_two_fundamentalVectorField ξ).mdifferentiable two_ne_zero) x
  -- Cartan's formula: `0 = L_{ξ_M} α = ι_{ξ_M} dα + d(α(ξ_M))`, with `α(ξ_M) = c(ξ)` constant.
  have h := mlieDerivForm_apply_eq_mextDeriv_add (f := fun _ ↦ c ξ) (fun y ↦ hα y ξ)
    (α.mdifferentiableAt x) hX v
  rw [mlieDerivForm_fundamentalVectorField_eq_zero hinv ξ, mvfderiv_const] at h
  rw [mextDerivₗ_apply]
  simpa [eq_comm] using h

end TauCeti
