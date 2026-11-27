/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Closure
public import TauCeti.Analysis.Holder.OpenSet.ConjWirtinger
public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Normed.Module.Ball.Opens
import TauCeti.Analysis.Complex.UnitDisc.RiemannHilbert
import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# The augmented Cauchy–Riemann operator with rotating-line boundary values is an isomorphism

Let `D` be the open unit disc and `0 < α < 1`. For an integer `k`, the elements `u` of the Hölder
space `C^{1,α}(D)` whose continuous extension to the closed disc takes boundary values on the
rotating lines `e^{ikθ/2} ℝ`, that is `u w = w ^ k * conj (u w)` on the unit circle, form a closed
real subspace `X_k` of `C^{1,α}(D)` (`TauCeti.rotatingLineSubspace`), hence a Banach space. The
augmented Cauchy–Riemann operator

`u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))`

is a continuous linear map from `C^{1,α}(D, F)` to `C^{0,α}(D, F) × F × F` for any complex normed
space `F` (`TauCeti.augmentedConjWirtingerDerivL`), where `∂ₛu(0)` is the real derivative of `u`
at the centre in the direction `1`. For `F = ℂ` and on `X_k` with `k ≥ 3` it is onto: the
rotating-line problem with `α`-Hölder forcing has `C^{1,α}` solutions with prescribed centre
value and first jet. For the normalization `k = 3` it is also injective, since then the kernel of
`∂/∂(conj z)` with these boundary values consists of the cubics
`a₀ + a₁ z + conj a₁ z² + conj a₀ z³`, which are determined by their centre value and first jet.
By the open mapping theorem the augmented operator is therefore a Banach isomorphism
`X_3 ≃L[ℝ] C^{0,α}(D) × ℂ × ℂ` (`TauCeti.rotatingLineAugmentedEquiv`), and its inverse gives the
a priori estimate
`‖u‖_{C^{1,α}} ≤ C (‖∂u/∂(conj z)‖_{C^α} + |u 0| + |∂ₛu(0)|)` on `X_3`
(`TauCeti.exists_norm_le_mul_norm_augmentedConjWirtingerDerivL`). This is the rank-one case of
the normalized real-boundary disc solver of the linear theory of holomorphic discs.

## Main declarations

* `TauCeti.rotatingLineSubspace`: the closed subspace `X_k` of `C^{1,α}(D)`, with
  `TauCeti.mem_rotatingLineSubspace_iff`.
* `TauCeti.augmentedConjWirtingerDerivL`: the augmented operator
  `C^{1,α}(D, F) →L[ℝ] C^{0,α}(D, F) × F × F`, which commutes with postcomposition by complex-linear
  maps (`TauCeti.augmentedConjWirtingerDerivL_compLeftL`).
* `TauCeti.exists_mem_rotatingLineSubspace_augmentedConjWirtingerDerivL_eq`: surjectivity on
  `X_k` for `k ≥ 3`.
* `TauCeti.injOn_augmentedConjWirtingerDerivL`: injectivity on `X_3`.
* `TauCeti.rotatingLineAugmentedEquiv`: the Banach isomorphism `X_3 ≃L[ℝ] C^{0,α}(D) × ℂ × ℂ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the boundary value problem on the disc).
-/

public section

noncomputable section

namespace TauCeti

open Complex Metric Set Filter TopologicalSpace Topology CkHolderSpaceOn
open scoped ComplexConjugate NNReal

/-! ### The boundary subspace -/

variable {k : ℤ} {α : ℝ≥0}

/-- The closed subspace of `C^{1,α}(D)`, for the open unit disc `D`, of the elements `u` whose
continuous extension to the closed disc takes its boundary values on the rotating lines
`e^{ikθ/2} ℝ`, that is `u w = w ^ k * conj (u w)` for `w` on the unit circle. -/
def rotatingLineSubspace (k : ℤ) (α : ℝ≥0) :
    Submodule ℝ (CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ) :=
  ⨅ w : sphere (0 : ℂ) 1, ((ContinuousLinearMap.id ℝ ℂ -
    ((w : ℂ) ^ k) • conjCLE.toContinuousLinearMap) ∘L
      closureEvalL (k := 0) (convex_unitBallOpens ℂ)
        (closure_unitBallOpens ℂ ▸ sphere_subset_closedBall w.property)).ker

/-- An element of `C^{1,α}(D)` lies in `rotatingLineSubspace k α` exactly when its extension to
the closed disc satisfies `u w = w ^ k * conj (u w)` on the unit circle. -/
theorem mem_rotatingLineSubspace_iff {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ} :
    u ∈ rotatingLineSubspace k α ↔
      ∀ w ∈ sphere (0 : ℂ) 1, u.closureExtend w = w ^ k * conj (u.closureExtend w) := by
  simp [rotatingLineSubspace, Submodule.mem_iInf, sub_eq_zero]

/-- The rotating-line boundary condition defines a closed subspace of `C^{1,α}(D)`: it is an
intersection of kernels of continuous linear functionals. -/
theorem isClosed_rotatingLineSubspace (k : ℤ) (α : ℝ≥0) :
    IsClosed (rotatingLineSubspace k α : Set (CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ)) := by
  rw [rotatingLineSubspace, Submodule.coe_iInf]
  exact isClosed_iInter fun w ↦ ContinuousLinearMap.isClosed_ker _

/-- The rotating-line boundary subspace is a Banach space. -/
instance : CompleteSpace (rotatingLineSubspace k α) :=
  (isClosed_rotatingLineSubspace k α).completeSpace_coe

/-! ### The augmented operator -/

section augmented

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

variable (α F) in
/-- The augmented Cauchy–Riemann operator `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` on `C^{1,α}(D, F)`,
for the open unit disc `D` and a complex normed space `F`, where `∂ₛu(0)` is the real derivative
of `u` at the centre in the direction `1`. -/
def augmentedConjWirtingerDerivL :
    CkHolderSpaceOn 1 α (unitBallOpens ℂ) F →L[ℝ] HolderSpace α (unitBallOpens ℂ) F × F × F :=
  (conjWirtingerDerivL α (unitBallOpens ℂ) F).prod
    ((BoundedContinuousFunction.evalCLM ℝ (⟨0, zero_mem_unitBallOpens ℂ⟩ : unitBallOpens ℂ) ∘L
        toBoundedContinuousFunctionCLM).prod
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 1 ↦ ℂ) F ![1] ∘L
        BoundedContinuousFunction.evalCLM ℝ (⟨0, zero_mem_unitBallOpens ℂ⟩ : unitBallOpens ℂ) ∘L
          iteratedFDerivL (k := 1) 1))

/-- The components of the augmented operator: the conjugate Wirtinger derivative, the centre
value and the first jet `∂ₛu(0)`. -/
@[simp]
theorem augmentedConjWirtingerDerivL_apply (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) F) :
    augmentedConjWirtingerDerivL α F u =
      (conjWirtingerDerivL α (unitBallOpens ℂ) F u, u.extend 0, fderiv ℝ u.extend 0 1) := by
  have h := u.iteratedFDeriv_extend 1 ⟨0, zero_mem_unitBallOpens ℂ⟩
  simp only [augmentedConjWirtingerDerivL, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, BoundedContinuousFunction.evalCLM_apply,
    toBoundedContinuousFunctionCLM_apply, coe_toBoundedContinuousFunction,
    ContinuousMultilinearMap.apply_apply, Prod.mk.injEq, true_and]
  refine ⟨(u.extend_apply ⟨0, zero_mem_unitBallOpens ℂ⟩).symm, ?_⟩
  rw [iteratedFDerivL_apply, ← h]
  simp

/-- The augmented operator commutes with postcomposition by a continuous complex-linear map `L`:
each of its three components is mapped by `L`. -/
theorem augmentedConjWirtingerDerivL_compLeftL {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] (L : F →L[ℂ] G) (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) F) :
    augmentedConjWirtingerDerivL α G (compLeftL (L.restrictScalars ℝ) u) =
      (HolderSpace.compLeftL (L.restrictScalars ℝ) (conjWirtingerDerivL α (unitBallOpens ℂ) F u),
        L (u.extend 0), L (fderiv ℝ u.extend 0 1)) := by
  have h0 := zero_mem_unitBallOpens ℂ
  have hgerm := extend_compLeftL_eventuallyEq (L.restrictScalars ℝ) u h0
  rw [augmentedConjWirtingerDerivL_apply, conjWirtingerDerivL_compLeftL, hgerm.eq_of_nhds,
    hgerm.fderiv_eq]
  have hd : fderiv ℝ (fun y ↦ L.restrictScalars ℝ (u.extend y)) 0 =
      L.restrictScalars ℝ ∘L fderiv ℝ u.extend 0 :=
    (L.restrictScalars ℝ).fderiv_comp_left (u.differentiableAt_extend h0)
  rw [hd]
  simp

end augmented

/-! ### Surjectivity -/

/-- **Existence with prescribed centre value and first jet.** Let `k ≥ 3` and `0 < α < 1`. For
every `α`-Hölder forcing `f` on the open unit disc and all `a b : ℂ`, some element `u` of
`C^{1,α}(D)` with boundary values on the rotating lines `e^{ikθ/2} ℝ` has `∂u/∂(conj z) = f`,
`u 0 = a` and `∂ₛu(0) = b`. -/
theorem exists_mem_rotatingLineSubspace_augmentedConjWirtingerDerivL_eq (hk : 3 ≤ k)
    (hα0 : 0 < α) (hα1 : α < 1) (y : HolderSpace α (unitBallOpens ℂ) ℂ × ℂ × ℂ) :
    ∃ u ∈ rotatingLineSubspace k α, augmentedConjWirtingerDerivL α ℂ u = y := by
  obtain ⟨f, a, b⟩ := y
  -- The forcing, extended to the closed disc as an `α`-Hölder function.
  obtain ⟨G, hGg, hG⟩ := f.exists_holderOnWith_closure hα0
  rw [closure_unitBallOpens] at hG
  obtain ⟨u, ⟨K, huH⟩, hud, ⟨u', K', hu'H, hu'⟩, hubar, hub, hu0, hu1⟩ :=
    exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_and_eq_and_fderiv_eq_of_holderOnWith hk
      hα0 hα1 hG a b
  -- The solution as an element of `C^{1,α}(D)`.
  obtain ⟨C, hC⟩ := (huH.isBounded_image isBounded_closedBall).exists_norm_le
  obtain ⟨U, hU⟩ := exists_apply_eq_of_differentiableOn_of_holderOnWith (Ω := unitBallOpens ℂ)
    hα0 (coe_unitBallOpens ℂ ▸ isBounded_ball) (coe_unitBallOpens ℂ ▸ hud)
    ⟨C, fun x hx ↦
      hC _ ⟨x, ball_subset_closedBall (mem_unitBallOpens_iff_mem_ball.1 hx), rfl⟩⟩
    (coe_unitBallOpens ℂ ▸ hu'H.mono ball_subset_closedBall)
    fun x hx ↦ hu' x (mem_unitBallOpens_iff_mem_ball.1 hx)
  have hUe {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : U.extend =ᶠ[𝓝 z] u := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx
    rw [U.extend_apply_of_mem (mem_unitBallOpens_iff_mem_ball.2 hx), hU]
  refine ⟨U, mem_rotatingLineSubspace_iff.2 fun w hw ↦ ?_, ?_⟩
  · -- The continuous extension of `U` to the closed disc is `u`.
    rw [U.closureExtend_eq_of_continuousWithinAt hU
      (closure_unitBallOpens ℂ ▸ sphere_subset_closedBall hw)
      (coe_unitBallOpens ℂ ▸
        (huH.continuousOn hα0 w (sphere_subset_closedBall hw)).mono ball_subset_closedBall)]
    exact hub w hw
  rw [augmentedConjWirtingerDerivL_apply, (hUe (mem_ball_self one_pos)).eq_of_nhds,
    (hUe (mem_ball_self one_pos)).fderiv_eq, hu0, hu1]
  refine Prod.ext (HolderSpace.ext fun z ↦ ?_) rfl
  have hz := mem_unitBallOpens_iff_mem_ball.1 z.property
  rw [conjWirtingerDerivL_apply U z (hUe hz), hubar z hz, hGg]

/-! ### Injectivity -/

/-- **Uniqueness for Maslov index three.** On the elements of `C^{1,α}(D)` with boundary values on
the rotating lines `e^{3iθ/2} ℝ`, the augmented operator `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` is
injective. -/
theorem injOn_augmentedConjWirtingerDerivL :
    InjOn (augmentedConjWirtingerDerivL α ℂ) (rotatingLineSubspace 3 α) := by
  intro u hu v hv huv
  simp only [augmentedConjWirtingerDerivL_apply, Prod.mk.injEq] at huv
  obtain ⟨hd, h0, h1⟩ := huv
  have hcl {u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
      u.closureExtend =ᶠ[𝓝 z] u.extend :=
    u.closureExtend_eventuallyEq_extend (mem_unitBallOpens_iff_mem_ball.2 hz)
  have hc (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ) :
      ContinuousOn u.closureExtend (closedBall 0 1) :=
    closure_unitBallOpens ℂ ▸ u.continuousOn_closureExtend (convex_unitBallOpens ℂ)
  have hdiff (u : CkHolderSpaceOn 1 α (unitBallOpens ℂ) ℂ) :
      DifferentiableOn ℝ u.closureExtend (ball 0 1) :=
    coe_unitBallOpens ℂ ▸ u.differentiableOn_closureExtend
  have h0' := mem_ball_self (x := (0 : ℂ)) one_pos
  have heq := eqOn_of_conjWirtingerDeriv_eq_of_eq_zpow_mul_conj_of_eq_of_fderiv_eq (hc u) (hc v)
    (hdiff u) (hdiff v) (fun z hz ↦ by
      rw [(hcl hz).conjWirtingerDeriv_eq, (hcl hz).conjWirtingerDeriv_eq,
        ← conjWirtingerDerivL_apply_eq_conjWirtingerDeriv_extend u
          ⟨z, mem_unitBallOpens_iff_mem_ball.2 hz⟩,
        ← conjWirtingerDerivL_apply_eq_conjWirtingerDeriv_extend v
          ⟨z, mem_unitBallOpens_iff_mem_ball.2 hz⟩, hd])
    (mem_rotatingLineSubspace_iff.1 hu) (mem_rotatingLineSubspace_iff.1 hv)
    (by rw [(hcl h0').eq_of_nhds, (hcl h0').eq_of_nhds, h0])
    (by rw [(hcl h0').fderiv_eq, (hcl h0').fderiv_eq, h1])
  ext z
  have := heq (ball_subset_closedBall (mem_unitBallOpens_iff_mem_ball.1 z.property))
  rwa [closureExtend_apply, closureExtend_apply] at this

/-! ### The Banach isomorphism -/

/-- **The normalized real-boundary disc solver.** For `0 < α < 1`, the augmented Cauchy–Riemann
operator `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` is a Banach isomorphism from the elements of
`C^{1,α}(D)` with boundary values on the rotating lines `e^{3iθ/2} ℝ` onto
`C^{0,α}(D) × ℂ × ℂ`. -/
def rotatingLineAugmentedEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    rotatingLineSubspace 3 α ≃L[ℝ] HolderSpace α (unitBallOpens ℂ) ℂ × ℂ × ℂ :=
  ContinuousLinearEquiv.ofBijective
    (augmentedConjWirtingerDerivL α ℂ ∘L (rotatingLineSubspace 3 α).subtypeL)
    (LinearMap.ker_eq_bot.2 fun u v huv ↦ Subtype.ext
      (injOn_augmentedConjWirtingerDerivL u.property v.property huv))
    (LinearMap.range_eq_top.2 fun y ↦ by
      obtain ⟨u, hu, rfl⟩ :=
        exists_mem_rotatingLineSubspace_augmentedConjWirtingerDerivL_eq le_rfl hα0 hα1 y
      exact ⟨⟨u, hu⟩, rfl⟩)

/-- The isomorphism `TauCeti.rotatingLineAugmentedEquiv` is the augmented operator. -/
@[simp]
theorem rotatingLineAugmentedEquiv_apply (hα0 : 0 < α) (hα1 : α < 1)
    (u : rotatingLineSubspace 3 α) :
    rotatingLineAugmentedEquiv hα0 hα1 u = augmentedConjWirtingerDerivL α ℂ u :=
  (rfl)

/-- **The Schauder estimate for the normalized disc problem.** For `0 < α < 1` there is a constant
`C` such that every element `u` of `C^{1,α}(D)` with boundary values on the rotating lines
`e^{3iθ/2} ℝ` satisfies `‖u‖ ≤ C ‖(∂u/∂(conj z), u 0, ∂ₛu(0))‖`. -/
theorem exists_norm_le_mul_norm_augmentedConjWirtingerDerivL (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C, ∀ u ∈ rotatingLineSubspace 3 α, ‖u‖ ≤ C * ‖augmentedConjWirtingerDerivL α ℂ u‖ := by
  set e := rotatingLineAugmentedEquiv hα0 hα1
  refine ⟨‖e.symm.toContinuousLinearMap‖, fun u hu ↦ ?_⟩
  have h := e.symm.toContinuousLinearMap.le_opNorm (e ⟨u, hu⟩)
  rw [ContinuousLinearEquiv.coe_coe, e.symm_apply_apply, rotatingLineAugmentedEquiv_apply] at h
  -- The norm on the subspace is the norm of `C^{1,α}(D)`.
  exact h

end TauCeti
