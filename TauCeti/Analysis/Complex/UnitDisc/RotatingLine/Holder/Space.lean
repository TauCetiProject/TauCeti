/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import TauCeti.Analysis.Complex.Wirtinger.Holder.Space
public import TauCeti.Analysis.Holder.OpenSet.Closure
import TauCeti.Analysis.Complex.UnitDisc.RiemannHilbert
import TauCeti.Analysis.Complex.UnitDisc.RotatingLine.Holder.Basic

/-!
# The augmented disc problem with rotating-line boundary values is a Banach isomorphism

Fix `0 < α < 1` and an integer `k`. On the open unit disc `D`, the elements of `C^{1,α}(D, ℂ)`
extend continuously to the closed disc (`TauCeti.CkHolderSpaceOn.closureExtend`). Those whose
boundary values lie on the rotating lines `e^{ikθ/2} ℝ`, that is `u w = w ^ k * conj (u w)` for
`|w| = 1`, form a closed real subspace `X_k` (`TauCeti.rotatingLineHolderSubspace`), a Banach
space. The augmented Cauchy–Riemann operator

`u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))`

(`TauCeti.rotatingLineHolderAugmentedL`), with `∂ₛu(0)` the real derivative of `u` at `0` in the
direction `1`, maps `X_k` continuously to `C^α(D, ℂ) × ℂ × ℂ`.

For `k ≥ 3` it is onto: the disc problem with Hölder forcing has a `C^{1,α}` solution with
prescribed centre value and first jet
(`TauCeti.exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_and_eq_and_fderiv_eq_of_holderOnWith`),
after the forcing is extended to the closed disc. For `k = 3` it is also one-to-one: the
homogeneous problem has the cubics `a₀ + a₁ z + conj a₁ z² + conj a₀ z³` as its solutions, and
the centre value and first jet read off `a₀` and `a₁`
(`TauCeti.eqOn_of_conjWirtingerDeriv_eq_of_eq_zpow_mul_conj_of_eq_of_fderiv_eq`). By the open
mapping theorem, for Maslov index three the augmented operator is therefore an isomorphism of
Banach spaces (`TauCeti.rotatingLineHolderAugmentedEquiv`): its inverse is bounded, which is what
the perturbation of this normalized problem by small lower-order terms needs.

## Main declarations

* `TauCeti.rotatingLineHolderSubspace k α`: the closed subspace `X_k` of `C^{1,α}(D, ℂ)` of
  elements with boundary values on the rotating lines `e^{ikθ/2} ℝ`; it is complete
  (`TauCeti.isClosed_rotatingLineHolderSubspace`).
* `TauCeti.rotatingLineHolderAugmentedL k α`: the augmented operator
  `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` on `X_k`.
* `TauCeti.rotatingLineHolderAugmentedL_injective`: it is one-to-one for `k = 3`.
* `TauCeti.rotatingLineHolderAugmentedL_surjective`: it is onto for `k ≥ 3` and `0 < α < 1`.
* `TauCeti.rotatingLineHolderAugmentedEquiv`: for `k = 3` and `0 < α < 1`, the augmented operator
  as an isomorphism of Banach spaces `X_3 ≃L[ℝ] C^α(D, ℂ) × ℂ × ℂ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C (the boundary value problem on the disc,
  Theorem C.4.1).
-/

public noncomputable section

namespace TauCeti

open Complex Filter Metric Set TopologicalSpace Topology
open scoped ComplexConjugate NNReal

variable {α : ℝ≥0}

/-- The open unit disc is convex. -/
private theorem convex_unitDisc : Convex ℝ ((⟨ball 0 1, isOpen_ball⟩ : Opens ℂ) : Set ℂ) :=
  convex_ball 0 1

/-- The closure of the open unit disc is the closed unit disc. -/
private theorem closure_unitDisc :
    closure ((⟨ball 0 1, isOpen_ball⟩ : Opens ℂ) : Set ℂ) = closedBall 0 1 := by
  rw [Opens.coe_mk, closure_ball 0 one_ne_zero]

/-- The points of the closed unit disc lie in the closure of the open unit disc. -/
private theorem mem_closure_unitDisc {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) 1) :
    w ∈ closure ((⟨ball 0 1, isOpen_ball⟩ : Opens ℂ) : Set ℂ) := by
  rwa [closure_unitDisc]

/-- The points of the unit circle lie in the closure of the open unit disc. -/
private theorem mem_closure_unitDisc_of_mem_sphere {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) :
    w ∈ closure ((⟨ball 0 1, isOpen_ball⟩ : Opens ℂ) : Set ℂ) :=
  mem_closure_unitDisc (sphere_subset_closedBall hw)

/-- The centre of the unit disc, as a point of the open disc. -/
private def unitDiscCentre : (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) :=
  ⟨0, mem_ball_self one_pos⟩

/-- The elements of `C^{1,α}` on the open unit disc whose continuous extensions to the closed disc
have boundary values on the rotating lines `e^{ikθ/2} ℝ`: `u w = w ^ k * conj (u w)` for `|w| = 1`.
-/
def rotatingLineHolderSubspace (k : ℤ) (α : ℝ≥0) :
    Submodule ℝ (CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ) where
  carrier := {u | ∀ w ∈ sphere (0 : ℂ) 1, u.closureExtend w = w ^ k * conj (u.closureExtend w)}
  add_mem' {u v} hu hv w hw := by
    rw [CkHolderSpaceOn.closureExtend_add u v convex_unitDisc
      (mem_closure_unitDisc_of_mem_sphere hw), map_add]
    linear_combination hu w hw + hv w hw
  zero_mem' w hw := by
    simp [CkHolderSpaceOn.closureExtend_zero (mem_closure_unitDisc_of_mem_sphere hw)]
  smul_mem' c u hu w hw := by
    rw [CkHolderSpaceOn.closureExtend_smul c u convex_unitDisc
      (mem_closure_unitDisc_of_mem_sphere hw), Complex.real_smul, map_mul,
      Complex.conj_ofReal]
    linear_combination (c : ℂ) * hu w hw

@[simp]
theorem mem_rotatingLineHolderSubspace_iff {k : ℤ}
    {u : CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ} :
    u ∈ rotatingLineHolderSubspace k α ↔
      ∀ w ∈ sphere (0 : ℂ) 1, u.closureExtend w = w ^ k * conj (u.closureExtend w) :=
  Iff.rfl

/-- The rotating-line boundary condition cuts out a closed subspace of `C^{1,α}(D, ℂ)`: it is an
intersection of kernels of continuous real-linear maps, the boundary value at `w` minus
`w ^ k` times its conjugate. -/
theorem isClosed_rotatingLineHolderSubspace (k : ℤ) (α : ℝ≥0) :
    IsClosed (rotatingLineHolderSubspace k α :
      Set (CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ)) := by
  have hset : (rotatingLineHolderSubspace k α :
      Set (CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ)) =
      ⋂ (w : ℂ) (hw : w ∈ sphere (0 : ℂ) 1),
        {u | CkHolderSpaceOn.closureExtendL convex_unitDisc
            (mem_closure_unitDisc_of_mem_sphere hw) u =
          w ^ k * conj (CkHolderSpaceOn.closureExtendL convex_unitDisc
            (mem_closure_unitDisc_of_mem_sphere hw) u)} := by
    ext u
    simp
  rw [hset]
  exact isClosed_iInter fun w ↦ isClosed_iInter fun hw ↦ isClosed_eq
    (ContinuousLinearMap.continuous _)
    (continuous_const.mul (Complex.continuous_conj.comp (ContinuousLinearMap.continuous _)))

instance (k : ℤ) (α : ℝ≥0) : CompleteSpace (rotatingLineHolderSubspace k α) :=
  (isClosed_rotatingLineHolderSubspace k α).completeSpace_coe

/-- The value of the derivative of an element at the centre in the direction `1`. -/
private def fderivCentreApplyOneL :
    CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).comp
    ((continuousMultilinearCurryFin1 ℝ ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((HolderSpace.evalCLM unitDiscCentre).comp CkHolderSpaceOn.iteratedFDerivHolderL))

private theorem fderivCentreApplyOneL_apply
    (u : CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ) :
    fderivCentreApplyOneL u = fderiv ℝ u.extend 0 1 := by
  simp [fderivCentreApplyOneL, ← u.iteratedFDeriv_extend, unitDiscCentre]

/-- The augmented Cauchy–Riemann operator `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` on the elements of
`C^{1,α}(D, ℂ)` with boundary values on the rotating lines `e^{ikθ/2} ℝ`, to
`C^α(D, ℂ) × ℂ × ℂ`. Here `∂ₛu(0)` is the real derivative of `u` at the centre in the direction
`1`. -/
def rotatingLineHolderAugmentedL (k : ℤ) (α : ℝ≥0) :
    rotatingLineHolderSubspace k α →L[ℝ]
      HolderSpace α (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) ℂ × ℂ × ℂ :=
  (conjWirtingerDerivHolderL.prod
      (((BoundedContinuousFunction.evalCLM ℝ unitDiscCentre).comp
          CkHolderSpaceOn.toBoundedContinuousFunctionCLM).prod fderivCentreApplyOneL)).comp
    (rotatingLineHolderSubspace k α).subtypeL

@[simp]
theorem rotatingLineHolderAugmentedL_apply (k : ℤ) (u : rotatingLineHolderSubspace k α) :
    rotatingLineHolderAugmentedL k α u =
      (conjWirtingerDerivHolderL (u : CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ),
        (u : CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ) ⟨0, mem_ball_self one_pos⟩,
        fderiv ℝ (u : CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ).extend 0 1) := by
  simp [rotatingLineHolderAugmentedL, fderivCentreApplyOneL_apply, unitDiscCentre]

/-- **Uniqueness for the augmented problem.** For Maslov index three, an element of
`C^{1,α}(D, ℂ)` with boundary values on the lines `e^{3iθ/2} ℝ` is determined by
`∂u/∂(conj z)`, its centre value and its first jet `∂ₛu(0)`. -/
theorem rotatingLineHolderAugmentedL_injective :
    Function.Injective (rotatingLineHolderAugmentedL 3 α) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
  set v : CkHolderSpaceOn 1 α ⟨ball (0 : ℂ) 1, isOpen_ball⟩ ℂ := u.val with hv
  rw [rotatingLineHolderAugmentedL_apply] at hu
  obtain ⟨hbar, h₀, h₁⟩ : conjWirtingerDerivHolderL v = 0 ∧ v ⟨0, mem_ball_self one_pos⟩ = 0 ∧
      fderiv ℝ v.extend 0 1 = 0 := by
    simpa only [Prod.mk_eq_zero] using hu
  have hfd (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : fderiv ℝ v.closureExtend z = fderiv ℝ v.extend z :=
    (v.closureExtend_eventuallyEq_extend ⟨z, hz⟩).fderiv_eq
  have hdiff : DifferentiableOn ℝ v.extend (ball 0 1) :=
    v.contDiffOn_extend.differentiableOn (by simp)
  have key := eqOn_of_conjWirtingerDeriv_eq_of_eq_zpow_mul_conj_of_eq_of_fderiv_eq
    (u₁ := v.closureExtend) (u₂ := 0)
    (closure_unitDisc ▸ v.continuousOn_closureExtend convex_unitDisc)
    continuousOn_const (hdiff.congr fun z hz ↦ by
      rw [v.closureExtend_apply ⟨z, hz⟩, v.extend_apply ⟨z, hz⟩])
    (differentiableOn_const 0) (fun z hz ↦ ?_) u.property (by simp)
    (by simp [v.closureExtend_apply ⟨0, mem_ball_self one_pos⟩, h₀])
    (by rw [hfd 0 (mem_ball_self one_pos), h₁]; simp)
  · refine Subtype.ext (CkHolderSpaceOn.ext fun x ↦ ?_)
    have hx := key (ball_subset_closedBall x.property)
    rw [v.closureExtend_apply x] at hx
    simp [← hv, hx]
  · rw [conjWirtingerDeriv_apply, conjWirtingerDeriv_apply, hfd z hz, ← conjWirtingerDeriv_apply,
      ← conjWirtingerDerivHolderL_apply_extend v ⟨z, hz⟩, hbar]
    simp

/-- **Existence for the augmented problem.** For `k ≥ 3` and `0 < α < 1`, every `C^α` forcing on
the open unit disc, centre value and first jet are attained by an element of `C^{1,α}(D, ℂ)` with
boundary values on the rotating lines `e^{ikθ/2} ℝ`. -/
theorem rotatingLineHolderAugmentedL_surjective {k : ℤ} (hk : 3 ≤ k) (hα0 : 0 < α)
    (hα1 : α < 1) : Function.Surjective (rotatingLineHolderAugmentedL k α) := by
  rintro ⟨g, a, b⟩
  obtain ⟨G, hGg, hG⟩ := g.exists_holderOnWith_closure hα0
  rw [closure_unitDisc] at hG
  obtain ⟨u, ⟨K, huH⟩, hud, ⟨u', K', hu'H, hu'⟩, hbar, hbd, hu0, hu1⟩ :=
    exists_conjWirtingerDeriv_eq_and_eq_zpow_mul_conj_and_eq_and_fderiv_eq_of_holderOnWith hk
      hα0 hα1 hG a b
  obtain ⟨U, hU⟩ := exists_ckHolderSpaceOn_one_of_isCompact_closure
    (closure_unitDisc ▸ isCompact_closedBall 0 1) (closure_unitDisc ▸ huH.continuousOn hα0) hud
    (closure_unitDisc ▸ hu'H.continuousOn hα0) (hu'H.mono ball_subset_closedBall) hu'
  have hcl (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) 1) : U.closureExtend w = u w :=
    U.closureExtend_eq_of_continuousWithinAt (fun x ↦ (hU x).symm) (mem_closure_unitDisc hw)
      ((huH.continuousOn hα0 w hw).mono ball_subset_closedBall)
  have hfd : fderiv ℝ U.extend 0 = fderiv ℝ u 0 := by
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1))] with y hy
    rw [U.extend_apply ⟨y, hy⟩, hU]
  refine ⟨⟨U, fun w hw ↦ ?_⟩, ?_⟩
  · rw [hcl w (sphere_subset_closedBall hw)]
    exact hbd w hw
  · rw [rotatingLineHolderAugmentedL_apply]
    refine Prod.ext (HolderSpace.ext fun x ↦ ?_) (Prod.ext ?_ ?_)
    · rw [conjWirtingerDerivHolderL_apply U (fun x ↦ (hU x).symm), hbar x x.property, hGg]
    · exact (hU _).trans hu0
    · exact (congrFun (congrArg DFunLike.coe hfd) 1).trans hu1

/-- **The augmented disc problem is a Banach isomorphism.** For `0 < α < 1`, the augmented
Cauchy–Riemann operator `u ↦ (∂u/∂(conj z), u 0, ∂ₛu(0))` is an isomorphism of Banach spaces from
the elements of `C^{1,α}(D, ℂ)` with boundary values on the lines `e^{3iθ/2} ℝ` onto
`C^α(D, ℂ) × ℂ × ℂ`. Its inverse is bounded by the open mapping theorem. -/
def rotatingLineHolderAugmentedEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    rotatingLineHolderSubspace 3 α ≃L[ℝ]
      HolderSpace α (⟨ball (0 : ℂ) 1, isOpen_ball⟩ : Opens ℂ) ℂ × ℂ × ℂ :=
  ContinuousLinearEquiv.ofBijective (rotatingLineHolderAugmentedL 3 α)
    (LinearMap.ker_eq_bot.2 rotatingLineHolderAugmentedL_injective)
    (LinearMap.range_eq_top.2 (rotatingLineHolderAugmentedL_surjective le_rfl hα0 hα1))

@[simp]
theorem coe_rotatingLineHolderAugmentedEquiv (hα0 : 0 < α) (hα1 : α < 1) :
    ⇑(rotatingLineHolderAugmentedEquiv hα0 hα1) = rotatingLineHolderAugmentedL 3 α :=
  (rfl)

end TauCeti
