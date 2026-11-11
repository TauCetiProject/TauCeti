/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Interior
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Inclusion

/-!
# Immersions of closed balls at interior points

A map `Φ` between the closed unit balls of two finite-dimensional real inner product spaces, in
the sense of manifolds with boundary, is often the restriction of a map `c` between the ambient
spaces. At a point `x` of the open unit ball which `Φ` maps into the open unit ball, `Φ` is an
immersion as soon as `c` is one at `x` (`TauCeti.isImmersionAt_closedBall_of_norm_lt_one`). The
inclusions of the closed balls have invertible derivatives
(`TauCeti.subtypeValClosedBallTangentEquiv`), so the derivative of `Φ` at `x` is injective, and
an injective derivative at an interior point mapped to an interior point gives an immersion
(`ContMDiffOn.isImmersionAt_of_injective_mfderiv_of_isInteriorPoint`).

Together with `TauCeti.isImmersionAt_of_comp_ballCollar_eventuallyEq_prodMap`, which treats points
near the boundary sphere where `Φ` is a cone, this decides immersivity of restrictions such as a
smooth disc in a ball which is a cone over a knot near its boundary circle.
-/

public section

noncomputable section

open Set Metric Function Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] {m n : ℕ} [NeZero m] [NeZero n] [Fact (Module.finrank ℝ F = m)]
  [Fact (Module.finrank ℝ E = n)]

/-- **Immersions of closed balls at interior points.** Let `Φ` be a map between the closed unit
balls of `F` and `E` which is the restriction of a map `c : F → E`. If `c` is a `C^k` immersion at a
point `x` of the open unit ball, `1 ≤ k`, and `Φ x` lies in the open unit ball, then `Φ` is a `C^k`
immersion at `x` in the sense of manifolds with boundary. -/
theorem isImmersionAt_closedBall_of_norm_lt_one {k : ℕ∞ω} (hk : 1 ≤ k)
    {Φ : closedBall (0 : F) 1 → closedBall (0 : E) 1} {c : F → E} (hΦ : ∀ y, (Φ y : E) = c y)
    {x : closedBall (0 : F) 1} (hc : IsImmersionAt 𝓘(ℝ, F) 𝓘(ℝ, E) k c x) (hx : ‖(x : F)‖ < 1)
    (hΦx : ‖(Φ x : E)‖ < 1) :
    IsImmersionAt (𝓡∂ m) (𝓡∂ n) k Φ x := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos <| by
    rw [(Fact.out : Module.finrank ℝ E = n)]
    exact Nat.pos_of_ne_zero (NeZero.ne n)
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  -- `Φ` is `C^k` near `x`, where `c` is.
  set s : Set (closedBall (0 : F) 1) := Subtype.val ⁻¹' hc.domChart.source
  have hs : IsOpen s := hc.domChart.open_source.preimage continuous_subtype_val
  have hxs : x ∈ s := hc.mem_domChart_source
  have hfun : Subtype.val ∘ Φ = c ∘ Subtype.val := funext hΦ
  have hΦs : ContMDiffOn (𝓡∂ m) (𝓡∂ n) k Φ s := by
    rw [contMDiffOn_iff_comp_subtypeVal_closedBall, hfun]
    exact hc.contMDiffOn.comp contMDiff_subtypeVal_closedBall.contMDiffOn fun _ hy ↦ hy
  refine hΦs.isImmersionAt_of_injective_mfderiv_of_isInteriorPoint hs hxs hk
    (isInteriorPoint_closedBall_iff.2 hx) (isInteriorPoint_closedBall_iff.2 hΦx) fun v w hvw ↦ ?_
  -- Differentiate `Subtype.val ∘ Φ = c ∘ Subtype.val` at `x`: both inclusions and `c` have
  -- injective derivatives.
  have hcomp : (mfderiv (𝓡∂ n) 𝓘(ℝ, E) Subtype.val (Φ x)).comp (mfderiv (𝓡∂ m) (𝓡∂ n) Φ x) =
      (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) c x).comp (mfderiv (𝓡∂ m) 𝓘(ℝ, F) Subtype.val x) := by
    rw [← mfderiv_comp x (contMDiff_subtypeVal_closedBall.mdifferentiableAt hk0)
        ((hΦs.contMDiffAt (hs.mem_nhds hxs)).mdifferentiableAt hk0), hfun,
      mfderiv_comp x (hc.contMDiffAt.mdifferentiableAt hk0)
        (contMDiff_subtypeVal_closedBall.mdifferentiableAt hk0)]
  refine injective_mfderiv_subtypeVal_closedBall x (hc.mfderiv_injective hk0 ?_)
  have h₁ := ContinuousLinearMap.ext_iff.1 hcomp v
  have h₂ := ContinuousLinearMap.ext_iff.1 hcomp w
  simp only [ContinuousLinearMap.comp_apply] at h₁ h₂
  exact h₁.symm.trans ((congrArg _ hvw).trans h₂)

end TauCeti
