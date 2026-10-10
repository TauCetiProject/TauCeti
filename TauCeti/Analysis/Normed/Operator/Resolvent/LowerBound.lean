/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import TauCeti.Analysis.Normed.Operator.LinearPMap.SmulSub

/-!
# Resolvents from lower bounds

A surjective shift of a partial linear map that is bounded below has a bounded two-sided
inverse. The inverse bound does not require completeness or closedness of the operator.
This criterion turns domainwise estimates into resolvent existence and operator-norm bounds,
in particular for nonreal shifts of self-adjoint operators.
-/

public section

noncomputable section

namespace TauCeti

open _root_.LinearPMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {z : 𝕜} {c : ℝ}

/-- A domainwise lower bound for a shift bounds every resolvent of that shift. -/
theorem _root_.LinearPMap.IsResolventAt.norm_le_inv {R : E →L[𝕜] E} (hR : IsResolventAt A z R)
    (hc : 0 < c) (hbound : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖z • (x : E) - A x‖) :
    ‖R‖ ≤ c⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have h := hbound ⟨R y, hR.mem_domain y⟩
  rw [hR.smul_sub_apply] at h
  exact (le_inv_mul_iff₀ hc).mpr h

/-- A surjective shift bounded below by a positive constant has a bounded two-sided inverse. -/
theorem _root_.LinearPMap.mem_resolventSet_of_surjective_of_norm_le
    (hsurj : Function.Surjective fun x : A.domain => z • (x : E) - A x)
    (hc : 0 < c) (hbound : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖z • (x : E) - A x‖) :
    z ∈ A.resolventSet := by
  have hinj : Function.Injective (A.smulSub z) := fun x y h =>
    smul_sub_injective_of_norm_le hc hbound (by simpa only [smulSub_apply] using h)
  have hsurj' : Function.Surjective (A.smulSub z) := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨x, by rw [smulSub_apply]; exact hx⟩
  let e := LinearEquiv.ofBijective (A.smulSub z) ⟨hinj, hsurj'⟩
  let J : E →ₗ[𝕜] E := A.domain.subtype.comp e.symm.toLinearMap
  have hJ (y : E) : J y = (e.symm y : E) := (rfl)
  have hright (y : E) : z • (e.symm y : E) - A (e.symm y) = y := by
    rw [← smulSub_apply]
    exact e.apply_symm_apply y
  have hnorm (y : E) : ‖J y‖ ≤ c⁻¹ * ‖y‖ := by
    rw [hJ, le_inv_mul_iff₀ hc]
    simpa only [hright] using hbound (e.symm y)
  let R := J.mkContinuous c⁻¹ hnorm
  have hR (y : E) : R y = (e.symm y : E) := by
    rw [LinearMap.mkContinuous_apply, hJ]
  refine IsResolventAt.mem_resolventSet (R := R) ⟨fun y => ?_, fun y => ?_, fun x => ?_⟩
  · rw [hR]
    exact (e.symm y).property
  · have hx : (⟨R y, by rw [hR]; exact (e.symm y).property⟩ : A.domain) = e.symm y :=
      Subtype.ext (hR y)
    simpa only [hx, hR] using hright y
  · rw [hR, ← smulSub_apply]
    exact congrArg Subtype.val (e.symm_apply_apply x)

end TauCeti
