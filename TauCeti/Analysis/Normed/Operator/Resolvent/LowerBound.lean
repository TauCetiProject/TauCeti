/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import TauCeti.Analysis.Normed.Operator.LinearPMap.SmulSub
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Characterization

/-!
# Resolvents from lower bounds

A surjective shift of a partial linear map that is bounded below has a bounded two-sided
inverse. The inverse bound does not require completeness or closedness of the operator.
This criterion turns domainwise estimates into resolvent existence and operator-norm bounds,
in particular for nonreal shifts of self-adjoint operators. Conversely, a resolvent bound
`‖R‖ ≤ c⁻¹` is the same as the lower bound `c * ‖x‖ ≤ ‖z • x - A x‖` on the domain.
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

/-- A resolvent of a shift is bounded by `c⁻¹` exactly when the shift is bounded below by `c` on
the domain: `‖R‖ ≤ c⁻¹ ↔ ∀ x ∈ D(A), c * ‖x‖ ≤ ‖z • x - A x‖`. -/
theorem _root_.LinearPMap.IsResolventAt.norm_le_inv_iff {R : E →L[𝕜] E}
    (hR : IsResolventAt A z R) (hc : 0 < c) :
    ‖R‖ ≤ c⁻¹ ↔ ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖z • (x : E) - A x‖ := by
  refine ⟨fun hRnorm x => ?_, hR.norm_le_inv hc⟩
  rw [← le_inv_mul_iff₀ hc]
  calc ‖(x : E)‖ = ‖R (z • (x : E) - A x)‖ := by rw [hR.apply_smul_sub]
    _ ≤ ‖R‖ * ‖z • (x : E) - A x‖ := R.le_opNorm _
    _ ≤ c⁻¹ * ‖z • (x : E) - A x‖ := by gcongr

/-- A surjective shift bounded below by a positive constant has a bounded two-sided inverse. -/
theorem _root_.LinearPMap.mem_resolventSet_of_surjective_of_norm_le
    (hsurj : Function.Surjective fun x : A.domain => z • (x : E) - A x)
    (hc : 0 < c) (hbound : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖z • (x : E) - A x‖) :
    z ∈ A.resolventSet := by
  obtain ⟨J, hJ, hright, hleft⟩ :=
    exists_linearMap_inverse_smul_sub ⟨smul_sub_injective_of_norm_le hc hbound, hsurj⟩
  have hnorm (y : E) : ‖J y‖ ≤ c⁻¹ * ‖y‖ := by
    rw [le_inv_mul_iff₀ hc]
    simpa only [hright] using hbound ⟨J y, hJ y⟩
  refine IsResolventAt.mem_resolventSet (R := J.mkContinuous c⁻¹ hnorm)
    (isResolventAt_iff_surjective_and_apply_smul_sub.mpr ⟨hsurj, fun x => ?_⟩)
  rw [LinearMap.mkContinuous_apply, hleft]

end TauCeti
