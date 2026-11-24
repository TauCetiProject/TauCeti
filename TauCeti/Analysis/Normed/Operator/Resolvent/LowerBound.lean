/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import TauCeti.Analysis.Normed.Operator.LinearPMap.SmulSub
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Characterization

/-!
# Resolvents from lower bounds

A surjective shift of a partial linear map that is bounded below has a bounded two-sided
inverse. The inverse bound does not require completeness or closedness of the operator.
This criterion turns domainwise estimates into resolvent existence and operator-norm bounds,
in particular for nonreal shifts of self-adjoint operators. Conversely, a resolvent bound
`‖R‖ ≤ c⁻¹` is the same as the lower bound `c * ‖x‖ ≤ ‖z • x - A x‖` on the domain, and every
resolvent satisfies `‖x‖ ≤ ‖R‖ * ‖z • x - A x‖`. In particular approximate eigenvectors of `A`
for `mu` force `‖z - mu‖⁻¹ ≤ ‖R‖`
(`LinearPMap.IsResolventAt.inv_norm_sub_le_norm_of_tendsto`).

The norm estimates hold on seminormed spaces. The inverse-existence criterion only needs a
normed additive group with a module structure over a commutative ring; it requires no norm on
the scalars or continuity of their action.
-/

public section

namespace LinearPMap

section Seminormed

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {A : E →ₗ.[𝕜] E} {z : 𝕜} {c : ℝ}

/-- The left-inverse identity `R (z • x - A x) = x` bounds every `x ∈ D(A)` through the
resolvent: `‖x‖ ≤ ‖R‖ * ‖z • x - A x‖`. -/
theorem IsResolventAt.norm_le_norm_mul_norm_smul_sub {R : E →L[𝕜] E}
    (hR : IsResolventAt A z R) (x : A.domain) : ‖(x : E)‖ ≤ ‖R‖ * ‖z • (x : E) - A x‖ := by
  simpa only [hR.apply_smul_sub] using R.le_opNorm (z • (x : E) - A x)

/-- A domainwise lower bound for a shift bounds every resolvent of that shift. -/
theorem IsResolventAt.norm_le_inv {R : E →L[𝕜] E} (hR : IsResolventAt A z R)
    (hc : 0 < c) (hbound : ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖z • (x : E) - A x‖) :
    ‖R‖ ≤ c⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have h := hbound ⟨R y, hR.mem_domain y⟩
  rw [hR.smul_sub_apply] at h
  exact (le_inv_mul_iff₀ hc).mpr h

/-- A resolvent of a shift is bounded by `c⁻¹` exactly when the shift is bounded below by `c` on
the domain: `‖R‖ ≤ c⁻¹ ↔ ∀ x ∈ D(A), c * ‖x‖ ≤ ‖z • x - A x‖`. -/
theorem IsResolventAt.norm_le_inv_iff {R : E →L[𝕜] E}
    (hR : IsResolventAt A z R) (hc : 0 < c) :
    ‖R‖ ≤ c⁻¹ ↔ ∀ x : A.domain, c * ‖(x : E)‖ ≤ ‖z • (x : E) - A x‖ := by
  refine ⟨fun hRnorm x => ?_, hR.norm_le_inv hc⟩
  rw [← le_inv_mul_iff₀ hc]
  exact (hR.norm_le_norm_mul_norm_smul_sub x).trans (by gcongr)

open Filter Topology in
/-- **Resolvent norm from approximate eigenvectors.** If `x i ∈ D(A)` with `‖x i‖ ≠ 0` are
approximate eigenvectors of `A` for `mu`, in the sense that `‖A (x i) - mu • x i‖ / ‖x i‖ → 0`
along a nontrivial filter, then every resolvent `R` of `A` at `z` satisfies
`‖z - mu‖⁻¹ ≤ ‖R‖`. -/
theorem IsResolventAt.inv_norm_sub_le_norm_of_tendsto {R : E →L[𝕜] E}
    (hR : IsResolventAt A z R) {mu : 𝕜} {ι : Type*} {l : Filter ι} [l.NeBot]
    (x : ι → A.domain) (hx : ∀ᶠ i in l, ‖(x i : E)‖ ≠ 0)
    (h : Tendsto (fun i => ‖A (x i) - mu • (x i : E)‖ / ‖(x i : E)‖) l (𝓝 0)) :
    ‖z - mu‖⁻¹ ≤ ‖R‖ := by
  -- Each `x i` gives `1 ≤ ‖R‖ * (‖z - mu‖ + ‖A (x i) - mu • x i‖ / ‖x i‖)`.
  have key : ∀ i, ‖(x i : E)‖ ≠ 0 →
      1 ≤ ‖R‖ * (‖z - mu‖ + ‖A (x i) - mu • (x i : E)‖ / ‖(x i : E)‖) := by
    intro i hxi
    -- Split `z x - A x = (z - mu) x - (A x - mu x)` and use the triangle inequality.
    have hle : ‖(x i : E)‖ ≤
        ‖R‖ * (‖z - mu‖ * ‖(x i : E)‖ + ‖A (x i) - mu • (x i : E)‖) :=
      calc ‖(x i : E)‖ ≤ ‖R‖ * ‖z • (x i : E) - A (x i)‖ :=
            hR.norm_le_norm_mul_norm_smul_sub (x i)
        _ = ‖R‖ * ‖(z - mu) • (x i : E) - (A (x i) - mu • (x i : E))‖ := by
            rw [sub_smul, sub_sub_sub_cancel_right]
        _ ≤ ‖R‖ * (‖(z - mu) • (x i : E)‖ + ‖A (x i) - mu • (x i : E)‖) := by
            gcongr
            exact norm_sub_le _ _
        _ = _ := by rw [norm_smul]
    calc 1 = ‖(x i : E)‖ / ‖(x i : E)‖ := (div_self hxi).symm
      _ ≤ ‖R‖ * (‖z - mu‖ * ‖(x i : E)‖ + ‖A (x i) - mu • (x i : E)‖) / ‖(x i : E)‖ := by
          gcongr
      _ = _ := by rw [mul_div_assoc, add_div, mul_div_cancel_right₀ _ hxi]
  -- Let the approximation error tend to zero.
  have hlim : Tendsto (fun i => ‖R‖ *
      (‖z - mu‖ + ‖A (x i) - mu • (x i : E)‖ / ‖(x i : E)‖)) l (𝓝 (‖R‖ * ‖z - mu‖)) := by
    simpa using (tendsto_const_nhds.add h).const_mul ‖R‖
  have h1 : 1 ≤ ‖R‖ * ‖z - mu‖ := ge_of_tendsto hlim (hx.mono key)
  have hpos : 0 < ‖z - mu‖ :=
    (norm_nonneg _).lt_of_ne fun h0 => by rw [← h0, mul_zero] at h1; norm_num at h1
  rwa [inv_le_iff_one_le_mul₀ hpos]

end Seminormed

section Normed

variable {𝕜 E : Type*} [CommRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E]
  {A : E →ₗ.[𝕜] E} {z : 𝕜} {c : ℝ}

/-- A surjective shift bounded below by a positive constant has a bounded two-sided inverse. -/
theorem mem_resolventSet_of_surjective_of_norm_le
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

end Normed

end LinearPMap
