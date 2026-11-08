/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic

/-!
# The Eulerian velocity field of a smooth family of diffeomorphisms

Let `φ_t`, `t ∈ ℝ`, be a family of bijections of a manifold `M`, jointly smooth in `(t, x)` and with
jointly smooth inverses, such as a smooth isotopy. Its **Eulerian velocity field** is the
time-dependent vector field

`X_t = (∂_t φ_t) ∘ φ_t⁻¹`, that is, `X_t(y) = ∂_u|_{u = t} φ_u(φ_t⁻¹ y)`

(`TauCeti.eulerianField`). It is the time-dependent vector field generating the family: every curve
`u ↦ φ_u x` has velocity `X_u (φ_u x)` (`TauCeti.hasMFDerivAt_eulerianField`), and the field is
jointly `C^m` when the family is `C^(m+1)` and its inverses are `C^m`
(`TauCeti.contMDiff_eulerianField`). Consequently the suspension of `X` is complete
(`TauCeti.isCompleteVectorField_timeDependentSuspensionField_eulerianField`), and on a Hausdorff
boundaryless manifold, where integral curves of a `C¹` field are unique, the time-dependent flow of
`X` from time `s` to time `t` is `φ_t ∘ φ_s⁻¹` (`TauCeti.timeDependentFlowOf_eulerianField`). This
lets every statement about time-dependent flows be applied to smooth isotopies.

The field transforms under the pointwise operations on families as follows. For the pointwise
composition `(φ ψ)_t = φ_t ∘ ψ_t` one has the **product velocity identity**

`X_(φ ψ) = X_φ + (φ_t)_* X_ψ`

(`TauCeti.eulerianField_trans`), and for the pointwise inverse `X_(φ⁻¹) = -(φ_t⁻¹)_* X_φ`
(`TauCeti.eulerianField_symm`). A constant family has zero velocity
(`TauCeti.eulerianField_const`).

These are the identities used to define the flux of a symplectic isotopy, whose velocity one-forms
are the contractions `ι_(X_t) ω` of the symplectic form with the Eulerian field.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Chapter 3 (the time-dependent vector field generating an isotopy) and Chapter 10
  (the flux homomorphism).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Theorem 9.48
  (time-dependent flows).
-/

public section

noncomputable section

open Set Bundle TauCeti.Manifold
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]

/-- The **Eulerian velocity field** of a family `φ` of bijections of `M`: the time-dependent vector
field `X_t(y) = ∂_u|_{u = t} φ_u(φ_t⁻¹ y)`, that is `X_t = (∂_t φ_t) ∘ φ_t⁻¹`. For a smooth isotopy
it is the time-dependent vector field whose flow is the isotopy. -/
def eulerianField (φ : ℝ → M ≃ M) (t : ℝ) (y : M) : TangentSpace I y :=
  curveVelocity I (fun u ↦ φ u ((φ t).symm y)) t

variable {I} {φ ψ : ℝ → M ≃ M} {t : ℝ}

/-- The Eulerian velocity field at `y` is the velocity at time `t` of the curve
`u ↦ φ_u(φ_t⁻¹ y)`. This restates the definition, whose body is not exposed. -/
theorem eulerianField_def (y : M) :
    eulerianField I φ t y = curveVelocity I (fun u ↦ φ u ((φ t).symm y)) t :=
  (rfl)

/-- At the image point `φ_t x`, the Eulerian velocity field is the velocity at time `t` of the
curve `u ↦ φ_u x`. -/
@[simp]
theorem eulerianField_apply_apply (x : M) :
    eulerianField I φ t (φ t x) = curveVelocity I (fun u ↦ φ u x) t := by
  have h : (fun u ↦ φ u ((φ t).symm (φ t x))) = fun u ↦ φ u x := by
    simp only [Equiv.symm_apply_apply]
  rw [eulerianField_def, h]

/-- **The Eulerian field generates the family.** If the curve `u ↦ φ_u x` is differentiable at
time `t`, its velocity there is the Eulerian velocity field at its current position,
`X_t (φ_t x)`. -/
theorem hasMFDerivAt_eulerianField {x : M}
    (h : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ φ u x) t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun u ↦ φ u x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (eulerianField I φ t (φ t x))) := by
  rw [eulerianField_apply_apply]
  exact hasMFDerivAt_curveVelocity h

/-- A constant family has zero Eulerian velocity. -/
@[simp]
theorem eulerianField_const (e : M ≃ M) : eulerianField I (fun _ ↦ e) = 0 := by
  funext t y
  exact curveVelocity_const _

/-! ### Products and inverses of families -/

/-- **The product velocity identity.** The Eulerian field of the pointwise composition
`(φ ψ)_t = φ_t ∘ ψ_t` of two families is `X_(φ ψ) = X_φ + (φ_t)_* X_ψ`: at the point `φ_t w`, it
is the sum of `X_φ(φ_t w)` and of the image under `dφ_t` of `X_ψ(w)`. -/
theorem eulerianField_trans {w : M}
    (hφ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M ↦ φ p.1 p.2) (t, w))
    (hψ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ ψ u ((ψ t).symm w)) t) :
    eulerianField I (fun u ↦ (ψ u).trans (φ u)) t (φ t w) =
      eulerianField I φ t (φ t w) + mfderiv I I (φ t) w (eulerianField I ψ t w) := by
  set γ : ℝ → M := fun u ↦ ψ u ((ψ t).symm w)
  have hγt : γ t = w := (ψ t).apply_symm_apply w
  have h := curveVelocity_apply_curve (f := fun u ↦ φ u) (γ := γ) (hγt ▸ hφ) hψ
  rw [hγt] at h
  have hfun : (fun u ↦ ((ψ u).trans (φ u)) (((ψ t).trans (φ t)).symm (φ t w))) =
      fun u ↦ φ u (γ u) := by
    funext u
    simp [γ]
  rw [eulerianField_def, hfun, h, eulerianField_apply_apply, eulerianField_def (φ := ψ) w]

/-- **The inverse velocity identity.** The Eulerian field of the pointwise inverse
`t ↦ φ_t⁻¹` of a family is `X_(φ⁻¹) = -(φ_t⁻¹)_* X_φ`: at the point `φ_t⁻¹ z`, it is minus the
image under `d(φ_t⁻¹)` of `X_φ(z)`. -/
theorem eulerianField_symm {z : M}
    (hφ : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I (fun p : ℝ × M ↦ (φ p.1).symm p.2) (t, z))
    (hφ' : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun u ↦ φ u ((φ t).symm z)) t) :
    eulerianField I (fun u ↦ (φ u).symm) t ((φ t).symm z) =
      -mfderiv I I (φ t).symm z (eulerianField I φ t z) := by
  have h := eulerianField_trans (φ := fun u ↦ (φ u).symm) (ψ := φ) (t := t) (w := z) hφ hφ'
  simp only [Equiv.self_trans_symm, eulerianField_const, Pi.zero_apply] at h
  rw [eq_neg_iff_add_eq_zero, ← h]

/-! ### Smoothness -/

/-- **The Eulerian field is jointly smooth.** If the family `(t, x) ↦ φ_t x` is `C^n` and its
inverses `(t, y) ↦ φ_t⁻¹ y` are `C^m`, with `m + 1 ≤ n`, then the Eulerian velocity field is a
jointly `C^m` time-dependent vector field. -/
theorem contMDiff_eulerianField [IsManifold I 1 M] {m n : ℕ∞ω} (hmn : m + 1 ≤ n)
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I n (fun p : ℝ × M ↦ φ p.1 p.2))
    (hφ' : ContMDiff (𝓘(ℝ, ℝ).prod I) I m (fun p : ℝ × M ↦ (φ p.1).symm p.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent m
      (fun p : ℝ × M ↦ (⟨p.2, eulerianField I φ p.1 p.2⟩ : TangentBundle I M)) := by
  have hn : 1 ≤ n := le_trans (by simp) hmn
  -- The Eulerian field is the derivative of `(u, x) ↦ φ_u x` in the direction `(1, 0)` at the
  -- point `(t, φ_t⁻¹ y)`, and this velocity is `C^m` along `(t, y) ↦ (t, φ_t⁻¹ y)`.
  refine ((Manifold.contMDiff_mfderiv_apply_one_zero hφ hmn).comp
    (contMDiff_fst.prodMk hφ')).congr fun p ↦ ?_
  have hdiff : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I (fun q : ℝ × M ↦ φ q.1 q.2)
      (p.1, (φ p.1).symm p.2) :=
    (hφ _).mdifferentiableAt (zero_lt_one.trans_le hn).ne'
  refine TotalSpace.ext ((φ p.1).apply_symm_apply p.2).symm (heq_of_eq ?_)
  -- By definition of `tangentMap` and of `equivTangentBundleProd`, the fibre of the left side is
  -- the derivative of `(u, x) ↦ φ_u x` applied to `(1, 0)`; `change` exposes this unfolding.
  change eulerianField I φ p.1 p.2 =
    mfderiv (𝓘(ℝ, ℝ).prod I) I (fun q : ℝ × M ↦ φ q.1 q.2) (p.1, (φ p.1).symm p.2) (1, 0)
  refine Eq.trans ?_ (mfderiv_prod_eq_add_apply hdiff).symm
  rw [eulerianField_def, curveVelocity_apply]
  exact (add_zero _).symm.trans (congrArg₂ (· + ·) rfl (map_zero _).symm)

/-! ### The time-dependent flow of the Eulerian field -/

section Flow

variable (hφ : ∀ x, MDifferentiable 𝓘(ℝ, ℝ) I fun u ↦ φ u x)
include hφ

/-- If every curve `u ↦ φ_u x` is differentiable, the suspension of the Eulerian field is complete:
its time-dependent flow is defined for all pairs of times. -/
theorem isCompleteVectorField_timeDependentSuspensionField_eulerianField :
    IsCompleteVectorField (timeDependentSuspensionField (eulerianField I φ)) := by
  refine isCompleteVectorField_iff_maximalIntegralCurveInterval.2 fun ⟨s, x⟩ ↦
    eq_univ_of_forall fun τ ↦ TauCeti.mem_flowDomain.1 ?_
  have h := mem_timeDependentFlowDomain_of_hasMFDerivAt (s := s) (t := s + τ)
    (γ := fun u ↦ φ u ((φ s).symm x)) (a := min s (s + τ) - 1) (b := max s (s + τ) + 1)
    (fun u _ ↦ hasMFDerivAt_eulerianField (hφ _ u))
    ⟨by linarith [min_le_left s (s + τ)], by linarith [le_max_left s (s + τ)]⟩
    ⟨by linarith [min_le_right s (s + τ)], by linarith [le_max_right s (s + τ)]⟩
  simpa [mem_timeDependentFlowDomain] using h

/-- **The isotopy is the flow of its Eulerian field.** For a family whose curves `u ↦ φ_u x` are
differentiable and whose Eulerian field is jointly `C¹`, the time-dependent flow of that field from
time `s` to time `t` is `φ_t ∘ φ_s⁻¹`. -/
theorem timeDependentFlowOf_eulerianField [T2Space M] [IsManifold I 1 M]
    [BoundarylessManifold I M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, eulerianField I φ p.1 p.2⟩ : TangentBundle I M)))
    (s t : ℝ) (x : M) :
    timeDependentFlowOf (eulerianField I φ) s t x = φ t ((φ s).symm x) := by
  have h := timeDependentFlowOf_eq_of_hasMFDerivAt hX (s := s) (t := t)
    (γ := fun u ↦ φ u ((φ s).symm x)) (a := min s t - 1) (b := max s t + 1)
    (fun u _ ↦ hasMFDerivAt_eulerianField (hφ _ u))
    ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩
    ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩
  simpa using h

end Flow

end TauCeti
