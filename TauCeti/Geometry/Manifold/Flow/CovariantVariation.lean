/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.IntegralCurve

/-!
# The covariant variational equation of a time-dependent flow

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional boundaryless
manifold `M`, with time-dependent flow `φ_{s, t} = TauCeti.timeDependentFlowOf X s t`, and let `∇`
be a torsion-free connection on `TM`. Differentiating a two-parameter variation
`(a, t) ↦ φ_{s, t}(c a)` of a trajectory gives, along the trajectory `t ↦ φ_{s, t}(x)`, the
**variational equation**

`∇_t (dφ_{s, t} v) = ∇_{dφ_{s, t} v} X_t`

for every tangent vector `v ∈ T_x M`
(`CovariantDerivative.alongCurve_mfderiv_timeDependentFlowOf`). Its right-hand side is the covariant
derivative of the vector field `X_t` at the moved point, in the direction of the moved vector. The
equation holds at every time at which the flow from `(s, x)` is defined; no completeness of `X`
and no metric are needed.

The proof is the symmetry lemma for parametrized surfaces: for a torsion-free connection the
covariant derivative in `t` of the transverse velocity `∂_a φ_{s, t}(c a)` is the covariant
derivative in `a` of the trajectory velocity `∂_t φ_{s, t}(c a) = X_t(φ_{s, t}(c a))`
(`CovariantDerivative.alongCurve_curveVelocity_eq_covariantDerivative`, which needs the field
equation only at the tested time, so it applies to the field `X_t` frozen at that time). The
transverse velocity of `a ↦ φ_{s, t}(c a)` is `dφ_{s, t}(c' 0)`, and every tangent vector is the
velocity of a smooth curve; for this last step the manifold is assumed boundaryless.

This intrinsic form of the variational equation is the one compared with the linearized Floer
operator at a stationary cylinder, in
`TauCeti.Geometry.Symplectic.Floer.CovariantLinearization`.

The connection-independent facts used here and there, the local regularity of the flow, the
transverse velocity `dφ_{s, t}(c')` and the injectivity of `dφ_{s, t}`, are in
`TauCeti.Geometry.Manifold.Flow.TimeDependent`; the behaviour of `dφ` over one more period of a
periodic field is in `TauCeti.Geometry.Manifold.Flow.Periodic`.

## Main results

* `CovariantDerivative.alongCurve_curveVelocity_timeDependentFlowOf`: the variational equation
  for the transverse velocity of the family of trajectories through a `C²` curve of initial points.
* `CovariantDerivative.alongCurve_mfderiv_timeDependentFlowOf`: the variational equation for the
  derivative `dφ_{s, t}` of the flow.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6
  (variations and the symmetry lemma).
-/

public section

open Bundle Filter Function Set
open TauCeti TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [BoundarylessManifold I M] {X : ℝ → (x : M) → TangentSpace I x} {s t : ℝ}

variable [IsManifold I 2 M]

/-- **The variational equation for a family of trajectories.** Let `X` be a jointly `C²`
time-dependent field on a finite-dimensional boundaryless manifold, let `c` be a curve of initial
points, `C²` at `q`, and let the flow from `(s, c q)` be defined at time `t`. Along the trajectory
`r ↦ φ_{s, r}(c q)`, the transverse velocity `V(r) = ∂_a φ_{s, r}(c a)` at `a = q` satisfies
`∇_t V = ∇_{V(t)} X_t` for every torsion-free connection. -/
theorem alongCurve_curveVelocity_timeDependentFlowOf
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.IsTorsionFree)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {c : ℝ → M} {q : ℝ} (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 2 c q)
    (h : ((s, t), c q) ∈ timeDependentFlowDomain X) :
    alongCurve cov (fun r ↦ timeDependentFlowOf X s r (c q))
        (fun r ↦ curveVelocity I (fun a ↦ timeDependentFlowOf X s r (c a)) q) t =
      cov (X t) (timeDependentFlowOf X s t (c q))
        (curveVelocity I (fun a ↦ timeDependentFlowOf X s t (c a)) q) := by
  have hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun z : ℝ × ℝ ↦ timeDependentFlowOf X s z.2 (c z.1)) (q, t) :=
    contMDiffAt_timeDependentFlowOf_comp (n := 2) (by norm_num) hX
      contMDiffAt_const (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffAt
      (hc.comp (q, t) (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffAt) h
  exact alongCurve_curveVelocity_eq_covariantDerivative (F := fun a r ↦
    timeDependentFlowOf X s r (c a)) cov htor hF
    -- At the frozen time `t`, the field `X_t` is a differentiable section.
    ((hX.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable two_ne_zero _)
    (eventually_curveVelocity_timeDependentFlowOf_eq (hX.of_le (by norm_num)) hc.continuousAt h)

/-- **The covariant variational equation of a time-dependent flow.** For a jointly `C²`
time-dependent field `X` on a finite-dimensional boundaryless manifold and a torsion-free
connection `∇`, the derivative of the flow along the trajectory `r ↦ φ_{s, r}(x)` satisfies
`∇_t (dφ_{s, t} v) = ∇_{dφ_{s, t} v} X_t` at every time `t` at which the flow from `(s, x)` is
defined. -/
theorem alongCurve_mfderiv_timeDependentFlowOf
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.IsTorsionFree)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {x : M} (v : TangentSpace I x) (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    alongCurve cov (fun r ↦ timeDependentFlowOf X s r x)
        (fun r ↦ mfderiv I I (timeDependentFlowOf X s r) x v) t =
      cov (X t) (timeDependentFlowOf X s t x)
        (mfderiv I I (timeDependentFlowOf X s t) x v) := by
  obtain ⟨c, rfl, hc, hvel⟩ := exists_contMDiffAt_curveVelocity_eq (I := I) (n := 2)
    (by norm_num) x v 0
  have hX₁ := hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  -- Near `t` the flow from `(s, c 0)` is defined, so the transverse velocity is `dφ v` there.
  have hdom : ∀ᶠ r in 𝓝 t, ((s, r), c 0) ∈ timeDependentFlowDomain X :=
    (by fun_prop : Continuous fun r : ℝ ↦ ((s, r), c 0)).continuousAt.preimage_mem_nhds
      ((isOpen_timeDependentFlowDomain hX₁).mem_nhds h)
  have hfield : ∀ᶠ r in 𝓝 t,
      curveVelocity I (fun a ↦ timeDependentFlowOf X s r (c a)) 0 =
        mfderiv I I (timeDependentFlowOf X s r) (c 0) v := by
    filter_upwards [hdom] with r hr
    rw [curveVelocity_timeDependentFlowOf_comp hX₁ (hc.mdifferentiableAt two_ne_zero) hr, hvel]
  rw [← alongCurve_congr cov _ _ hfield, ← hfield.self_of_nhds]
  exact alongCurve_curveVelocity_timeDependentFlowOf cov htor hX hc h

end CovariantDerivative
