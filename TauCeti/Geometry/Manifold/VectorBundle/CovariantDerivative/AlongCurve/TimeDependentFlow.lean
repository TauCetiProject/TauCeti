/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.IntegralCurve

/-!
# The variational equation of a time-dependent flow

Let `X` be a jointly `C²` time-dependent vector field on a finite-dimensional boundaryless
manifold `M`, with time-dependent flow `φ_{s,t} = TauCeti.timeDependentFlowOf X s t`, and let `∇`
be a torsion-free connection on `TM`. For a point `x` and a tangent vector `v ∈ T_x M`, the
linearized flow `V(t) = dφ_{s,t}(x) v` is a vector field along the trajectory
`γ(t) = φ_{s,t}(x)`. It solves the **variational equation**

`D_t V = ∇_V X_t`,  `V(s) = v`,

wherever the flow is defined (`CovariantDerivative.alongCurve_mfderiv_timeDependentFlowOf`,
with the initial value `TauCeti.mfderiv_timeDependentFlowOf_self`). Its right-hand side is the
covariant derivative of the vector field `X_t` at the moved point, in the direction of the moved
vector. No completeness of `X` and no metric are assumed: the equation holds at every time `t`
with `((s, t), x)` in the flow domain.

The proof is the symmetry lemma for parametrized surfaces: for a torsion-free connection the
covariant derivative in `t` of the transverse velocity `∂_a φ_{s,t}(c a)` of a family of
trajectories is the covariant derivative in `a` of the trajectory velocity
`∂_t φ_{s,t}(c a) = X_t(φ_{s,t}(c a))`
(`CovariantDerivative.alongCurve_curveVelocity_eq_covariantDerivative`, which needs the field
equation only at the tested time, so it applies to the field `X_t` frozen at that time). This
gives the variational equation for the family
(`CovariantDerivative.alongCurve_curveVelocity_timeDependentFlowOf`). The transverse velocity of
`a ↦ φ_{s,t}(c a)` is `dφ_{s,t}(c' 0)` by the chain rule, and every tangent vector is the
velocity of a smooth curve; for this last step the manifold is assumed boundaryless.

For a time-dependent Hamiltonian `H`, with `X_t` the Hamiltonian vector field of `H_t`, this is
the equation satisfied by the linearized Hamiltonian flow along a trajectory, whose solutions at
a one-periodic orbit give the linearized return map entering the Conley–Zehnder index and the
asymptotic operators of Floer cylinders. It is the form compared with the linearized Floer
operator at a stationary cylinder, in `TauCeti.Geometry.Symplectic.Floer.CovariantLinearization`.

## Main results

* `CovariantDerivative.alongCurve_curveVelocity_timeDependentFlowOf`: the variational equation
  for the transverse velocity of the family of trajectories through a `C²` curve of initial points.
* `CovariantDerivative.alongCurve_mfderiv_timeDependentFlowOf`: the variational equation
  `D_t (dφ_{s,t} v) = ∇_{dφ_{s,t} v} X_t` along the trajectory through `x`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6
  (variations and the symmetry lemma).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, the linearized flow along a periodic orbit.
-/

public section

open Bundle Filter Set
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

open TauCeti TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [BoundarylessManifold I M]
  [IsManifold I 2 M] {X : ℝ → Π x : M, TangentSpace I x} {s t : ℝ} {x : M}

/-- **The variational equation for a family of trajectories.** Let `X` be a jointly `C²`
time-dependent field on a finite-dimensional boundaryless manifold, let `c` be a curve of initial
points, `C²` at `q`, and let the flow from `(s, c q)` be defined at time `t`. Along the trajectory
`r ↦ φ_{s,r}(c q)`, the transverse velocity `V(r) = ∂_a φ_{s,r}(c a)` at `a = q` satisfies
`D_t V = ∇_{V(t)} X_t` for every torsion-free connection. -/
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

/-- **The variational equation of a time-dependent flow.** Let `X` be a jointly `C²`
time-dependent vector field with time-dependent flow `φ_{s,t}`, and `∇` a torsion-free
connection. If the flow from time `s` is defined at `x` up to time `t`, the linearized flow
`V(u) = dφ_{s,u}(x) v` along the trajectory `u ↦ φ_{s,u}(x)` satisfies
`D_t V = ∇_{V(t)} X_t` at `t`. -/
theorem alongCurve_mfderiv_timeDependentFlowOf
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) (htor : cov.IsTorsionFree)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (h : ((s, t), x) ∈ timeDependentFlowDomain X) (v : TangentSpace I x) :
    alongCurve cov (fun u ↦ timeDependentFlowOf X s u x)
        (fun u ↦ mfderiv I I (timeDependentFlowOf X s u) x v) t =
      cov (X t) (timeDependentFlowOf X s t x) (mfderiv I I (timeDependentFlowOf X s t) x v) := by
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
