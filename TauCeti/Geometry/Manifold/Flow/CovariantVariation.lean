/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic
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
(`TauCeti.alongCurve_mfderiv_timeDependentFlowOf`). Its right-hand side is the covariant
derivative of the vector field `X_t` at the moved point, in the direction of the moved vector. The
equation holds at every time at which the flow from `(s, x)` is defined; no completeness of `X`
and no metric are needed.

The proof is the symmetry lemma for parametrized surfaces: for a torsion-free connection the
covariant derivative in `t` of the transverse velocity `∂_a φ_{s, t}(c a)` is the covariant
derivative in `a` of the trajectory velocity `∂_t φ_{s, t}(c a) = X_t(φ_{s, t}(c a))`
(`CovariantDerivative.alongCurve_curveVelocity_eq_covariantDerivative`, which needs the field
equation only at the tested time, so it applies to the field `X_t` frozen at that time). The
transverse velocity of `a ↦ φ_{s, t}(c a)` is `dφ_{s, t}(c' 0)`, and every tangent vector is the
velocity of a smooth curve; for this last step the model is assumed boundaryless.

This intrinsic form of the variational equation is the one compared with the linearized Floer
operator at a stationary cylinder, in
`TauCeti.Geometry.Symplectic.Floer.CovariantLinearization`.

For a time-periodic field and a point returning to itself after one period, the derivative of
the flow over one more period is the derivative over the first period followed by that of the
return map (`TauCeti.mfderiv_timeDependentFlowOf_add_period_apply`). So a vector fixed by the
derivative of the return map spreads along the periodic orbit to a periodic solution of the
variational equation (`TauCeti.mfderiv_timeDependentFlowOf_add_period_apply_of_eq`): this is how
degeneracy of a periodic orbit produces periodic solutions of the linearized equation. Flowing
back is a local left inverse of the flow, so its derivative is injective
(`TauCeti.injective_mfderiv_timeDependentFlowOf`) and these solutions vanish nowhere.

## Main results

* `TauCeti.alongCurve_curveVelocity_timeDependentFlowOf`: the variational equation for the
  transverse velocity of the family of trajectories through a `C²` curve of initial points.
* `TauCeti.alongCurve_mfderiv_timeDependentFlowOf`: the variational equation for the derivative
  `dφ_{s, t}` of the flow.
* `TauCeti.mfderiv_timeDependentFlowOf_add_period_apply`: for a periodic field, the derivative of
  the flow over one more period factors through the derivative of the return map.
* `TauCeti.injective_mfderiv_timeDependentFlowOf`: the derivative of the flow is injective
  wherever the flow is defined.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6
  (variations and the symmetry lemma).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 8.1 (linearized Hamiltonian flows and nondegenerate orbits).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2.
-/

public section

open Bundle CovariantDerivative Filter Function Set
open TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [BoundarylessManifold I M] {X : ℝ → (x : M) → TangentSpace I x} {s t : ℝ}

/-- The time-dependent flow of a jointly `C^n` field, `1 ≤ n`, is `C^n` near every point of its
domain, as a function of the final time and the initial point. -/
theorem contMDiffAt_timeDependentFlowOf_comp [IsManifold I 1 M] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M] {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {τ : N → ℝ} {c : N → M} {z : N} (hτ : ContMDiffAt J 𝓘(ℝ, ℝ) n τ z)
    (hc : ContMDiffAt J I n c z) (h : ((s, τ z), c z) ∈ timeDependentFlowDomain X) :
    ContMDiffAt J I n (fun y ↦ timeDependentFlowOf X s (τ y) (c y)) z := by
  have hflow : ContMDiffAt ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I n
      (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) ((s, τ z), c z) :=
    (contMDiffOn_timeDependentFlowOf hn hX).contMDiffAt
      ((isOpen_timeDependentFlowDomain (hX.of_le (by exact_mod_cast hn))).mem_nhds h)
  exact hflow.comp z ((contMDiffAt_const.prodMk hτ).prodMk hc)

/-- The time map of the time-dependent flow of a jointly `C^n` field, `1 ≤ n`, is `C^n` at every
point at which it is defined. -/
theorem contMDiffAt_timeDependentFlowOf [IsManifold I 1 M] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {x : M} (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    ContMDiffAt I I n (timeDependentFlowOf X s t) x :=
  contMDiffAt_timeDependentFlowOf_comp hn hX contMDiffAt_const contMDiffAt_id h

/-- Near a point of the domain of the flow from time `s`, the trajectories through the points of
a continuous curve of initial points solve the field equation at time `t`. -/
theorem eventually_curveVelocity_timeDependentFlowOf_eq [IsManifold I 1 M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {c : ℝ → M} {q : ℝ} (hc : ContinuousAt c q)
    (h : ((s, t), c q) ∈ timeDependentFlowDomain X) :
    ∀ᶠ r in 𝓝 q, curveVelocity I (fun u ↦ timeDependentFlowOf X s u (c r)) t =
      X t (timeDependentFlowOf X s t (c r)) := by
  have hdom : ∀ᶠ r in 𝓝 q, ((s, t), c r) ∈ timeDependentFlowDomain X :=
    (continuousAt_const.prodMk hc).preimage_mem_nhds
      ((isOpen_timeDependentFlowDomain hX).mem_nhds h)
  filter_upwards [hdom] with r hr
  simpa only [curveVelocityWithin_univ] using curveVelocityWithin_eq_of_hasMFDerivWithinAt
    (hasMFDerivAt_timeDependentFlowOf hX hr).hasMFDerivWithinAt uniqueDiffWithinAt_univ

variable [IsManifold I 2 M]

/-- **The variational equation for a family of trajectories.** Let `c` be a curve of initial
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
      (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffAt
      (hc.comp (q, t) (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffAt) h
  exact alongCurve_curveVelocity_eq_covariantDerivative (F := fun a r ↦
    timeDependentFlowOf X s r (c a)) cov htor hF
    -- At the frozen time `t`, the field `X_t` is a differentiable section.
    ((hX.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable two_ne_zero _)
    (eventually_curveVelocity_timeDependentFlowOf_eq (hX.of_le (by norm_num)) hc.continuousAt h)

/-- The transverse velocity of the trajectories through a curve of initial points is the
derivative of the flow applied to the velocity of the curve. -/
theorem curveVelocity_timeDependentFlowOf_comp
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {c : ℝ → M} {q : ℝ} (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c q)
    (h : ((s, t), c q) ∈ timeDependentFlowDomain X) :
    curveVelocity I (fun a ↦ timeDependentFlowOf X s t (c a)) q =
      mfderiv I I (timeDependentFlowOf X s t) (c q) (curveVelocity I c q) := by
  have hφ : MDifferentiableAt I I (timeDependentFlowOf X s t) (c q) :=
    (contMDiffAt_timeDependentFlowOf (n := 2) (by norm_num) hX
      h).mdifferentiableAt two_ne_zero
  simpa only [curveVelocityWithin_univ, Function.comp_def] using
    curveVelocityWithin_map hφ uniqueDiffWithinAt_univ hc.mdifferentiableWithinAt

/-- **The covariant variational equation of a time-dependent flow.** For a jointly `C²`
time-dependent field `X` on a finite-dimensional boundaryless manifold and a torsion-free
connection `∇`, the derivative of the flow along the trajectory `r ↦ φ_{s, r}(x)` satisfies
`∇_t (dφ_{s, t} v) = ∇_{dφ_{s, t} v} X_t` at every time `t` at which the flow from `(s, x)` is
defined. -/
theorem alongCurve_mfderiv_timeDependentFlowOf [I.Boundaryless]
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
    rw [curveVelocity_timeDependentFlowOf_comp hX (hc.mdifferentiableAt two_ne_zero) hr, hvel]
  rw [← alongCurve_congr cov _ _ hfield, ← hfield.self_of_nhds]
  exact alongCurve_curveVelocity_timeDependentFlowOf cov htor hX hc h

/-- **The derivative of the flow over one more period.** Let `X` be a `T`-periodic jointly `C²`
field, `T ≠ 0`, and let `x` be a fixed point of the return map `φ_{s, s + T}`. Then the flow from
`(s, x)` exists for all time, and its derivative at time `t + T` is that of the return map followed
by that at time `t`: `dφ_{s, t + T} v = dφ_{s, t} (dφ_{s, s + T} v)`. -/
theorem mfderiv_timeDependentFlowOf_add_period_apply {T : ℝ} {x : M} (hT : Periodic X T)
    (hT0 : T ≠ 0)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (h : ((s, s + T), x) ∈ timeDependentFlowDomain X)
    (hfix : IsFixedPt (timeDependentFlowOf X s (s + T)) x) (t : ℝ) (v : TangentSpace I x) :
    mfderiv I I (timeDependentFlowOf X s (t + T)) x v =
      mfderiv I I (timeDependentFlowOf X s t) x
        (mfderiv I I (timeDependentFlowOf X s (s + T)) x v) := by
  have hX₁ := hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hopen := isOpen_timeDependentFlowDomain hX₁
  set R := timeDependentFlowOf X s (s + T)
  have hall (u : ℝ) := mem_timeDependentFlowDomain_of_isFixedPt hX₁ hT hT0 h hfix u
  have hR : ContMDiffAt I I 2 R x :=
    contMDiffAt_timeDependentFlowOf (n := 2) (by norm_num) hX h
  have hRt : ((s, t), R x) ∈ timeDependentFlowDomain X := by
    rw [hfix.eq]
    exact hall t
  -- Near `x`, flowing to `t + T` is the return map followed by the flow to `t`.
  have heq : timeDependentFlowOf X s (t + T) =ᶠ[𝓝 x] timeDependentFlowOf X s t ∘ R := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
        (hopen.mem_nhds h),
      (continuousAt_const.prodMk hR.continuousAt).preimage_mem_nhds (hopen.mem_nhds hRt)]
      with y h₁ h₂
    obtain ⟨hmem, hshift⟩ := timeDependentFlowOf_add_period_of_mem hX₁ hT h₂
    exact (timeDependentFlowOf_trans_of_mem hX₁ h₁ hmem).2.symm.trans hshift
  have hφ : MDifferentiableAt I I (timeDependentFlowOf X s t) (R x) :=
    (contMDiffAt_timeDependentFlowOf (n := 2) (by norm_num) hX
      hRt).mdifferentiableAt two_ne_zero
  rw [heq.mfderiv_eq, mfderiv_comp x hφ (hR.mdifferentiableAt two_ne_zero)]
  -- The two sides differ by the identity cast between the tangent spaces at `R x = x`.
  have hcast : ∀ y, y = x → mfderiv I I (timeDependentFlowOf X s t) y (mfderiv I I R x v) =
      mfderiv I I (timeDependentFlowOf X s t) x (mfderiv I I R x v) := by
    rintro _ rfl
    rfl
  exact hcast _ hfix.eq

/-- **Periodic solutions of the variational equation.** If `X` is `T`-periodic, `T ≠ 0`, `x` is a
fixed point of the return map `φ_{s, s + T}`, and `v` is fixed by its derivative, then the
solution `t ↦ dφ_{s, t} v` of the variational equation along the periodic orbit of `x` is
`T`-periodic. -/
theorem mfderiv_timeDependentFlowOf_add_period_apply_of_eq {T : ℝ} {x : M} (hT : Periodic X T)
    (hT0 : T ≠ 0)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (h : ((s, s + T), x) ∈ timeDependentFlowDomain X)
    (hfix : IsFixedPt (timeDependentFlowOf X s (s + T)) x) {v : TangentSpace I x}
    (hv : mfderiv I I (timeDependentFlowOf X s (s + T)) x v = v) (t : ℝ) :
    mfderiv I I (timeDependentFlowOf X s (t + T)) x v =
      mfderiv I I (timeDependentFlowOf X s t) x v := by
  rw [mfderiv_timeDependentFlowOf_add_period_apply hT hT0 hX h hfix t v, hv]

/-- **The derivative of the flow is injective.** Wherever the time-dependent flow from `s` to `t`
is defined at `x`, flowing back from `t` to `s` is a left inverse near `x`, so `dφ_{s, t}` is
injective at `x`. No completeness of the field is needed. -/
theorem injective_mfderiv_timeDependentFlowOf {x : M}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    Injective (mfderiv I I (timeDependentFlowOf X s t) x) := by
  have hX₁ := hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hφ : MDifferentiableAt I I (timeDependentFlowOf X s t) x :=
    (contMDiffAt_timeDependentFlowOf (n := 2) (by norm_num) hX
      h).mdifferentiableAt two_ne_zero
  have hψ : MDifferentiableAt I I (timeDependentFlowOf X t s) (timeDependentFlowOf X s t x) :=
    (contMDiffAt_timeDependentFlowOf (n := 2) (by norm_num) hX
      (timeDependentFlowOf_symm_of_mem hX₁ h).1).mdifferentiableAt two_ne_zero
  have heq : timeDependentFlowOf X t s ∘ timeDependentFlowOf X s t =ᶠ[𝓝 x] id := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
      ((isOpen_timeDependentFlowDomain hX₁).mem_nhds h)] with y hy
    exact (timeDependentFlowOf_symm_of_mem hX₁ hy).2
  -- Applied to `v`, the derivative of the composite is `v`, up to the identity cast.
  have hleft (v : TangentSpace I x) : mfderiv I I (timeDependentFlowOf X t s)
      (timeDependentFlowOf X s t x) (mfderiv I I (timeDependentFlowOf X s t) x v) = v := by
    have hv := congrArg (fun L ↦ L v) (heq.mfderiv_eq (I := I) (I' := I))
    simp only [mfderiv_comp x hψ hφ, mfderiv_id, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.id_apply] at hv
    exact hv
  intro v w hvw
  rw [← hleft v, ← hleft w, hvw]

end TauCeti
