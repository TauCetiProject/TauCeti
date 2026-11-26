/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Periodic

/-!
# The linearized flow along a solution

Let `X` be a jointly `C¹` time-dependent vector field on a boundaryless manifold `M` modelled on a
complete normed space, and let `γ : ℝ → M` be a solution defined for all time,
`γ' u = X u (γ u)`. The time map `φ_{0,t} = TauCeti.timeDependentFlowOf X 0 t` is defined near
`γ 0` and carries it to `γ t`, and it is a local diffeomorphism there, with local inverse the time
map from `t` back to `0` (`TauCeti.isLocalDiffeomorphAt_timeDependentFlowOf`). Its differential
is therefore a continuous linear equivalence

`Φ(t) = dφ_{0,t}(γ 0) : T_(γ 0) M ≃ T_(γ t) M`,

the **linearized flow along `γ`** (`TauCeti.linearizedFlowAlong`). Unlike
`TauCeti.timeDependentFlowMFDerivEquiv`, which is defined at every point for a field with complete
suspension, no completeness of the field is needed: only the flow along `γ` is used. It starts at
the identity (`TauCeti.linearizedFlowAlong_zero`), and the tangent vector `Φ(t) v` at `γ t`
depends continuously on the pair `(t, v)` (`TauCeti.continuous_linearizedFlowAlong`): this is the
regularity of `Φ` as a family of linear maps along the curve that the Conley–Zehnder index of a
capped orbit takes as input.

For a solution with `γ T = γ 0` (for instance a `T`-periodic one), `Φ(T)` is the differential of
the return map `φ_{0,T}` at its fixed point `γ 0`, and the solution is nondegenerate, in the sense
that `γ 0` is a nondegenerate fixed point of the return map, exactly when `Φ(T)` fixes no nonzero
tangent vector (`TauCeti.isNondegenerateFixedPt_iff_linearizedFlowAlong`).

For a contractible `1`-periodic solution `x`, the family `Φ(t)`, `t ∈ [0, 1]`, is read along the
based loop `TauCeti.orbitLoop x` of the orbit (`TauCeti.orbitLinearizedFlow`), the form in which
the Conley–Zehnder index of the cap classes of the orbit takes it.

## Main definitions

* `TauCeti.linearizedFlowAlong`: the linearized flow along a solution.
* `TauCeti.orbitLinearizedFlow`: the linearized flow along the loop of a contractible orbit.

## Main results

* `TauCeti.linearizedFlowAlong_apply`: it is the differential of the time map of the flow.
* `TauCeti.continuous_linearizedFlowAlong`: it is continuous as a family of tangent vectors.
* `TauCeti.isNondegenerateFixedPt_iff_linearizedFlowAlong`: nondegeneracy of a solution returning
  to its starting point, in terms of its linearized flow up to the return time.
* `TauCeti.continuous_orbitLinearizedFlow`,
  `TauCeti.isNondegenerateFixedPt_iff_orbitLinearizedFlow`: the same along the loop of an orbit.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the linearized flow along a periodic orbit, whose
  Conley–Zehnder index grades the orbit).
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M] {X : ℝ → (x : M) → TangentSpace I x}
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
  {γ : ℝ → M} (hγ : ∀ u, HasMFDerivAt 𝓘(ℝ, ℝ) I γ u ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (γ u))))

/-- The **linearized flow along a solution** `γ` of a jointly `C¹` time-dependent field `X`: the
differential `dφ_{0,t}(γ 0) : T_(γ 0) M ≃ T_(γ t) M` of the time map of the flow from `0` to `t`,
which is a local diffeomorphism at `γ 0` carrying it to `γ t`. Tangent spaces of `M` are the model
space `E` by definition, so the differential, valued in the tangent space at `φ_{0,t}(γ 0)`, is
read in the tangent space at the same point `γ t`. -/
def linearizedFlowAlong (t : ℝ) : TangentSpace I (γ 0) ≃L[ℝ] TangentSpace I (γ t) :=
  (isLocalDiffeomorphAt_timeDependentFlowOf le_rfl hX
    (mem_timeDependentFlowDomain_of_forall_hasMFDerivAt hγ 0 t)).mfderivToContinuousLinearEquiv
    (by simp)

/-- The linearized flow along a solution is the differential of the time map of the flow. -/
@[simp]
theorem linearizedFlowAlong_apply (t : ℝ) (v : TangentSpace I (γ 0)) :
    linearizedFlowAlong hX hγ t v = mfderiv I I (timeDependentFlowOf X 0 t) (γ 0) v :=
  (rfl)

/-- The linearized flow along a solution starts at the identity. -/
theorem linearizedFlowAlong_zero (v : TangentSpace I (γ 0)) :
    linearizedFlowAlong hX hγ 0 v = v := by
  rw [linearizedFlowAlong_apply, mfderiv_timeDependentFlowOf_self]
  exact ContinuousLinearMap.id_apply v

/-- **The linearized flow is continuous along the solution.** The tangent vector `Φ(t) v` at
`γ t` is a continuous function of the time `t` and the vector `v`. -/
theorem continuous_linearizedFlowAlong :
    Continuous fun q : ℝ × TangentSpace I (γ 0) ↦
      (⟨γ q.1, linearizedFlowAlong hX hγ q.1 q.2⟩ : TangentBundle I M) := by
  refine continuous_iff_continuousAt.2 fun q ↦ ?_
  have h := (contMDiffAt_totalSpaceMk_mfderiv_timeDependentFlowOf_prod (m := 0) (by simp) hX q.2
    (mem_timeDependentFlowDomain_of_forall_hasMFDerivAt hγ 0 q.1)).continuousAt
  refine h.congr (Filter.Eventually.of_forall fun p ↦ ?_)
  dsimp only
  -- The flow carries `γ 0` to `γ t`, so the two tangent vectors have the same base point.
  rw [linearizedFlowAlong_apply, timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ 0 p.1]

/-- **Nondegeneracy of a returning solution through its linearized flow.** A solution `γ` that
returns to its starting point at time `T` (for instance a `T`-periodic solution) is nondegenerate,
in the sense that `γ 0` is a nondegenerate fixed point of the return map `φ_{0,T}`, exactly when the
linearized flow up to time `T` fixes no nonzero tangent vector. -/
theorem isNondegenerateFixedPt_iff_linearizedFlowAlong {T : ℝ} (hγT : γ T = γ 0) :
    IsNondegenerateFixedPt I (timeDependentFlowOf X 0 T) (γ 0) ↔
      ∀ v : TangentSpace I (γ 0), linearizedFlowAlong hX hγ T v = v → v = 0 := by
  have hfix : Function.IsFixedPt (timeDependentFlowOf X 0 T) (γ 0) :=
    (timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ 0 T).trans hγT
  simp only [isNondegenerateFixedPt_iff, hfix, mdifferentiableAt_timeDependentFlowOf hX
    (mem_timeDependentFlowDomain_of_forall_hasMFDerivAt hγ 0 T), linearizedFlowAlong_apply,
    true_and]
  -- The two sides differ only in reading `dφ_{0,T}(γ 0) v` in `T_(γ 0) M` or in `T_(γ T) M`,
  -- both of which are the model space `E`.
  exact Iff.rfl

omit hγ

/-! ### The linearized flow along the loop of a contractible orbit -/

/-- The **linearized flow along the loop of a contractible `1`-periodic solution** `x`: the
linearized flow `Φ(t) : T_(x 0) M ≃ T_(x t) M` along `x` (`TauCeti.linearizedFlowAlong`), for the
times `t ∈ [0, 1]` that parametrize the loop `TauCeti.orbitLoop x`. Tangent spaces of `M` are the
model space `E` by definition, so it is read between the tangent spaces at the points of the loop.
-/
def orbitLinearizedFlow (x : contractiblePeriodicSolutions X 1) (t : unitInterval) :
    TangentSpace I (orbitLoop x 0) ≃L[ℝ] TangentSpace I (orbitLoop x t) :=
  linearizedFlowAlong hX
    (mem_periodicSolutions.1 (contractiblePeriodicSolutions_subset x.property)).1 t

/-- The linearized flow along the loop of an orbit is the differential of the time map of the
flow. -/
@[simp]
theorem orbitLinearizedFlow_apply (x : contractiblePeriodicSolutions X 1) (t : unitInterval)
    (v : TangentSpace I (orbitLoop x 0)) :
    orbitLinearizedFlow hX x t v = mfderiv I I (timeDependentFlowOf X 0 t) (x.val 0) v :=
  linearizedFlowAlong_apply hX _ t v

/-- The linearized flow along the loop of an orbit starts at the identity. -/
theorem orbitLinearizedFlow_zero (x : contractiblePeriodicSolutions X 1)
    (v : TangentSpace I (orbitLoop x 0)) : orbitLinearizedFlow hX x 0 v = v :=
  linearizedFlowAlong_zero hX _ v

/-- **The linearized flow is continuous along the loop of an orbit.** The tangent vector `Φ(t) v`
at the point `t` of the loop of `x` is a continuous function of `t ∈ [0, 1]` and of `v`. -/
theorem continuous_orbitLinearizedFlow (x : contractiblePeriodicSolutions X 1) :
    Continuous fun q : unitInterval × TangentSpace I (orbitLoop x 0) ↦
      (⟨orbitLoop x q.1, orbitLinearizedFlow hX x q.1 q.2⟩ : TangentBundle I M) := by
  have hx := (mem_periodicSolutions.1 (contractiblePeriodicSolutions_subset x.property)).1
  refine ((continuous_linearizedFlowAlong hX hx).comp
    (continuous_subtypeVal.prodMap continuous_id)).congr fun q ↦ ?_
  -- The point `t` of the loop is `x t`; the tangent vectors over it are elements of `E`.
  have h : ∀ (b : M) (w : E), b = x.val q.1 →
      (⟨x.val q.1, w⟩ : TangentBundle I M) = ⟨b, w⟩ := by
    rintro _ _ rfl
    rfl
  exact h _ _ (orbitLoop_apply x q.1)

/-- **Nondegeneracy of a contractible orbit through its linearized flow.** A contractible
`1`-periodic solution `x` is nondegenerate, in the sense that `x 0` is a nondegenerate fixed point
of the return map `φ_{0,1}`, exactly when the linearized flow at the end of its loop fixes no
nonzero tangent vector. -/
theorem isNondegenerateFixedPt_iff_orbitLinearizedFlow (x : contractiblePeriodicSolutions X 1) :
    IsNondegenerateFixedPt I (timeDependentFlowOf X 0 1) (x.val 0) ↔
      ∀ v : TangentSpace I (orbitLoop x 0), orbitLinearizedFlow hX x 1 v = v → v = 0 :=
  isNondegenerateFixedPt_iff_linearizedFlowAlong hX _ <| by
    simpa using (mem_periodicSolutions.1 (contractiblePeriodicSolutions_subset x.property)).2 0

end TauCeti
