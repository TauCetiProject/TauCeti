/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Topology.Homotopy.AddCircle
import TauCeti.Algebra.Ring.Periodic
import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
import TauCeti.Geometry.Manifold.Immersion.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Translation
import TauCeti.Geometry.Manifold.Topology
import TauCeti.Topology.Compactness.Compact

/-!
# Periodic solutions of time-periodic vector fields on manifolds

Let `X` be a time-dependent vector field on a manifold `M` which is periodic in time,
`X (t + T) = X t`. Its `T`-periodic solutions (`TauCeti.periodicSolutions X T`) are the curves
`γ : ℝ → M` defined for all time with `γ' t = X t (γ t)` and `γ (t + T) = γ t`. For `T = 1` and the
Hamiltonian vector field of a time-dependent Hamiltonian these are the 1-periodic orbits whose
count is the subject of the Arnold conjecture, and which generate the Hamiltonian Floer complex.

The time-dependent flow `TauCeti.timeDependentFlowOf X s t` of a jointly `C¹` field is only defined
on the open set `TauCeti.timeDependentFlowDomain X`, and this file works on that domain, with no
completeness assumption. Translating both times by a period of the field preserves the domain and
the flow (`TauCeti.timeDependentFlowOf_add_period_of_mem`). So for `T ≠ 0` a point `x` which
returns to itself after one period, `timeDependentFlowOf X s (s + T) x = x`, can be flowed on period
after period in both directions: its trajectory is defined for all time
(`TauCeti.mem_timeDependentFlowDomain_of_isFixedPt`) and is a `T`-periodic solution. Evaluation at
the initial time `s` is therefore an equivalence between `T`-periodic solutions and the fixed points
of the **return map** `timeDependentFlowOf X s (s + T)` in its domain
(`TauCeti.periodicSolutionsEquivFixedPoints`). In particular a periodic solution whose initial
point is isolated among the fixed points of the return map is isolated among the periodic
solutions (`TauCeti.eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt`).

Periodic solutions can be read through a map `e : M → F` into a finite-dimensional normed space
which is injective on a compact set `K`, with injective differential at the points of `K`: every
periodic solution in `e(K)` of a field on `F` agreeing on `e(K)` with the pushforward `d e (X_t)`
is `e ∘ x` for a periodic solution `x` of `X` in `K`
(`TauCeti.exists_mem_periodicSolutions_comp_eq`).

On a compact boundaryless manifold (whose model space is then finite-dimensional when the manifold
is nonempty), the flow of any jointly `C¹` time-dependent field is defined and `C¹` everywhere. The
initial points of the `T`-periodic solutions form a closed, hence compact, subset of the manifold,
without assuming that `X` itself is `T`-periodic or that `T ≠ 0`. If every `T`-periodic solution is
nondegenerate, meaning that its initial point is a nondegenerate fixed point of the return map
`timeDependentFlowOf X s (s + T)` (`TauCeti.IsNondegenerateFixedPt`), this compact set is discrete,
so there are only finitely many `T`-periodic solutions (`TauCeti.finite_periodicSolutions`).

This is the manifold counterpart of `TauCeti.periodicSolutionEquivFixedPoints` in
`TauCeti.Dynamics.Flow.Periodic.Basic`, which treats globally Lipschitz fields on Banach spaces.

Hamiltonian Floer theory on the contractible sector uses only the **contractible** periodic
solutions (`TauCeti.contractiblePeriodicSolutions`), those whose loop `ℝ ⧸ Tℤ → M` is
null-homotopic, and assumes nondegeneracy only for them. If they are all nondegenerate, there are
still only finitely many of them (`TauCeti.finite_contractiblePeriodicSolutions`). For `T ≠ 0`, the
trajectory of an initial point of a periodic solution over one period `[s, s + |T|]` is a loop
depending continuously on the initial point, and on a manifold null-homotopy of such a family of
loops is locally constant (`isClopen_setOf_homotopic_refl`). So the initial points of the
contractible solutions form a closed, hence compact, set of nondegenerate, hence isolated, fixed
points, which is finite.

**Shifting time.** The shift `t ↦ γ (t + θ)` of a periodic solution of `X` is a periodic solution
of the shifted field `t ↦ X (t + θ)`, contractible exactly when `γ` is
(`TauCeti.comp_add_right_mem_periodicSolutions_iff`,
`TauCeti.comp_add_right_mem_contractiblePeriodicSolutions_iff`). On a manifold modelled on a
complete normed space, the flow along a `T`-periodic solution `γ` of a `T`-periodic field `X`
conjugates the differentials of the return maps at any two initial times `s` and `s'`, with no
completeness or finite-dimensionality assumption, so nondegeneracy of `γ` does not depend on the
initial time (`TauCeti.isNondegenerateFixedPt_timeDependentFlowOf_iff_of_mem_periodicSolutions`),
and shifting time preserves it
(`TauCeti.isNondegenerateFixedPt_timeDependentFlowOf_comp_add_right_iff`). When the suspension is
complete, the flow from time `s` to time `s'` globally conjugates the return maps at `s` and `s'`
(`TauCeti.semiconj_timeDependentFlowOf_add_period`), giving the same equivalence at any point `x`
(`TauCeti.isNondegenerateFixedPt_timeDependentFlowOf_iff`). For a Hamiltonian field, the shift is
the change of the asymptotic marker of an end of a Floer solution, which rotates the orbit at that
end.

## Main definitions

* `TauCeti.periodicSolutions X T`: the `T`-periodic solutions of `X`.
* `TauCeti.periodicSolutionsEquivFixedPoints`: periodic solutions correspond to fixed points of the
  return map.
* `TauCeti.contractiblePeriodicSolutions X T`: the `T`-periodic solutions whose loop is
  null-homotopic.
* `TauCeti.orbitLoop`: the based loop traced by a contractible `1`-periodic solution over one
  period, null-homotopic relative to its base point (`TauCeti.orbitLoop_homotopic_refl`).

## Main results

* `TauCeti.mem_periodicSolutions_const_iff`: the periodic solutions of an autonomous field are its
  periodic integral curves.
* `TauCeti.comp_neg_mem_periodicSolutions_iff`: reversing time turns the periodic solutions of `X`
  into those of the reversed field `(t, x) ↦ -X (-t) x`.
* `TauCeti.comp_add_right_mem_periodicSolutions_iff`,
  `TauCeti.comp_add_right_mem_contractiblePeriodicSolutions_iff`: shifting time identifies the
  (contractible) periodic solutions of `X` and of the shifted field `t ↦ X (t + θ)`.
* `TauCeti.exists_mem_periodicSolutions_comp_eq`: periodic solutions in `e(K)` of a field agreeing
  there with the pushforward `d e (X_t)` are read through `e` from periodic solutions in `K`.
* `TauCeti.timeDependentFlowOf_add_period_add_period`,
  `TauCeti.timeDependentFlowOf_add_period_of_mem`: translating both times by a period of the field
  preserves the flow and its domain.
* `TauCeti.mem_timeDependentFlowDomain_of_isFixedPt`: for `T ≠ 0`, the trajectory of a fixed point
  of the return map is defined for all time.
* `TauCeti.mfderiv_timeDependentFlowOf_add_period_apply`: for a jointly `C¹` periodic field, the
  derivative of the flow over one more period factors through the derivative of the return map,
  wherever both are defined. At a fixed point of the return map in its domain, a vector fixed by
  the derivative of the return map therefore spreads to a periodic solution of the linearized flow
  (`TauCeti.mfderiv_timeDependentFlowOf_add_period_apply_of_eq`).
* `TauCeti.eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt`,
  `TauCeti.IsNondegenerateFixedPt.eventually_forall_mem_periodicSolutions_eq`: periodic solutions
  through isolated (in particular nondegenerate) fixed points of the return map are isolated.
* `TauCeti.timeDependentFlowOf_add_period` and `TauCeti.timeDependentFlowOf_add_period_eq_iff`:
  for a complete suspension, the flow over one more period is the return map followed by the flow,
  so points at times `t + T` and `t` match exactly across the inverse return map.
* `TauCeti.isNondegenerateFixedPt_timeDependentFlowOf_iff_of_mem_periodicSolutions`: on a complete
  model space, nondegeneracy of a periodic solution of a periodic field does not depend on the
  initial time.
* `TauCeti.isNondegenerateFixedPt_timeDependentFlowOf_comp_add_right_iff`: on a complete model
  space, shifting time preserves nondegeneracy of a periodic solution of a periodic field.
* `TauCeti.finite_periodicSolutions`: on a compact boundaryless manifold, a jointly `C¹` field
  whose `T`-periodic solutions are all nondegenerate has finitely many of them.
* `TauCeti.finite_contractiblePeriodicSolutions`: the same for the contractible `T`-periodic
  solutions, assuming only that they are nondegenerate.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 11.1 (periodic orbits of time-dependent Hamiltonians as fixed points of the time-one
  map).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
-/

public section

noncomputable section

open Filter Function Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {X : ℝ → (x : M) → TangentSpace I x} {T : ℝ}

/-- The **`T`-periodic solutions** of a time-dependent vector field `X`: the curves `γ` defined for
all time, with `γ' t = X t (γ t)` and `γ (t + T) = γ t` for every `t`. -/
def periodicSolutions (X : ℝ → (x : M) → TangentSpace I x) (T : ℝ) : Set (ℝ → M) :=
  {γ | (∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) ∧
    ∀ t, γ (t + T) = γ t}

/-- The defining characterization of a periodic solution. -/
@[simp]
theorem mem_periodicSolutions {γ : ℝ → M} :
    γ ∈ periodicSolutions X T ↔
      (∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (γ t)))) ∧
        ∀ t, γ (t + T) = γ t :=
  Iff.rfl

/-- The periodic solutions of an autonomous field `Y` are its periodic integral curves. -/
theorem mem_periodicSolutions_const_iff {Y : (x : M) → TangentSpace I x} {γ : ℝ → M} :
    γ ∈ periodicSolutions (fun _ ↦ Y) T ↔ IsMIntegralCurve γ Y ∧ Periodic γ T :=
  Iff.rfl

/-- A periodic solution is continuous. -/
theorem continuous_of_mem_periodicSolutions {γ : ℝ → M} (hγ : γ ∈ periodicSolutions X T) :
    Continuous γ :=
  continuous_iff_continuousAt.2 fun t ↦ (hγ.1 t).continuousAt

/-- A periodic solution is periodic. -/
theorem periodic_of_mem_periodicSolutions {γ : ℝ → M} (hγ : γ ∈ periodicSolutions X T) :
    Periodic γ T :=
  (mem_periodicSolutions.1 hγ).2

/-- **Reversing time.** If `γ` is a `T`-periodic solution of `X`, then `t ↦ γ (-t)` is a
`T`-periodic solution of the reversed field `(t, x) ↦ -X (-t) x`. -/
theorem comp_neg_mem_periodicSolutions {γ : ℝ → M} (hγ : γ ∈ periodicSolutions X T) :
    (fun t ↦ γ (-t)) ∈ periodicSolutions (fun t x ↦ -X (-t) x) T := by
  refine ⟨fun t ↦ ?_, Periodic.comp_neg hγ.2⟩
  have hneg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ ↦ -t) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (-1 : ℝ)) :=
    (hasDerivAt_neg t).hasFDerivAt.hasMFDerivAt
  have h : (1 : ℝ →L[ℝ] ℝ).smulRight (-X (-t) (γ (-t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (X (-t) (γ (-t))) ∘SL (1 : ℝ →L[ℝ] ℝ).smulRight (-1 : ℝ) := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight]
  rw [h]
  exact (hγ.1 (-t)).comp t hneg

/-- **Reversing time**, as a characterization: `t ↦ γ (-t)` is a `T`-periodic solution of `X`
exactly when `γ` is a `T`-periodic solution of the reversed field `(t, x) ↦ -X (-t) x`. -/
theorem comp_neg_mem_periodicSolutions_iff {γ : ℝ → M} :
    (fun t ↦ γ (-t)) ∈ periodicSolutions X T ↔
      γ ∈ periodicSolutions (fun t x ↦ -X (-t) x) T := by
  -- Each direction is the reversal of the other side, since reversing twice is the identity.
  constructor <;> intro h <;> simpa only [neg_neg] using comp_neg_mem_periodicSolutions h

/-- **Shifting time.** If `γ` is a `T`-periodic solution of `X`, then its shift `t ↦ γ (t + θ)` is a
`T`-periodic solution of the shifted field `t ↦ X (t + θ)`. -/
theorem comp_add_right_mem_periodicSolutions {γ : ℝ → M} (hγ : γ ∈ periodicSolutions X T)
    (θ : ℝ) : (fun t ↦ γ (t + θ)) ∈ periodicSolutions (fun t ↦ X (t + θ)) T :=
  ⟨fun t ↦ HasMFDerivAt.comp_add_right (hγ.1 (t + θ)),
    fun t ↦ by simp only [add_right_comm t T θ, hγ.2 (t + θ)]⟩

/-- **Shifting time**, as a characterization: `t ↦ γ (t + θ)` is a `T`-periodic solution of the
shifted field `t ↦ X (t + θ)` exactly when `γ` is a `T`-periodic solution of `X`. -/
theorem comp_add_right_mem_periodicSolutions_iff {γ : ℝ → M} (θ : ℝ) :
    (fun t ↦ γ (t + θ)) ∈ periodicSolutions (fun t ↦ X (t + θ)) T ↔ γ ∈ periodicSolutions X T := by
  refine ⟨fun h ↦ ?_, fun h ↦ comp_add_right_mem_periodicSolutions h θ⟩
  -- Shifting back by `-θ` recovers `γ` and `X`.
  simpa only [neg_add_cancel_right] using comp_add_right_mem_periodicSolutions h (-θ)

/-- **Periodic solutions read through `e`.** Let `K` be a compact subset of `M` and `e : M → F` a
map into a finite-dimensional normed space, injective on `K`, with injective differential at the
points of `K`. Let `Y` be a time-dependent field on `F` agreeing on `e(K)` with the pushforward
`d e (X_t)`. Then every `T`-periodic solution `y` of `y' = Y(t, y)` with values in `e(K)` is
`e ∘ x` for a `T`-periodic solution `x` of `X` with values in `K`. -/
theorem exists_mem_periodicSolutions_comp_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {e : M → F} {K : Set M} (hK : IsCompact K) (he_inj : InjOn e K)
    (hde : ∀ p ∈ K, Injective (mvfderiv I e p))
    {Y : ℝ → F → F} (hY : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (X t p)) {y : ℝ → F}
    (hyper : Periodic y T) (hy : ∀ t, HasDerivAt y (Y t (y t)) t) (hyK : ∀ t, y t ∈ e '' K) :
    ∃ x ∈ periodicSolutions X T, (∀ t, x t ∈ K) ∧ e ∘ x = y := by
  -- A map with injective differential at a point is differentiable, hence continuous, there.
  have he : ContinuousOn e K := fun p hp ↦ (mdifferentiableAt_of_mfderiv_injective
    (injective_mvfderiv_iff.1 (hde p hp))).continuousAt.continuousWithinAt
  choose x hxK hx using hyK
  have hex : e ∘ x = y := funext hx
  -- Inside `K`, continuity is read through `e`.
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t ↦
    hK.tendsto_nhds_of_tendsto_comp he he_inj (Eventually.of_forall hxK) (hxK t) <| by
      rw [hex, hx]
      exact (hy t).continuousAt
  refine ⟨x, mem_periodicSolutions.2 ⟨fun t ↦ ?_, fun t ↦ he_inj (hxK _) (hxK _)
    (by rw [hx, hx, hyper t])⟩, hxK, hex⟩
  -- Since `d e` is injective, the velocity of `x` is read off from that of `e ∘ x`.
  refine hxc.continuousAt.hasMFDerivAt_of_hasDerivAt_comp (hde _ (hxK t)) ?_
  rw [hex, ← hY t _ (hxK t), hx]
  exact hy t

/-- **Isolated periodic solutions read through `e`.** In the setting of
`TauCeti.exists_mem_periodicSolutions_comp_eq`, suppose that the `T`-periodic solutions of `X` in
`K` are isolated: for each such solution `x`, every `T`-periodic solution in `K` starting close
enough to `x 0` is `x`. Then every `T`-periodic solution `y` of `y' = Y(t, y)` with values in
`e(K)` is isolated in the uniform distance among the `T`-periodic solutions with values in
`e(K)`. -/
theorem exists_pos_forall_eq_of_forall_dist_lt_of_mem_image {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {e : M → F} {K : Set M} (hK : IsCompact K)
    (he_inj : InjOn e K) (hde : ∀ p ∈ K, Injective (mvfderiv I e p))
    {Y : ℝ → F → F} (hY : ∀ t, ∀ p ∈ K, Y t (e p) = mvfderiv I e p (X t p))
    (hiso : ∀ x ∈ periodicSolutions X T, (∀ t, x t ∈ K) →
      ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ periodicSolutions X T, (∀ t, x' t ∈ K) → x' 0 = p → x' = x)
    {y : ℝ → F} (hyper : Periodic y T) (hy : ∀ t, HasDerivAt y (Y t (y t)) t)
    (hyK : ∀ t, y t ∈ e '' K) :
    ∃ ε > 0, ∀ y' : ℝ → F, Periodic y' T → (∀ t, HasDerivAt y' (Y t (y' t)) t) →
      (∀ t, y' t ∈ e '' K) → (∀ t, dist (y' t) (y t) < ε) → y' = y := by
  have he : ContinuousOn e K := fun p hp ↦ (mdifferentiableAt_of_mfderiv_injective
    (injective_mvfderiv_iff.1 (hde p hp))).continuousAt.continuousWithinAt
  obtain ⟨x, hx, hxK, rfl⟩ := exists_mem_periodicSolutions_comp_eq hK he_inj hde hY hyper hy hyK
  -- Inside `K`, the neighbourhoods of `x 0` are read through `e`.
  obtain ⟨V, hV, hVx⟩ := hK.exists_mem_nhds_inter_preimage_subset he he_inj (hxK 0)
    (mem_nhdsWithin_of_mem_nhds (hiso x hx hxK))
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨ε, hε, fun y' hy'per hy' hy'K hdist ↦ ?_⟩
  obtain ⟨x', hx', hx'K, rfl⟩ :=
    exists_mem_periodicSolutions_comp_eq hK he_inj hde hY hy'per hy' hy'K
  rw [hVx ⟨hx'K 0, hεV (Metric.mem_ball.2 (hdist 0))⟩ x' hx' hx'K rfl]

/-- The **contractible** `T`-periodic solutions of `X`: the `T`-periodic solutions `γ` whose loop
`ℝ ⧸ Tℤ → M`, `t ↦ γ t`, is null-homotopic. -/
def contractiblePeriodicSolutions (X : ℝ → (x : M) → TangentSpace I x) (T : ℝ) : Set (ℝ → M) :=
  {γ ∈ periodicSolutions X T | ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t}

/-- The defining characterization of a contractible periodic solution. -/
@[simp]
theorem mem_contractiblePeriodicSolutions {γ : ℝ → M} :
    γ ∈ contractiblePeriodicSolutions X T ↔ γ ∈ periodicSolutions X T ∧
      ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t :=
  Iff.rfl

/-- Contractible periodic solutions are periodic solutions. -/
theorem contractiblePeriodicSolutions_subset :
    contractiblePeriodicSolutions X T ⊆ periodicSolutions X T :=
  fun _ hγ ↦ hγ.1

/-- The **loop of a contractible `1`-periodic solution** `γ`: the loop `t ↦ γ t`, `t ∈ [0, 1]`,
based at `γ 0`. -/
def orbitLoop (γ : contractiblePeriodicSolutions X 1) : Path (γ.val 0) (γ.val 0) :=
  (periodic_of_mem_periodicSolutions (contractiblePeriodicSolutions_subset γ.property)).loop
    (continuous_of_mem_periodicSolutions (contractiblePeriodicSolutions_subset γ.property)) 0

/-- Evaluating the loop of a contractible `1`-periodic solution. -/
@[simp]
theorem orbitLoop_apply (γ : contractiblePeriodicSolutions X 1) (t : unitInterval) :
    orbitLoop γ t = γ.val t := by
  simp [orbitLoop]

/-- The loop of a contractible `1`-periodic solution is null-homotopic relative to its base
point. -/
theorem orbitLoop_homotopic_refl (γ : contractiblePeriodicSolutions X 1) :
    (orbitLoop γ).Homotopic (Path.refl (γ.val 0)) := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hγ := contractiblePeriodicSolutions_subset γ.property
  exact ((periodic_of_mem_periodicSolutions hγ).exists_nullhomotopic_iff_loop_homotopic_refl
    (continuous_of_mem_periodicSolutions hγ) 0).1 (mem_contractiblePeriodicSolutions.1 γ.property).2

/-- **Shifting time preserves contractibility.** If `γ` is a contractible `T`-periodic solution of
`X`, then `t ↦ γ (t + θ)` is a contractible `T`-periodic solution of the shifted field
`t ↦ X (t + θ)`: its loop is the loop of `γ` precomposed with a rotation of the circle. -/
theorem comp_add_right_mem_contractiblePeriodicSolutions {γ : ℝ → M}
    (hγ : γ ∈ contractiblePeriodicSolutions X T) (θ : ℝ) :
    (fun t ↦ γ (t + θ)) ∈ contractiblePeriodicSolutions (fun t ↦ X (t + θ)) T := by
  obtain ⟨hγ, g, hg, hgγ⟩ := hγ
  refine ⟨comp_add_right_mem_periodicSolutions hγ θ,
    g.comp ⟨(· + (θ : AddCircle T)), continuous_id.add continuous_const⟩, hg.comp_left _,
    fun t ↦ ?_⟩
  exact (congrArg g (AddCircle.coe_add T t θ).symm).trans (hgγ (t + θ))

/-- **Shifting time preserves contractibility**, as a characterization: `t ↦ γ (t + θ)` is a
contractible `T`-periodic solution of the shifted field `t ↦ X (t + θ)` exactly when `γ` is a
contractible `T`-periodic solution of `X`. -/
theorem comp_add_right_mem_contractiblePeriodicSolutions_iff {γ : ℝ → M} (θ : ℝ) :
    (fun t ↦ γ (t + θ)) ∈ contractiblePeriodicSolutions (fun t ↦ X (t + θ)) T ↔
      γ ∈ contractiblePeriodicSolutions X T := by
  refine ⟨fun h ↦ ?_, fun h ↦ comp_add_right_mem_contractiblePeriodicSolutions h θ⟩
  -- Shifting back by `-θ` recovers `γ` and `X`.
  simpa only [neg_add_cancel_right] using comp_add_right_mem_contractiblePeriodicSolutions h (-θ)

/-- A periodic solution stays in the domain of the time-dependent flow between any two times. -/
private theorem mem_timeDependentFlowDomain_of_mem_periodicSolutions {γ : ℝ → M}
    (hγ : γ ∈ periodicSolutions X T) (s t : ℝ) :
    ((s, t), γ s) ∈ timeDependentFlowDomain X :=
  mem_timeDependentFlowDomain_of_hasMFDerivAt (a := min s t - 1) (b := max s t + 1)
    (fun u _ ↦ hγ.1 u)
    ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩
    ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩

/-- Negating the period does not change the set of contractible periodic solutions. -/
private theorem contractiblePeriodicSolutions_neg (X : ℝ → (x : M) → TangentSpace I x) (T : ℝ) :
    contractiblePeriodicSolutions X (-T) = contractiblePeriodicSolutions X T := by
  have hsub (p : ℝ) :
      contractiblePeriodicSolutions X p ⊆ contractiblePeriodicSolutions X (-p) := by
    rintro γ ⟨hγ, g, hg, hgγ⟩
    refine ⟨⟨hγ.1, Periodic.neg hγ.2⟩,
      g.comp ⟨QuotientAddGroup.map _ _ (AddMonoidHom.id ℝ) (by
        rw [AddSubgroup.comap_id, AddSubgroup.zmultiples_le]
        exact neg_mem (AddSubgroup.mem_zmultiples p)),
        isQuotientMap_quotient_mk'.continuous_iff.2 continuous_quotient_mk'⟩,
      hg.comp_left _, hgγ⟩
  exact subset_antisymm (by simpa only [neg_neg] using hsub (-T)) (hsub T)

section Flow

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
  {s t : ℝ} {x : M}
include hX

/-- **The flow of a time-periodic field is invariant under translation of time by a period.** If
`X (t + T) = X t` for all `t`, the flow from `s + T` to `t + T` is the flow from `s` to `t`. Both
sides take the junk value outside the flow domain, which is also invariant
(`TauCeti.timeDependentFlowOf_add_period_of_mem`). -/
theorem timeDependentFlowOf_add_period_add_period (hT : Periodic X T) (s t : ℝ) :
    timeDependentFlowOf X (s + T) (t + T) = timeDependentFlowOf X s t := by
  -- Shifting a `T`-periodic field by `T` does not change it, so neither does shifting its flow.
  funext y
  rw [← timeDependentFlowOf_comp_add_right hX T, funext hT]

/-- **The flow domain of a time-periodic field is invariant under translation of time by a
period.** If `X (t + T) = X t` for all `t` and the flow from `s` to `t` is defined at `x`, then so
is the flow from `s + T` to `t + T`, with the same value. -/
theorem timeDependentFlowOf_add_period_of_mem (hT : Periodic X T)
    (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    ((s + T, t + T), x) ∈ timeDependentFlowDomain X ∧
      timeDependentFlowOf X (s + T) (t + T) x = timeDependentFlowOf X s t x := by
  -- Shifting a `T`-periodic field by `T` does not change it.
  have h' : ((s, t), x) ∈ timeDependentFlowDomain (fun u ↦ X (u + T)) := by rwa [funext hT]
  exact ⟨(mem_timeDependentFlowDomain_comp_add_right_iff hX T).1 h',
    congrFun (timeDependentFlowOf_add_period_add_period hX hT s t) x⟩

/-- If the return map of a time-periodic field fixes `x`, so does its `k`-th iterate: the flow
from `s` to `s + k T` is defined at `x` and fixes it. -/
private theorem timeDependentFlowOf_nat_mul_of_isFixedPt (hT : Periodic X T)
    (h : ((s, s + T), x) ∈ timeDependentFlowDomain X)
    (hfix : IsFixedPt (timeDependentFlowOf X s (s + T)) x) (k : ℕ) :
    ((s, s + k * T), x) ∈ timeDependentFlowDomain X ∧
      timeDependentFlowOf X s (s + k * T) x = x := by
  induction k with
  | zero =>
    simpa using mem_timeDependentFlowDomain_self_of_mem h
  | succ k ih =>
    -- The `(k + 1)`-st period is the first one translated by `k T`.
    obtain ⟨hmem, heq⟩ := timeDependentFlowOf_add_period_of_mem hX (hT.nat_mul k) h
    rw [← ih.2] at hmem
    rw [hfix.eq] at heq
    obtain ⟨hmem', heq'⟩ := timeDependentFlowOf_trans_of_mem hX ih.1 hmem
    rw [ih.2, heq] at heq'
    have hk : s + T + k * T = s + (k + 1 : ℕ) * T := by push_cast; ring
    rw [hk] at hmem' heq'
    exact ⟨hmem', heq'.symm⟩

/-- **A trajectory that returns to its start after a period exists for all time.** If `X` is
`T`-periodic with `T ≠ 0`, and the flow from `s` to `s + T` is defined at `x` and fixes it, then
the flow from `s` is defined at `x` at every time. -/
theorem mem_timeDependentFlowDomain_of_isFixedPt (hT : Periodic X T) (hT0 : T ≠ 0)
    (h : ((s, s + T), x) ∈ timeDependentFlowDomain X)
    (hfix : IsFixedPt (timeDependentFlowOf X s (s + T)) x) (t : ℝ) :
    ((s, t), x) ∈ timeDependentFlowDomain X := by
  -- The flow is defined at the times `s + k T` and `s - k T` for every `k : ℕ`.
  have hpos (k : ℕ) := timeDependentFlowOf_nat_mul_of_isFixedPt hX hT h hfix k
  have hneg (k : ℕ) : ((s, s - k * T), x) ∈ timeDependentFlowDomain X := by
    obtain ⟨hmem, heq⟩ := timeDependentFlowOf_add_period_of_mem hX (hT.nat_mul k).neg (hpos k).1
    rw [add_neg_cancel_right, ← sub_eq_add_neg, (hpos k).2] at heq
    rw [add_neg_cancel_right, ← sub_eq_add_neg] at hmem
    simpa only [heq] using (timeDependentFlowOf_symm_of_mem hX hmem).1
  -- Choose `k` with `|t - s| ≤ k |T|`; then `t` lies between `s - k T` and `s + k T`.
  obtain ⟨k, hk⟩ := exists_nat_ge (|t - s| / |T|)
  have hk' : |t - s| ≤ k * |T| := (div_le_iff₀ (abs_pos.2 hT0)).1 hk
  have hts := abs_le.1 hk'
  have hcon := ordConnected_setOf_mem_timeDependentFlowDomain (X := X) s x
  rcases le_or_gt 0 T with hT' | hT'
  · rw [abs_of_nonneg hT'] at hts
    exact hcon.out (hneg k) (hpos k).1 ⟨by linarith [hts.1], by linarith [hts.2]⟩
  · rw [abs_of_neg hT'] at hts
    exact hcon.out (hpos k).1 (hneg k) ⟨by linarith [hts.1], by linarith [hts.2]⟩

/-- **Periodic solutions are fixed points of the return map.** For a `T`-periodic field `X`, with
`T ≠ 0`, evaluation at the initial time `s` identifies the `T`-periodic solutions of `X` with the
fixed points of the return map `timeDependentFlowOf X s (s + T)` in its domain. The inverse sends a
fixed point to its trajectory under the flow from time `s`. -/
def periodicSolutionsEquivFixedPoints (hT : Periodic X T) (hT0 : T ≠ 0) (s : ℝ) :
    periodicSolutions X T ≃ {x | ((s, s + T), x) ∈ timeDependentFlowDomain X ∧
      IsFixedPt (timeDependentFlowOf X s (s + T)) x} where
  toFun γ := ⟨γ.val s, mem_timeDependentFlowDomain_of_mem_periodicSolutions γ.property s (s + T),
    (timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX γ.property.1 s (s + T)).trans
      (γ.property.2 s)⟩
  invFun x := ⟨fun t ↦ timeDependentFlowOf X s t x, fun t ↦ hasMFDerivAt_timeDependentFlowOf hX
      (mem_timeDependentFlowDomain_of_isFixedPt hX hT hT0 x.property.1 x.property.2 t), fun t ↦ by
    -- Flow for one period, which fixes `x`, then translate the remaining time back by `T`.
    have hall := mem_timeDependentFlowDomain_of_isFixedPt hX hT hT0 x.property.1 x.property.2
    obtain ⟨hmem, heq⟩ := timeDependentFlowOf_add_period_of_mem hX hT (hall t)
    have htr := (timeDependentFlowOf_trans_of_mem hX x.property.1
      (by rwa [x.property.2.eq])).2
    dsimp only
    rw [← htr, x.property.2.eq, heq]⟩
  left_inv γ := Subtype.ext <| funext <| timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX
    γ.property.1 s
  right_inv x := Subtype.ext (timeDependentFlowOf_self X s x)

/-- The correspondence from periodic solutions to fixed points evaluates at the initial time. -/
@[simp]
theorem periodicSolutionsEquivFixedPoints_apply (hT : Periodic X T) (hT0 : T ≠ 0) (s : ℝ)
    (γ : periodicSolutions X T) :
    (periodicSolutionsEquivFixedPoints hX hT hT0 s γ : M) = γ.val s :=
  (rfl)

/-- The periodic solution of a fixed point of the return map is its trajectory under the flow. -/
@[simp]
theorem periodicSolutionsEquivFixedPoints_symm_apply (hT : Periodic X T) (hT0 : T ≠ 0) (s : ℝ)
    (x : {x | ((s, s + T), x) ∈ timeDependentFlowDomain X ∧
      IsFixedPt (timeDependentFlowOf X s (s + T)) x}) (t : ℝ) :
    ((periodicSolutionsEquivFixedPoints hX hT hT0 s).symm x).val t =
      timeDependentFlowOf X s t x :=
  (rfl)

/-- **Periodic solutions through isolated fixed points are isolated.** Let `γ` be a `T`-periodic
solution of `X` whose value `γ s` is isolated among the fixed points of the return map
`timeDependentFlowOf X s (s + T)`. Then every `T`-periodic solution `δ` whose value `δ s` is close
enough to `γ s` is `γ` itself. For a nondegenerate fixed point the isolation is
`TauCeti.IsNondegenerateFixedPt.eventually_not_isFixedPt`. -/
theorem eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt {γ : ℝ → M}
    (hγ : γ ∈ periodicSolutions X T)
    (hiso : ∀ᶠ p in 𝓝[≠] γ s, ¬IsFixedPt (timeDependentFlowOf X s (s + T)) p) :
    ∀ᶠ p in 𝓝 (γ s), ∀ δ ∈ periodicSolutions X T, δ s = p → δ = γ := by
  -- A solution defined for all time is the trajectory of the flow from time `s`.
  have hflow {δ : ℝ → M} (hδ : δ ∈ periodicSolutions X T) (t : ℝ) :
      timeDependentFlowOf X s t (δ s) = δ t :=
    timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hδ.1 s t
  filter_upwards [eventually_nhdsWithin_iff.1 hiso] with p hp δ hδ hδp
  -- The value `δ s` is a fixed point of the return map close to `γ s`, hence equal to it.
  have hδγ : δ s = γ s := by
    by_contra hne
    exact hp (hδp ▸ hne) (hδp ▸ (hflow hδ (s + T)).trans (hδ.2 s))
  funext t
  rw [← hflow hδ t, ← hflow hγ t, hδγ]

/-- **Periodic solutions through nondegenerate fixed points are isolated.** If `γ` is a
`T`-periodic solution of `X` and `γ s` is a nondegenerate fixed point of the return map
`timeDependentFlowOf X s (s + T)`, then for `y` close enough to `γ s` the only `T`-periodic
solution passing through `y` at time `s` is `γ` itself. -/
theorem IsNondegenerateFixedPt.eventually_forall_mem_periodicSolutions_eq [FiniteDimensional ℝ E]
    {γ : ℝ → M} (hγ : γ ∈ periodicSolutions X T)
    (hnd : IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) (γ s)) :
    ∀ᶠ y in 𝓝 (γ s), ∀ γ' ∈ periodicSolutions X T, γ' s = y → γ' = γ :=
  eventually_forall_mem_periodicSolutions_eq_of_eventually_not_isFixedPt hX hγ
    hnd.eventually_not_isFixedPt

section CompleteSpace

variable [CompleteSpace E]

/-- **The derivative of the flow over one more period.** Let `X` be a `T`-periodic jointly `C¹`
field, let the flow from `(s, x)` be defined at time `s + T`, and the flow from `s` at time `t` at
the image `φ_{s, s + T}(x)`. Then the derivative of the flow to time `t + T` is that of the return
map followed by that of the flow to time `t`:
`dφ_{s, t + T} v = dφ_{s, t} (dφ_{s, s + T} v)`. -/
theorem mfderiv_timeDependentFlowOf_add_period_apply (hT : Periodic X T)
    (h : ((s, s + T), x) ∈ timeDependentFlowDomain X)
    (ht : ((s, t), timeDependentFlowOf X s (s + T) x) ∈ timeDependentFlowDomain X)
    (v : TangentSpace I x) :
    mfderiv I I (timeDependentFlowOf X s (t + T)) x v =
      mfderiv I I (timeDependentFlowOf X s t) (timeDependentFlowOf X s (s + T) x)
        (mfderiv I I (timeDependentFlowOf X s (s + T)) x v) := by
  rw [mfderiv_timeDependentFlowOf_trans_of_mem hX h
    (timeDependentFlowOf_add_period_of_mem hX hT ht).1,
    timeDependentFlowOf_add_period_add_period hX hT]
  -- The goal is `ContinuousLinearMap.comp_apply`, except that the coercion on the left still has
  -- the codomain `TangentSpace I (φ_{s, t + T} x)` of the original derivative, while the composite
  -- lands in `TangentSpace I (φ_{s, t} (φ_{s, s + T} x))`. Both unfold to `E`, so `rfl` closes it,
  -- whereas rewriting with `comp_apply` fails on the mismatched codomain.
  rfl

/-- **Periodic solutions of the linearized flow.** If `X` is jointly `C¹` and `T`-periodic, `x` is
a fixed point of the return map `φ_{s, s + T}` in its domain, and `v` is fixed by its derivative,
then `t ↦ dφ_{s, t} v` along the periodic orbit of `x` is `T`-periodic. -/
theorem mfderiv_timeDependentFlowOf_add_period_apply_of_eq (hT : Periodic X T)
    (h : ((s, s + T), x) ∈ timeDependentFlowDomain X)
    (hfix : IsFixedPt (timeDependentFlowOf X s (s + T)) x) {v : TangentSpace I x}
    (hv : mfderiv I I (timeDependentFlowOf X s (s + T)) x v = v) (t : ℝ) :
    mfderiv I I (timeDependentFlowOf X s (t + T)) x v =
      mfderiv I I (timeDependentFlowOf X s t) x v := by
  rcases eq_or_ne T 0 with rfl | hT0
  · rw [add_zero]
  have hall := mem_timeDependentFlowDomain_of_isFixedPt hX hT hT0 h hfix t
  have hRt : ((s, t), timeDependentFlowOf X s (s + T) x) ∈ timeDependentFlowDomain X := by
    rw [hfix.eq]
    exact hall
  have hR : MDifferentiableAt I I (timeDependentFlowOf X s (s + T)) x :=
    mdifferentiableAt_timeDependentFlowOf hX h
  have hφR :
      MDifferentiableAt I I (timeDependentFlowOf X s t) (timeDependentFlowOf X s (s + T) x) :=
    mdifferentiableAt_timeDependentFlowOf hX hRt
  have hφ : MDifferentiableAt I I (timeDependentFlowOf X s t) x :=
    mdifferentiableAt_timeDependentFlowOf hX hall
  -- Both chain rules compute the derivative of `φ_{s, t} ∘ φ_{s, s + T}` at `x`: the first at the
  -- image point, the second at `x`, which it equals.
  exact (mfderiv_timeDependentFlowOf_add_period_apply hX hT h hRt v).trans
    ((mfderiv_comp_apply x hφR hR v).symm.trans
      ((mfderiv_comp_apply_of_eq x hφ hR hfix.eq v).trans
        (congrArg (mfderiv I I (timeDependentFlowOf X s t) x) hv)))

/-- **Nondegeneracy of a periodic solution does not depend on the initial time.** If `X` is jointly
`C¹` and `T`-periodic on a manifold modelled on a complete normed space and `γ` is a `T`-periodic
solution, then `γ s'` is a nondegenerate fixed point of the return map at time `s'` exactly when
`γ s` is one of the return map at time `s`. -/
theorem isNondegenerateFixedPt_timeDependentFlowOf_iff_of_mem_periodicSolutions
    (hT : Periodic X T) {γ : ℝ → M} (hγ : γ ∈ periodicSolutions X T) (s s' : ℝ) :
    IsNondegenerateFixedPt I (timeDependentFlowOf X s' (s' + T)) (γ s') ↔
      IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) (γ s) := by
  suffices hmp : ∀ a b : ℝ, IsNondegenerateFixedPt I (timeDependentFlowOf X a (a + T)) (γ a) →
      IsNondegenerateFixedPt I (timeDependentFlowOf X b (b + T)) (γ b) from
    ⟨hmp s' s, hmp s s'⟩
  intro a b ha
  have hdom (u v : ℝ) : ((u, v), γ u) ∈ timeDependentFlowDomain X :=
    mem_timeDependentFlowDomain_of_mem_periodicSolutions hγ u v
  have hflow (u v : ℝ) : timeDependentFlowOf X u v (γ u) = γ v :=
    timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ.1 u v
  have hfix (u : ℝ) : IsFixedPt (timeDependentFlowOf X u (u + T)) (γ u) :=
    (hflow u (u + T)).trans (hγ.2 u)
  -- Differentiating `φ_{a, b} ∘ φ_{b, a} = id` and
  -- `φ_{a, a + T} ∘ φ_{b, a} = φ_{b, a} ∘ φ_{b, b + T}` at `γ b` shows that `dφ_{b, a}` is
  -- injective and intertwines the return derivatives.
  have hAB : (mfderiv I I (timeDependentFlowOf X a b) (γ a) : E →L[ℝ] E).comp
      (mfderiv I I (timeDependentFlowOf X b a) (γ b)) = ContinuousLinearMap.id ℝ E := by
    have h := mfderiv_timeDependentFlowOf_trans_of_mem hX (hdom b a)
      (by rw [hflow b a]; exact hdom a b)
    rw [hflow b a, mfderiv_timeDependentFlowOf_self] at h
    exact h.symm
  have hinter : (mfderiv I I (timeDependentFlowOf X a (a + T)) (γ a) : E →L[ℝ] E).comp
      (mfderiv I I (timeDependentFlowOf X b a) (γ b)) =
      (mfderiv I I (timeDependentFlowOf X b a) (γ b) : E →L[ℝ] E).comp
        (mfderiv I I (timeDependentFlowOf X b (b + T)) (γ b)) := by
    have h₁ := mfderiv_timeDependentFlowOf_trans_of_mem hX (hdom b a)
      (by rw [hflow b a]; exact hdom a (a + T))
    have h₂ := mfderiv_timeDependentFlowOf_trans_of_mem hX (hdom b (b + T))
      (by rw [hfix b]; exact (timeDependentFlowOf_add_period_of_mem hX hT (hdom b a)).1)
    rw [hflow b a] at h₁
    rw [hfix b, timeDependentFlowOf_add_period_add_period hX hT] at h₂
    exact h₁.symm.trans h₂
  refine isNondegenerateFixedPt_iff.2
    ⟨hfix b, mdifferentiableAt_timeDependentFlowOf hX (hdom b (b + T)), fun v hv ↦ ?_⟩
  have h1 : mfderiv I I (timeDependentFlowOf X a (a + T)) (γ a)
      (mfderiv I I (timeDependentFlowOf X b a) (γ b) v) =
      mfderiv I I (timeDependentFlowOf X b a) (γ b) v :=
    (congrArg (fun L : E →L[ℝ] E ↦ L v) hinter).trans
      (congrArg (mfderiv I I (timeDependentFlowOf X b a) (γ b) : E →L[ℝ] E) hv)
  have h0 := ha.eq_zero_of_mfderiv_apply_eq h1
  exact (congrArg (fun L : E →L[ℝ] E ↦ L v) hAB).symm.trans
    ((congrArg (mfderiv I I (timeDependentFlowOf X a b) (γ a) : E →L[ℝ] E) h0).trans (map_zero _))

/-- **Shifting time preserves nondegeneracy.** If `X` is jointly `C¹` and `T`-periodic on a
manifold modelled on a complete normed space and `γ` is a `T`-periodic solution, then the shifted
solution `t ↦ γ (t + θ)` of the shifted field `t ↦ X (t + θ)` starts at a nondegenerate fixed point
of its return map at time `s` exactly when `γ` starts at a nondegenerate fixed point of the return
map of `X` at time `s`. -/
theorem isNondegenerateFixedPt_timeDependentFlowOf_comp_add_right_iff (hT : Periodic X T)
    {γ : ℝ → M} (hγ : γ ∈ periodicSolutions X T) (θ s : ℝ) :
    IsNondegenerateFixedPt I (timeDependentFlowOf (fun t ↦ X (t + θ)) s (s + T)) (γ (s + θ)) ↔
      IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) (γ s) := by
  -- The return map of the shifted field at time `s` is that of `X` at time `s + θ`.
  have hflow : timeDependentFlowOf (fun t ↦ X (t + θ)) s (s + T) =
      timeDependentFlowOf X (s + θ) (s + θ + T) := funext fun y ↦ by
    rw [timeDependentFlowOf_comp_add_right hX, add_right_comm]
  rw [hflow]
  exact isNondegenerateFixedPt_timeDependentFlowOf_iff_of_mem_periodicSolutions hX hT hγ s (s + θ)

end CompleteSpace

section Complete

variable (hc : IsCompleteVectorField (timeDependentSuspensionField X))
include hc

/-- **Flowing over one more period.** If `X` is `T`-periodic and its suspension is complete, the
flow from `s` to `t + T` is the return map `timeDependentFlowOf X s (s + T)` followed by the flow
from `s` to `t`. -/
theorem timeDependentFlowOf_add_period (hT : Periodic X T) (s t : ℝ) (x : M) :
    timeDependentFlowOf X s (t + T) x =
      timeDependentFlowOf X s t (timeDependentFlowOf X s (s + T) x) := by
  have h : ((s, t), timeDependentFlowOf X s (s + T) x) ∈ timeDependentFlowDomain X := by
    rw [timeDependentFlowDomain_eq_univ hc]
    exact mem_univ _
  rw [← (timeDependentFlowOf_add_period_of_mem hX hT h).2, timeDependentFlowOf_trans hc hX]

/-- **Matching across a period.** If `X` is `T`-periodic and its suspension is complete, the flow
from `s` takes `y` at time `t + T` and `x` at time `t` to the same point exactly when `y` is the
preimage of `x` under the return map, `y = timeDependentFlowOf X (s + T) s x`. -/
theorem timeDependentFlowOf_add_period_eq_iff (hT : Periodic X T) (s t : ℝ) (x y : M) :
    timeDependentFlowOf X s (t + T) y = timeDependentFlowOf X s t x ↔
      y = timeDependentFlowOf X (s + T) s x := by
  have hinv (a b : ℝ) : LeftInverse (timeDependentFlowOf X b a) (timeDependentFlowOf X a b) :=
    fun z ↦ by rw [timeDependentFlowOf_trans hc hX, timeDependentFlowOf_self]
  rw [timeDependentFlowOf_add_period hX hc hT, (hinv s t).injective.eq_iff]
  constructor
  · rintro rfl
    exact (hinv s (s + T) y).symm
  · rintro rfl
    exact (hinv (s + T) s x)

/-- **The return maps at two initial times are conjugate.** If `X` is `T`-periodic and its
suspension is complete, the flow from time `s` to time `s'` carries the return map
`timeDependentFlowOf X s (s + T)` to the return map `timeDependentFlowOf X s' (s' + T)`. -/
theorem semiconj_timeDependentFlowOf_add_period (hT : Periodic X T) (s s' : ℝ) :
    Semiconj (timeDependentFlowOf X s s') (timeDependentFlowOf X s (s + T))
      (timeDependentFlowOf X s' (s' + T)) := fun y ↦ by
  -- Flowing from `s` to `s'` is flowing from `s + T` to `s' + T`, since `X` is `T`-periodic.
  have hper := timeDependentFlowOf_add_period_add_period hX hT s s'
  calc timeDependentFlowOf X s s' (timeDependentFlowOf X s (s + T) y)
      = timeDependentFlowOf X (s + T) (s' + T) (timeDependentFlowOf X s (s + T) y) := by
        rw [hper]
    _ = timeDependentFlowOf X s' (s' + T) (timeDependentFlowOf X s s' y) := by
        rw [timeDependentFlowOf_trans hc hX, timeDependentFlowOf_trans hc hX]

/-- **Nondegeneracy does not depend on the initial time.** If `X` is `T`-periodic and its
suspension is complete on a manifold modelled on a complete normed space,
`timeDependentFlowOf X s s' x` is a nondegenerate fixed point of the return map at time `s'`
exactly when `x` is a nondegenerate fixed point of the return map at time `s`. -/
theorem isNondegenerateFixedPt_timeDependentFlowOf_iff [CompleteSpace E] (hT : Periodic X T)
    (s s' : ℝ) (x : M) :
    IsNondegenerateFixedPt I (timeDependentFlowOf X s' (s' + T)) (timeDependentFlowOf X s s' x) ↔
      IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) x := by
  -- The flow from `s` to `s'` is a `C¹` diffeomorphism conjugating the two return maps.
  have hcont : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I 1
      (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) := by
    rw [← contMDiffOn_univ, ← timeDependentFlowDomain_eq_univ hc]
    exact contMDiffOn_timeDependentFlowOf le_rfl hX
  let Φ : Diffeomorph I I M M 1 :=
    { toFun := timeDependentFlowOf X s s'
      invFun := timeDependentFlowOf X s' s
      left_inv y := by rw [timeDependentFlowOf_trans hc hX, timeDependentFlowOf_self]
      right_inv y := by rw [timeDependentFlowOf_trans hc hX, timeDependentFlowOf_self]
      contMDiff_toFun := hcont.comp ((contMDiff_const (c := (s, s'))).prodMk contMDiff_id)
      contMDiff_invFun := hcont.comp ((contMDiff_const (c := (s', s))).prodMk contMDiff_id) }
  exact Φ.isNondegenerateFixedPt_iff_of_semiconj (x := x) one_ne_zero
    (semiconj_timeDependentFlowOf_add_period hX hc hT s s')

end Complete

section Compact

variable [CompactSpace M]

/-- On a compact manifold, the initial points whose trajectory from time `s` is `T`-periodic form
a closed set. -/
private theorem isClosed_setOf_forall_timeDependentFlowOf_add_eq [FiniteDimensional ℝ E] (s T : ℝ) :
    IsClosed {x : M | ∀ t, timeDependentFlowOf X s (t + T) x = timeDependentFlowOf X s t x} := by
  have hc := isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hX
  rw [ofPred_forall]
  exact isClosed_iInter fun t ↦
    isClosed_eq (continuous_timeDependentFlowOf hc le_rfl hX s (t + T))
      (continuous_timeDependentFlowOf hc le_rfl hX s t)

/-- **Finiteness of nondegenerate periodic solutions.** Let `X` be a jointly `C¹` time-dependent
vector field on a compact boundaryless manifold (whose model space is then automatically
finite-dimensional if the manifold is nonempty). If every `T`-periodic solution `γ` is
nondegenerate, in the sense that `γ s` is a nondegenerate fixed point of the return map
`timeDependentFlowOf X s (s + T)`, then `X` has only finitely many `T`-periodic solutions. -/
theorem finite_periodicSolutions (s : ℝ)
    (h : ∀ γ ∈ periodicSolutions X T,
      IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) (γ s)) :
    (periodicSolutions X T).Finite := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have : IsEmpty (ℝ → M) := ⟨fun γ ↦ hM.false (γ 0)⟩
    exact Set.toFinite _
  have := FiniteDimensional.of_locallyCompact_manifold M I
  have hc := isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hX
  -- The initial points of `T`-periodic solutions form a closed, hence compact, set of nondegenerate
  -- fixed points of the return map, so there are finitely many of them.
  have hSfin := (isClosed_setOf_forall_timeDependentFlowOf_add_eq hX s T).isCompact
    |>.finite_of_isNondegenerateFixedPt (I := I) fun x hx ↦ by
      have hγ : (fun t ↦ timeDependentFlowOf X s t x) ∈ periodicSolutions X T :=
        ⟨fun t ↦ hasMFDerivAt_timeDependentFlowOf hX
          (by rw [timeDependentFlowDomain_eq_univ hc]; exact mem_univ _), hx⟩
      simpa only [timeDependentFlowOf_self] using h _ hγ
  refine Set.Finite.of_finite_image (f := fun γ ↦ γ s) (hSfin.subset ?_) fun γ₁ hγ₁ γ₂ hγ₂ hs ↦ ?_
  · rintro _ ⟨γ, hγ, rfl⟩ t
    rw [timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ.1,
      timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ.1, hγ.2]
  · funext t
    rw [← timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ₁.1 s t,
      ← timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ₂.1 s t]
    exact congrArg (timeDependentFlowOf X s t) hs

/-- On a compact manifold, for `0 < T`, the initial points whose trajectory from time `s` is a
contractible `T`-periodic solution form a closed set. -/
private theorem isClosed_setOf_timeDependentFlowOf_mem_contractiblePeriodicSolutions
    [FiniteDimensional ℝ E] (hT0 : 0 < T) (s : ℝ) :
    IsClosed {x : M |
      (fun t ↦ timeDependentFlowOf X s t x) ∈ contractiblePeriodicSolutions X T} := by
  have : Fact (0 < T) := ⟨hT0⟩
  let _ : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let _ : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  have hc := isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hX
  have hflow := (contMDiff_timeDependentFlowOf hc le_rfl hX).continuous
  let S := {x : M | ∀ t, timeDependentFlowOf X s (t + T) x = timeDependentFlowOf X s t x}
  have hS : IsClosed S := isClosed_setOf_forall_timeDependentFlowOf_add_eq hX s T
  have hsol (y : S) : (fun t ↦ timeDependentFlowOf X s t y.val) ∈ periodicSolutions X T :=
    ⟨fun t ↦ hasMFDerivAt_timeDependentFlowOf hX
      (by rw [timeDependentFlowDomain_eq_univ hc]; exact mem_univ _), y.property⟩
  have hper (y : S) : Periodic (fun t ↦ timeDependentFlowOf X s t y.val) T := y.property
  have hcont (y : S) : Continuous (fun t ↦ timeDependentFlowOf X s t y.val) :=
    continuous_of_mem_periodicSolutions (hsol y)
  -- The loops over `[s, s + T]` depend continuously on `y ∈ S`, so contractibility is closed in
  -- `S`.
  have hfam : Continuous ↿fun y : S ↦ (hper y).loop (hcont y) s := by
    have heq : (↿fun y : S ↦ (hper y).loop (hcont y) s) =
        (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) ∘
          fun q ↦ ((s, s + q.2 * T), q.1.val) :=
      funext fun q ↦ Periodic.loop_apply _ _ _ _
    rw [heq]
    exact hflow.comp (by fun_prop)
  have hK : IsClosed (Subtype.val ''
      {y : S | ((hper y).loop (hcont y) s).Homotopic (Path.refl _)}) :=
    hS.isClosedMap_subtypeVal _ (isClopen_setOf_homotopic_refl _ hfam).isClosed
  have hEq : {x : M | (fun t ↦ timeDependentFlowOf X s t x) ∈ contractiblePeriodicSolutions X T} =
      Subtype.val '' {y : S | ((hper y).loop (hcont y) s).Homotopic (Path.refl _)} := by
    ext x
    refine ⟨fun hx ↦ ⟨⟨x, hx.1.2⟩, ((hper ⟨x, hx.1.2⟩).exists_nullhomotopic_iff_loop_homotopic_refl
      (hcont ⟨x, hx.1.2⟩) s).1 hx.2, rfl⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    exact ⟨hsol y, ((hper y).exists_nullhomotopic_iff_loop_homotopic_refl (hcont y) s).2 hy⟩
  rwa [hEq]

/-- Positive-period core of `TauCeti.finite_contractiblePeriodicSolutions`, allowing an arbitrary
map `f` in the nondegeneracy hypothesis so that negative periods reduce directly to `0 < -T`. -/
private theorem finite_contractiblePeriodicSolutions_of_pos {f : M → M} (hT0 : 0 < T) (s : ℝ)
    (h : ∀ γ ∈ contractiblePeriodicSolutions X T, IsNondegenerateFixedPt I f (γ s)) :
    (contractiblePeriodicSolutions X T).Finite := by
  rcases isEmpty_or_nonempty M with hM | hM
  · have : IsEmpty (ℝ → M) := ⟨fun γ ↦ hM.false (γ 0)⟩
    exact Set.toFinite _
  have := FiniteDimensional.of_locallyCompact_manifold M I
  have hKfin := (isClosed_setOf_timeDependentFlowOf_mem_contractiblePeriodicSolutions hX hT0 s)
    |>.isCompact.finite_of_isNondegenerateFixedPt (I := I) fun x hx ↦ by
      simpa only [timeDependentFlowOf_self] using h _ hx
  refine Set.Finite.of_finite_image (f := fun γ ↦ γ s) (hKfin.subset ?_) fun γ₁ hγ₁ γ₂ hγ₂ hs ↦ ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    rw [mem_ofPred_eq, funext (timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ.1.1 s)]
    exact hγ
  · funext t
    rw [← timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ₁.1.1 s t,
      ← timeDependentFlowOf_eq_of_forall_hasMFDerivAt hX hγ₂.1.1 s t]
    exact congrArg (timeDependentFlowOf X s t) hs

/-- **Finiteness of nondegenerate contractible periodic solutions.** Let `X` be a jointly `C¹`
time-dependent vector field on a compact boundaryless manifold (whose model space is then
automatically finite-dimensional if the manifold is nonempty). If every contractible `T`-periodic
solution `γ` is nondegenerate, in the sense that `γ s` is a nondegenerate fixed point of the return
map `timeDependentFlowOf X s (s + T)`, then `X` has only finitely many contractible `T`-periodic
solutions. Noncontractible solutions may be degenerate, and there may be infinitely many of
them. -/
theorem finite_contractiblePeriodicSolutions (s : ℝ)
    (h : ∀ γ ∈ contractiblePeriodicSolutions X T,
      IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) (γ s)) :
    (contractiblePeriodicSolutions X T).Finite := by
  rcases lt_trichotomy T 0 with hT | rfl | hT
  · rw [← contractiblePeriodicSolutions_neg]
    exact finite_contractiblePeriodicSolutions_of_pos hX (neg_pos.2 hT) s
      fun γ hγ ↦ h γ ((contractiblePeriodicSolutions_neg X T).subset hγ)
  · rcases subsingleton_or_nontrivial E with _ | hE
    · -- On a 0-dimensional compact manifold every point is a nondegenerate fixed point of `id`.
      refine (finite_periodicSolutions hX s fun γ _ ↦ ?_).subset
        contractiblePeriodicSolutions_subset
      rw [add_zero]
      exact isNondegenerateFixedPt_iff.2 ⟨timeDependentFlowOf_self X s (γ s),
        mdifferentiableAt_id.congr_of_eventuallyEq
          (Eventually.of_forall (timeDependentFlowOf_self X s)),
        fun v _ ↦ Subsingleton.elim (α := E) v 0⟩
    · -- When `dim E > 0`, `φ_{s, s} = id` has no nondegenerate fixed points.
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hempty : contractiblePeriodicSolutions X 0 = ∅ := eq_empty_of_forall_notMem fun γ hγ ↦ by
        have hnd := h γ hγ
        rw [add_zero] at hnd
        exact hv (hnd.eq_zero_of_mfderiv_apply_eq (by
          rw [mfderiv_timeDependentFlowOf_self]
          rfl))
      rw [hempty]
      exact finite_empty
  · exact finite_contractiblePeriodicSolutions_of_pos hX hT s h

end Compact

end Flow

end TauCeti
