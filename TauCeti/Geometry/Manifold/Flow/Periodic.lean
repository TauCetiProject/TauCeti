/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.On
public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Manifold.Topology
public import TauCeti.Topology.Homotopy.AddCircle
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.UniformConvergence

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
(`TauCeti.periodicSolutionsEquivFixedPoints`).

On a compact boundaryless manifold modelled on a finite-dimensional space the return map is defined
and `C¹` everywhere. If every periodic solution is nondegenerate, meaning that its initial point is
a nondegenerate fixed point of the return map (`TauCeti.IsNondegenerateFixedPt`), the fixed points
are isolated, so there are only finitely many periodic solutions
(`TauCeti.finite_periodicSolutions`).

This is the manifold counterpart of `TauCeti.periodicSolutionEquivFixedPoints` in
`TauCeti.Dynamics.Flow.Periodic.Basic`, which treats globally Lipschitz fields on Banach spaces.

Hamiltonian Floer theory on the contractible sector uses only the **contractible** periodic
solutions (`TauCeti.contractiblePeriodicSolutions`), those whose loop `ℝ ⧸ Tℤ → M` is
null-homotopic, and assumes nondegeneracy only for them. If they are all nondegenerate, there are
still only finitely many of them (`TauCeti.finite_contractiblePeriodicSolutions`). The trajectory
of a fixed point of the return map over one period is a loop depending continuously on the fixed
point, and on a manifold null-homotopy of such a family of loops is locally constant
(`isClopen_setOf_homotopic_refl`). So the initial points of the contractible solutions form a
closed subset of the compact set of fixed points, and a compact set of nondegenerate, hence
isolated, fixed points is finite.

## Main definitions

* `TauCeti.periodicSolutions X T`: the `T`-periodic solutions of `X`.
* `TauCeti.periodicSolutionsEquivFixedPoints`: periodic solutions correspond to fixed points of the
  return map.
* `TauCeti.contractiblePeriodicSolutions X T`: the `T`-periodic solutions whose loop is
  null-homotopic.

## Main results

* `TauCeti.mem_periodicSolutions_const_iff`: the periodic solutions of an autonomous field are its
  periodic integral curves.
* `TauCeti.timeDependentFlowOf_add_period_of_mem`: translating both times by a period of the field
  preserves the domain and the flow.
* `TauCeti.mem_timeDependentFlowDomain_of_isFixedPt`: for `T ≠ 0`, the trajectory of a fixed point
  of the return map is defined for all time.
* `TauCeti.timeDependentFlowOf_add_period` and `TauCeti.timeDependentFlowOf_add_period_eq_iff`:
  for a complete suspension, the flow over one more period is the return map followed by the flow,
  so points at times `t + T` and `t` match exactly across the inverse return map.
* `TauCeti.finite_periodicSolutions`: on a compact boundaryless finite-dimensional manifold, a
  field whose periodic solutions are all nondegenerate has finitely many of them.
* `TauCeti.finite_contractiblePeriodicSolutions`: the same for the contractible periodic solutions,
  assuming only that they are nondegenerate.
* `TauCeti.exists_nullhomotopic_slice_iff_of_isPreconnected`: null-homotopy of `T`-periodic slices
  is invariant along preconnected parameter sets.
* `TauCeti.exists_nullhomotopic_iff_of_tendstoUniformly_comp` and
  `TauCeti.mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp`: uniform convergence
  through an injective map on a compact set preserves loop contractibility.
* `TauCeti.exists_pos_forall_eq_of_isNondegenerateFixedPt`: a periodic solution through a
  nondegenerate fixed point of the return map is metric-isolated in any compact set.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 11.1 (periodic orbits of time-dependent Hamiltonians as fixed points of the time-one
  map).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
-/

public section

noncomputable section

open Function Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {X : ℝ → (x : M) → TangentSpace I x} {s t T : ℝ} {x : M}

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

section Flow

variable [CompleteSpace E] [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]
  (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
    (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
include hX

omit [CompleteSpace E] in
/-- **The flow of a time-periodic field is invariant under translation of time by a period.** If
`X (t + T) = X t` for all `t` and the flow from `s` to `t` is defined at `x`, then so is the flow
from `s + T` to `t + T`, with the same value. -/
theorem timeDependentFlowOf_add_period_of_mem (hT : Periodic X T)
    (h : ((s, t), x) ∈ timeDependentFlowDomain X) :
    ((s + T, t + T), x) ∈ timeDependentFlowDomain X ∧
      timeDependentFlowOf X (s + T) (t + T) x = timeDependentFlowOf X s t x := by
  obtain ⟨a, b, hs, ht, hab⟩ := exists_Ioo_of_mem_timeDependentFlowDomain h
  -- The trajectory delayed by `T` solves the equation, since the field is `T`-periodic.
  have hγ (u : ℝ) (hu : u ∈ Ioo (a + T) (b + T)) :
      HasMFDerivAt 𝓘(ℝ, ℝ) I (fun r ↦ timeDependentFlowOf X s (r - T) x) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X u (timeDependentFlowOf X s (u - T) x))) := by
    have hd := hasMFDerivAt_timeDependentFlowOf hX
      (hab (u - T) ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    have hsub : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun r : ℝ ↦ r - T) u
        (ContinuousLinearMap.id ℝ ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.2 ((hasFDerivAt_id u).sub_const T)
    have hX' : X (u - T) = X u := by simpa using (hT (u - T)).symm
    rw [← hX']
    -- Composing with the derivative `id` of the translation leaves the velocity unchanged.
    exact (hd.comp u hsub).congr_mfderiv (ContinuousLinearMap.ext fun r ↦ rfl)
  have hs' : s + T ∈ Ioo (a + T) (b + T) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have ht' : t + T ∈ Ioo (a + T) (b + T) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmem := mem_timeDependentFlowDomain_of_hasMFDerivAt hγ hs' ht'
  have heq := timeDependentFlowOf_eq_of_hasMFDerivAt hX hγ hs' ht'
  simp only [add_sub_cancel_right, timeDependentFlowOf_self] at hmem heq
  exact ⟨hmem, heq⟩

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
/-- **Periodic solutions are fixed points of the return map.** For a `T`-periodic field `X`, with
`T ≠ 0`, evaluation at the initial time `s` identifies the `T`-periodic solutions of `X` with the
fixed points of the return map `timeDependentFlowOf X s (s + T)` in its domain. The inverse sends a
fixed point to its trajectory under the flow from time `s`. -/
def periodicSolutionsEquivFixedPoints (hT : Periodic X T) (hT0 : T ≠ 0) (s : ℝ) :
    periodicSolutions X T ≃ {x | ((s, s + T), x) ∈ timeDependentFlowDomain X ∧
      IsFixedPt (timeDependentFlowOf X s (s + T)) x} where
  toFun γ := ⟨γ.1 s, by
    -- A global solution stays in the domain and is the trajectory of the flow.
    have hγ (u : ℝ) (_ : u ∈ Ioo (s - |T| - 1) (s + |T| + 1)) := γ.2.1 u
    have hs : s ∈ Ioo (s - |T| - 1) (s + |T| + 1) :=
      ⟨by linarith [abs_nonneg T], by linarith [abs_nonneg T]⟩
    have hsT : s + T ∈ Ioo (s - |T| - 1) (s + |T| + 1) :=
      ⟨by linarith [neg_abs_le T], by linarith [le_abs_self T]⟩
    exact ⟨mem_timeDependentFlowDomain_of_hasMFDerivAt hγ hs hsT,
      (timeDependentFlowOf_eq_of_hasMFDerivAt hX hγ hs hsT).trans (γ.2.2 s)⟩⟩
  invFun x := ⟨fun t ↦ timeDependentFlowOf X s t x, fun t ↦ hasMFDerivAt_timeDependentFlowOf hX
      (mem_timeDependentFlowDomain_of_isFixedPt hX hT hT0 x.2.1 x.2.2 t), fun t ↦ by
    -- Flow for one period, which fixes `x`, then translate the remaining time back by `T`.
    have hall := mem_timeDependentFlowDomain_of_isFixedPt hX hT hT0 x.2.1 x.2.2
    obtain ⟨hmem, heq⟩ := timeDependentFlowOf_add_period_of_mem hX hT (hall t)
    have htr := (timeDependentFlowOf_trans_of_mem hX x.2.1
      (by rwa [x.2.2.eq])).2
    dsimp only
    rw [← htr, x.2.2.eq, heq]⟩
  left_inv γ := Subtype.ext <| funext fun t ↦ by
    have hγ (u : ℝ) (_ : u ∈ Ioo (min s t - 1) (max s t + 1)) := γ.2.1 u
    exact timeDependentFlowOf_eq_of_hasMFDerivAt hX hγ
      ⟨by linarith [min_le_left s t], by linarith [le_max_left s t]⟩
      ⟨by linarith [min_le_right s t], by linarith [le_max_right s t]⟩
  right_inv x := Subtype.ext (timeDependentFlowOf_self X s x)

omit [CompleteSpace E] in
/-- The correspondence from periodic solutions to fixed points evaluates at the initial time. -/
@[simp]
theorem periodicSolutionsEquivFixedPoints_apply (hT : Periodic X T) (hT0 : T ≠ 0) (s : ℝ)
    (γ : periodicSolutions X T) :
    (periodicSolutionsEquivFixedPoints hX hT hT0 s γ : M) = γ.1 s :=
  (rfl)

omit [CompleteSpace E] in
/-- The periodic solution of a fixed point of the return map is its trajectory under the flow. -/
@[simp]
theorem periodicSolutionsEquivFixedPoints_symm_apply (hT : Periodic X T) (hT0 : T ≠ 0) (s : ℝ)
    (x : {x | ((s, s + T), x) ∈ timeDependentFlowDomain X ∧
      IsFixedPt (timeDependentFlowOf X s (s + T)) x}) (t : ℝ) :
    ((periodicSolutionsEquivFixedPoints hX hT hT0 s).symm x).1 t =
      timeDependentFlowOf X s t x :=
  (rfl)

section Complete

variable (hc : IsCompleteVectorField (timeDependentSuspensionField X))
include hc

omit [CompleteSpace E] in
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

omit [CompleteSpace E] in
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

end Complete

end Flow

/-- **Finiteness of nondegenerate periodic solutions.** Let `X` be a jointly `C¹` time-dependent
vector field on a compact boundaryless manifold modelled on a finite-dimensional space, `T`-periodic
in time with `T ≠ 0`. If every `T`-periodic solution `γ` is nondegenerate, in the sense that `γ s`
is a nondegenerate fixed point of the return map `timeDependentFlowOf X s (s + T)`, then `X` has
only finitely many `T`-periodic solutions. -/
theorem finite_periodicSolutions [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
    [IsManifold I 1 M] [BoundarylessManifold I M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hT : Periodic X T) (hT0 : T ≠ 0) (s : ℝ)
    (h : ∀ γ ∈ periodicSolutions X T,
      IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) (γ s)) :
    (periodicSolutions X T).Finite := by
  -- On a compact manifold the flow is defined everywhere, so the return map is continuous.
  have hcomplete := isCompleteVectorField_timeDependentSuspensionField hX isCompact_univ
    (fun _ _ hy ↦ (hy (mem_univ _)).elim)
  have hφ : Continuous (timeDependentFlowOf X s (s + T)) :=
    ((contMDiff_timeDependentFlowOf hcomplete le_rfl hX).comp
      ((contMDiff_const (c := (s, s + T))).prodMk contMDiff_id)).continuous
  set e := periodicSolutionsEquivFixedPoints hX hT hT0 s
  -- Every fixed point of the return map is the initial point of a periodic solution.
  have hfin := finite_fixedPoints_of_isNondegenerateFixedPt hφ fun x hx ↦ by
    have hx' : x ∈ {x | ((s, s + T), x) ∈ timeDependentFlowDomain X ∧
        IsFixedPt (timeDependentFlowOf X s (s + T)) x} :=
      ⟨by rw [timeDependentFlowDomain_eq_univ hcomplete]; exact mem_univ _, hx⟩
    have hγ := h _ (e.symm ⟨x, hx'⟩).2
    rwa [periodicSolutionsEquivFixedPoints_symm_apply, timeDependentFlowOf_self] at hγ
  have : Finite {x | ((s, s + T), x) ∈ timeDependentFlowDomain X ∧
      IsFixedPt (timeDependentFlowOf X s (s + T)) x} :=
    (hfin.subset (ofPred_subset_ofPred.2 fun _ hx ↦ hx.2)).to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)

/-- **Finiteness of nondegenerate contractible periodic solutions.** Let `X` be a jointly `C¹`
time-dependent vector field on a compact boundaryless manifold (whose model space is then
automatically finite-dimensional if the manifold is nonempty), `T`-periodic in time with
`0 < T`. If every contractible `T`-periodic solution `γ` is nondegenerate, in the sense that
`γ s` is a nondegenerate fixed point of the return map `timeDependentFlowOf X s (s + T)`, then
`X` has only finitely many contractible `T`-periodic solutions. Noncontractible solutions may be
degenerate, and there may be infinitely many of them. -/
theorem finite_contractiblePeriodicSolutions [CompactSpace M] [T2Space M]
    [IsManifold I 1 M] [BoundarylessManifold I M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hT : Periodic X T) (hT0 : 0 < T) (s : ℝ)
    (h : ∀ γ ∈ contractiblePeriodicSolutions X T,
      IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) (γ s)) :
    (contractiblePeriodicSolutions X T).Finite := by
  -- Without points there are no solutions; otherwise compactness forces `E` finite-dimensional.
  rcases isEmpty_or_nonempty M with hM | hM
  · have : IsEmpty (ℝ → M) := ⟨fun γ ↦ hM.false (γ 0)⟩
    exact Set.toFinite _
  have := FiniteDimensional.of_locallyCompact_manifold M I
  have : Fact (0 < T) := ⟨hT0⟩
  let _ : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let _ : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  -- On a compact manifold the flow is defined everywhere and is continuous.
  have hcomplete := isCompleteVectorField_timeDependentSuspensionField hX isCompact_univ
    (fun _ _ hy ↦ (hy (mem_univ _)).elim)
  have hflow := (contMDiff_timeDependentFlowOf hcomplete le_rfl hX).continuous
  let e := periodicSolutionsEquivFixedPoints hX hT hT0.ne' s
  -- A periodic solution is contractible exactly when its loop over `[s, s + T]` is
  -- null-homotopic.
  have hcont (γ : periodicSolutions X T) : Continuous γ.1 := continuous_of_mem_periodicSolutions γ.2
  have hper (γ : periodicSolutions X T) : Periodic γ.1 T := γ.2.2
  let P (γ : periodicSolutions X T) : Prop :=
    ((hper γ).loop (hcont γ) s).Homotopic (Path.refl (γ.1 s))
  have hP (γ : periodicSolutions X T) : P γ ↔ γ.1 ∈ contractiblePeriodicSolutions X T :=
    ⟨fun hγ ↦ ⟨γ.2, ((hper γ).exists_nullhomotopic_iff_loop_homotopic_refl (hcont γ) s).2 hγ⟩,
      fun hγ ↦ ((hper γ).exists_nullhomotopic_iff_loop_homotopic_refl (hcont γ) s).1 hγ.2⟩
  -- These loops depend continuously on the fixed point, which ranges over a closed set.
  have hfam : Continuous ↿fun y ↦ (hper (e.symm y)).loop (hcont (e.symm y)) s := by
    have heq : (↿fun y ↦ (hper (e.symm y)).loop (hcont (e.symm y)) s) =
        (fun p : (ℝ × ℝ) × M ↦ timeDependentFlowOf X p.1.1 p.1.2 p.2) ∘
          fun q ↦ ((s, s + q.2 * T), q.1.1) :=
      funext fun q ↦ (Periodic.loop_apply _ _ _ _).trans
        (periodicSolutionsEquivFixedPoints_symm_apply hX hT hT0.ne' s _ _)
    rw [heq]
    exact hflow.comp (by fun_prop)
  have hY : IsClosed {x | ((s, s + T), x) ∈ timeDependentFlowDomain X ∧
      IsFixedPt (timeDependentFlowOf X s (s + T)) x} := by
    have hφ : Continuous (timeDependentFlowOf X s (s + T)) :=
      hflow.comp (by fun_prop : Continuous fun x : M ↦ ((s, s + T), x))
    convert isClosed_fixedPoints hφ using 1
    ext x
    simp [timeDependentFlowDomain_eq_univ hcomplete]
  -- The initial points of the contractible solutions form a closed set of nondegenerate fixed
  -- points, hence a finite set.
  have hK : IsClosed (Subtype.val '' {y | P (e.symm y)}) :=
    hY.isClosedMap_subtype_val _ (isClopen_setOf_homotopic_refl _ hfam).isClosed
  have hKfin := hK.isCompact.finite_of_isNondegenerateFixedPt (I := I) <| by
    rintro _ ⟨y, hy, rfl⟩
    have hnd := h _ ((hP _).1 hy)
    rwa [periodicSolutionsEquivFixedPoints_symm_apply, timeDependentFlowOf_self] at hnd
  refine Set.Finite.of_finite_image (f := fun γ ↦ γ s) (hKfin.subset ?_) fun γ₁ hγ₁ γ₂ hγ₂ hs ↦ ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨e ⟨γ, hγ.1⟩, ?_, by simp [e]⟩
    rw [Set.mem_ofPred_eq, Equiv.symm_apply_apply]
    exact (hP _).2 hγ
  · exact congrArg Subtype.val
      (e.injective (a₁ := ⟨γ₁, hγ₁.1⟩) (a₂ := ⟨γ₂, hγ₂.1⟩) (Subtype.ext (by simpa [e] using hs)))

section NullhomotopyAndIsolation

open Filter Topology
open scoped UniformConvergence

/-- **Null-homotopy of periodic slices is constant along preconnected parameter sets.** Let `M` be
a charted space modelled on `I : ModelWithCorners ℝ E H`, `U` a preconnected subset of a
topological space `P`, and `u : P × ℝ → M` continuous on `U × ℝ` with `T`-periodic slices (`0 < T`).
Then the circle map `AddCircle T → M` of `u(p₁, ·)` is null-homotopic if and only if that of
`u(p₂, ·)` is, for any `p₁, p₂ ∈ U`. -/
theorem exists_nullhomotopic_slice_iff_of_isPreconnected (I : ModelWithCorners ℝ E H)
    {P : Type*} [TopologicalSpace P] {U : Set P} (hU : IsPreconnected U) {u : P × ℝ → M}
    (hu : ContinuousOn u (U ×ˢ univ)) (hT : 0 < T)
    (hper : ∀ p ∈ U, Periodic (fun t ↦ u (p, t)) T) {p₁ p₂ : P} (hp₁ : p₁ ∈ U) (hp₂ : p₂ ∈ U) :
    (∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (p₁, t)) ↔
      ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = u (p₂, t) := by
  have : Fact (0 < T) := ⟨hT⟩
  let _ : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let _ : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  let _ : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.1 hU
  have hslice (p : U) : Continuous fun t ↦ u (p.1, t) :=
    hu.comp_continuous (continuous_const.prodMk continuous_id) fun t ↦ ⟨p.2, mem_univ t⟩
  let γ (p : U) : Path (u (p.1, 0)) (u (p.1, 0)) := (hper p.1 p.2).loop (hslice p) 0
  have hγ_eq : ↿γ = fun q : U × unitInterval ↦ u (q.1.1, (0 : ℝ) + (q.2 : ℝ) * T) :=
    funext fun q ↦ (hper q.1.1 q.1.2).loop_apply (hslice q.1) 0 q.2
  have hγ : Continuous ↿γ := by
    rw [hγ_eq]
    exact hu.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_const.add ((continuous_subtype_val.comp continuous_snd).mul continuous_const)))
      fun q ↦ ⟨q.1.2, mem_univ _⟩
  have hclopen := isClopen_setOf_homotopic_refl γ hγ
  rw [(hper p₁ hp₁).exists_nullhomotopic_iff_loop_homotopic_refl (hslice ⟨p₁, hp₁⟩) 0,
    (hper p₂ hp₂).exists_nullhomotopic_iff_loop_homotopic_refl (hslice ⟨p₂, hp₂⟩) 0]
  rcases isClopen_iff.1 hclopen with h | h
  · have h₁ : (⟨p₁, hp₁⟩ : U) ∉ {p : U | (γ p).Homotopic (Path.refl (u (p.1, 0)))} :=
      h ▸ notMem_empty _
    have h₂ : (⟨p₂, hp₂⟩ : U) ∉ {p : U | (γ p).Homotopic (Path.refl (u (p.1, 0)))} :=
      h ▸ notMem_empty _
    exact iff_of_false h₁ h₂
  · have h₁ : (⟨p₁, hp₁⟩ : U) ∈ {p : U | (γ p).Homotopic (Path.refl (u (p.1, 0)))} :=
      h.symm ▸ mem_univ _
    have h₂ : (⟨p₂, hp₂⟩ : U) ∈ {p : U | (γ p).Homotopic (Path.refl (u (p.1, 0)))} :=
      h.symm ▸ mem_univ _
    exact iff_of_true h₁ h₂

/-- Inside the space of continuous `T`-periodic curves in `e(K)` equipped with the topology of
uniform convergence, those whose unique lift in `K` descends to a null-homotopic map on
`AddCircle T` form a clopen subset. -/
private theorem isClopen_setOf_exists_nullhomotopic_of_isCompact (I : ModelWithCorners ℝ E H)
    {F : Type*} [MetricSpace F] {e : M → F} {K : Set M} (hK : IsCompact K)
    (he : ContinuousOn e K) (he_inj : InjOn e K) (hT : 0 < T) :
    IsClopen {f : {f : ℝ →ᵤ F | Continuous (UniformFun.toFun f) ∧
        Periodic (UniformFun.toFun f) T ∧ ∀ t, UniformFun.toFun f t ∈ e '' K} |
      ∃ γ : ℝ → M, (∀ t, γ t ∈ K) ∧ e ∘ γ = UniformFun.toFun f.1 ∧
        ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t} := by
  have : Fact (0 < T) := ⟨hT⟩
  let _ : LocallyPathConnectedSpace M := I.locallyPathConnectedSpace_of_chartedSpace M
  let _ : SemilocallySimplyConnectedSpace M := I.semilocallySimplyConnectedSpace M
  have := isCompact_iff_compactSpace.1 hK
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    (he.comp_continuous continuous_subtype_val Subtype.prop).isClosedEmbedding fun p q h ↦
      Subtype.ext (he_inj p.2 q.2 h)
  let φ : range (fun p : K ↦ e p) ≃ₜ K := hemb.isEmbedding.toHomeomorph.symm
  let L := {f : ℝ →ᵤ F | Continuous (UniformFun.toFun f) ∧ Periodic (UniformFun.toFun f) T ∧
    ∀ t, UniformFun.toFun f t ∈ e '' K}
  have hmem (f : L) (t : ℝ) : UniformFun.toFun f.1 t ∈ range fun p : K ↦ e p := by
    obtain ⟨p, hp, hp'⟩ := f.2.2.2 t
    exact ⟨⟨p, hp⟩, hp'⟩
  let lift (f : L) (t : ℝ) : M := (φ ⟨UniformFun.toFun f.1 t, hmem f t⟩ : K)
  have hliftK (f : L) (t : ℝ) : lift f t ∈ K := (φ _).2
  have helift (f : L) : e ∘ lift f = UniformFun.toFun f.1 := funext fun t ↦
    congrArg Subtype.val
      (hemb.isEmbedding.toHomeomorph.apply_symm_apply ⟨UniformFun.toFun f.1 t, hmem f t⟩)
  have hliftc (f : L) : Continuous (lift f) :=
    continuous_subtype_val.comp (φ.continuous.comp (f.2.1.subtype_mk (hmem f)))
  have hliftp (f : L) : Periodic (lift f) T := fun t ↦ by
    dsimp only [lift]
    congr 2
    exact Subtype.ext (f.2.2.1 t)
  have hθc : Continuous fun θ : unitInterval ↦ (0 : ℝ) + (θ : ℝ) * T :=
    continuous_const.add ((continuous_subtype_val.comp continuous_id).mul continuous_const)
  have heval : Continuous fun q : L × unitInterval ↦
      UniformFun.toFun q.1.1 ((0 : ℝ) + (q.2 : ℝ) * T) := by
    refine continuous_iff_continuousAt.2 fun ⟨f₀, θ₀⟩ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    have hθ : ∀ᶠ θ : unitInterval in 𝓝 θ₀,
        dist (UniformFun.toFun f₀.1 ((0 : ℝ) + (θ : ℝ) * T))
          (UniformFun.toFun f₀.1 ((0 : ℝ) + (θ₀ : ℝ) * T)) < ε / 2 :=
      Metric.tendsto_nhds.1 ((f₀.2.1.comp hθc).tendsto θ₀) (ε / 2) (half_pos hε)
    have hf : ∀ᶠ f : L in 𝓝 f₀, edist f.1 f₀.1 < ENNReal.ofReal (ε / 2) :=
      (continuous_subtype_val.tendsto f₀).eventually
        (Metric.eball_mem_nhds f₀.1 (ENNReal.ofReal_pos.2 (half_pos hε)))
    filter_upwards [prod_mem_nhds hf hθ] with ⟨f, θ⟩ ⟨hf', hθ'⟩
    calc dist (UniformFun.toFun f.1 ((0 : ℝ) + (θ : ℝ) * T))
          (UniformFun.toFun f₀.1 ((0 : ℝ) + (θ₀ : ℝ) * T))
        ≤ dist (UniformFun.toFun f.1 ((0 : ℝ) + (θ : ℝ) * T))
            (UniformFun.toFun f₀.1 ((0 : ℝ) + (θ : ℝ) * T)) +
          dist (UniformFun.toFun f₀.1 ((0 : ℝ) + (θ : ℝ) * T))
            (UniformFun.toFun f₀.1 ((0 : ℝ) + (θ₀ : ℝ) * T)) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add
          (edist_lt_ofReal.1 ((UniformFun.edist_le.1 le_rfl _).trans_lt hf')) hθ'
      _ = ε := add_halves ε
  have hfam_eq : (↿fun f : L ↦ (hliftp f).loop (hliftc f) 0) =
      fun q : L × unitInterval ↦ lift q.1 ((0 : ℝ) + (q.2 : ℝ) * T) :=
    funext fun q ↦ (hliftp q.1).loop_apply (hliftc q.1) 0 q.2
  have hfam : Continuous ↿fun f : L ↦ (hliftp f).loop (hliftc f) 0 := by
    rw [hfam_eq]
    exact continuous_subtype_val.comp
      (φ.continuous.comp (heval.subtype_mk fun q ↦ hmem q.1 ((0 : ℝ) + (q.2 : ℝ) * T)))
  convert isClopen_setOf_homotopic_refl (fun f : L ↦ (hliftp f).loop (hliftc f) 0) hfam using 1
  refine Set.ext fun f ↦ ?_
  change (∃ γ : ℝ → M, (∀ t, γ t ∈ K) ∧ e ∘ γ = UniformFun.toFun f.1 ∧
      ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ t) ↔
    ((hliftp f).loop (hliftc f) 0).Homotopic (Path.refl (lift f 0))
  rw [← (hliftp f).exists_nullhomotopic_iff_loop_homotopic_refl (hliftc f) 0]
  refine ⟨?_, fun h ↦ ⟨lift f, hliftK f, helift f, h⟩⟩
  rintro ⟨γ, hγK, heγ, hnull⟩
  have hγeq : γ = lift f := funext fun t ↦
    he_inj (hγK t) (hliftK f t) (congrFun (heγ.trans (helift f).symm) t)
  exact hγeq ▸ hnull

/-- **Uniform convergence through an injective map on a compact set preserves loop
contractibility.** Let `M` be a charted space modelled on `I : ModelWithCorners ℝ E H`, `K ⊆ M`
compact, and `e : M → F` continuous and injective on `K`. If continuous `T`-periodic curves `γ_i` in
`K` (`0 < T`) converge uniformly after applying `e` to `e ∘ γ₀` for a continuous `T`-periodic curve
`γ₀` in `K`, then eventually `γ_i` is null-homotopic as a map `AddCircle T → M` if and only if `γ₀`
is. -/
theorem exists_nullhomotopic_iff_of_tendstoUniformly_comp (I : ModelWithCorners ℝ E H)
    {F : Type*} [MetricSpace F] {e : M → F} {K : Set M} (hK : IsCompact K)
    (he : ContinuousOn e K) (he_inj : InjOn e K) (hT : 0 < T) {ι : Type*} {l : Filter ι}
    {γ : ι → ℝ → M} {γ₀ : ℝ → M} (hγ₀c : Continuous γ₀) (hγ₀p : Periodic γ₀ T)
    (hγ₀K : ∀ t, γ₀ t ∈ K) (hγc : ∀ᶠ i in l, Continuous (γ i))
    (hγp : ∀ᶠ i in l, Periodic (γ i) T) (hγK : ∀ᶠ i in l, ∀ t, γ i t ∈ K)
    (hconv : TendstoUniformly (fun i t ↦ e (γ i t)) (e ∘ γ₀) l) :
    ∀ᶠ i in l, (∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ i t) ↔
      ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ₀ t := by
  let L := {f : ℝ →ᵤ F | Continuous (UniformFun.toFun f) ∧ Periodic (UniformFun.toFun f) T ∧
    ∀ t, UniformFun.toFun f t ∈ e '' K}
  let P : Set L := {f | ∃ γ' : ℝ → M, (∀ t, γ' t ∈ K) ∧ e ∘ γ' = UniformFun.toFun f.1 ∧
    ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ' t}
  have hclopen : IsClopen P :=
    isClopen_setOf_exists_nullhomotopic_of_isCompact I hK he he_inj hT
  have hmemP {δ : ℝ → M} (hδK : ∀ t, δ t ∈ K) (f : L) (hf : UniformFun.toFun f.1 = e ∘ δ) :
      f ∈ P ↔ ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = δ t := by
    refine ⟨?_, fun h ↦ ⟨δ, hδK, hf.symm, h⟩⟩
    rintro ⟨γ', hγ'K, heγ', hnull⟩
    have heq : γ' = δ := funext fun t ↦
      he_inj (hγ'K t) (hδK t) (congrFun (heγ'.trans hf) t)
    exact heq ▸ hnull
  let f₀ : L := ⟨UniformFun.ofFun (e ∘ γ₀), he.comp_continuous hγ₀c hγ₀K,
    fun t ↦ by simp only [UniformFun.toFun_ofFun, comp_apply, hγ₀p t],
    fun t ↦ mem_image_of_mem e (hγ₀K t)⟩
  have hf₀P : f₀ ∈ P ↔ ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ₀ t :=
    hmemP hγ₀K f₀ rfl
  have hlim : Tendsto (fun i ↦ UniformFun.ofFun fun t ↦ e (γ i t)) l (𝓝 f₀.1) :=
    UniformFun.tendsto_iff_tendstoUniformly.2 hconv
  by_cases hxP : f₀ ∈ P
  · obtain ⟨U, hU, hUP⟩ := (mem_nhds_subtype L f₀ P).1 (hclopen.isOpen.mem_nhds hxP)
    filter_upwards [hγc, hγp, hγK, hlim.eventually hU] with i hic hip hiK hiU
    let fi : L := ⟨UniformFun.ofFun (e ∘ γ i), he.comp_continuous hic hiK,
      fun t ↦ by simp only [UniformFun.toFun_ofFun, comp_apply, hip t],
      fun t ↦ mem_image_of_mem e (hiK t)⟩
    exact iff_of_true ((hmemP hiK fi rfl).1 (hUP hiU)) (hf₀P.1 hxP)
  · obtain ⟨U, hU, hUP⟩ := (mem_nhds_subtype L f₀ Pᶜ).1 (hclopen.compl.isOpen.mem_nhds hxP)
    filter_upwards [hγc, hγp, hγK, hlim.eventually hU] with i hic hip hiK hiU
    let fi : L := ⟨UniformFun.ofFun (e ∘ γ i), he.comp_continuous hic hiK,
      fun t ↦ by simp only [UniformFun.toFun_ofFun, comp_apply, hip t],
      fun t ↦ mem_image_of_mem e (hiK t)⟩
    exact iff_of_false (fun hi ↦ hUP hiU ((hmemP hiK fi rfl).2 hi)) (fun hx' ↦ hxP (hf₀P.2 hx'))

/-- **Uniform convergence of periodic loops characterizes contractibility of a limit orbit.** Let
`γ₀` be a `T`-periodic solution (`0 < T`) of a vector field `X` in a compact set `K ⊆ M`, and let
continuous `T`-periodic loops `γ_i` in `K` converge uniformly to `γ₀` through a continuous map
`e : M → F` injective on `K` along a nontrivial filter `l`. Then `γ₀ ∈ contractiblePeriodicSolutions
X T` if and only if the `γ_i` are eventually null-homotopic. -/
theorem mem_contractiblePeriodicSolutions_iff_of_tendstoUniformly_comp
    {F : Type*} [MetricSpace F] {e : M → F} {K : Set M} (hK : IsCompact K)
    (he : ContinuousOn e K) (he_inj : InjOn e K) (hT : 0 < T) {γ₀ : ℝ → M}
    (hγ₀ : γ₀ ∈ periodicSolutions X T) (hγ₀K : ∀ t, γ₀ t ∈ K) {ι : Type*} {l : Filter ι}
    [NeBot l] {γ : ι → ℝ → M} (hγc : ∀ᶠ i in l, Continuous (γ i))
    (hγp : ∀ᶠ i in l, Periodic (γ i) T) (hγK : ∀ᶠ i in l, ∀ t, γ i t ∈ K)
    (hconv : TendstoUniformly (fun i t ↦ e (γ i t)) (e ∘ γ₀) l) :
    γ₀ ∈ contractiblePeriodicSolutions X T ↔
      ∀ᶠ i in l, ∃ g : C(AddCircle T, M), g.Nullhomotopic ∧ ∀ t : ℝ, g t = γ i t := by
  have hev := exists_nullhomotopic_iff_of_tendstoUniformly_comp I hK he he_inj hT
    (continuous_of_mem_periodicSolutions hγ₀) (mem_periodicSolutions.1 hγ₀).2 hγ₀K hγc hγp hγK hconv
  refine ⟨fun hx' ↦ hev.mono fun i hi ↦ hi.2 (mem_contractiblePeriodicSolutions.1 hx').2,
    fun hγn ↦ mem_contractiblePeriodicSolutions.2 ⟨hγ₀, ?_⟩⟩
  obtain ⟨i, hi, hin⟩ := (hev.and hγn).exists
  exact hi.1 hin

/-- **Nondegenerate periodic solutions are isolated in `K`.** Let `X` be a jointly `C¹`,
`T`-periodic (`T ≠ 0`) vector field on a Hausdorff boundaryless finite-dimensional manifold `M`,
and `e : M → F` continuous and injective on a compact set `K ⊆ M`. If `γ₀` is a `T`-periodic
solution of `X` in `K` whose point `γ₀ s` at time `s` is a nondegenerate fixed point of the return
map `timeDependentFlowOf X s (s + T)`, then there is `ε > 0` such that no other `T`-periodic
solution `γ` in `K` has `dist (e (γ s)) (e (γ₀ s)) < ε`. -/
theorem exists_pos_forall_eq_of_isNondegenerateFixedPt [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold I 1 M] [BoundarylessManifold I M] {F : Type*} [MetricSpace F] {e : M → F}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hT : Periodic X T) (hT0 : T ≠ 0) {K : Set M} (hK : IsCompact K)
    (he : ContinuousOn e K) (he_inj : InjOn e K) {γ₀ : ℝ → M} (hγ₀ : γ₀ ∈ periodicSolutions X T)
    (hγ₀K : ∀ t, γ₀ t ∈ K)
    (hnd : IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) (γ₀ s)) :
    ∃ ε > 0, ∀ γ ∈ periodicSolutions X T, (∀ t, γ t ∈ K) → dist (e (γ s)) (e (γ₀ s)) < ε →
      γ = γ₀ := by
  have := isCompact_iff_compactSpace.1 hK
  have hemb : IsClosedEmbedding fun p : K ↦ e p :=
    (he.comp_continuous continuous_subtype_val Subtype.prop).isClosedEmbedding fun p q h ↦
      Subtype.ext (he_inj p.2 q.2 h)
  have hisoM : ∀ᶠ p in 𝓝 (γ₀ s), IsFixedPt (timeDependentFlowOf X s (s + T)) p → p = γ₀ s :=
    (eventually_nhdsWithin_iff.1 hnd.eventually_not_isFixedPt).mono fun p hp hfix ↦
      Classical.byContradiction fun hne ↦ hp hne hfix
  have hisoK : ∀ᶠ p : K in 𝓝 ⟨γ₀ s, hγ₀K s⟩,
      IsFixedPt (timeDependentFlowOf X s (s + T)) p.1 → p.1 = γ₀ s :=
    (continuous_subtype_val.tendsto ⟨γ₀ s, hγ₀K s⟩).eventually hisoM
  rw [hemb.isEmbedding.nhds_eq_comap] at hisoK
  obtain ⟨V, hV, hVK⟩ := hisoK
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hV
  let eqv := periodicSolutionsEquivFixedPoints hX hT hT0 s
  refine ⟨ε, hε, fun γ hγ hγK hγx ↦ ?_⟩
  have hγfix : IsFixedPt (timeDependentFlowOf X s (s + T)) (γ s) := by
    simpa only [eqv, periodicSolutionsEquivFixedPoints_apply] using (eqv ⟨γ, hγ⟩).2.2
  have hγs : γ s = γ₀ s := @hVK ⟨γ s, hγK s⟩ (hball (Metric.mem_ball.2 hγx)) hγfix
  exact congrArg Subtype.val
    (eqv.injective (a₁ := ⟨γ, hγ⟩) (a₂ := ⟨γ₀, hγ₀⟩) (Subtype.ext (by simpa [eqv] using hγs)))

end NullhomotopyAndIsolation

end TauCeti
