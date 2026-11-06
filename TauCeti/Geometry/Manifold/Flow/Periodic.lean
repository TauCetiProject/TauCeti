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

* `TauCeti.timeDependentFlowOf_add_period_of_mem`: translating both times by a period of the field
  preserves the domain and the flow.
* `TauCeti.mem_timeDependentFlowDomain_of_isFixedPt`: for `T ≠ 0`, the trajectory of a fixed point
  of the return map is defined for all time.
* `TauCeti.finite_periodicSolutions`: on a compact boundaryless finite-dimensional manifold, a
  field whose periodic solutions are all nondegenerate has finitely many of them.
* `TauCeti.finite_contractiblePeriodicSolutions`: the same for the contractible periodic solutions,
  assuming only that they are nondegenerate.

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
  simp only [add_sub_cancel_right, timeDependentFlowOf_self hX] at hmem heq
  exact ⟨hmem, heq⟩

/-- If the return map of a time-periodic field fixes `x`, so does its `k`-th iterate: the flow
from `s` to `s + k T` is defined at `x` and fixes it. -/
private theorem timeDependentFlowOf_nat_mul_of_isFixedPt (hT : Periodic X T)
    (h : ((s, s + T), x) ∈ timeDependentFlowDomain X)
    (hfix : IsFixedPt (timeDependentFlowOf X s (s + T)) x) (k : ℕ) :
    ((s, s + k * T), x) ∈ timeDependentFlowDomain X ∧
      timeDependentFlowOf X s (s + k * T) x = x := by
  induction k with
  | zero => simpa using ⟨mem_timeDependentFlowDomain_self hX s x, timeDependentFlowOf_self hX s x⟩
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
  right_inv x := Subtype.ext (timeDependentFlowOf_self hX s x)

/-- The correspondence from periodic solutions to fixed points evaluates at the initial time. -/
@[simp]
theorem periodicSolutionsEquivFixedPoints_apply (hT : Periodic X T) (hT0 : T ≠ 0) (s : ℝ)
    (γ : periodicSolutions X T) :
    (periodicSolutionsEquivFixedPoints hX hT hT0 s γ : M) = γ.1 s :=
  (rfl)

/-- The periodic solution of a fixed point of the return map is its trajectory under the flow. -/
@[simp]
theorem periodicSolutionsEquivFixedPoints_symm_apply (hT : Periodic X T) (hT0 : T ≠ 0) (s : ℝ)
    (x : {x | ((s, s + T), x) ∈ timeDependentFlowDomain X ∧
      IsFixedPt (timeDependentFlowOf X s (s + T)) x}) (t : ℝ) :
    ((periodicSolutionsEquivFixedPoints hX hT hT0 s).symm x).1 t =
      timeDependentFlowOf X s t x :=
  (rfl)

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
    rwa [periodicSolutionsEquivFixedPoints_symm_apply, timeDependentFlowOf_self hX] at hγ
  have : Finite {x | ((s, s + T), x) ∈ timeDependentFlowDomain X ∧
      IsFixedPt (timeDependentFlowOf X s (s + T)) x} :=
    (hfin.subset (ofPred_subset_ofPred.2 fun _ hx ↦ hx.2)).to_subtype
  exact Set.finite_coe_iff.1 (Finite.of_equiv _ e.symm)

/-- **Finiteness of nondegenerate contractible periodic solutions.** Let `X` be a jointly `C¹`
time-dependent vector field on a compact boundaryless manifold modelled on a finite-dimensional
space, `T`-periodic in time with `0 < T`. If every contractible `T`-periodic solution `γ` is
nondegenerate, in the sense that `γ s` is a nondegenerate fixed point of the return map
`timeDependentFlowOf X s (s + T)`, then `X` has only finitely many contractible `T`-periodic
solutions. Noncontractible solutions may be degenerate, and there may be infinitely many of
them. -/
theorem finite_contractiblePeriodicSolutions [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]
    [IsManifold I 1 M] [BoundarylessManifold I M]
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    (hT : Periodic X T) (hT0 : 0 < T) (s : ℝ)
    (h : ∀ γ ∈ contractiblePeriodicSolutions X T,
      IsNondegenerateFixedPt I (timeDependentFlowOf X s (s + T)) (γ s)) :
    (contractiblePeriodicSolutions X T).Finite := by
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
    ⟨fun hγ ↦ ⟨γ.2, ((hper γ).exists_nullhomotopic_iff_homotopic_loop (hcont γ) s).2 hγ⟩,
      fun hγ ↦ ((hper γ).exists_nullhomotopic_iff_homotopic_loop (hcont γ) s).1 hγ.2⟩
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
  have hKfin := hK.finite_of_isNondegenerateFixedPt (I := I) <| by
    rintro _ ⟨y, hy, rfl⟩
    have hnd := h _ ((hP _).1 hy)
    rwa [periodicSolutionsEquivFixedPoints_symm_apply, timeDependentFlowOf_self hX] at hnd
  refine Set.Finite.of_finite_image (f := fun γ ↦ γ s) (hKfin.subset ?_) fun γ₁ hγ₁ γ₂ hγ₂ hs ↦ ?_
  · rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨e ⟨γ, hγ.1⟩, ?_, by simp [e]⟩
    rw [Set.mem_ofPred_eq, Equiv.symm_apply_apply]
    exact (hP _).2 hγ
  · exact congrArg Subtype.val
      (e.injective (a₁ := ⟨γ₁, hγ₁.1⟩) (a₂ := ⟨γ₂, hγ₂.1⟩) (Subtype.ext (by simpa [e] using hs)))

end TauCeti
