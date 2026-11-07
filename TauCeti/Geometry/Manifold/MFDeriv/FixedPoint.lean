/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Dynamics.FixedPoints.Defs
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.DiscreteSubset

/-!
# Nondegenerate fixed points of maps of manifolds

A fixed point `x` of a map `f : M → M` is **nondegenerate** (`TauCeti.IsNondegenerateFixedPt`)
when `f` is differentiable at `x` and `1` is not an eigenvalue of its differential
`df_x : T_x M → T_x M`: the only tangent vector fixed by `df_x` is zero. In finite dimensions this
says that `df_x - 1` is invertible, or that the graph of `f` meets the diagonal of `M × M`
transversally at `(x, x)`. For the time-one map of a
time-dependent Hamiltonian this is the nondegeneracy of a 1-periodic orbit, the hypothesis under
which the orbits generate the Hamiltonian Floer complex.

When `M` is modelled on a finite-dimensional space over a complete field, a nondegenerate fixed
point is isolated among the fixed points
(`TauCeti.IsNondegenerateFixedPt.eventually_not_isFixedPt`): in a chart at `x` the coordinate
expression `g` of `f` has `g - id` with injective derivative at `x`, so `g z ≠ z` for `z ≠ x` close
to `x`, because an injective linear map of a finite-dimensional space is bounded below. Without
finite dimensionality, injectivity of `df_x - 1` does not imply isolation. The argument is carried
out within the range of the model with corners, so it also applies at boundary points.
Consequently a compact set of nondegenerate fixed points is discrete, hence finite
(`IsCompact.finite_of_isNondegenerateFixedPt`). In particular a continuous self-map of such a
compact manifold all of whose fixed points are nondegenerate has only finitely many fixed points
(`TauCeti.finite_fixedPoints_of_isNondegenerateFixedPt`), since its fixed-point set is closed,
hence compact.

At a fixed point the differential of `f^[n]` is `(df_x) ^ n`, so `x` is a nondegenerate fixed point
of `f^[n]` exactly when `(df_x) ^ n` fixes no nonzero vector. For a periodic point of period `k`,
the differential of `f^[k]` is the return map of its orbit, and its `m`-th power is the return map
of the `m`-fold cover. A map is nondegenerate up to period `N`
(`TauCeti.IsNondegenerateUpToPeriod`) when every periodic orbit of period at most `N` is
nondegenerate. On a compact manifold such a map has finitely many periodic points of each period
at most `N`. A vector with `D v = -v` is fixed by `D ^ 2`, so nondegeneracy up to period `2 * N`
excludes both eigenvalues `1` and `-1` from the return maps of all covers of period at most `N`.

## Main definitions

* `TauCeti.IsNondegenerateFixedPt I f x`: `x` is a fixed point of `f`, `f` is differentiable at
  `x`, and `df_x` fixes no nonzero tangent vector.
* `TauCeti.IsNondegenerateUpToPeriod I f N`: every periodic point of positive period `k ≤ N` is a
  nondegenerate fixed point of `f^[k]`.

## Main results

* `TauCeti.IsNondegenerateFixedPt.eventually_not_isFixedPt`: on a manifold modelled on a
  finite-dimensional space over a complete field, nondegenerate fixed points are isolated.
* `IsCompact.finite_of_isNondegenerateFixedPt`: on a manifold modelled on a finite-dimensional
  space over a complete field, a compact set of nondegenerate fixed points is finite.
* `TauCeti.finite_fixedPoints_of_isNondegenerateFixedPt`: on a compact manifold modelled on a
  finite-dimensional space over a complete field, a continuous map whose fixed points are all
  nondegenerate has finitely many fixed points.
* `TauCeti.isNondegenerateFixedPt_iterate_iff`: at a fixed point with differential `D`, the point is
  a nondegenerate fixed point of `f^[n]` exactly when `D ^ n` fixes no nonzero vector.
* `TauCeti.IsNondegenerateFixedPt.eq_zero_of_pow_apply_eq_smul`: at a nondegenerate fixed point of
  `f^[m * j]`, no `ε` with `ε ^ j = 1` is an eigenvalue of `D ^ m`.
* `TauCeti.IsNondegenerateUpToPeriod.finite_ptsOfPeriod`,
  `TauCeti.IsNondegenerateUpToPeriod.finite_setOf_isPeriodicPt`: finitely many periodic points of
  period at most `N` on a compact manifold.
* `TauCeti.IsNondegenerateUpToPeriod.eq_zero_of_pow_apply_eq_smul`,
  `TauCeti.IsNondegenerateUpToPeriod.det_smul_one_sub_pow_ne_zero`: nondegeneracy up to period
  `N` excludes every `ε` with `ε ^ j = 1` as an eigenvalue of the return map of the `m`-fold cover
  of an orbit of period `k` when `k * m * j ≤ N`. For `j = 2`, nondegeneracy up to period `2 * N`
  excludes the eigenvalues `±1` of the return maps of all covers of period at most `N`.

## References

* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 3, §4
  (Lefschetz fixed points: nondegeneracy, isolation and finiteness on compact manifolds).
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 11.1 (nondegenerate fixed points of Hamiltonian symplectomorphisms).
-/

public section

open Filter Function Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] {f : M → M} {x : M}

variable (I) in
/-- A **nondegenerate fixed point** of `f : M → M` is a fixed point `x` at which `f` is
differentiable and `1` is not an eigenvalue of the differential: `df_x v = v` only for `v = 0`.
In finite dimensions this says that `df_x - 1` is invertible. -/
def IsNondegenerateFixedPt (f : M → M) (x : M) : Prop :=
  IsFixedPt f x ∧ MDifferentiableAt I I f x ∧ ∀ v : TangentSpace I x, mfderiv I I f x v = v → v = 0

/-- The defining characterization of a nondegenerate fixed point. -/
theorem isNondegenerateFixedPt_iff :
    IsNondegenerateFixedPt I f x ↔
      IsFixedPt f x ∧ MDifferentiableAt I I f x ∧
        ∀ v : TangentSpace I x, mfderiv I I f x v = v → v = 0 :=
  Iff.rfl

namespace IsNondegenerateFixedPt

/-- A nondegenerate fixed point is a fixed point. -/
theorem isFixedPt (h : IsNondegenerateFixedPt I f x) : IsFixedPt f x :=
  h.1

/-- A map is differentiable at each of its nondegenerate fixed points. -/
theorem mdifferentiableAt (h : IsNondegenerateFixedPt I f x) : MDifferentiableAt I I f x :=
  h.2.1

/-- At a nondegenerate fixed point, the only tangent vector fixed by the differential is zero. -/
theorem eq_zero_of_mfderiv_apply_eq (h : IsNondegenerateFixedPt I f x) {v : TangentSpace I x}
    (hv : mfderiv I I f x v = v) : v = 0 :=
  h.2.2 v hv

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- **Nondegenerate fixed points are isolated.** On a manifold modelled on a finite-dimensional
space over a complete field, if `x` is a nondegenerate fixed point of `f`, then no point `y ≠ x`
close to `x` is fixed by `f`. The manifold may have boundary or corners. -/
theorem eventually_not_isFixedPt (h : IsNondegenerateFixedPt I f x) :
    ∀ᶠ y in 𝓝[≠] x, ¬IsFixedPt f y := by
  have hf := h.mdifferentiableAt
  set φ := extChartAt I x
  have hfx : f x = x := h.isFixedPt
  have hφ : extChartAt I (f x) = φ := by rw [hfx]
  -- In the chart at `x`, the coordinate expression `g` of `f` has derivative `D = df_x` within
  -- `range I`, so `z ↦ g z - z` has derivative `D - 1`, which is injective.
  set D : E →L[𝕜] E := mfderiv I I f x
  have hg : HasFDerivWithinAt (fun z ↦ φ (f (φ.symm z)) - z) (D - ContinuousLinearMap.id 𝕜 E)
      (range I) (φ x) := by
    have h2 := hf.hasMFDerivAt.2
    simp only [writtenInExtChartAt, hφ] at h2
    exact h2.sub (hasFDerivWithinAt_id _ _)
  have hinj : Injective (D - ContinuousLinearMap.id 𝕜 E) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact h.eq_zero_of_mfderiv_apply_eq (sub_eq_zero.1 hv)
  obtain ⟨K, -, hK⟩ :=
    (D - ContinuousLinearMap.id 𝕜 E).toLinearMap.injective_iff_antilipschitz.1 hinj
  have hne := hg.eventually_ne (c := 0) ⟨K, hK⟩
  -- The chart sends points `y ≠ x` near `x` to points `≠ φ x` of `range I`.
  have hsource : (extChartAt I x).source ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds x)
  have htends : Tendsto φ (𝓝[≠] x) (𝓝[range I \ {φ x}] (φ x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuousAt_extChartAt x).tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [hsource, self_mem_nhdsWithin] with y hy hyx
    exact ⟨extChartAt_target_subset_range x ((extChartAt I x).map_source hy),
      fun hφy ↦ hyx ((extChartAt I x).injOn hy (mem_extChartAt_source x) hφy)⟩
  have hfsource : f ⁻¹' (extChartAt I x).source ∈ 𝓝[≠] x :=
    mem_nhdsWithin_of_mem_nhds (hf.continuousAt.preimage_mem_nhds
      (by rw [hfx]; exact extChartAt_source_mem_nhds x))
  filter_upwards [htends.eventually hne, hsource, hfsource] with y hy hys _ hfix
  apply hy
  rw [(extChartAt I x).left_inv hys, hfix.eq, sub_self]

end IsNondegenerateFixedPt

/-- **Finiteness of compact sets of nondegenerate fixed points.** On a manifold modelled on a
finite-dimensional space, a compact set all of whose points are nondegenerate fixed points of `f`
is finite, since each of its points is isolated among the fixed points of `f`. -/
theorem _root_.IsCompact.finite_of_isNondegenerateFixedPt [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] {s : Set M} (hs : IsCompact s)
    (h : ∀ x ∈ s, IsNondegenerateFixedPt I f x) : s.Finite :=
  hs.finite <| isDiscrete_iff_nhdsNE.2 fun x hx ↦ inf_principal_eq_bot.2 <|
    (h x hx).eventually_not_isFixedPt.mono fun y hy hys ↦ hy (h y hys).isFixedPt

/-- **Finiteness of nondegenerate fixed points.** A continuous self-map of a compact manifold,
modelled on a finite-dimensional space, all of whose fixed points are nondegenerate has only
finitely many fixed points. -/
theorem finite_fixedPoints_of_isNondegenerateFixedPt [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    [CompactSpace M] [T2Space M] (hf : Continuous f)
    (h : ∀ x ∈ fixedPoints f, IsNondegenerateFixedPt I f x) : (fixedPoints f).Finite :=
  (isClosed_fixedPoints hf).isCompact.finite_of_isNondegenerateFixedPt h

/-! ### Iterates

At a fixed point `x` of `f` the chain rule makes the differential of the iterate `f^[n]` the
`n`-th power of `df_x` (`HasMFDerivAt.iterate`). For a periodic point of period `k`, applied to
`f^[k]`, this says that the return map of the `m`-fold cover of the periodic orbit is the `m`-th
power of the return map of the orbit. -/

/-- At a fixed point `x` of `f` with differential `D`, the point `x` is a nondegenerate fixed point
of `f^[n]` exactly when `D ^ n` fixes no nonzero tangent vector. -/
theorem isNondegenerateFixedPt_iterate_iff {D : TangentSpace I x →L[𝕜] TangentSpace I x}
    (hD : HasMFDerivAt I I f x D) (hx : IsFixedPt f x) {n : ℕ} :
    IsNondegenerateFixedPt I f^[n] x ↔ ∀ v : TangentSpace I x, (D ^ n) v = v → v = 0 := by
  have hDn := hD.iterate hx.eq n
  rw [isNondegenerateFixedPt_iff, hDn.mfderiv]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨hx.iterate n, hDn.mdifferentiableAt, h⟩⟩

namespace IsNondegenerateFixedPt

/-- **Roots of unity are not eigenvalues at a nondegenerate fixed point of an iterate.** Let `f`
fix `x` with differential `D`. If `x` is a nondegenerate fixed point of `f^[m * j]` and
`ε ^ j = 1`, then `(D ^ m) v = ε • v` only for `v = 0`. For `j = 2` this excludes both eigenvalues
`1` and `-1` of `D ^ m`. -/
theorem eq_zero_of_pow_apply_eq_smul {D : TangentSpace I x →L[𝕜] TangentSpace I x}
    (hD : HasMFDerivAt I I f x D) (hx : IsFixedPt f x) {m j : ℕ}
    (h : IsNondegenerateFixedPt I f^[m * j] x) {ε : 𝕜} (hε : ε ^ j = 1) {v : TangentSpace I x}
    (hv : (D ^ m) v = ε • v) : v = 0 := by
  refine (isNondegenerateFixedPt_iterate_iff hD hx).1 h v ?_
  rcases eq_or_ne v 0 with rfl | hv0
  · exact map_zero _
  have hev : Module.End.HasEigenvector (↑(D ^ m) : TangentSpace I x →ₗ[𝕜] TangentSpace I x) ε v :=
    ⟨Module.End.mem_eigenspace_iff.2 hv, hv0⟩
  have hj := hev.pow_apply j
  rw [← ContinuousLinearMap.toLinearMap_pow, hε, one_smul] at hj
  rwa [pow_mul]

/-- A fixed point of `f` at which `f` is differentiable is nondegenerate as soon as it is a
nondegenerate fixed point of some iterate `f^[n]`. -/
theorem of_iterate (hf : MDifferentiableAt I I f x) (hx : IsFixedPt f x) {n : ℕ}
    (h : IsNondegenerateFixedPt I f^[n] x) : IsNondegenerateFixedPt I f x := by
  -- Name the differential with the endomorphism type that `HasMFDerivAt.iterate` expects.
  let D : TangentSpace I x →L[𝕜] TangentSpace I x := mfderiv I I f x
  have hD : HasMFDerivAt I I f x D := hf.hasMFDerivAt
  rw [← one_mul n] at h
  refine ⟨hx, hf, fun v hv ↦ h.eq_zero_of_pow_apply_eq_smul hD hx (one_pow n) ?_⟩
  rwa [pow_one, one_smul]

end IsNondegenerateFixedPt

/-! ### Nondegeneracy up to a period

A map is nondegenerate up to period `N` when every periodic orbit of period at most `N` is
nondegenerate. On a compact manifold such a map has finitely many periodic points of each of these
periods. Since the return map of the `m`-fold cover of an orbit of period `k` is the `m`-th power of
the return map of the orbit, nondegeneracy up to period `2 * N` also excludes the eigenvalue `-1`
from the return maps of all covers of period at most `N`. In the count of pseudoholomorphic tori in
a symplectic suspension, these two eigenvalues govern the normal operators twisted by the trivial
and by the nontrivial sign character along the orbit. -/

variable (I) in
/-- A map `f : M → M` is **nondegenerate up to period `N`** when every periodic point of `f` with a
positive period `k ≤ N` is a nondegenerate fixed point of `f^[k]`: the return map of no periodic
orbit of period at most `N` has the eigenvalue `1`. A map that is nondegenerate up to every period
is called strongly nondegenerate. -/
def IsNondegenerateUpToPeriod (f : M → M) (N : ℕ) : Prop :=
  ∀ ⦃k : ℕ⦄, 0 < k → k ≤ N → ∀ ⦃x : M⦄, IsPeriodicPt f k x → IsNondegenerateFixedPt I f^[k] x

/-- The defining characterization of nondegeneracy up to a period. -/
theorem isNondegenerateUpToPeriod_iff {N : ℕ} :
    IsNondegenerateUpToPeriod I f N ↔
      ∀ ⦃k : ℕ⦄, 0 < k → k ≤ N → ∀ ⦃x : M⦄, IsPeriodicPt f k x →
        IsNondegenerateFixedPt I f^[k] x :=
  Iff.rfl

/-- Every map is nondegenerate up to period `0`. -/
@[simp]
theorem isNondegenerateUpToPeriod_zero : IsNondegenerateUpToPeriod I f 0 :=
  fun _ hk hk0 ↦ absurd hk (by omega)

namespace IsNondegenerateUpToPeriod

variable {N : ℕ}

/-- Nondegeneracy up to period `N` implies nondegeneracy up to every smaller period. -/
theorem mono (h : IsNondegenerateUpToPeriod I f N) {N' : ℕ} (hN : N' ≤ N) :
    IsNondegenerateUpToPeriod I f N' :=
  fun _ hk hkN _ hx ↦ h hk (hkN.trans hN) hx

/-- A periodic point of positive period `k ≤ N` of a map nondegenerate up to period `N` is a
nondegenerate fixed point of `f^[k]`. -/
theorem isNondegenerateFixedPt (h : IsNondegenerateUpToPeriod I f N) {k : ℕ} (hk : 0 < k)
    (hkN : k ≤ N) (hx : IsPeriodicPt f k x) : IsNondegenerateFixedPt I f^[k] x :=
  h hk hkN hx

/-- **Covers of nondegenerate orbits and roots of unity.** Let `f` be nondegenerate up to period
`N`, let `x` be a periodic point of period `k > 0`, and let `D` be the differential of `f^[k]` at
`x`, the return map of its orbit. If `k * m * j ≤ N` with `m, j > 0` and `ε ^ j = 1`, then
`(D ^ m) v = ε • v` forces `v = 0`: the return map `D ^ m` of the `m`-fold cover does not have the
eigenvalue `ε`. For `j = 2`, nondegeneracy up to period `2 * N` excludes both eigenvalues `1` and
`-1` of the return maps of all covers of period `k * m ≤ N`. -/
theorem eq_zero_of_pow_apply_eq_smul (h : IsNondegenerateUpToPeriod I f N) {k m j : ℕ}
    (hk : 0 < k) (hm : 0 < m) (hj : 0 < j) (hkmj : k * m * j ≤ N) (hx : IsPeriodicPt f k x)
    {D : TangentSpace I x →L[𝕜] TangentSpace I x} (hD : HasMFDerivAt I I f^[k] x D) {ε : 𝕜}
    (hε : ε ^ j = 1) {v : TangentSpace I x} (hv : (D ^ m) v = ε • v) : v = 0 := by
  have hnd := h (by positivity) (by rwa [← mul_assoc]) (hx.mul_const (m * j))
  rw [iterate_mul] at hnd
  exact hnd.eq_zero_of_pow_apply_eq_smul hD hx.isFixedPt hε hv

/-- **Covers of nondegenerate orbits.** Let `f` be nondegenerate up to period `N`, let `x` be a
periodic point of period `k > 0`, and let `D` be the differential of `f^[k]` at `x`, the return map
of its orbit. If `k * m ≤ N` with `m > 0`, then the return map `D ^ m` of the `m`-fold cover fixes
no nonzero tangent vector. -/
theorem eq_zero_of_pow_apply_eq (h : IsNondegenerateUpToPeriod I f N) {k m : ℕ} (hk : 0 < k)
    (hm : 0 < m) (hkm : k * m ≤ N) (hx : IsPeriodicPt f k x)
    {D : TangentSpace I x →L[𝕜] TangentSpace I x} (hD : HasMFDerivAt I I f^[k] x D)
    {v : TangentSpace I x} (hv : (D ^ m) v = v) : v = 0 :=
  h.eq_zero_of_pow_apply_eq_smul hk hm one_pos (by rwa [mul_one]) hx hD (one_pow 1)
    (by rwa [one_smul])

/-- **Determinant form of `TauCeti.IsNondegenerateUpToPeriod.eq_zero_of_pow_apply_eq_smul`.** In
finite dimension, if `f` is nondegenerate up to period `N`, `x` has period `k > 0` and `D` is the
differential of `f^[k]` at `x`, then `det (ε - D ^ m) ≠ 0` for `ε ^ j = 1`, `m, j > 0` and
`k * m * j ≤ N`. For `j = 2`, nondegeneracy up to period `2 * N` gives `det (±1 - D ^ m) ≠ 0` for
all covers of period `k * m ≤ N`. -/
theorem det_smul_one_sub_pow_ne_zero [FiniteDimensional 𝕜 E]
    (h : IsNondegenerateUpToPeriod I f N) {k m j : ℕ} (hk : 0 < k) (hm : 0 < m) (hj : 0 < j)
    (hkmj : k * m * j ≤ N) (hx : IsPeriodicPt f k x)
    {D : TangentSpace I x →L[𝕜] TangentSpace I x} (hD : HasMFDerivAt I I f^[k] x D) {ε : 𝕜}
    (hε : ε ^ j = 1) :
    LinearMap.det
      ((ε • 1 - D ^ m : TangentSpace I x →L[𝕜] TangentSpace I x) :
        TangentSpace I x →ₗ[𝕜] TangentSpace I x) ≠ 0 := by
  -- The tangent space is the model space `E`.
  have : FiniteDimensional 𝕜 (TangentSpace I x) := ‹FiniteDimensional 𝕜 E›
  rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, eq_bot_iff]
  intro v hv
  refine (Submodule.mem_bot 𝕜).2 (h.eq_zero_of_pow_apply_eq_smul hk hm hj hkmj hx hD hε ?_)
  simpa [sub_eq_zero, eq_comm (b := ε • v), ← ContinuousLinearMap.toLinearMap_pow] using hv

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [CompactSpace M] [T2Space M]

/-- **Finiteness of nondegenerate periodic points.** On a compact manifold modelled on a
finite-dimensional space over a complete field, a continuous map nondegenerate up to period `N`
has only finitely many periodic points of each positive period `k ≤ N`. -/
theorem finite_ptsOfPeriod (h : IsNondegenerateUpToPeriod I f N) (hf : Continuous f) {k : ℕ}
    (hk : 0 < k) (hkN : k ≤ N) : (ptsOfPeriod f k).Finite :=
  -- `ptsOfPeriod f k` is by definition the fixed-point set of `f^[k]`.
  finite_fixedPoints_of_isNondegenerateFixedPt (hf.iterate k) fun _ hx ↦ h hk hkN hx

/-- On a compact manifold modelled on a finite-dimensional space over a complete field, a
continuous map nondegenerate up to period `N` has only finitely many points of some positive
period at most `N`. -/
theorem finite_setOf_isPeriodicPt (h : IsNondegenerateUpToPeriod I f N) (hf : Continuous f) :
    {x | ∃ k, 0 < k ∧ k ≤ N ∧ IsPeriodicPt f k x}.Finite := by
  refine ((Set.finite_Icc 1 N).biUnion fun k hk ↦ h.finite_ptsOfPeriod hf hk.1 hk.2).subset ?_
  rintro x ⟨k, hk, hkN, hx⟩
  exact Set.mem_biUnion ⟨hk, hkN⟩ hx

end IsNondegenerateUpToPeriod

end TauCeti
