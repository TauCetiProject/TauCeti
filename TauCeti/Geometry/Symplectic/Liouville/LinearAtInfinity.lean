/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.Completion

/-!
# The radial coordinate of a completion and Hamiltonians linear at infinity

Let `M` be a completion of the Liouville domain `W ⊆ M` (`TauCeti.IsLiouvilleCompletion`), with
Liouville field `Z` and Liouville flow `ψ`. Every point `x` of `M` outside `W` is `ψ_t(y)` for a
unique point `y` of the boundary `∂W` and a unique time `t > 0`
(`TauCeti.IsLiouvilleCompletion.existsUnique_flowOf_eq`). In the model `W ∪ (∂W × [1, ∞))` of the
completion, where `Z = r ∂_r` on the cylindrical end, this point is `(y, e^t)`: its **radial
coordinate** is `r = e^t`. A Hamiltonian on the completion is **linear at infinity** with slope
`a` when it equals `a r + b` outside a compact set. Symplectic homology is the direct limit of the
Floer homologies of such Hamiltonians as the slope tends to infinity.

Here the radial coordinate is the function `TauCeti.liouvilleRadialCoordinate Z W`, sending `x`
to `e^τ`, where `τ ≥ 0` is the least time for which the backward Liouville flow carries `x` into
`W`. It is `1` exactly on `W`, and on the cylindrical end it is the coordinate `r` above:

* `r(ψ_t y) = e^t` for `y ∈ ∂W` and `t ≥ 0`
  (`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_flowOf`), and more generally
  `r(ψ_t x) = e^t r(x)` for `x` outside the interior of `W`;
* conversely `ψ_{-log r(x)}(x)` is the boundary point on the trajectory through such an `x`
  (`TauCeti.IsLiouvilleCompletion.flowOf_neg_log_liouvilleRadialCoordinate_mem_frontier`).

Its sublevel sets are images of `W` under the flow: `r(x) ≤ e^T` exactly when `ψ_{-T}(x) ∈ W`
(`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_le_exp_iff`), and `r(x) < e^T` exactly
when `ψ_{-T}(x)` lies in the interior of `W`. Hence `r` is continuous and its sublevel sets
`{r ≤ c}` are compact, so that "outside a compact set" and "where `r` is large" mean the same
thing. Smoothness of `r` on the cylindrical end is not treated here.

A function `F : M → ℝ` is linear at infinity with slope `a` (`TauCeti.IsLinearAtInfinity`) when
`F = a r + b` outside a compact set; on a completion this holds exactly when `F = a r + b` on some
region `{r ≥ R}` (`TauCeti.IsLiouvilleCompletion.isLinearAtInfinity_iff`), and the slope is then
determined by `F` as soon as `W ≠ M` (`TauCeti.IsLinearAtInfinity.unique`).

## Main definitions

* `TauCeti.liouvilleRadialCoordinate`: the radial coordinate `r` of the cylindrical end, equal to
  `1` on the Liouville domain.
* `TauCeti.IsLinearAtInfinity`: functions equal to `a r + b` outside a compact set.

## Main results

* `TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_le_exp_iff`,
  `TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_lt_exp_iff`: the sublevel sets of `r`
  are the preimages of `W` and of its interior under the backward Liouville flow.
* `TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_flowOf_of_notMem_interior`:
  `r(ψ_t x) = e^t r(x)` on the cylindrical end.
* `TauCeti.IsLiouvilleCompletion.continuous_liouvilleRadialCoordinate`,
  `TauCeti.IsLiouvilleCompletion.isCompact_setOf_liouvilleRadialCoordinate_le`: `r` is continuous
  with compact sublevel sets.
* `TauCeti.IsLiouvilleCompletion.isLinearAtInfinity_iff`: linearity at infinity in terms of the
  region where `r` is large.
* `TauCeti.IsLinearAtInfinity.unique`: the slope at infinity is unique.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (completions and Hamiltonians linear at infinity).
* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953.
-/

public section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Z : (x : M) → TangentSpace I x} {W : Set M} {F G : M → ℝ} {a a' : ℝ}

/-- The **radial coordinate** of the cylindrical end of a completion of the Liouville domain `W`
with Liouville field `Z`: it sends `x` to `e^τ`, where `τ ≥ 0` is the least time for which the
backward flow of `Z` carries `x` into `W`. It equals `1` on `W`, and `e^t` at the point reached
from the boundary of `W` by flowing for time `t ≥ 0`
(`TauCeti.IsLiouvilleCompletion.liouvilleRadialCoordinate_flowOf`). -/
noncomputable def liouvilleRadialCoordinate (Z : (x : M) → TangentSpace I x) (W : Set M) (x : M) :
    ℝ :=
  Real.exp (sInf {t : ℝ | 0 ≤ t ∧ flowOf Z (-t) x ∈ W})

/-- The radial coordinate is `e^τ` for the least time `τ ≥ 0` at which the backward flow carries
the point into `W`. -/
theorem liouvilleRadialCoordinate_def (Z : (x : M) → TangentSpace I x) (W : Set M) (x : M) :
    liouvilleRadialCoordinate Z W x = Real.exp (sInf {t : ℝ | 0 ≤ t ∧ flowOf Z (-t) x ∈ W}) :=
  (rfl)

/-- The radial coordinate is at least `1`. -/
theorem one_le_liouvilleRadialCoordinate (Z : (x : M) → TangentSpace I x) (W : Set M) (x : M) :
    1 ≤ liouvilleRadialCoordinate Z W x := by
  rw [liouvilleRadialCoordinate, Real.one_le_exp_iff]
  exact Real.sInf_nonneg fun _ ht ↦ ht.1

/-- A function `F` on a completion of the Liouville domain `W` with Liouville field `Z` is
**linear at infinity** with slope `a` when `F = a r + b` outside a compact set, for a constant `b`,
where `r` is the radial coordinate `TauCeti.liouvilleRadialCoordinate Z W`. -/
def IsLinearAtInfinity (Z : (x : M) → TangentSpace I x) (W : Set M) (F : M → ℝ) (a : ℝ) : Prop :=
  ∃ K : Set M, IsCompact K ∧ ∃ b : ℝ, ∀ x ∉ K, F x = a * liouvilleRadialCoordinate Z W x + b

/-- The defining property of a function linear at infinity. -/
theorem isLinearAtInfinity_def : IsLinearAtInfinity Z W F a ↔
    ∃ K : Set M, IsCompact K ∧ ∃ b : ℝ, ∀ x ∉ K, F x = a * liouvilleRadialCoordinate Z W x + b :=
  Iff.rfl

/-- Constant functions are linear at infinity with slope `0`. -/
theorem isLinearAtInfinity_const (c : ℝ) : IsLinearAtInfinity Z W (fun _ ↦ c) 0 :=
  ⟨∅, isCompact_empty, c, fun _ _ ↦ by simp⟩

/-- The radial coordinate is linear at infinity with slope `1`. -/
theorem isLinearAtInfinity_liouvilleRadialCoordinate :
    IsLinearAtInfinity Z W (liouvilleRadialCoordinate Z W) 1 :=
  ⟨∅, isCompact_empty, 0, fun _ _ ↦ by simp⟩

/-- The sum of functions linear at infinity is linear at infinity, and the slopes add. -/
theorem IsLinearAtInfinity.add (hF : IsLinearAtInfinity Z W F a)
    (hG : IsLinearAtInfinity Z W G a') : IsLinearAtInfinity Z W (F + G) (a + a') := by
  obtain ⟨K, hK, b, hb⟩ := hF
  obtain ⟨K', hK', b', hb'⟩ := hG
  refine ⟨K ∪ K', hK.union hK', b + b', fun x hx ↦ ?_⟩
  rw [mem_union, not_or] at hx
  simp only [Pi.add_apply, hb x hx.1, hb' x hx.2]
  ring

/-- A multiple of a function linear at infinity is linear at infinity, with the slope multiplied
by the same constant. -/
theorem IsLinearAtInfinity.const_smul (hF : IsLinearAtInfinity Z W F a) (c : ℝ) :
    IsLinearAtInfinity Z W (c • F) (c * a) := by
  obtain ⟨K, hK, b, hb⟩ := hF
  refine ⟨K, hK, c * b, fun x hx ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hb x hx]
  ring

namespace IsLiouvilleCompletion

variable [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [T2Space M] [I.Boundaryless]
  {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {x y : M} {t T : ℝ}

/-- On a completion, the maximal Liouville flow is a global flow. -/
private theorem exists_flow_eq (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) : ∃ ψ : Flow ℝ M, ∀ t x, flowOf Z t x = ψ t x := by
  have hZs : ContMDiff I I.tangent 1 (T% Z) := (h.contMDiff_of_interior_eq hZ).of_le (by simp)
  exact ⟨globalFlow Z hZs (h.isCompleteVectorField hZ), fun t x ↦
    (flowOf_apply Z t x).trans (globalFlow_apply hZs (h.isCompleteVectorField hZ) t x).symm⟩

/-- The backward Liouville flow carries the Liouville domain into its interior. -/
private theorem flowOf_neg_mem_interior (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∈ W) (ht : 0 < t) :
    flowOf Z (-t) x ∈ interior W := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  by_contra hn
  refine h.flowOf_notMem hZ hn ht ((h.isCompleteVectorField hZ).mem_flowDomain _ _) ?_
  rwa [hψ, hψ, ← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

/-- The backward Liouville flow preserves the Liouville domain. -/
private theorem flowOf_neg_mem (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∈ W) (ht : 0 ≤ t) : flowOf Z (-t) x ∈ W := by
  rcases ht.lt_or_eq with ht | rfl
  · exact interior_subset (h.flowOf_neg_mem_interior hZ hx ht)
  · obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
    rwa [neg_zero, hψ, Flow.map_zero_apply]

/-- The trajectory of a boundary point lies in the Liouville domain exactly at nonpositive
times. -/
private theorem flowOf_mem_iff_of_mem_frontier (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hy : y ∈ frontier W) : flowOf Z t y ∈ W ↔ t ≤ 0 := by
  refine ⟨fun ht ↦ not_lt.1 fun ht' ↦ h.flowOf_notMem hZ hy.2 ht'
    ((h.isCompleteVectorField hZ).mem_flowDomain _ _) ht, fun ht ↦ ?_⟩
  simpa using h.flowOf_neg_mem hZ (h.isClosed.frontier_subset hy) (neg_nonneg.2 ht)

/-- Every point outside the interior of the Liouville domain is reached from the boundary by the
forward Liouville flow, at a nonnegative time. -/
private theorem exists_mem_frontier_flowOf_eq (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ interior W) :
    ∃ y ∈ frontier W, ∃ s, 0 ≤ s ∧ flowOf Z s y = x := by
  by_cases hxW : x ∈ W
  · obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
    refine ⟨x, ?_, 0, le_rfl, by rw [hψ, Flow.map_zero_apply]⟩
    rw [h.isClosed.frontier_eq]
    exact ⟨hxW, hx⟩
  · obtain ⟨⟨y, s⟩, ⟨hy, hs, hyx⟩, -⟩ := h.existsUnique_flowOf_eq hZ hxW
    exact ⟨y, hy, s, hs.le, hyx⟩

/-- The times `t ≥ 0` for which the backward Liouville flow carries `x` into the Liouville domain
form the closed half-line starting at their infimum. -/
private theorem sInf_le_iff (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (x : M) (hT : 0 ≤ T) :
    sInf {t : ℝ | 0 ≤ t ∧ flowOf Z (-t) x ∈ W} ≤ T ↔ flowOf Z (-T) x ∈ W := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  set S := {t : ℝ | 0 ≤ t ∧ flowOf Z (-t) x ∈ W}
  have hbdd : BddBelow S := ⟨0, fun _ ht ↦ ht.1⟩
  -- The set is closed upwards, since the backward flow preserves `W`.
  have hup : ∀ ⦃s t⦄, s ∈ S → s ≤ t → t ∈ S := fun s t hs hst ↦ by
    refine ⟨hs.1.trans hst, ?_⟩
    have := h.flowOf_neg_mem hZ hs.2 (sub_nonneg.2 hst)
    rwa [hψ, hψ, ← Flow.map_add, show -(t - s) + -s = -t by ring, ← hψ] at this
  -- It is nonempty: if the flow carries `x` into `W` at a positive time, then `x` already lies
  -- in the interior of `W`.
  have hne : S.Nonempty := by
    obtain ⟨t, ht⟩ := h.exists_flowOf_mem hZ x
    rcases le_or_gt t 0 with ht0 | ht0
    · exact ⟨-t, neg_nonneg.2 ht0, by rwa [neg_neg]⟩
    · refine ⟨0, le_rfl, ?_⟩
      by_contra hn
      refine h.flowOf_notMem hZ (fun hx ↦ hn ?_) ht0
        ((h.isCompleteVectorField hZ).mem_flowDomain _ _) ht
      rw [neg_zero, hψ, Flow.map_zero_apply]
      exact interior_subset hx
  have hclosed : IsClosed S := by
    refine (isClosed_le continuous_const continuous_id).inter (h.isClosed.preimage ?_)
    simp only [hψ]
    exact ψ.continuous continuous_neg continuous_const
  exact ⟨fun hle ↦ (hup (hclosed.csInf_mem hne hbdd) hle).2, fun hT' ↦ csInf_le hbdd ⟨hT, hT'⟩⟩

/-- **The sublevel sets of the radial coordinate.** For `T ≥ 0`, `r(x) ≤ e^T` exactly when the
backward Liouville flow `ψ_{-T}` carries `x` into the Liouville domain. -/
theorem liouvilleRadialCoordinate_le_exp_iff (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hT : 0 ≤ T) :
    liouvilleRadialCoordinate Z W x ≤ Real.exp T ↔ flowOf Z (-T) x ∈ W := by
  rw [liouvilleRadialCoordinate, Real.exp_le_exp, h.sInf_le_iff hZ x hT]

/-- The radial coordinate equals `1` exactly on the Liouville domain. -/
theorem liouvilleRadialCoordinate_eq_one_iff (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) : liouvilleRadialCoordinate Z W x = 1 ↔ x ∈ W := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  rw [← (one_le_liouvilleRadialCoordinate Z W x).ge_iff_eq', ← Real.exp_zero,
    h.liouvilleRadialCoordinate_le_exp_iff hZ le_rfl, neg_zero, hψ, Flow.map_zero_apply]

/-- The radial coordinate is greater than `1` exactly outside the Liouville domain. -/
theorem one_lt_liouvilleRadialCoordinate_iff (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) : 1 < liouvilleRadialCoordinate Z W x ↔ x ∉ W := by
  rw [← h.liouvilleRadialCoordinate_eq_one_iff hZ,
    (one_le_liouvilleRadialCoordinate Z W x).lt_iff_ne', ne_eq]

/-- **The strict sublevel sets of the radial coordinate.** For `T > 0`, `r(x) < e^T` exactly
when the backward Liouville flow `ψ_{-T}` carries `x` into the interior of the Liouville
domain. -/
theorem liouvilleRadialCoordinate_lt_exp_iff (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hT : 0 < T) :
    liouvilleRadialCoordinate Z W x < Real.exp T ↔ flowOf Z (-T) x ∈ interior W := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  have h1 := one_le_liouvilleRadialCoordinate Z W x
  have hlog := Real.exp_log (one_pos.trans_le h1)
  constructor
  · -- Flow back to the time `τ = log r(x) < T` at which `x` enters `W`, then further back.
    intro hlt
    have hτT : Real.log (liouvilleRadialCoordinate Z W x) < T := by
      rwa [← hlog, Real.exp_lt_exp] at hlt
    have hmem := (h.liouvilleRadialCoordinate_le_exp_iff hZ (Real.log_nonneg h1)).1 hlog.ge
    have := h.flowOf_neg_mem_interior hZ hmem (sub_pos.2 hτT)
    rwa [hψ, hψ, ← Flow.map_add, show ∀ τ, -(T - τ) + -τ = -T from fun τ ↦ by ring, ← hψ]
      at this
  · -- Times slightly smaller than `T` also flow `x` into the interior of `W`.
    intro hint
    by_contra hle
    rw [not_lt] at hle
    have hcont : Continuous fun t ↦ flowOf Z (-t) x := by
      simp only [hψ]
      exact ψ.continuous continuous_neg continuous_const
    have hev : ∀ᶠ t in 𝓝[<] T, 0 ≤ t ∧ flowOf Z (-t) x ∈ interior W :=
      eventually_nhdsWithin_of_eventually_nhds <| ((lt_mem_nhds hT).mono fun _ ↦ le_of_lt).and
        (hcont.continuousAt.eventually_mem (isOpen_interior.mem_nhds hint))
    obtain ⟨t, ⟨ht0, ht⟩, htT⟩ := (hev.and self_mem_nhdsWithin).exists
    have := (h.liouvilleRadialCoordinate_le_exp_iff hZ ht0).2 (interior_subset ht)
    exact absurd (hle.trans this) (not_le.2 (Real.exp_lt_exp.2 htT))

/-- **The radial coordinate on a Liouville trajectory from the boundary.** If `y` lies on the
boundary of the Liouville domain and `t ≥ 0`, then `r(ψ_t y) = e^t`. -/
theorem liouvilleRadialCoordinate_flowOf (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hy : y ∈ frontier W) (ht : 0 ≤ t) :
    liouvilleRadialCoordinate Z W (flowOf Z t y) = Real.exp t := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  -- For `T ≥ 0`, `r(ψ_t y) ≤ e^T` exactly when `ψ_{t - T} y ∈ W`, that is when `t ≤ T`.
  have key : ∀ T, 0 ≤ T → (liouvilleRadialCoordinate Z W (flowOf Z t y) ≤ Real.exp T ↔ t ≤ T) :=
    fun T hT ↦ by
      rw [h.liouvilleRadialCoordinate_le_exp_iff hZ hT, hψ, hψ, ← Flow.map_add, ← hψ,
        h.flowOf_mem_iff_of_mem_frontier hZ hy, neg_add_nonpos_iff]
  have h1 := one_le_liouvilleRadialCoordinate Z W (flowOf Z t y)
  have hlog := Real.exp_log (one_pos.trans_le h1)
  refine le_antisymm ((key t ht).2 le_rfl) ?_
  calc Real.exp t ≤ Real.exp (Real.log (liouvilleRadialCoordinate Z W (flowOf Z t y))) :=
        Real.exp_le_exp.2 ((key _ (Real.log_nonneg h1)).1 hlog.ge)
    _ = _ := hlog

/-- **The Liouville flow rescales the radial coordinate.** If `x` lies outside the interior of the
Liouville domain and `t ≥ 0`, then `r(ψ_t x) = e^t r(x)`. -/
theorem liouvilleRadialCoordinate_flowOf_of_notMem_interior (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ interior W) (ht : 0 ≤ t) :
    liouvilleRadialCoordinate Z W (flowOf Z t x) =
      Real.exp t * liouvilleRadialCoordinate Z W x := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  obtain ⟨y, hy, s, hs, rfl⟩ := h.exists_mem_frontier_flowOf_eq hZ hx
  rw [h.liouvilleRadialCoordinate_flowOf hZ hy hs, hψ, hψ, ← Flow.map_add, ← hψ,
    h.liouvilleRadialCoordinate_flowOf hZ hy (add_nonneg ht hs), Real.exp_add]

/-- **The boundary point of a Liouville trajectory.** If `x` lies outside the interior of the
Liouville domain, then flowing `x` backwards for time `log r(x)` lands on the boundary. -/
theorem flowOf_neg_log_liouvilleRadialCoordinate_mem_frontier (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (hx : x ∉ interior W) :
    flowOf Z (-Real.log (liouvilleRadialCoordinate Z W x)) x ∈ frontier W := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  obtain ⟨y, hy, s, hs, rfl⟩ := h.exists_mem_frontier_flowOf_eq hZ hx
  rwa [h.liouvilleRadialCoordinate_flowOf hZ hy hs, Real.log_exp, hψ, hψ, ← Flow.map_add,
    neg_add_cancel, Flow.map_zero_apply]

/-- For `c ≥ 1`, the sublevel set `{r ≤ c}` of the radial coordinate is the preimage of the
Liouville domain under the backward Liouville flow for time `log c`. -/
private theorem setOf_liouvilleRadialCoordinate_le_eq (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) {c : ℝ} (hc : 1 ≤ c) :
    {x | liouvilleRadialCoordinate Z W x ≤ c} = (flowOf Z (-Real.log c)) ⁻¹' W := by
  ext x
  rw [mem_preimage, ← h.liouvilleRadialCoordinate_le_exp_iff hZ (Real.log_nonneg hc),
    Real.exp_log (one_pos.trans_le hc)]
  rfl

/-- The radial coordinate of a completion is continuous. -/
theorem continuous_liouvilleRadialCoordinate (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) : Continuous (liouvilleRadialCoordinate Z W) := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  have hcont : ∀ T, Continuous (flowOf Z T) := fun T ↦ by
    simp only [funext (hψ T)]
    exact ψ.continuous continuous_const continuous_id
  have h1 := one_le_liouvilleRadialCoordinate Z W
  rw [continuous_iff_lower_upperSemicontinuous, lowerSemicontinuous_iff_isClosed_preimage,
    upperSemicontinuous_iff_isOpen_preimage]
  refine ⟨fun c ↦ ?_, fun c ↦ ?_⟩
  · -- The sublevel set `{r ≤ c}` is empty for `c < 1`, and a preimage of `W` otherwise.
    rcases lt_or_ge c 1 with hc | hc
    · convert isClosed_empty
      exact eq_empty_of_forall_notMem fun x hx ↦ (hc.trans_le (h1 x)).not_ge hx
    · have := h.isClosed.preimage (hcont (-Real.log c))
      rwa [← h.setOf_liouvilleRadialCoordinate_le_eq hZ hc] at this
  · -- The strict sublevel set `{r < c}` is empty for `c ≤ 1`, and a preimage of the interior of
    -- `W` otherwise.
    rcases le_or_gt c 1 with hc | hc
    · convert isOpen_empty
      exact eq_empty_of_forall_notMem fun x hx ↦ (hc.trans (h1 x)).not_gt hx
    · have : liouvilleRadialCoordinate Z W ⁻¹' Iio c =
          (flowOf Z (-Real.log c)) ⁻¹' interior W := by
        ext x
        rw [mem_preimage, mem_Iio, mem_preimage,
          ← h.liouvilleRadialCoordinate_lt_exp_iff hZ (Real.log_pos hc),
          Real.exp_log (one_pos.trans hc)]
      exact this ▸ isOpen_interior.preimage (hcont _)

/-- The sublevel sets `{r ≤ c}` of the radial coordinate of a completion are compact. -/
theorem isCompact_setOf_liouvilleRadialCoordinate_le (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) (c : ℝ) :
    IsCompact {x | liouvilleRadialCoordinate Z W x ≤ c} := by
  obtain ⟨ψ, hψ⟩ := h.exists_flow_eq hZ
  rcases lt_or_ge c 1 with hc | hc
  · have : {x | liouvilleRadialCoordinate Z W x ≤ c} = ∅ := eq_empty_of_forall_notMem
      fun x hx ↦ (hc.trans_le (one_le_liouvilleRadialCoordinate Z W x)).not_ge hx
    exact this ▸ isCompact_empty
  · -- The preimage of `W` under `ψ_{-log c}` is its image under the inverse map `ψ_{log c}`.
    rw [h.setOf_liouvilleRadialCoordinate_le_eq hZ hc, funext (hψ _), ← ψ.image_eq_preimage_symm]
    exact h.isCompact.image (ψ.continuous continuous_const continuous_id)

/-- **Linearity at infinity on a completion.** A function is linear at infinity with slope `a`
exactly when it equals `a r + b` on the region `{r ≥ R}` where the radial coordinate is large. -/
theorem isLinearAtInfinity_iff (h : IsLiouvilleCompletion ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) :
    IsLinearAtInfinity Z W F a ↔ ∃ R b : ℝ, ∀ x, R ≤ liouvilleRadialCoordinate Z W x →
      F x = a * liouvilleRadialCoordinate Z W x + b := by
  constructor
  · rintro ⟨K, hK, b, hb⟩
    obtain ⟨R, hR⟩ := hK.bddAbove_image (h.continuous_liouvilleRadialCoordinate hZ).continuousOn
    refine ⟨R + 1, b, fun x hx ↦ hb x fun hxK ↦ ?_⟩
    linarith [hR (mem_image_of_mem _ hxK)]
  · rintro ⟨R, b, hb⟩
    exact ⟨_, h.isCompact_setOf_liouvilleRadialCoordinate_le hZ R, b,
      fun x hx ↦ hb x (not_le.1 hx).le⟩

end IsLiouvilleCompletion

/-- **The slope at infinity is unique.** On a completion of a Liouville domain `W ≠ M`, a function
linear at infinity has only one slope. -/
theorem IsLinearAtInfinity.unique [IsManifold I (⊤ : ℕ∞) M] [FiniteDimensional ℝ E] [T2Space M]
    [I.Boundaryless] {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1}
    (hF : IsLinearAtInfinity Z W F a) (hF' : IsLinearAtInfinity Z W F a')
    (h : IsLiouvilleCompletion ω α W) (hZ : RoughForm.interior Z ω.1 = α.1) (hW : W ≠ univ) :
    a = a' := by
  obtain ⟨R, b, hb⟩ := (h.isLinearAtInfinity_iff hZ).1 hF
  obtain ⟨R', b', hb'⟩ := (h.isLinearAtInfinity_iff hZ).1 hF'
  -- The radial coordinate takes all values `e^s`, `s ≥ 0`, along the trajectory of a boundary
  -- point, so `F` is `a e^s + b = a' e^s + b'` for all large `s`.
  obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem W).1 hW
  obtain ⟨y, hy, -⟩ := h.exists_mem_frontier_flowOf_eq hZ fun hx' ↦ hx (interior_subset hx')
  set T := max 0 (max R R')
  have key : ∀ s, T ≤ s → a * Real.exp s + b = a' * Real.exp s + b' := fun s hs ↦ by
    have hr := h.liouvilleRadialCoordinate_flowOf hZ hy ((le_max_left _ _).trans hs)
    have hRs : max R R' ≤ Real.exp s :=
      (le_max_right _ _).trans (hs.trans (by linarith [Real.add_one_le_exp s]))
    rw [← hr, ← hb _ (hr ▸ (le_max_left _ _).trans hRs),
      ← hb' _ (hr ▸ (le_max_right _ _).trans hRs)]
  have hlt : Real.exp T < Real.exp (T + 1) := Real.exp_lt_exp.2 (lt_add_one T)
  have hmul : (a - a') * (Real.exp (T + 1) - Real.exp T) = 0 := by
    linear_combination key (T + 1) (by linarith) - key T le_rfl
  rcases mul_eq_zero.1 hmul with h0 | h0
  · linarith
  · linarith

end TauCeti
