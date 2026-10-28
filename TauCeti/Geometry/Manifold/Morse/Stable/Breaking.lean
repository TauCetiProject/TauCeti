/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.Transversality
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Dynamics.Flow.Breaking
import TauCeti.Dynamics.Flow.ConnectingOrbit

/-!
# Breaking of trajectories and finite index-one trajectory spaces on a compact manifold

Let `f` be a Morse function on a compact boundaryless manifold `M`, and `X` a Morse–Smale
pseudo-gradient field adapted to `f`. This file proves that between critical points `a` and `b`
with `ind a = ind b + 1` there are only finitely many trajectories: the level slice
`W^u(a) ∩ W^s(b) ∩ f⁻¹(c)` at a value `f b < c < f a`, which meets each trajectory from `a` to `b`
exactly once, is finite. This is the finiteness behind the coefficients of the Morse boundary
operator on `M`.

The slice is closed because trajectories can only break at critical points of intermediate index.
If the closure of an invariant set `S` meets the stable manifold `W^s(x)` of a critical point `x`
without `S` meeting it, then the closure of `S` also meets `W^u(x)` away from `x`
(`TauCeti.IsAdaptedPseudoGradient.exists_ne_mem_closure_inter_unstableSet`): orbits of `S` that
follow a trajectory into `x` must leave a small sphere about `x` along `W^u(x)`. This is the
breaking theorem `Flow.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet`, for a
metric inducing the topology of `M` and a radius isolating `x` among the finitely many critical
points. Following the broken pieces, each of which lowers the Morse index under the Morse–Smale
condition, a limit of trajectories converging to `b` that converges instead to another critical
point `x` forces `ind b < ind x`; dually for trajectories leaving `a`. When `ind a = ind b + 1`
there is no room for an intermediate index, so a limit of points of the slice is again a point of
the slice.

The slice is also discrete
(`TauCeti.IsAdaptedPseudoGradient.isDiscrete_unstableSet_inter_stableSet_level`), so, being
compact, it is finite.

These are the manifold forms of the results of `TauCeti.Analysis.Calculus.Morse.Breaking` for a
negative-gradient flow on a vector space. On a compact manifold no hypothesis on the convergence
of orbits is needed, since every orbit converges to a critical point in both time directions.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.exists_ne_mem_closure_inter_unstableSet`: breaking at a
  critical point.
* `manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet` and
  `manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet` (in the namespace
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale`): the Morse index drops strictly along broken
  limits of trajectories.
* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.isClosed_unstableSet_inter_stableSet_inter_level`
  and `finite_unstableSet_inter_stableSet_inter_level` (in the same namespace): for critical points
  of consecutive indices, the level slice of the space of trajectories is closed and finite.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of the spaces of trajectories, and the definition of the Morse complex).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {a b x y : M}

namespace IsAdaptedPseudoGradient

section Breaking

variable (hX : IsAdaptedPseudoGradient f X)
include hX

/-- **Breaking at a critical point.** Let `S` be an invariant set disjoint from the stable set of a
point `x`. If the closure of `S` meets `W^s(x)` (so that `x`, a limit of orbits, is a critical
point), then it also meets `W^u(x)` at a point other than `x`: orbits of `S` passing close to a
trajectory into `x` linger near `x` and leave along `W^u(x)`. -/
theorem exists_ne_mem_closure_inter_unstableSet (hf : IsMorse 𝓘(ℝ, E) f)
    {S : Set M} (hS : IsInvariant hX.flow S)
    (hSx : Disjoint S (hX.flow.stableSet x)) (hy : (closure S ∩ hX.flow.stableSet x).Nonempty) :
    ∃ z ∈ closure S ∩ hX.flow.unstableSet x, z ≠ x := by
  let := Manifold.metrizableSpace 𝓘(ℝ, E) M
  let := TopologicalSpace.metrizableSpaceMetric M
  -- A closed ball about `x` containing no other critical point traps orbits converging to `x`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
    (hf.finite_criticalPoints.sdiff (t := {x})).isClosed.isOpen_compl x (by simp)
  have hcrit : ∀ c, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f c = 0 → c ∈ Metric.closedBall x (ε / 2) → c = x :=
    fun c hc hcx ↦ by
      by_contra hne
      exact hball (Metric.closedBall_subset_ball (half_lt_self hε) hcx)
        ⟨mem_criticalPoints_iff_mfderiv_eq_zero.2 hc, hne⟩
  have hfwd : ∀ w, (∀ t, 0 ≤ t → hX.flow t w ∈ Metric.closedBall x (ε / 2)) →
      w ∈ hX.flow.stableSet x := fun w hw ↦ by
    obtain ⟨c, hc, hlim⟩ := hX.exists_tendsto_atTop hf w
    rw [hcrit c hc (Metric.isClosed_closedBall.mem_of_tendsto hlim
      ((eventually_ge_atTop 0).mono hw))] at hlim
    exact Flow.mem_stableSet.2 hlim
  have hbwd : ∀ w, (∀ t, t ≤ 0 → hX.flow t w ∈ Metric.closedBall x (ε / 2)) →
      w ∈ hX.flow.unstableSet x := fun w hw ↦ by
    obtain ⟨c, hc, hlim⟩ := hX.exists_tendsto_atBot hf w
    rw [hcrit c hc (Metric.isClosed_closedBall.mem_of_tendsto hlim
      ((eventually_le_atBot 0).mono hw))] at hlim
    exact Flow.mem_unstableSet.2 hlim
  obtain ⟨y, hy⟩ := hy
  obtain ⟨z, hz, hzx⟩ := Flow.exists_mem_closure_inter_unstableSet_of_mem_closure_inter_stableSet
    (half_pos hε) Metric.isClosed_sphere.isCompact hfwd hbwd hS hSx hy
  refine ⟨z, hz, fun h ↦ ?_⟩
  rw [h, dist_self] at hzx
  exact (half_pos hε).ne hzx

end Breaking

/-! ### Morse-index control along broken limits -/

/-- **The Morse index drops along a broken forward limit.** Under the Morse–Smale condition, if
the closure of the stable manifold of a critical point `q` meets the stable manifold of a
different critical point `x`, then `ind q < ind x`. -/
theorem IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {q : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (hqx : q ≠ x)
    (hy : (closure (hX.flow.stableSet q) ∩ hX.flow.stableSet x).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f q < manifoldMorseIndex 𝓘(ℝ, E) f x := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  -- Break at `x`, follow the broken piece to its forward limit `a`, and induct on the index.
  induction hn : manifoldMorseIndex 𝓘(ℝ, E) f x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    obtain ⟨z, hz, hzx⟩ := hX.exists_ne_mem_closure_inter_unstableSet hf
      (Flow.isInvariant_stableSet _ q) (Flow.disjoint_stableSet hqx) hy
    obtain ⟨a, ha, hlim⟩ := hX.exists_tendsto_atTop hf z
    have hza : z ∈ hX.flow.stableSet a := Flow.mem_stableSet.2 hlim
    have hax : x ≠ a := fun hxa ↦ hzx (hX.eq_of_mem_unstableSet_inter_stableSet hdf
      ⟨hz.2, hxa ▸ hza⟩)
    have hdrop := h.manifoldMorseIndex_lt hf hx ha hax ⟨z, hz.2, hza⟩
    rcases eq_or_ne q a with rfl | hqa
    · exact hn ▸ hdrop
    · exact (ih _ (hn ▸ hdrop) ha hqa ⟨z, hz.1, hza⟩ rfl).trans (hn ▸ hdrop)

/-- **The Morse index drops along a broken backward limit.** Under the Morse–Smale condition, if
the closure of the unstable manifold of a critical point `p` meets the unstable manifold of a
different critical point `x`, then `ind x < ind p`. This is the forward statement for the
reversed pseudo-gradient `-X`, adapted to `-f`, whose indices are complementary. -/
theorem IsMorseSmale.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p : M}
    (hx : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x = 0) (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hpx : p ≠ x)
    (hy : (closure (hX.flow.unstableSet p) ∩ hX.flow.unstableSet x).Nonempty) :
    manifoldMorseIndex 𝓘(ℝ, E) f x < manifoldMorseIndex 𝓘(ℝ, E) f p := by
  have hneg := (h.neg hf).manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf.neg
    (mfderiv_neg_eq_zero_iff.2 hx) hpx
    (by simpa only [hX.neg_flow hf, Flow.stableSet_reverse] using hy)
  have hx' := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    hx).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have hp' := (hf.isManifoldNondegenerateCriticalPoint_of_mfderiv_eq_zero
    hp).manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  omega

/-! ### Index-one trajectory spaces -/

/-- **An index-one trajectory slice is closed.** Under the Morse–Smale condition, if the Morse
indices of critical points `a` and `b` differ by one, then the points of trajectories from `a` to
`b` on a level `c` strictly between `f b` and `f a` form a closed set. -/
theorem IsMorseSmale.isClosed_unstableSet_inter_stableSet_inter_level
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + 1) {c : ℝ}
    (hc : f b < c ∧ c < f a) :
    IsClosed (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {z | f z = c}) := by
  -- A limit point `y` has backward and forward limits `a'` and `b'`. Each break lowers the index,
  -- and the indices of `a` and `b` are consecutive, so `a' = a` and `b' = b`; the remaining
  -- degenerate cases put `y` at `a` or `b`, off the level `c`.
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  refine isClosed_of_closure_subset fun y hy ↦ ?_
  have hyU : y ∈ closure (hX.flow.unstableSet a) := closure_mono (by exact fun _ hz ↦ hz.1.1) hy
  have hyS : y ∈ closure (hX.flow.stableSet b) := closure_mono (by exact fun _ hz ↦ hz.1.2) hy
  have hyc : f y = c := (isClosed_eq hdf.continuous continuous_const).closure_subset
    (closure_mono (by exact fun _ hz ↦ hz.2) hy)
  obtain ⟨a', ha', hlima⟩ := hX.exists_tendsto_atBot hf y
  obtain ⟨b', hb', hlimb⟩ := hX.exists_tendsto_atTop hf y
  have hya : y ∈ hX.flow.unstableSet a' := Flow.mem_unstableSet.2 hlima
  have hyb : y ∈ hX.flow.stableSet b' := Flow.mem_stableSet.2 hlimb
  -- If `y` runs from a critical point to itself, it is that point, which is not on the level.
  have hne : ∀ x, y ∈ hX.flow.unstableSet x → y ∈ hX.flow.stableSet x →
      x ≠ a ∧ x ≠ b := fun x hu hs ↦ by
    have hyx := hX.eq_of_mem_unstableSet_inter_stableSet hdf ⟨hu, hs⟩
    constructor <;> rintro rfl <;> rw [hyx] at hyc <;> linarith
  have hab' : a' ≠ b' → manifoldMorseIndex 𝓘(ℝ, E) f b' < manifoldMorseIndex 𝓘(ℝ, E) f a' :=
    fun hne' ↦ h.manifoldMorseIndex_lt hf ha' hb' hne' ⟨y, hya, hyb⟩
  have hbb : b' ≠ b → manifoldMorseIndex 𝓘(ℝ, E) f b < manifoldMorseIndex 𝓘(ℝ, E) f b' :=
    fun hne' ↦ h.manifoldMorseIndex_lt_of_mem_closure_stableSet_inter_stableSet hf hb'
      (Ne.symm hne') ⟨y, hyS, hyb⟩
  have haa : a' ≠ a → manifoldMorseIndex 𝓘(ℝ, E) f a' < manifoldMorseIndex 𝓘(ℝ, E) f a :=
    fun hne' ↦ h.manifoldMorseIndex_lt_of_mem_closure_unstableSet_inter_unstableSet hf ha' ha
      (Ne.symm hne') ⟨y, hyU, hya⟩
  rcases eq_or_ne a' a with rfl | ha'a <;> rcases eq_or_ne b' b with rfl | hb'b
  · exact ⟨⟨hya, hyb⟩, hyc⟩
  · rcases eq_or_ne a' b' with rfl | hab
    · exact ((hne a' hya hyb).1 rfl).elim
    · have := hab' hab; have := hbb hb'b; omega
  · rcases eq_or_ne a' b' with rfl | hab
    · exact ((hne a' hya hyb).2 rfl).elim
    · have := hab' hab; have := haa ha'a; omega
  · rcases eq_or_ne a' b' with rfl | hab
    · have := hbb hb'b; have := haa ha'a; omega
    · have := hab' hab; have := hbb hb'b; have := haa ha'a; omega

/-- **There are finitely many index-one trajectories.** Under the Morse–Smale condition, if the
Morse indices of critical points `a` and `b` differ by one, then on a level `c` strictly between
`f b` and `f a`, which every trajectory from `a` to `b` crosses exactly once, there are only
finitely many points of such trajectories. -/
theorem IsMorseSmale.finite_unstableSet_inter_stableSet_inter_level
    {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    (ha : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f a = 0) (hb : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f b = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f a = manifoldMorseIndex 𝓘(ℝ, E) f b + 1) {c : ℝ}
    (hc : f b < c ∧ c < f a) :
    (hX.flow.unstableSet a ∩ hX.flow.stableSet b ∩ {z | f z = c}).Finite :=
  (h.isClosed_unstableSet_inter_stableSet_inter_level hf ha hb hind hc).isCompact.finite
    (hX.isDiscrete_unstableSet_inter_stableSet_level hf ha hb hind fun _ hy ↦
      h.span_mtangentConeAt_sup_eq_top ha hb hy.1)

end IsAdaptedPseudoGradient

end TauCeti
