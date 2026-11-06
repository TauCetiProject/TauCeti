/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice
public import TauCeti.Geometry.Manifold.Morse.Stable.SequentialCompactness
public import TauCeti.Geometry.Manifold.Boundary.OneDimensional
import Mathlib.Geometry.Manifold.Metrizable
import TauCeti.Dynamics.Flow.Lyapunov
import TauCeti.Geometry.Manifold.Morse.CriticalPoints

/-!
# The compactified space of index-two trajectories on a compact manifold

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition, and `p`, `r` critical points with
`ind p = ind r + 2`. Choose levels `f r < b < a < f p` such that every critical value strictly
between `f r` and `f p` lies strictly between `b` and `a`; such levels exist because `f` has
finitely many critical points (`TauCeti.IsMorse.exists_levels_between_criticalValues`).

Record a trajectory from `p` to `r` by the pair `(y₁, y₂) ∈ M × M` of its points on the levels `a`
and `b`. These pairs form the set `TauCeti.IsAdaptedPseudoGradient.morseTrajectoryPairs`. A broken
trajectory, from `p` to a critical point `q` of the intermediate index and then from `q` to `r`,
crosses the level `a` on its first component and the level `b` on its second, because `b < f q < a`.
Recording it by these two points gives the set
`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectoryPairs`. Since `y₁` determines the first
component and `y₂` the second, distinct broken trajectories give distinct pairs. This is why two
levels are used: on a single level, the two arcs of trajectories ending at broken trajectories with
a common component would end at the same point.

The closure of the unbroken pairs in `M × M` is the compactified space of index-two trajectories.
This file proves:

* it is compact and Hausdorff, as a closed subset of `M × M`;
* the points it adds are broken pairs
  (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.closure_morseTrajectoryPairs_subset`). This is the
  compatibility of the topology with broken convergence: if trajectories converge on the level `a`
  to a point of a trajectory broken at `q`, their points on the level `b` converge to the point of
  the second component on that level;
* there are finitely many broken pairs, none of them unbroken;
* the unbroken pairs form an open subset of the compactified space, homeomorphic to the level slice
  `W^u(p) ∩ W^s(r) ∩ {f = a}` by the first projection, so every unbroken point has a neighbourhood
  homeomorphic to an open subset of `ℝ`.

Consequently, if each broken pair has a neighbourhood in the compactified space homeomorphic to a
half-open interval `[0, ε)` with endpoint the broken pair, the compactified space is a compact
one-dimensional manifold whose boundary is the set of broken pairs, and the number of broken pairs
is even (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.even_ncard_morseBrokenTrajectoryPairs`).
Those half-open neighbourhoods are supplied by gluing broken trajectories
(compare `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.exists_homeomorph_closure_splitGluingPairs`
for the model flow in a Morse chart), which is not done here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseTrajectoryPairs` and `morseBrokenTrajectoryPairs`: unbroken and broken trajectories from
  `p` to `r`, recorded by their points on the levels `a` and `b`.
* `exists_homeomorph_morseTrajectoryPairs`: the first projection identifies the unbroken pairs with
  the level slice on the level `a`.
* `IsMorseSmale.closure_morseTrajectoryPairs_subset`: the limits of unbroken pairs are unbroken or
  broken pairs.
* `disjoint_morseTrajectoryPairs_morseBrokenTrajectoryPairs`: no broken pair is unbroken.
* `IsMorseSmale.finite_morseBrokenTrajectoryPairs`: there are finitely many broken pairs.
* `IsMorseSmale.isOpen_preimage_val_morseTrajectoryPairs`: the unbroken pairs are open in their
  closure.
* `IsMorseSmale.exists_nhds_homeomorph_of_mem_morseTrajectoryPairs`: unbroken points of the
  compactified space have neighbourhoods homeomorphic to open subsets of `ℝ`.
* `IsMorseSmale.even_ncard_morseBrokenTrajectoryPairs`: given half-open neighbourhoods of the broken
  pairs, there is an even number of broken pairs.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (compactness of spaces of trajectories, and the compactified spaces of index-two
  trajectories as compact one-manifolds with boundary).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold Set.Notation

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- The unbroken trajectories from `p` to `r`, recorded by their points on the levels `a` and `b`:
the pairs `(y₁, y₂)` of points of one trajectory from `p` to `r` with `f y₁ = a` and `f y₂ = b`. -/
def morseTrajectoryPairs (p r : M) (a b : ℝ) : Set (M × M) :=
  {y | y.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ f y.1 = a ∧ f y.2 = b ∧
    ∃ t, hX.flow t y.1 = y.2}

/-- Membership in the set of unbroken trajectory pairs. -/
@[simp]
theorem mem_morseTrajectoryPairs {p r : M} {a b : ℝ} {y : M × M} :
    y ∈ hX.morseTrajectoryPairs p r a b ↔
      y.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r ∧ f y.1 = a ∧ f y.2 = b ∧
        ∃ t, hX.flow t y.1 = y.2 :=
  Iff.rfl

/-- The broken index-two trajectories from `p` to `r`, recorded by their points on the levels `a`
and `b`: the pairs `(y₁, y₂)` such that, for some critical point `q` with
`ind p = ind q + 1 = ind r + 2`, the point `y₁` lies on a trajectory from `p` to `q` with `f y₁ = a`
and the point `y₂` on a trajectory from `q` to `r` with `f y₂ = b`. -/
def morseBrokenTrajectoryPairs (p r : M) (a b : ℝ) : Set (M × M) :=
  {y | ∃ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
    y.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧ f y.1 = a ∧
    y.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∧ f y.2 = b}

/-- Membership in the set of broken trajectory pairs. -/
@[simp]
theorem mem_morseBrokenTrajectoryPairs {p r : M} {a b : ℝ} {y : M × M} :
    y ∈ hX.morseBrokenTrajectoryPairs p r a b ↔
      ∃ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
        y.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q ∧ f y.1 = a ∧
        y.2 ∈ hX.flow.unstableSet q ∩ hX.flow.stableSet r ∧ f y.2 = b :=
  Iff.rfl

variable {hX}

/-- If `u i → w`, with `w` on a trajectory joining distinct critical points, and the orbit of
`u i` meets the level of `w` at time `s i`, then these crossing points converge to `w`. -/
private theorem tendsto_of_apply_eq (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {a b w : M}
    (hab : a ≠ b) (hw : w ∈ hX.flow.unstableSet a ∩ hX.flow.stableSet b) {ι : Type*}
    {l : Filter ι} {u : ι → M} {s : ι → ℝ} (hu : Tendsto u l (𝓝 w))
    (hs : ∀ᶠ i in l, f (hX.flow (s i) (u i)) = f w) :
    Tendsto (fun i ↦ hX.flow (s i) (u i)) l (𝓝 w) :=
  Flow.tendsto_apply_of_apply_eq_of_antitone hf.continuous (hX.antitone_flow hf)
    (hX.strictAnti_flow_of_mem_unstableSet_inter_stableSet hf hab hw) hu hs

/-- **Unbroken pairs are read on the level `a`.** For distinct critical points `p` and `r` and a
level `f r < b < f p`, the first projection is a homeomorphism from the unbroken trajectory pairs
onto the level slice `W^u(p) ∩ W^s(r) ∩ {f = a}`: a trajectory crosses the level `b` at a single
point, which depends continuously on its point on the level `a`. -/
theorem exists_homeomorph_morseTrajectoryPairs (hX : IsAdaptedPseudoGradient f X)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p r : M} (hpr : p ≠ r) {a b : ℝ} (hrb : f r < b)
    (hbp : b < f p) :
    ∃ e : hX.morseTrajectoryPairs p r a b ≃ₜ
        ↥(hX.flow.unstableSet p ∩ hX.flow.stableSet r ∩ {x | f x = a}),
      ∀ y, (e y : M) = (y : M × M).1 := by
  set L := hX.flow.unstableSet p ∩ hX.flow.stableSet r ∩ {x | f x = a}
  -- Each trajectory through the slice crosses the level `b` at a unique time `τ y`.
  have hcross (y : L) : ∃! t, f (hX.flow t y.1) = b :=
    hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hf hpr y.2.1 hrb hbp
  choose τ hτ hτu using hcross
  have hmem (y : L) (t : ℝ) : hX.flow t y.1 ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet r :=
    hX.flow.isInvariant_unstableSet_inter_stableSet p r t y.2.1
  -- The crossing point depends continuously on the point of the slice.
  have hcont : Continuous fun y : L ↦ hX.flow (τ y) y.1 := by
    refine continuous_iff_continuousAt.2 fun y₀ ↦ ?_
    have hu : Tendsto (fun y : L ↦ hX.flow (τ y₀) y.1) (𝓝 y₀) (𝓝 (hX.flow (τ y₀) y₀.1)) :=
      ((hX.flow.continuous_toFun _).comp continuous_subtype_val).continuousAt
    have h := tendsto_of_apply_eq hf hpr (hmem y₀ (τ y₀)) hu (s := fun y ↦ τ y - τ y₀)
      (Eventually.of_forall fun y ↦ by rw [← Flow.map_add, sub_add_cancel, hτ, hτ])
    have h' : Tendsto (fun y : L ↦ hX.flow (τ y) y.1) (𝓝 y₀) (𝓝 (hX.flow (τ y₀) y₀.1)) := by
      simpa only [← Flow.map_add, sub_add_cancel] using h
    exact h'
  refine ⟨{ toFun := fun y ↦ ⟨y.1.1, y.2.1, y.2.2.1⟩
            invFun := fun y ↦ ⟨(y.1, hX.flow (τ y) y.1), y.2.1, y.2.2, hτ y, τ y, rfl⟩
            left_inv := fun y ↦ ?_
            right_inv := fun y ↦ rfl
            continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
            continuous_invFun := (continuous_subtype_val.prodMk hcont).subtype_mk _ },
    fun _ ↦ rfl⟩
  obtain ⟨⟨y₁, y₂⟩, hy, hya, hyb, t, ht⟩ := y
  have hτt : τ ⟨y₁, hy, hya⟩ = t :=
    (hτu ⟨y₁, hy, hya⟩ t (by simpa only [ht] using hyb)).symm
  simp only [hτt, ht]

/-- **Broken pairs are not unbroken.** For critical points with `ind p = ind r + 2`, no pair is both
an unbroken and a broken trajectory pair: its first point would converge both to `r` and to an
intermediate critical point. -/
theorem disjoint_morseTrajectoryPairs_morseBrokenTrajectoryPairs (hX : IsAdaptedPseudoGradient f X)
    {p r : M}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) (a b : ℝ) :
    Disjoint (hX.morseTrajectoryPairs p r a b) (hX.morseBrokenTrajectoryPairs p r a b) := by
  refine disjoint_left.2 fun y hy ⟨q, _, _, hqr, hyq, _⟩ ↦ ?_
  have hqr' : q ≠ r := by rintro rfl; omega
  exact (Flow.disjoint_stableSet hqr').notMem_of_mem_left hyq.2 hy.1.2

namespace IsMorseSmale

/-- **Broken convergence in the compactified trajectory space.** Let `p` and `r` be critical
points with `ind p = ind r + 2`, and `f r < b < a < f p` levels such that every critical value
strictly between `f r` and `f p` lies strictly between `b` and `a`. A limit of unbroken trajectory
pairs is an unbroken or a broken trajectory pair: if trajectories converge on the level `a` to a
point of a trajectory from `p` to `q`, their points on the level `b` converge to a point of a
trajectory from `q` to `r`. -/
theorem closure_morseTrajectoryPairs_subset (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {a b : ℝ}
    (hrb : f r < b) (hba : b < a) (hap : a < f p)
    (hcrit : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f r < f q → f q < f p → b < f q ∧ f q < a) :
    closure (hX.morseTrajectoryPairs p r a b) ⊆
      hX.morseTrajectoryPairs p r a b ∪ hX.morseBrokenTrajectoryPairs p r a b := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have := Manifold.metrizableSpace 𝓘(ℝ, E) M
  have hpr : p ≠ r := by rintro rfl; omega
  intro Y hY
  obtain ⟨y, hyP, hyY⟩ := mem_closure_iff_seq_limit.1 hY
  choose t ht using fun k ↦ (hyP k).2.2.2
  -- The level `a` contains no critical point.
  have hreg : ∀ z, f z = a → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z ≠ 0 := fun z hz hcz ↦ by
    have := hcrit z hcz (by linarith) (by linarith)
    linarith [this.2]
  obtain ⟨n, Y₁, hn, -, hY₁, hcase⟩ :=
    h.exists_subseq_unbroken_or_broken_of_manifoldMorseIndex_eq_add_two hf hp hr hind hreg
      (fun k ↦ (y k).1) fun k ↦ ⟨(hyP k).1, (hyP k).2.1⟩
  have hfst : Tendsto (fun k ↦ (y (n k)).1) atTop (𝓝 Y.1) :=
    ((continuous_fst.tendsto Y).comp hyY).comp hn.tendsto_atTop
  have hsnd : Tendsto (fun k ↦ (y (n k)).2) atTop (𝓝 Y.2) :=
    ((continuous_snd.tendsto Y).comp hyY).comp hn.tendsto_atTop
  obtain rfl : Y₁ = Y.1 := tendsto_nhds_unique hY₁ hfst
  have hYa : f Y.1 = a :=
    (isClosed_eq hdf.continuous continuous_const).mem_of_tendsto hfst
      (Eventually.of_forall fun k ↦ (hyP (n k)).2.1)
  -- If the orbits of the `(y (n k)).1`, shifted by the times `σ k`, converge to a point `w` of a
  -- trajectory from `c` to `r` crossing the level `b` at time `s`, then `Y.2` is that crossing.
  have hlim : ∀ {c w : M} {σ : ℕ → ℝ}, c ≠ r →
      w ∈ hX.flow.unstableSet c ∩ hX.flow.stableSet r → b < f c →
      Tendsto (fun k ↦ hX.flow (σ k) (y (n k)).1) atTop (𝓝 w) →
      Y.2 ∈ hX.flow.unstableSet c ∩ hX.flow.stableSet r ∧ f Y.2 = b ∧
        ∃ s, hX.flow s w = Y.2 := by
    intro c w σ hcr hw hbc hσ
    obtain ⟨s, hs, -⟩ :=
      hX.existsUnique_flow_eq_of_mem_unstableSet_inter_stableSet hdf hcr hw hrb hbc
    have hws := hX.flow.isInvariant_unstableSet_inter_stableSet c r s hw
    have hu : Tendsto (fun k ↦ hX.flow (s + σ k) (y (n k)).1) atTop (𝓝 (hX.flow s w)) := by
      simpa only [Flow.map_add, Function.comp_def] using
        ((hX.flow.continuous_toFun s).tendsto w).comp hσ
    have hv := tendsto_of_apply_eq hdf hcr hws hu (s := fun k ↦ t (n k) - (s + σ k))
      (Eventually.of_forall fun k ↦ by
        rw [← Flow.map_add, sub_add_cancel, ht, (hyP (n k)).2.2.1, hs])
    simp only [← Flow.map_add, sub_add_cancel, ht] at hv
    rw [tendsto_nhds_unique hsnd hv]
    exact ⟨hws, hs, s, rfl⟩
  rcases hcase with hunb | ⟨q, z, τ, hq, hpq, hqr, hzlim, hbr⟩
  · -- The limit is unbroken: the shift is zero and the trajectory runs from `p` to `r`.
    obtain ⟨-, hY₂b, s, hs⟩ := hlim (σ := fun _ ↦ 0) hpr hunb (hba.trans hap)
      (by simpa only [Flow.map_zero_apply] using hfst)
    exact Or.inl ⟨hunb, hYa, hY₂b, s, hs⟩
  · have hpq' : p ≠ q := by rintro rfl; omega
    have hqr' : q ≠ r := by rintro rfl; omega
    rcases hbr with ⟨hY₁q, hz, -⟩ | ⟨hY₁q, hz, -⟩
    · -- The limit breaks at `q` after crossing the level `a`, which lies above `f q`.
      have hY₁v := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hpq' hY₁q
      have hzv := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hqr' hz
      have hbq := (hcrit q hq (hzv.1.trans hzv.2) (hY₁v.1.trans hY₁v.2)).1
      obtain ⟨hY₂, hY₂b, -⟩ := hlim hqr' hz hbq hzlim
      exact Or.inr ⟨q, hq, hpq, hqr, hY₁q, hYa, hY₂, hY₂b⟩
    · -- A limit on the level `a` cannot lie on a trajectory leaving `q`, as `f q < a`.
      have hY₁v := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hqr' hY₁q
      have hzv := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hpq' hz
      have := (hcrit q hq (hY₁v.1.trans hY₁v.2) (hzv.1.trans hzv.2)).2
      linarith [hY₁v.2]

/-- **There are finitely many broken trajectories.** For critical points with `ind p = ind r + 2`
and levels `b < a` separating the critical values strictly between `f r` and `f p`, the set of
broken trajectory pairs is finite. -/
theorem finite_morseBrokenTrajectoryPairs (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    {a b : ℝ} (hrb : f r < b) (hap : a < f p)
    (hcrit : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f r < f q → f q < f p → b < f q ∧ f q < a) :
    (hX.morseBrokenTrajectoryPairs p r a b).Finite := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  -- The intermediate critical points through which a broken trajectory can pass.
  set Q := {q | mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
    f r < f q ∧ f q < f p}
  have hQ : Q.Finite := hf.finite_criticalPoints.subset fun q hq ↦ by
    rw [criticalPoints_eq_setOf_mfderiv_eq_zero]
    exact hq.1
  refine (hQ.biUnion fun q hq ↦
    ((h.finite_unstableSet_inter_stableSet_inter_level hf hp hq.1 hq.2.1
      ⟨(hcrit q hq.1 hq.2.2.2.1 hq.2.2.2.2).2, hap⟩).prod
    (h.finite_unstableSet_inter_stableSet_inter_level hf hq.1 hr hq.2.2.1
      ⟨hrb, (hcrit q hq.1 hq.2.2.2.1 hq.2.2.2.2).1⟩))).subset ?_
  rintro y ⟨q, hq, hpq, hqr, hy₁, hya, hy₂, hyb⟩
  have hpq' : p ≠ q := by rintro rfl; omega
  have hqr' : q ≠ r := by rintro rfl; omega
  have hy₁v := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hpq' hy₁
  have hy₂v := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hdf hqr' hy₂
  exact mem_biUnion (x := q) ⟨hq, hpq, hqr, hy₂v.1.trans hy₂v.2, hy₁v.1.trans hy₁v.2⟩
    ⟨⟨hy₁, hya⟩, hy₂, hyb⟩

/-- **Unbroken trajectories are open in the compactified space.** For critical points with
`ind p = ind r + 2` and levels `b < a` separating the critical values strictly between `f r` and
`f p`, the unbroken trajectory pairs form an open subset of their closure: the points the closure
adds are finitely many broken pairs. -/
theorem isOpen_preimage_val_morseTrajectoryPairs (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p r : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {a b : ℝ}
    (hrb : f r < b) (hba : b < a) (hap : a < f p)
    (hcrit : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f r < f q → f q < f p → b < f q ∧ f q < a) :
    IsOpen (closure (hX.morseTrajectoryPairs p r a b) ↓∩ hX.morseTrajectoryPairs p r a b) := by
  have hfin :
      (closure (hX.morseTrajectoryPairs p r a b) \ hX.morseTrajectoryPairs p r a b).Finite :=
    (h.finite_morseBrokenTrajectoryPairs hf hp hr hrb hap hcrit).subset fun y hy ↦
      (h.closure_morseTrajectoryPairs_subset hf hp hr hind hrb hba hap hcrit hy.1).resolve_left hy.2
  rw [← isClosed_compl_iff]
  convert hfin.isClosed.preimage continuous_subtype_val using 1
  ext y
  simp

/-- **Unbroken points of the compactified space are interior points of a curve.** For critical
points with `ind p = ind r + 2` and levels `b < a` separating the critical values strictly between
`f r` and `f p`, every unbroken trajectory pair has a neighbourhood in the closure of the unbroken
pairs that is homeomorphic to an open subset of `ℝ`. -/
theorem exists_nhds_homeomorph_of_mem_morseTrajectoryPairs (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {a b : ℝ}
    (hrb : f r < b) (hba : b < a) (hap : a < f p)
    (hcrit : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f r < f q → f q < f p → b < f q ∧ f q < a)
    (x : closure (hX.morseTrajectoryPairs p r a b))
    (hx : (x : M × M) ∈ hX.morseTrajectoryPairs p r a b) :
    ∃ N ∈ 𝓝 x, ∃ V : Set ℝ, IsOpen V ∧ Nonempty (V ≃ₜ N) := by
  have hdf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f := hf.contMDiff.mdifferentiable (by simp)
  have hpr : p ≠ r := by rintro rfl; omega
  obtain ⟨e, he⟩ := exists_homeomorph_morseTrajectoryPairs hX hdf hpr hrb (hba.trans hap)
  -- The level slice is a manifold of dimension `ind p - ind r - 1 = 1`.
  obtain ⟨K, hK, C, -, -⟩ := h.exists_unstableSet_inter_stableSet_level_isManifold hf hp hr hpr
    ⟨x.1.1, hx.1, hx.2.1⟩
  let := C
  let ℓ : K ≃L[ℝ] ℝ := ContinuousLinearEquiv.ofFinrankEq (by rw [Module.finrank_self]; omega)
  set y := e ⟨x.1, hx⟩
  set c := chartAt K y
  -- Read the chart at `y` in `ℝ` and push it into the compactified space.
  let j : ℓ.toHomeomorph '' c.target → closure (hX.morseTrajectoryPairs p r a b) :=
    inclusion subset_closure ∘ e.symm ∘ Subtype.val ∘ c.toHomeomorphSourceTarget.symm ∘
      (ℓ.toHomeomorph.image c.target).symm
  have hj : IsOpenEmbedding j :=
    (IsOpenEmbedding.inclusion subset_closure
      (h.isOpen_preimage_val_morseTrajectoryPairs hf hp hr hind hrb hba hap hcrit)).comp
    (e.symm.isOpenEmbedding.comp (c.open_source.isOpenEmbedding_subtypeVal.comp
      (c.toHomeomorphSourceTarget.symm.isOpenEmbedding.comp
        (ℓ.toHomeomorph.image c.target).symm.isOpenEmbedding)))
  have hxj : x ∈ range j := by
    have hcy : c y ∈ c.target := c.map_source (mem_chart_source K y)
    have h₁ : (ℓ.toHomeomorph.image c.target).symm ⟨ℓ (c y), mem_image_of_mem _ hcy⟩ =
        ⟨c y, hcy⟩ := (Homeomorph.symm_apply_eq _).2 (Subtype.ext rfl)
    have h₂ : c.toHomeomorphSourceTarget.symm ⟨c y, hcy⟩ = ⟨y, mem_chart_source K y⟩ :=
      (Homeomorph.symm_apply_eq _).2 (Subtype.ext rfl)
    refine ⟨⟨ℓ (c y), mem_image_of_mem _ hcy⟩, Subtype.ext ?_⟩
    simp only [j, Function.comp_apply, h₁, h₂, y, Homeomorph.symm_apply_apply, coe_inclusion]
  exact ⟨range j, hj.isOpen_range.mem_nhds hxj, _, ℓ.toHomeomorph.isOpenMap _ c.open_target,
    ⟨hj.isEmbedding.toHomeomorph⟩⟩

/-- **Broken trajectories come in pairs, given gluing charts.** Let `p` and `r` be critical points
with `ind p = ind r + 2`, and `b < a` levels separating the critical values strictly between `f r`
and `f p`. Suppose that each broken trajectory pair lies in the closure of the unbroken pairs, with
a neighbourhood there homeomorphic to a half-open interval `[0, ε)` by a homeomorphism sending `0`
to it. Then the closure is a compact one-dimensional manifold whose boundary consists of the broken
pairs, so there is an even number of broken pairs. -/
theorem even_ncard_morseBrokenTrajectoryPairs (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p r : M} (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hr : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f r = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f r + 2) {a b : ℝ}
    (hrb : f r < b) (hba : b < a) (hap : a < f p)
    (hcrit : ∀ q, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0 → f r < f q → f q < f p → b < f q ∧ f q < a)
    (hglue : ∀ y ∈ hX.morseBrokenTrajectoryPairs p r a b,
      ∃ hy : y ∈ closure (hX.morseTrajectoryPairs p r a b),
        ∃ N ∈ 𝓝 (⟨y, hy⟩ : closure (hX.morseTrajectoryPairs p r a b)),
          ∃ (ε : ℝ) (hε : 0 < ε) (e : Ico (0 : ℝ) ε ≃ₜ N),
            (e ⟨0, left_mem_Ico.2 hε⟩ : closure (hX.morseTrajectoryPairs p r a b)) = ⟨y, hy⟩) :
    Even (hX.morseBrokenTrajectoryPairs p r a b).ncard := by
  have : CompactSpace (closure (hX.morseTrajectoryPairs p r a b)) :=
    isCompact_iff_compactSpace.1 isClosed_closure.isCompact
  have key := even_ncard_of_forall_exists_homeomorph_Ico
    (B := closure (hX.morseTrajectoryPairs p r a b) ↓∩ hX.morseBrokenTrajectoryPairs p r a b)
    (F := ℝ) (Module.finrank_self ℝ) (fun x hx ↦ ?_) fun x hx ↦ ?_
  · rwa [ncard_preimage_of_injective_subset_range Subtype.val_injective
      fun y hy ↦ ⟨⟨y, (hglue y hy).1⟩, rfl⟩] at key
  · obtain ⟨_, hN⟩ := hglue x.1 hx
    exact hN
  · exact h.exists_nhds_homeomorph_of_mem_morseTrajectoryPairs hf hp hr hind hrb hba hap hcrit x
      ((h.closure_morseTrajectoryPairs_subset hf hp hr hind hrb hba hap hcrit x.2).resolve_right hx)

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
