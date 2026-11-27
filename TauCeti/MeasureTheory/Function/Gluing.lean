/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.Bases
public import TauCeti.MeasureTheory.Measure.OpenPos
public import TauCeti.Topology.MetricSpace.Holder

/-!
# Gluing functions from local pieces

Functions prescribed on a sequence of measurable sets, which agree almost everywhere on the
pairwise intersections, come from a single function. This is the step which glues local limits,
obtained on each member of a compact exhaustion, into one function, as in the diagonal argument
for sequential compactness in `Lᵖ_loc`.

In a second-countable space, a property holding almost everywhere on each member of an open cover
of a set holds almost everywhere on that set, even if the cover is uncountable: Mathlib's
`TopologicalSpace.isOpen_iUnion_countable` extracts a countable subcover. Likewise, continuous
local representatives of one function on the neighbourhoods of a Lindelöf set agree on overlaps and
glue to one representative on the set.

Pieces that are continuous up to the boundary are determined by their almost-everywhere values:
for a measure charging every nonempty open set, two functions continuous on `closure U ∩ V`, for
open `U` and `V`, which agree almost everywhere on `U ∩ V` agree on `closure U ∩ V`
(`IsOpen.eqOn_closure_inter_of_ae_eq`). Consequently bounded Hölder functions on the balls of a
cover of a compact closure `closure U`, each agreeing almost everywhere on `U` with one function
`F`, glue along a finite subcover to a single bounded Hölder function on `closure U`. Its constant
depends only on `U`, the radii and weights of the cover and the exponent, so it is uniform over all
such families of pieces. This is the step that assembles local regularity estimates, in the
interior and up to the boundary, into global ones.

## Main results

* `TauCeti.exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter`: functions on a sequence of
  measurable sets which agree almost everywhere on the pairwise intersections glue to a single
  function.
* `TauCeti.ae_restrict_of_subset_iUnion_isOpen`: almost-everywhere statements on the members of an
  open cover hold almost everywhere on the covered set.
* `IsLindelof.exists_ae_eq_and_eqOn_of_forall_ae_eq_continuousOn`: continuous local
  representatives of a function near the points of a Lindelöf set glue to a single representative
  agreeing with each of them on its domain within the set.
* `IsOpen.exists_holderOnWith_closure_of_forall_ae_eq`: Hölder functions on the balls of a cover
  of a compact closure `closure U`, each agreeing almost everywhere on `U` with one function `F`,
  glue to a single Hölder function on `closure U`, with a constant uniform over all such pieces.
  This is how local regularity estimates up to the boundary assemble into a global one.
-/

public section

namespace TauCeti

open MeasureTheory Filter Metric Set
open scoped NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Gluing along a sequence of sets.** If `L` is a sequence of measurable sets and the functions
`a m` are compatible, in the sense that `a k = a m` almost everywhere on `L k ∩ L m`, then a single
function agrees almost everywhere on each `L m` with `a m`. -/
theorem exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter {Y : Type*} {L : ℕ → Set X}
    (hL : ∀ m, MeasurableSet (L m)) {a : ℕ → X → Y}
    (ha : ∀ k m, a k =ᵐ[μ.restrict (L k ∩ L m)] a m) :
    ∃ v : X → Y, ∀ m, v =ᵐ[μ.restrict (L m)] a m := by
  classical
  -- On the points of `⋃ k, L k`, take `v = a k` for the least `k` with the point in `L k`.
  refine ⟨fun y => if h : ∃ m, y ∈ L m then a (Nat.find h) y else a 0 y, fun m => ?_⟩
  have hall : ∀ᵐ y ∂μ.restrict (L m), ∀ k, y ∈ L k → a k y = a m y := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' ((hL k).inter (hL m))).1 (ha k m)),
      ae_restrict_mem (hL m)] with y hy hym hyk using hy ⟨hyk, hym⟩
  filter_upwards [hall, ae_restrict_mem (hL m)] with y hy hym
  have h : ∃ m, y ∈ L m := ⟨m, hym⟩
  rw [dite_eq_left h]
  exact hy _ (Nat.find_spec h)

/-- **Almost everywhere along an open cover.** In a second-countable space, a property holding
almost everywhere on each member of a family of open sets covering `s` holds almost everywhere on
`s`. The family may be uncountable. -/
theorem ae_restrict_of_subset_iUnion_isOpen [TopologicalSpace X] [SecondCountableTopology X]
    {ι : Type*} {s : Set X} {t : ι → Set X} (ht : ∀ i, IsOpen (t i)) (hs : s ⊆ ⋃ i, t i)
    {P : X → Prop} (h : ∀ i, ∀ᵐ x ∂μ.restrict (t i), P x) : ∀ᵐ x ∂μ.restrict s, P x := by
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable t ht
  have : Countable T := hTc.to_subtype
  rw [← hT, Set.biUnion_eq_iUnion] at hs
  exact ae_mono (Measure.restrict_mono_set μ hs) ((ae_restrict_iUnion_iff _ _).2 fun i => h i)

/-- **Continuous local representatives glue.** Let `μ` charge every nonempty open set, and let
every point `x` of a Lindelöf set `s` have an open neighbourhood `U x` on which `f` agrees
`μ`-almost everywhere with a function `g x` continuous on `U x`. Then a single function agrees
with every `g x` on `U x ∩ s`, and with `f` almost everywhere. -/
theorem _root_.IsLindelof.exists_ae_eq_and_eqOn_of_forall_ae_eq_continuousOn
    [TopologicalSpace X] [μ.IsOpenPosMeasure] {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {s : Set X} (hs : IsLindelof s) {f : X → Y} {U : X → Set X} {g : X → X → Y}
    (hU : ∀ x ∈ s, IsOpen (U x)) (hxU : ∀ x ∈ s, x ∈ U x)
    (hg : ∀ x ∈ s, ContinuousOn (g x) (U x)) (hfg : ∀ x ∈ s, f =ᵐ[μ.restrict (U x)] g x) :
    ∃ G : X → Y, f =ᵐ[μ] G ∧ ∀ x ∈ s, EqOn G (g x) (U x ∩ s) := by
  classical
  -- Two local representatives are continuous and agree almost everywhere on the overlap of their
  -- domains, hence agree everywhere there.
  have hgg : ∀ x ∈ s, ∀ y ∈ s, EqOn (g x) (g y) (U x ∩ U y) := fun x hx y hy ↦ by
    have hfx : f =ᵐ[μ.restrict (U x ∩ U y)] g x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hfg x hx)
    have hfy : f =ᵐ[μ.restrict (U x ∩ U y)] g y :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hfg y hy)
    exact Measure.eqOn_open_of_ae_eq (hfx.symm.trans hfy) ((hU x hx).inter (hU y hy))
      ((hg x hx).mono inter_subset_left) ((hg y hy).mono inter_subset_right)
  -- At a point of `s` take the value of its own representative; outside `s` keep `f`.
  let G : X → Y := fun y ↦ if y ∈ s then g y y else f y
  have hG : ∀ x ∈ s, EqOn G (g x) (U x ∩ s) := fun x hx y hy ↦ by
    simp only [G, hy.2, ↓reduceIte]
    exact hgg y hy.2 x hx ⟨hxU y hy.2, hy.1⟩
  refine ⟨G, ae_iff.2 ?_, hG⟩
  -- Countably many of the neighbourhoods cover `s`, where all disagreement of `f` and `G` lies.
  obtain ⟨t, htc, hts, hst⟩ :=
    hs.elim_nhds_subcover U fun x hx ↦ (hU x hx).mem_nhds (hxU x hx)
  have hsub : {y | ¬f y = G y} ⊆ ⋃ x ∈ t, {y | ¬f y = g x y} ∩ U x := fun y hy ↦ by
    have hys : y ∈ s := by
      by_contra h
      exact hy (by simp only [G, h, ↓reduceIte])
    obtain ⟨x, hxt, hyU⟩ := mem_iUnion₂.1 (hst hys)
    exact mem_iUnion₂.2 ⟨x, hxt, fun h ↦ hy (h.trans (hG x (hts x hxt) ⟨hyU, hys⟩).symm), hyU⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff htc).2 fun x hx ↦ ?_)
  exact nonpos_iff_eq_zero.1
    ((Measure.le_restrict_apply _ _).trans (ae_iff.1 (hfg x (hts x hx))).le)

/-- **Gluing Hölder pieces that agree almost everywhere.** Let `U` be open with compact closure in
a pseudometric space with a measure charging every nonempty open set, and assign to each
`x ∈ closure U` a radius `ρ x > 0` and a weight `κ x`. Then there is a constant `A`, depending only
on `U`, `ρ`, `κ` and `β`, with the following property. Suppose that, for each `x ∈ closure U`, a
function `g x` is `β`-Hölder with constant `κ x * B` and bounded by `κ x * B` on
`B(x, ρ x) ∩ closure U`, and agrees almost everywhere on `U ∩ B(x, ρ x)` with one function `F`.
Then the pieces agree with each other where their balls overlap, and glue to a function `h` on
`closure U` which is `β`-Hölder with constant `A * B`, bounded by `A * B`, agrees with every piece
on its ball and agrees with `F` almost everywhere on `U`. -/
theorem _root_.IsOpen.exists_holderOnWith_closure_of_forall_ae_eq [PseudoMetricSpace X]
    [OpensMeasurableSpace X] [μ.IsOpenPosMeasure] {Y : Type*} [NormedAddCommGroup Y] {U : Set X}
    (hU : IsOpen U) (hc : IsCompact (closure U)) {β : ℝ≥0} (hβ : 0 < β) {ρ : X → ℝ}
    (hρ : ∀ x ∈ closure U, 0 < ρ x) (κ : X → ℝ≥0) :
    ∃ A : ℝ≥0, ∀ {F : X → Y} {g : X → X → Y} {B : ℝ≥0},
      (∀ x ∈ closure U, HolderOnWith (κ x * B) β (g x) (ball x (ρ x) ∩ closure U)) →
      (∀ x ∈ closure U, ∀ y ∈ ball x (ρ x) ∩ closure U, ‖g x y‖ ≤ κ x * B) →
      (∀ x ∈ closure U, g x =ᵐ[μ.restrict (U ∩ ball x (ρ x))] F) →
      ∃ h : X → Y, HolderOnWith (A * B) β h (closure U) ∧ (∀ y ∈ closure U, ‖h y‖ ≤ A * B) ∧
        (∀ x ∈ closure U, EqOn h (g x) (ball x (ρ x) ∩ closure U)) ∧ F =ᵐ[μ.restrict U] h := by
  obtain ⟨t, hts, hcover⟩ := hc.elim_nhds_subcover (fun x => ball x (ρ x)) fun x hx =>
    ball_mem_nhds x (hρ x hx)
  -- The weight `D` bounds every piece of the finite subcover, and the Hölder constants of the
  -- pieces are rescaled to `κ x / D` times the bound `D * B` of the glued function.
  set D : ℝ≥0 := 1 + ∑ z ∈ t, κ z
  have hD : D ≠ 0 := (lt_of_lt_of_le one_pos le_self_add).ne'
  obtain ⟨A, hA⟩ := hc.exists_holderOnWith_of_forall_holderOnWith_ball_inter (Y := Y) (α := β) hρ
    fun x => κ x / D
  refine ⟨max (A * D) D, fun {F g B} hhol hbd hae => ⟨fun y => g y y, ?_⟩⟩
  -- Two pieces agree on the overlap of their balls, since both agree with `F` there.
  have heq : ∀ x ∈ closure U, EqOn (fun y => g y y) (g x) (ball x (ρ x) ∩ closure U) := by
    intro x hx y hy
    have hsx : closure U ∩ (ball x (ρ x) ∩ ball y (ρ y)) ⊆ ball x (ρ x) ∩ closure U :=
      fun w hw => ⟨hw.2.1, hw.1⟩
    have hsy : closure U ∩ (ball x (ρ x) ∩ ball y (ρ y)) ⊆ ball y (ρ y) ∩ closure U :=
      fun w hw => ⟨hw.2.2, hw.1⟩
    have hUy : U ∩ (ball x (ρ x) ∩ ball y (ρ y)) ⊆ U ∩ ball y (ρ y) := fun w hw => ⟨hw.1, hw.2.2⟩
    have hUx : U ∩ (ball x (ρ x) ∩ ball y (ρ y)) ⊆ U ∩ ball x (ρ x) := fun w hw => ⟨hw.1, hw.2.1⟩
    refine hU.eqOn_closure_inter_of_ae_eq (μ := μ) (isOpen_ball.inter isOpen_ball)
      (((hhol y hy.2).continuousOn hβ).mono hsy) (((hhol x hx).continuousOn hβ).mono hsx)
      (((hae y hy.2).filter_mono (ae_mono (Measure.restrict_mono hUy le_rfl))).trans
        ((hae x hx).filter_mono (ae_mono (Measure.restrict_mono hUx le_rfl))).symm)
      ⟨hy.2, hy.1, mem_ball_self (hρ y hy.2)⟩
  -- Every point of `closure U` lies in a ball of the finite subcover.
  have hmem : ∀ y ∈ closure U, ∃ z ∈ t, y ∈ ball z (ρ z) := fun y hy => by
    simpa only [mem_iUnion₂, exists_prop] using hcover hy
  have hbound : ∀ y ∈ closure U, ‖g y y‖ ≤ D * B := fun y hy => by
    obtain ⟨z, hz, hyz⟩ := hmem y hy
    rw [show g y y = g z y from heq z (hts z hz) ⟨hyz, hy⟩]
    refine (hbd z (hts z hz) y ⟨hyz, hy⟩).trans ?_
    gcongr
    exact le_add_left (Finset.single_le_sum (fun _ _ => zero_le) hz)
  have hAB := hA (f := fun y => g y y) (B := D * B) (fun y hy => by exact_mod_cast hbound y hy)
    fun x hx => ((hhol x hx).congr (heq x hx).symm).mono_const (le_of_eq (by
      rw [← mul_assoc, div_mul_cancel₀ _ hD]))
  refine ⟨hAB.mono_const (by rw [← mul_assoc]; gcongr; exact le_max_left _ _),
    fun y hy => (hbound y hy).trans (by gcongr; exact le_max_right _ _), heq, ?_⟩
  -- `F` agrees with the piece of each ball of the finite subcover, hence with `h`.
  rw [Filter.EventuallyEq]
  refine ae_restrict_of_ae_restrict_of_subset (t := ⋃ z ∈ t, U ∩ ball z (ρ z)) (fun y hy => ?_)
    ((ae_restrict_biUnion_finset_iff (μ := μ) _ t _).2 fun z hz => ?_)
  · obtain ⟨z, hz, hyz⟩ := hmem y (subset_closure hy)
    exact mem_iUnion₂.2 ⟨z, hz, hy, hyz⟩
  · filter_upwards [hae z (hts z hz), ae_restrict_mem (hU.inter isOpen_ball).measurableSet]
      with y hy hyU
    rw [show g y y = g z y from heq z (hts z hz) ⟨hyU.2, subset_closure hyU.1⟩]
    exact hy.symm

end TauCeti
