/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.Transitive
public import TauCeti.Topology.Instances.AddCircle.Flow
public import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Checks: topologically transitive flows

* The unit-speed flow on the circle `UnitAddCircle` is topologically transitive, while its time-`1`
  map is the identity, which is not: transitivity of the flow does not pass to its time-`t` maps.
* The translation flow `x ↦ x + t` on `EReal`, a compact metrizable space without isolated points,
  is topologically transitive, since the orbit of `0` is the dense set of reals. No forward orbit
  is dense, as the forward orbit of `x` lies in `[x, ⊤]`. So a transitive flow on a compact metric
  space without isolated points need not have a dense forward orbit; it has a dense orbit
  (`Flow.isTopologicallyTransitive_iff_exists_dense_orbit`).
-/

public section

open Set Filter Topology

namespace TauCeti.Examples.FlowTransitive

/-! ### The unit-speed flow on the circle -/

/-- **Check.** The unit-speed flow on the circle is topologically transitive: every orbit is the
whole circle. -/
theorem isTopologicallyTransitive_translationFlow :
    (AddCircle.translationFlow (1 : ℝ)).IsTopologicallyTransitive := by
  refine Flow.isTopologicallyTransitive_of_dense_orbit (x := 0) ?_
  convert dense_univ
  refine eq_univ_of_forall fun y ↦ ?_
  induction y using QuotientAddGroup.induction_on with
  | H z =>
    refine ⟨z, ?_⟩
    change AddCircle.translationFlow 1 z 0 = _
    simp

/-- **Check.** The time-`1` map of the unit-speed flow on the circle is the identity, and its
iterates are not topologically transitive: the time-`t` map of a transitive flow need not be
transitive. -/
theorem not_isTopologicallyTransitive_translationFlow_one :
    AddCircle.translationFlow (1 : ℝ) 1 = id ∧
      ¬ MulAction.IsTopologicallyTransitive
        (IterateMulAct (AddCircle.translationFlow (1 : ℝ) 1)) UnitAddCircle := by
  have hid : AddCircle.translationFlow (1 : ℝ) 1 = id :=
    (AddCircle.translationFlow_eq_id_iff 1).2 (AddSubgroup.mem_zmultiples 1)
  refine ⟨hid, fun h ↦ ?_⟩
  have hne : ((0 : ℝ) : UnitAddCircle) ≠ ((1 / 2 : ℝ) : UnitAddCircle) := by
    rw [ne_comm, Ne, AddCircle.coe_zero, AddCircle.coe_eq_zero_iff_of_mem_Ico] <;> norm_num
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne
  obtain ⟨⟨n⟩, hn⟩ := h.exists_smul_inter hU ⟨_, hxU⟩ hV ⟨_, hyV⟩
  rw [← image_smul] at hn
  simp only [IterateMulAct.mk_smul, hid, Function.iterate_id, image_id] at hn
  exact (Set.disjoint_iff_inter_eq_empty.1 hUV ▸ hn).ne_empty rfl

/-! ### The translation flow on `EReal` -/

/-- The translation flow `x ↦ x + t` of `ℝ` on the extended reals, fixing `⊥` and `⊤`. -/
noncomputable def erealTranslationFlow : Flow ℝ EReal where
  toFun t x := x + t
  cont' := by
    refine continuous_iff_continuousAt.2 fun p ↦ ?_
    have h : ContinuousAt (fun q : EReal × EReal ↦ q.1 + q.2) (p.2, (p.1 : EReal)) :=
      EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
    have hg : Continuous fun q : ℝ × EReal ↦ (q.2, (q.1 : EReal)) :=
      continuous_snd.prodMk (continuous_coe_real_ereal.comp continuous_fst)
    exact ContinuousAt.comp (f := fun q : ℝ × EReal ↦ (q.2, (q.1 : EReal))) h hg.continuousAt
  map_add' t s x := by
    simp only [EReal.coe_add]
    rw [add_comm (t : EReal), add_assoc]
  map_zero' x := by simp

@[simp]
theorem erealTranslationFlow_apply (t : ℝ) (x : EReal) : erealTranslationFlow t x = x + t :=
  (rfl)

/-- The reals are dense in `EReal`. -/
theorem dense_range_coe_ereal : Dense (range ((↑) : ℝ → EReal)) := by
  refine dense_iff_inter_open.2 fun U hU ⟨x, hx⟩ ↦ ?_
  induction x using EReal.rec with
  | bot =>
    obtain ⟨y, hy⟩ := EReal.mem_nhds_bot_iff.1 (hU.mem_nhds hx)
    exact ⟨_, hy (EReal.coe_lt_coe_iff.2 (sub_one_lt y)), _, rfl⟩
  | coe x => exact ⟨_, hx, _, rfl⟩
  | top =>
    obtain ⟨y, hy⟩ := EReal.mem_nhds_top_iff.1 (hU.mem_nhds hx)
    exact ⟨_, hy (EReal.coe_lt_coe_iff.2 (lt_add_one y)), _, rfl⟩

/-- **Check.** The translation flow on `EReal` is topologically transitive: the orbit of `0` is
the dense set of reals. -/
theorem isTopologicallyTransitive_erealTranslationFlow :
    erealTranslationFlow.IsTopologicallyTransitive := by
  refine Flow.isTopologicallyTransitive_of_dense_orbit (x := 0) ?_
  convert dense_range_coe_ereal using 1
  ext y
  simp [Flow.orbit_eq_range]

/-- The forward orbit of `x` under the translation flow on `EReal` lies in `[x, ⊤]`. -/
theorem forwardOrbit_erealTranslationFlow_subset (x : EReal) :
    erealTranslationFlow.forwardOrbit x ⊆ Ici x := by
  rintro _ ⟨⟨t, ht⟩, rfl⟩
  exact le_add_of_nonneg_right (EReal.coe_nonneg.2 ht)

/-- **Check.** No forward orbit of the translation flow on `EReal` is dense, although `EReal` is a
compact metrizable space without isolated points and the flow is topologically transitive. -/
theorem not_dense_forwardOrbit_erealTranslationFlow (x : EReal) :
    ¬ Dense (erealTranslationFlow.forwardOrbit x) := by
  intro h
  have hx : Ici x = univ :=
    (h.mono (forwardOrbit_erealTranslationFlow_subset x)).closure_eq.symm.trans
      isClosed_Ici.closure_eq |>.symm
  obtain rfl : x = ⊥ := le_bot_iff.1 (hx ▸ mem_univ ⊥ : ⊥ ∈ Ici x)
  have hsub : erealTranslationFlow.forwardOrbit ⊥ ⊆ {⊥} := by
    rintro _ ⟨⟨t, -⟩, rfl⟩
    exact EReal.bot_add (t : EReal)
  have := (h.mono hsub).closure_eq
  rw [closure_singleton] at this
  exact bot_ne_top ((this ▸ mem_univ ⊤ : ⊤ ∈ ({⊥} : Set EReal))).symm

example : CompactSpace EReal := inferInstance

example : TopologicalSpace.MetrizableSpace EReal := inferInstance

example (x : EReal) : (𝓝[≠] x).NeBot := inferInstance

end TauCeti.Examples.FlowTransitive
