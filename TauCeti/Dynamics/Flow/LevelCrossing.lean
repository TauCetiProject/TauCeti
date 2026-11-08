/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Flow.ConnectingOrbit
public import TauCeti.Dynamics.Flow.TimeSlice
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Level slices of connecting orbits

Let `φ` be a real flow on a topological space `X` and `f : X → ℝ` a function that is continuous
on the connecting set `C = Wᵘ(p) ∩ Wˢ(q)` and strictly decreasing along every orbit in `C`, as a
Morse function is along the trajectories of its negative gradient or of an adapted
pseudo-gradient. If every orbit of `C` meets the level `{f = c}`, it meets it exactly once, at the
time `Flow.levelCrossingTime φ f c x`, and this time depends continuously on the point of `C`.
When `f` is continuous along the orbits and at `p` and `q`, every level strictly between `f q`
and `f p` is met (`Flow.exists_apply_flow_eq_of_mem_unstableSet_inter_stableSet`).

The crossing time is a global time coordinate on `C`, so:

* `C` is the product of `ℝ` with the level slice `C ∩ {f = c}`, the flow acting by translation
  of the first factor (`Flow.connectingHomeomorphProdLevelSlice`);
* the action of time translation on `C` is proper (`Flow.isProperMap_restrict_pair`);
* the space of unparametrized connecting orbits, the quotient of `C` by time translation, is
  homeomorphic to the level slice (`Flow.orbitQuotientHomeomorphLevelSlice`);
* the level slices at two such levels are homeomorphic by following the flow
  (`Flow.levelSliceHomeomorph`).

These are the topological statements behind the spaces of unparametrized Morse trajectories:
their quotient topology is the topology of any intermediate level slice, independently of the
level. They use neither smoothness nor transversality.

## Main definitions

* `Flow.levelCrossingTime`: the time at which an orbit meets a level.
* `Flow.connectingHomeomorphProdLevelSlice`: `C ≃ₜ ℝ × (C ∩ {f = c})`.
* `Flow.orbitQuotientHomeomorphLevelSlice`: the orbit quotient of `C` is homeomorphic to
  `C ∩ {f = c}`.
* `Flow.levelSliceHomeomorph`: `C ∩ {f = c} ≃ₜ C ∩ {f = c'}`.

## Main results

* `Flow.continuousOn_levelCrossingTime`: the crossing time is continuous on `C`.
* `Flow.levelCrossingTime_flow`: flowing for time `t` subtracts `t` from the crossing time.
* `Flow.isProperMap_restrict_pair`: time translation on `C` is a proper action.
* `Flow.bijOn_flow_levelCrossingTime`: following the flow is a bijection between two level slices.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2 (connecting trajectories modulo time translation, represented on a level).
-/

public section

open Filter Set Topology

noncomputable section

namespace Flow

variable {X : Type*} [TopologicalSpace X] {φ : _root_.Flow ℝ X} {f : X → ℝ} {p q x : X}
  {c c' : ℝ}

/-- A connecting orbit along which `f` is continuous, with `f` continuous at the two ends, meets
every level strictly between `f q` and `f p`. -/
theorem exists_apply_flow_eq_of_mem_unstableSet_inter_stableSet
    (hf : Continuous fun t ↦ f (φ t x)) (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hx : x ∈ unstableSet φ p ∩ stableSet φ q) (hc : f q < c ∧ c < f p) :
    ∃ t : ℝ, f (φ t x) = c :=
  mem_range_of_exists_le_of_exists_ge hf
    (((hfq.tendsto.comp (mem_stableSet.mp hx.2)).eventually
      (eventually_lt_nhds hc.1)).exists.imp fun _ h ↦ h.le)
    (((hfp.tendsto.comp (mem_unstableSet.mp hx.1)).eventually
      (eventually_gt_nhds hc.2)).exists.imp fun _ h ↦ h.le)

/-- A connecting orbit along which `f` is continuous and strictly decreasing, with `f` continuous
at the two ends, crosses every value strictly between `f q` and `f p` at exactly one time. -/
theorem existsUnique_apply_flow_eq_of_mem_unstableSet_inter_stableSet
    (hf : Continuous fun t ↦ f (φ t x)) (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
    (hanti : StrictAnti fun t ↦ f (φ t x)) (hx : x ∈ unstableSet φ p ∩ stableSet φ q)
    (hc : f q < c ∧ c < f p) :
    ∃! t : ℝ, f (φ t x) = c := by
  obtain ⟨t, ht⟩ := exists_apply_flow_eq_of_mem_unstableSet_inter_stableSet hf hfp hfq hx hc
  exact ⟨t, ht, fun s hs ↦ hanti.injective (hs.trans ht.symm)⟩

/-- The time at which the orbit of `x` meets the level `c` of `f`, or `0` if it never does. When
`f` is strictly decreasing along the orbit, this time is the unique one
(`Flow.eq_levelCrossingTime_iff`). -/
def levelCrossingTime (φ : _root_.Flow ℝ X) (f : X → ℝ) (c : ℝ) (x : X) : ℝ :=
  open Classical in if h : ∃ t, f (φ t x) = c then h.choose else 0

/-- At the crossing time the orbit lies on the level. -/
theorem apply_flow_levelCrossingTime (h : ∃ t, f (φ t x) = c) :
    f (φ (levelCrossingTime φ f c x) x) = c := by
  have ht : levelCrossingTime φ f c x = h.choose := by simp [levelCrossingTime, h]
  exact ht ▸ h.choose_spec

/-- If the orbit never meets the level, the crossing time is `0` by convention. -/
theorem levelCrossingTime_of_forall_ne (h : ∀ t, f (φ t x) ≠ c) : levelCrossingTime φ f c x = 0 :=
  by simp [levelCrossingTime, h]

/-- Along an orbit on which `f` is strictly decreasing, the crossing time is the only time at which
the orbit lies on the level. -/
theorem eq_levelCrossingTime_iff (hanti : StrictAnti fun t ↦ f (φ t x))
    (h : ∃ t, f (φ t x) = c) {t : ℝ} :
    t = levelCrossingTime φ f c x ↔ f (φ t x) = c := by
  refine ⟨?_, fun ht ↦ hanti.injective (ht.trans (apply_flow_levelCrossingTime h).symm)⟩
  rintro rfl
  exact apply_flow_levelCrossingTime h

/-- A point lies on the level exactly when its crossing time is zero. -/
@[simp]
theorem levelCrossingTime_eq_zero_iff (hanti : StrictAnti fun t ↦ f (φ t x))
    (h : ∃ t, f (φ t x) = c) :
    levelCrossingTime φ f c x = 0 ↔ f x = c := by
  rw [eq_comm, eq_levelCrossingTime_iff hanti h, φ.map_zero_apply]

/-- Flowing a point for time `t` subtracts `t` from its crossing time. -/
@[simp]
theorem levelCrossingTime_flow (hanti : StrictAnti fun t ↦ f (φ t x))
    (h : ∃ t, f (φ t x) = c) (t : ℝ) :
    levelCrossingTime φ f c (φ t x) = levelCrossingTime φ f c x - t := by
  obtain ⟨s, hs⟩ := h
  have h' : ∃ s, f (φ s (φ t x)) = c := ⟨s - t, by rwa [← φ.map_add, sub_add_cancel]⟩
  have hanti' : StrictAnti fun s ↦ f (φ s (φ t x)) := fun a b hab ↦ by
    simpa only [← φ.map_add] using hanti (add_lt_add_left hab t)
  refine ((eq_levelCrossingTime_iff hanti' h').2 ?_).symm
  rw [← φ.map_add, sub_add_cancel]
  exact apply_flow_levelCrossingTime ⟨s, hs⟩

section Connecting

variable (hf : ContinuousOn f (unstableSet φ p ∩ stableSet φ q))
  (hanti : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, StrictAnti fun t ↦ f (φ t x))
  (hex : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, ∃ t, f (φ t x) = c)

include hf hanti hex in
/-- **The crossing time is continuous** on the connecting set. -/
theorem continuousOn_levelCrossingTime :
    ContinuousOn (levelCrossingTime φ f c) (unstableSet φ p ∩ stableSet φ q) := by
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_continuousAt]
  intro x
  have hvalue (u : ℝ) : Continuous fun y : ↥(unstableSet φ p ∩ stableSet φ q) ↦ f (φ u y.1) :=
    hf.comp_continuous (φ.continuous continuous_const continuous_subtype_val)
      fun y ↦ isInvariant_unstableSet_inter_stableSet φ p q u y.2
  have ht (y : ↥(unstableSet φ p ∩ stableSet φ q)) :
      f (φ (levelCrossingTime φ f c y) y.1) = c :=
    apply_flow_levelCrossingTime (hex y y.2)
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- Before the crossing time of `x` the orbit is above the level, and so are nearby orbits.
    have hval : c < f (φ a x.1) := ht x ▸ hanti x x.2 ha
    filter_upwards [(hvalue a).continuousAt.eventually (eventually_gt_nhds hval)] with y hy
    by_contra hle
    exact (hanti y y.2).antitone (not_lt.1 hle) |>.trans_eq (ht y) |>.not_gt hy
  · have hval : f (φ b x.1) < c := ht x ▸ hanti x x.2 hb
    filter_upwards [(hvalue b).continuousAt.eventually (eventually_lt_nhds hval)] with y hy
    by_contra hle
    exact (ht y).symm.trans_le ((hanti y y.2).antitone (not_lt.1 hle)) |>.not_gt hy

/-- The negative crossing time, a time coordinate on the connecting set. -/
private def connectingTimeCoord (φ : _root_.Flow ℝ X) (f : X → ℝ) (p q : X) (c : ℝ)
    (x : ↥(unstableSet φ p ∩ stableSet φ q)) : ℝ :=
  -levelCrossingTime φ f c x

/- Not a `rfl` lemma, so that `simp` does not unfold `connectingTimeCoord` inside the dependent
arguments of `Flow.timeSliceHomeomorph`, which would block its projection lemmas. -/
private theorem connectingTimeCoord_apply (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    connectingTimeCoord φ f p q c x = -levelCrossingTime φ f c x := by
  rw [connectingTimeCoord]

include hf hanti hex in
private theorem continuous_connectingTimeCoord : Continuous (connectingTimeCoord φ f p q c) :=
  (continuousOn_iff_continuous_domRestrict.1 (continuousOn_levelCrossingTime hf hanti hex)).neg

include hanti hex in
private theorem connectingTimeCoord_flow (t : ℝ) (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    connectingTimeCoord φ f p q c
        ((φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)) t x) =
      t + connectingTimeCoord φ f p q c x := by
  simp only [connectingTimeCoord, coe_restrict_apply,
    levelCrossingTime_flow (hanti _ x.2) (hex _ x.2)]
  ring

/-- Identify the zero fibre of the negative crossing time with the level slice. -/
private def zeroCrossingTimeHomeomorphLevelSlice :
    {x : ↥(unstableSet φ p ∩ stableSet φ q) | connectingTimeCoord φ f p q c x = 0} ≃ₜ
      ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) where
  toFun x := ⟨x.1.1, x.1.2,
    (levelCrossingTime_eq_zero_iff (hanti _ x.1.2) (hex _ x.1.2)).1 (neg_eq_zero.1 x.2)⟩
  invFun x := ⟨⟨x.1, x.2.1⟩,
    neg_eq_zero.2 ((levelCrossingTime_eq_zero_iff (hanti _ x.2.1) (hex _ x.2.1)).2 x.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem coe_zeroCrossingTimeHomeomorphLevelSlice
    (x : {x : ↥(unstableSet φ p ∩ stableSet φ q) | connectingTimeCoord φ f p q c x = 0}) :
    (zeroCrossingTimeHomeomorphLevelSlice hanti hex x : X) = x.1.1 :=
  rfl

/-- **The connecting set is the product of time with a level slice.** The first coordinate is the
negative crossing time, and the inverse flows a point of the slice for the given time. -/
def connectingHomeomorphProdLevelSlice :
    ↥(unstableSet φ p ∩ stableSet φ q) ≃ₜ
      ℝ × ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) :=
  ((φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)).timeSliceHomeomorph
    (connectingTimeCoord φ f p q c) (continuous_connectingTimeCoord hf hanti hex)
    (connectingTimeCoord_flow hanti hex)).trans
    ((Homeomorph.refl ℝ).prodCongr (zeroCrossingTimeHomeomorphLevelSlice hanti hex))

@[simp]
theorem connectingHomeomorphProdLevelSlice_fst (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    (connectingHomeomorphProdLevelSlice hf hanti hex x).1 = -levelCrossingTime φ f c x := by
  simp [connectingHomeomorphProdLevelSlice, Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
    connectingTimeCoord_apply]

@[simp]
theorem connectingHomeomorphProdLevelSlice_snd_coe (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    ((connectingHomeomorphProdLevelSlice hf hanti hex x).2 : X) =
      φ (levelCrossingTime φ f c x) x := by
  simp [connectingHomeomorphProdLevelSlice, Homeomorph.trans_apply, Homeomorph.coe_prodCongr,
    coe_zeroCrossingTimeHomeomorphLevelSlice, connectingTimeCoord_apply]

@[simp]
theorem connectingHomeomorphProdLevelSlice_symm_apply
    (tx : ℝ × ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
    ((connectingHomeomorphProdLevelSlice hf hanti hex).symm tx : X) = φ tx.1 tx.2.1 := by
  simp [connectingHomeomorphProdLevelSlice, zeroCrossingTimeHomeomorphLevelSlice]

/-- In product coordinates time translation changes only the real coordinate. -/
@[simp]
theorem connectingHomeomorphProdLevelSlice_flow (t : ℝ)
    (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    connectingHomeomorphProdLevelSlice hf hanti hex
        ((φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)) t x) =
      (t + (connectingHomeomorphProdLevelSlice hf hanti hex x).1,
        (connectingHomeomorphProdLevelSlice hf hanti hex x).2) := by
  have h := levelCrossingTime_flow (hanti _ x.2) (hex _ x.2) t
  refine Prod.ext ?_ (Subtype.ext ?_)
  · simp only [connectingHomeomorphProdLevelSlice_fst, coe_restrict_apply, h]
    ring
  · simp only [connectingHomeomorphProdLevelSlice_snd_coe, coe_restrict_apply, h, ← φ.map_add,
      sub_add_cancel]

include hf hanti hex in
/-- **Time translation on the connecting set is proper.** This is properness of the action map
`(t, x) ↦ (φ t x, x)` for the subspace topology of `Wᵘ(p) ∩ Wˢ(q)`, not properness of an
individual trajectory in `X`. -/
theorem isProperMap_restrict_pair [T2Space X] :
    IsProperMap fun tx : ℝ × ↥(unstableSet φ p ∩ stableSet φ q) ↦
      ((φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)) tx.1 tx.2, tx.2) :=
  isProperMap_flow_pair_of_timeCoordinate _ _ (continuous_connectingTimeCoord hf hanti hex)
    (connectingTimeCoord_flow hanti hex)

include hf hanti hex in
private theorem exists_homeomorph_levelSlice :
    ∃ e : Quotient (connectingOrbitSetoid φ p q) ≃ₜ
        ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}),
      ∀ x, e.symm x = Quotient.mk _ ⟨x.1, x.2.1⟩ := by
  let i : C(↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}),
      ↥(unstableSet φ p ∩ stableSet φ q)) :=
    ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩
  -- The retraction onto the slice is the second coordinate of the product homeomorphism.
  let s : C(↥(unstableSet φ p ∩ stableSet φ q),
      ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :=
    ⟨fun x ↦ (connectingHomeomorphProdLevelSlice hf hanti hex x).2,
      continuous_snd.comp (connectingHomeomorphProdLevelSlice hf hanti hex).continuous⟩
  have hs (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
      (s x : X) = φ (levelCrossingTime φ f c x) x :=
    connectingHomeomorphProdLevelSlice_snd_coe hf hanti hex x
  have hzero (x : ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
      levelCrossingTime φ f c (i x) = 0 :=
    (levelCrossingTime_eq_zero_iff (hanti _ x.2.1) (hex _ x.2.1)).2 x.2.2
  have hright : Function.RightInverse i s := fun x ↦ Subtype.ext <| by
    rw [hs, hzero, φ.map_zero_apply]
    rfl
  have hrel (x y : ↥(unstableSet φ p ∩ stableSet φ q)) :
      connectingOrbitSetoid φ p q x y ↔ Setoid.ker s x y := by
    rw [Setoid.ker_def, connectingOrbitSetoid_apply, ← Subtype.coe_inj, hs, hs]
    constructor
    · rintro ⟨t, ht⟩
      have hxy : x = (φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)) t y :=
        Subtype.ext ht.symm
      rw [hxy, coe_restrict_apply, levelCrossingTime_flow (hanti _ y.2) (hex _ y.2), ← φ.map_add,
        sub_add_cancel]
    · intro h
      refine ⟨levelCrossingTime φ f c y - levelCrossingTime φ f c x, ?_⟩
      rw [sub_eq_neg_add, φ.map_add, ← h, ← φ.map_add, neg_add_cancel, φ.map_zero_apply]
  refine ⟨(Homeomorph.Quotient.congrRight hrel).trans hright.homeomorph, fun x ↦ ?_⟩
  -- The inverse of `Function.RightInverse.homeomorph` is `Quotient.mk` composed with `i`, and the
  -- inverse of `Homeomorph.Quotient.congrRight` preserves representatives.
  rfl

/-- **Unparametrized connecting orbits are a level slice.** The quotient of the connecting set by
time translation is homeomorphic to the level slice; the inverse sends a point of the slice to its
orbit class. -/
def orbitQuotientHomeomorphLevelSlice :
    Quotient (connectingOrbitSetoid φ p q) ≃ₜ
      ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) :=
  Classical.choose (exists_homeomorph_levelSlice hf hanti hex)

/-- The inverse sends a point of the slice to its connecting orbit class. -/
@[simp]
theorem orbitQuotientHomeomorphLevelSlice_symm_apply
    (x : ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
    (orbitQuotientHomeomorphLevelSlice hf hanti hex).symm x = Quotient.mk _ ⟨x.1, x.2.1⟩ :=
  Classical.choose_spec (exists_homeomorph_levelSlice hf hanti hex) x

/-- The image of a connecting orbit class is the point of that orbit on the slice. -/
theorem orbitQuotientHomeomorphLevelSlice_mk_eq_iff (x : ↥(unstableSet φ p ∩ stableSet φ q))
    (y : ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
    orbitQuotientHomeomorphLevelSlice hf hanti hex (Quotient.mk _ x) = y ↔
      ∃ t : ℝ, φ t y.1 = x.1 := by
  rw [← Homeomorph.eq_symm_apply, orbitQuotientHomeomorphLevelSlice_symm_apply, Quotient.eq]
  exact connectingOrbitSetoid_apply _ _

/-- The image of a connecting orbit class is the point of the orbit at its crossing time. -/
@[simp]
theorem coe_orbitQuotientHomeomorphLevelSlice_mk (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    (orbitQuotientHomeomorphLevelSlice hf hanti hex (Quotient.mk _ x) : X) =
      φ (levelCrossingTime φ f c x) x := by
  have hy : φ (levelCrossingTime φ f c x) x.1 ∈ (unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c} :=
    ⟨isInvariant_unstableSet_inter_stableSet φ p q _ x.2, apply_flow_levelCrossingTime (hex x x.2)⟩
  rw [(orbitQuotientHomeomorphLevelSlice_mk_eq_iff hf hanti hex x ⟨_, hy⟩).2
    ⟨-levelCrossingTime φ f c x, by rw [← φ.map_add, neg_add_cancel, φ.map_zero_apply]⟩]

/-- **Level slices do not depend on the level.** Two level slices of the connecting set, each met
by every connecting orbit, are homeomorphic by following the flow: a point of the first slice is
sent to the point of its orbit on the second. -/
def levelSliceHomeomorph (hex' : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, ∃ t, f (φ t x) = c') :
    ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) ≃ₜ
      ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c'}) :=
  (orbitQuotientHomeomorphLevelSlice hf hanti hex).symm.trans
    (orbitQuotientHomeomorphLevelSlice hf hanti hex')

@[simp]
theorem coe_levelSliceHomeomorph
    (hex' : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, ∃ t, f (φ t x) = c')
    (x : ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
    (levelSliceHomeomorph hf hanti hex hex' x : X) = φ (levelCrossingTime φ f c' x) x := by
  simp [levelSliceHomeomorph]

/-- Following the flow back from the second slice to the first inverts `Flow.levelSliceHomeomorph`.
-/
@[simp]
theorem levelSliceHomeomorph_symm
    (hex' : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, ∃ t, f (φ t x) = c') :
    (levelSliceHomeomorph hf hanti hex hex').symm = levelSliceHomeomorph hf hanti hex' hex := by
  ext x
  simp only [levelSliceHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    Homeomorph.trans_apply]

include hf hanti hex in
/-- **Following the flow is a bijection between level slices.** Sending a point of the slice
`C ∩ {f = c}` to the point of its orbit on the level `c'` is a bijection onto `C ∩ {f = c'}`;
this is `Flow.levelSliceHomeomorph` read on the underlying sets. -/
theorem bijOn_flow_levelCrossingTime
    (hex' : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, ∃ t, f (φ t x) = c') :
    BijOn (fun x ↦ φ (levelCrossingTime φ f c' x) x)
      ((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})
      ((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c'}) := by
  set e := levelSliceHomeomorph hf hanti hex hex'
  have he (x) : (e x : X) = φ (levelCrossingTime φ f c' x) x := coe_levelSliceHomeomorph ..
  refine ⟨fun x hx ↦ ?_, fun x hx x' hx' h ↦ ?_, fun y hy ↦ ?_⟩
  · simpa only [he] using (e ⟨x, hx⟩).2
  · exact congrArg Subtype.val (e.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨x', hx'⟩)
      (Subtype.ext (by simpa only [he] using h)))
  · exact ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).2,
      by simpa only [he] using congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)⟩

end Connecting

end Flow
