/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PolygonalTable
public import TauCeti.Dynamics.Billiard.SideReflection
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Dynamics.Billiard.PolygonalTable.Frontier

/-!
# The phase space of a polygonal billiard table

A state of the billiard in a polygonal table `P` is a position `x ∈ P` and a unit direction
`v ∈ Circle`. At a point `x` of the relative interior of a side `S` with unit direction `d`
(`TauCeti.PolygonalTable.Side.direction`), the incoming and the reflected directions describe the
same state: the *phase space* `Z_P = (P × Circle)/∼` (`TauCeti.PolygonalTable.PhaseSpace`)
identifies `(x, v)` with `(x, σ_S v)`, where `σ_S v = d² conj v` is the reflection of directions
in `S` (`TauCeti.Billiard.directionReflection`). It carries the quotient topology and the
quotient σ-algebra.

* `TauCeti.PolygonalTable.PhaseRel`, `TauCeti.PolygonalTable.phaseSetoid`: the identification,
  an equivalence relation because the relative interiors of distinct sides are disjoint and each
  `σ_S` is an involution.
* `TauCeti.PolygonalTable.PhaseSpace.lift`, `TauCeti.PolygonalTable.PhaseSpace.ind`: maps out of
  the phase space and induction on it.
* `TauCeti.PolygonalTable.encard_setOf_mk_eq_le_two`: every class has at most two points.
* `TauCeti.PolygonalTable.PhaseSpace.flip`: the time reversal `J(x, v) = (x, -v)` descends to
  the phase space, because `σ_S (-v) = -σ_S v`; it is a continuous and measurable involution.
* `TauCeti.PolygonalTable.PhaseSpace.position`: the position of a state, well defined because
  identified states have the same position.
* `TauCeti.PolygonalTable.liouville`: the Liouville probability measure `μ_P`, the image of
  `(2π area P)⁻¹ Leb_P ⊗ dθ` (`TauCeti.circleArcLength`).
* `TauCeti.PolygonalTable.liouville_setOf_position_mem_eq_zero`: the states whose position lies
  in a Lebesgue-null set form a `μ_P`-null set.
* `TauCeti.PolygonalTable.liouville_setOf_position_mem_frontier_eq_zero`: the states whose
  position lies on the frontier of the table form a `μ_P`-null set, since the frontier is
  Lebesgue-null (`TauCeti.PolygonalTable.volume_frontier_carrier`).

## References

* N. Chernov, R. Markarian, *Chaotic Billiards*, Mathematical Surveys and Monographs 127, AMS
  (2006), Chapter 2.
* C. Boldrighini, M. Keane, F. Marchetti, *Billiards in polygons*, Ann. Probab. 6 (1978),
  Section 2.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real

namespace TauCeti

namespace PolygonalTable

variable (T : PolygonalTable)

/-- The identification of states of a polygonal table: `(x, v)` and `(y, w)` are identified when
they are equal, or when `x = y` lies in the relative interior of a side `S` and `w = σ_S v`. -/
def PhaseRel (p q : T.carrier × Circle) : Prop :=
  p = q ∨ (p.1 = q.1 ∧ ∃ s : T.Side, (p.1 : ℂ) ∈ T.sideInterior s ∧
    q.2 = Billiard.directionReflection s.direction p.2)

variable {T}

theorem phaseRel_iff {p q : T.carrier × Circle} :
    T.PhaseRel p q ↔ p = q ∨ (p.1 = q.1 ∧ ∃ s : T.Side, (p.1 : ℂ) ∈ T.sideInterior s ∧
      q.2 = Billiard.directionReflection s.direction p.2) :=
  Iff.rfl

/-- At a point `x` of the relative interior of a side `S`, the state `(x, v)` is identified exactly
with itself and with `(x, σ_S v)`. -/
theorem phaseRel_iff_of_mem_sideInterior {p q : T.carrier × Circle} {s : T.Side}
    (hs : (p.1 : ℂ) ∈ T.sideInterior s) :
    T.PhaseRel p q ↔ q = p ∨ q = (p.1, Billiard.directionReflection s.direction p.2) := by
  constructor
  · rintro (rfl | ⟨h₁, t, ht, h₂⟩)
    · exact Or.inl rfl
    · obtain rfl := T.eq_of_mem_sideInterior hs ht
      exact Or.inr (Prod.ext h₁.symm h₂)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, s, hs, rfl⟩

/-- Off the relative interiors of the sides, a state is identified only with itself. -/
theorem phaseRel_iff_of_forall_notMem {p q : T.carrier × Circle}
    (hp : ∀ s : T.Side, (p.1 : ℂ) ∉ T.sideInterior s) : T.PhaseRel p q ↔ q = p := by
  constructor
  · rintro (rfl | ⟨-, s, hs, -⟩)
    · rfl
    · exact (hp s hs).elim
  · rintro rfl
    exact Or.inl rfl

theorem PhaseRel.symm {p q : T.carrier × Circle} (h : T.PhaseRel p q) : T.PhaseRel q p := by
  rcases h with rfl | ⟨h₁, s, hs, h₂⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨h₁.symm, s, h₁ ▸ hs, ?_⟩
    rw [h₂, Billiard.directionReflection_directionReflection]

theorem PhaseRel.trans {p q r : T.carrier × Circle} (hpq : T.PhaseRel p q)
    (hqr : T.PhaseRel q r) : T.PhaseRel p r := by
  rcases hpq with rfl | ⟨h₁, s, hs, h₂⟩
  · exact hqr
  obtain rfl : q = (p.1, Billiard.directionReflection s.direction p.2) := Prod.ext h₁.symm h₂
  rcases (phaseRel_iff_of_mem_sideInterior
    (p := (p.1, Billiard.directionReflection s.direction p.2)) hs).1 hqr with rfl | rfl
  · exact Or.inr ⟨rfl, s, hs, rfl⟩
  · exact Or.inl (by simp)

variable (T)

/-- The identification of states as a setoid. -/
def phaseSetoid : Setoid (T.carrier × Circle) where
  r := T.PhaseRel
  iseqv := ⟨fun _ => Or.inl rfl, PhaseRel.symm, PhaseRel.trans⟩

/-- **The phase space** `Z_P = (P × Circle)/∼` of a polygonal table, identifying `(x, v)` with
`(x, σ_S v)` at points `x` of the relative interior of a side `S`. -/
def PhaseSpace : Type := Quotient T.phaseSetoid

instance : TopologicalSpace T.PhaseSpace :=
  inferInstanceAs (TopologicalSpace (Quotient T.phaseSetoid))

instance : MeasurableSpace T.PhaseSpace :=
  inferInstanceAs (MeasurableSpace (Quotient T.phaseSetoid))

variable {T}

/-- The state of the phase space represented by a position and a direction. -/
def PhaseSpace.mk (p : T.carrier × Circle) : T.PhaseSpace :=
  Quotient.mk T.phaseSetoid p

theorem PhaseSpace.mk_eq_mk {p q : T.carrier × Circle} :
    PhaseSpace.mk p = PhaseSpace.mk q ↔ T.PhaseRel p q :=
  Quotient.eq

theorem PhaseSpace.mk_surjective : Function.Surjective (PhaseSpace.mk (T := T)) :=
  Quotient.mk_surjective

/-- Induction on the phase space: a property of all states represented by a position and a
direction holds for all states. -/
@[elab_as_elim]
theorem PhaseSpace.ind {motive : T.PhaseSpace → Prop} (h : ∀ p, motive (PhaseSpace.mk p))
    (z : T.PhaseSpace) : motive z :=
  Quotient.ind h z

/-- A function of positions and directions that agrees on identified states descends to the phase
space. -/
def PhaseSpace.lift {β : Sort*} (f : T.carrier × Circle → β)
    (hf : ∀ p q, T.PhaseRel p q → f p = f q) : T.PhaseSpace → β :=
  Quotient.lift f hf

@[simp]
theorem PhaseSpace.lift_mk {β : Sort*} (f : T.carrier × Circle → β)
    (hf : ∀ p q, T.PhaseRel p q → f p = f q) (p : T.carrier × Circle) :
    PhaseSpace.lift f hf (PhaseSpace.mk p) = f p :=
  (rfl)

theorem PhaseSpace.continuous_mk : Continuous (PhaseSpace.mk (T := T)) :=
  continuous_quotient_mk'

theorem PhaseSpace.measurable_mk : Measurable (PhaseSpace.mk (T := T)) :=
  measurable_quotient_mk' (s := T.phaseSetoid)

theorem PhaseSpace.continuous_lift {X : Type*} [TopologicalSpace X] {f : T.carrier × Circle → X}
    {hf : ∀ p q, T.PhaseRel p q → f p = f q} (h : Continuous f) :
    Continuous (PhaseSpace.lift f hf) :=
  h.quotient_lift hf

theorem PhaseSpace.measurable_lift {X : Type*} [MeasurableSpace X] {f : T.carrier × Circle → X}
    {hf : ∀ p q, T.PhaseRel p q → f p = f q} (h : Measurable f) :
    Measurable (PhaseSpace.lift f hf) :=
  measurable_from_quotient.2 h

/-- At a point of the relative interior of a side `S`, the states `(x, v)` and `(x, σ_S v)`
agree. -/
theorem PhaseSpace.mk_directionReflection {x : T.carrier} {s : T.Side}
    (hx : (x : ℂ) ∈ T.sideInterior s) (v : Circle) :
    PhaseSpace.mk (x, Billiard.directionReflection s.direction v) = PhaseSpace.mk (x, v) :=
  PhaseSpace.mk_eq_mk.2
    (Or.inr ⟨rfl, s, hx, (Billiard.directionReflection_directionReflection _ _).symm⟩)

/-- **Every class of the phase space has at most two points.** -/
theorem encard_setOf_mk_eq_le_two (p : T.carrier × Circle) :
    {q | PhaseSpace.mk q = PhaseSpace.mk p}.encard ≤ 2 := by
  by_cases hp : ∃ s : T.Side, (p.1 : ℂ) ∈ T.sideInterior s
  · obtain ⟨s, hs⟩ := hp
    have hsub : {q | PhaseSpace.mk q = PhaseSpace.mk p} ⊆
        {p, (p.1, Billiard.directionReflection s.direction p.2)} := fun q hq =>
      (phaseRel_iff_of_mem_sideInterior hs).1 (PhaseSpace.mk_eq_mk.1 hq).symm
    exact (encard_le_encard hsub).trans ((encard_insert_le _ _).trans (by norm_num))
  · have hsub : {q | PhaseSpace.mk q = PhaseSpace.mk p} ⊆ {p} := fun q hq =>
      (phaseRel_iff_of_forall_notMem (not_exists.1 hp)).1 (PhaseSpace.mk_eq_mk.1 hq).symm
    exact (encard_le_encard hsub).trans (by simp)

/-- Time reversal `J(x, v) = (x, -v)` preserves the identification of states. -/
theorem PhaseRel.neg {p q : T.carrier × Circle} (h : T.PhaseRel p q) :
    T.PhaseRel (p.1, -p.2) (q.1, -q.2) := by
  rcases h with rfl | ⟨h₁, s, hs, h₂⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨h₁, s, hs, by rw [h₂, Billiard.directionReflection_apply_neg]⟩

/-- **Time reversal** `J(x, v) = (x, -v)` on the phase space. -/
def PhaseSpace.flip : T.PhaseSpace → T.PhaseSpace :=
  Quotient.map (fun p => (p.1, -p.2)) fun _ _ => PhaseRel.neg

@[simp]
theorem PhaseSpace.flip_mk (p : T.carrier × Circle) :
    PhaseSpace.flip (PhaseSpace.mk p) = PhaseSpace.mk (p.1, -p.2) :=
  (rfl)

@[simp]
theorem PhaseSpace.flip_flip (z : T.PhaseSpace) : PhaseSpace.flip (PhaseSpace.flip z) = z := by
  induction z using PhaseSpace.ind
  simp

/-- Time reversal is an involution. -/
theorem PhaseSpace.flip_involutive : Function.Involutive (PhaseSpace.flip (T := T)) :=
  PhaseSpace.flip_flip

/-- Time reversal is continuous. -/
theorem PhaseSpace.continuous_flip : Continuous (PhaseSpace.flip (T := T)) :=
  Continuous.quotient_map' (continuous_fst.prodMk continuous_snd.neg) fun _ _ => PhaseRel.neg

/-- Time reversal is measurable. -/
theorem PhaseSpace.measurable_flip : Measurable (PhaseSpace.flip (T := T)) :=
  measurable_from_quotient.2 <|
    PhaseSpace.measurable_mk.comp (continuous_fst.prodMk continuous_snd.neg).measurable

/-- The position of a state of the phase space: identified states have the same position. -/
def PhaseSpace.position : T.PhaseSpace → T.carrier :=
  PhaseSpace.lift Prod.fst fun _ _ h => by
    rcases h with rfl | ⟨h, -⟩
    · rfl
    · exact h

@[simp]
theorem PhaseSpace.position_mk (p : T.carrier × Circle) :
    PhaseSpace.position (PhaseSpace.mk p) = p.1 :=
  (rfl)

/-- Time reversal does not move the position of a state. -/
@[simp]
theorem PhaseSpace.position_flip (z : T.PhaseSpace) :
    PhaseSpace.position (PhaseSpace.flip z) = PhaseSpace.position z := by
  induction z using PhaseSpace.ind
  simp

theorem PhaseSpace.continuous_position : Continuous (PhaseSpace.position (T := T)) :=
  PhaseSpace.continuous_lift continuous_fst

theorem PhaseSpace.measurable_position : Measurable (PhaseSpace.position (T := T)) :=
  PhaseSpace.measurable_lift measurable_fst

variable (T)

/-- **The Liouville probability measure** `μ_P` on the phase space: the image of the normalised
product `(2π area P)⁻¹ Leb_P ⊗ dθ` of the area measure on the table and the arclength measure on
directions. -/
def liouville : Measure T.PhaseSpace :=
  ((ENNReal.ofReal (2 * π) * volume T.carrier)⁻¹ •
    ((volume.comap ((↑) : T.carrier → ℂ)).prod circleArcLength)).map PhaseSpace.mk

theorem liouville_def : T.liouville =
    ((ENNReal.ofReal (2 * π) * volume T.carrier)⁻¹ •
      ((volume.comap ((↑) : T.carrier → ℂ)).prod circleArcLength)).map PhaseSpace.mk :=
  (rfl)

theorem liouville_apply {s : Set T.PhaseSpace} (hs : MeasurableSet s) :
    T.liouville s = (ENNReal.ofReal (2 * π) * volume T.carrier)⁻¹ *
      (volume.comap ((↑) : T.carrier → ℂ)).prod circleArcLength (PhaseSpace.mk ⁻¹' s) := by
  rw [liouville_def, Measure.map_apply PhaseSpace.measurable_mk hs, smul_apply, smul_eq_mul]

/-- The product of the area measure on the table and the arclength measure on directions has total
mass `2π area P`. -/
theorem comap_volume_prod_circleArcLength_univ :
    (volume.comap ((↑) : T.carrier → ℂ)).prod circleArcLength univ =
      ENNReal.ofReal (2 * π) * volume T.carrier := by
  simp [← univ_prod_univ, Measure.prod_prod,
    comap_subtypeVal_apply T.isClosed_carrier.measurableSet, circleArcLength_univ, mul_comm]

/-- The area of a polygonal table is positive. -/
theorem volume_carrier_pos : 0 < volume T.carrier :=
  Measure.measure_pos_of_nonempty_interior _ T.nonempty_interior

/-- The area of a polygonal table is finite. -/
theorem volume_carrier_lt_top : volume T.carrier < ∞ :=
  T.isCompact_carrier.measure_lt_top

instance : IsProbabilityMeasure T.liouville := by
  constructor
  rw [liouville_apply T MeasurableSet.univ, preimage_univ, comap_volume_prod_circleArcLength_univ]
  exact ENNReal.inv_mul_cancel
    (mul_ne_zero (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne' T.volume_carrier_pos.ne')
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top T.volume_carrier_lt_top.ne)

/-- The states of the phase space whose position lies in a Lebesgue-null set of positions form a
`μ_P`-null set. -/
theorem liouville_setOf_position_mem_eq_zero {s : Set ℂ} (hs : volume s = 0) :
    T.liouville {z | (PhaseSpace.position z : ℂ) ∈ s} = 0 := by
  set t := toMeasurable volume s
  have ht : volume.comap ((↑) : T.carrier → ℂ) ((↑) ⁻¹' t) = 0 := by
    rw [comap_subtypeVal_apply T.isClosed_carrier.measurableSet]
    exact measure_mono_null (image_preimage_subset _ _) (by rwa [measure_toMeasurable])
  set F := {z : T.PhaseSpace | (PhaseSpace.position z : ℂ) ∈ t}
  have hm : MeasurableSet F :=
    (measurable_subtypeVal.comp PhaseSpace.measurable_position) (measurableSet_toMeasurable _ _)
  have hpre : PhaseSpace.mk ⁻¹' F = ((↑) ⁻¹' t : Set T.carrier) ×ˢ univ := by
    ext p
    simp [F]
  have hsub : {z : T.PhaseSpace | (PhaseSpace.position z : ℂ) ∈ s} ⊆ F := fun _ hz =>
    subset_toMeasurable volume s hz
  refine measure_mono_null hsub ?_
  rw [liouville_apply T hm, hpre, Measure.prod_prod, ht]
  simp

/-- **The frontier states are null**: the states of the phase space whose position lies on the
frontier of the table form a `μ_P`-null set, because the frontier is Lebesgue-null. -/
theorem liouville_setOf_position_mem_frontier_eq_zero :
    T.liouville {z | (PhaseSpace.position z : ℂ) ∈ frontier T.carrier} = 0 :=
  T.liouville_setOf_position_mem_eq_zero T.volume_frontier_carrier

end PolygonalTable

end TauCeti
