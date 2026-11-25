/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.PolygonalTable
public import TauCeti.Dynamics.Billiard.SideReflection
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The phase space of a polygonal billiard table

A state of the billiard in a polygonal table `P` is a position `x ∈ P` and a unit direction
`v ∈ Circle`. At a point `x` of the relative interior of a side `S` with unit direction `d`, the
incoming and the reflected directions describe the same state: the *phase space*
`Z_P = (P × Circle)/∼` (`TauCeti.PolygonalTable.PhaseSpace`) identifies `(x, v)` with
`(x, σ_S v)`, where `σ_S v = d² v̄` is the reflection of directions in `S`
(`TauCeti.Billiard.directionReflection`). It carries the quotient topology and the quotient
σ-algebra.

* `TauCeti.PolygonalTable.Side.direction`: the unit direction of a side.
* `TauCeti.PolygonalTable.PhaseRel`, `TauCeti.PolygonalTable.phaseSetoid`: the identification,
  an equivalence relation because the relative interiors of distinct sides are disjoint and each
  `σ_S` is an involution.
* `TauCeti.PolygonalTable.encard_setOf_mk_eq_le_two`: every class has at most two points.
* `TauCeti.PolygonalTable.PhaseSpace.flip`: the time reversal `J(x, v) = (x, -v)` descends to
  the phase space, because `σ_S (-v) = -σ_S v`; it is a continuous involution.
* `TauCeti.PolygonalTable.liouville`: the Liouville probability measure `μ_P`, the image of
  `(2π area P)⁻¹ Leb_P ⊗ dθ` (`TauCeti.circleArcLength`).

## References

* N. Chernov, R. Markarian, *Chaotic Billiards*, Mathematical Surveys and Monographs 127, AMS
  (2006), Chapter 2.
* C. Boldrighini, M. Keane, F. Marchetti, *Billiards in polygons*, Ann. Probab. 6 (1978),
  Section 2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Real

namespace TauCeti

namespace PolygonalTable

variable {T : PolygonalTable}

/-- The unit direction `exp(i arg(b − a))` of a side from its start `a` to its finish `b`. -/
def Side.direction (s : T.Side) : Circle :=
  Circle.exp (Complex.arg (s.finish - s.start))

theorem Side.direction_def (s : T.Side) :
    s.direction = Circle.exp (Complex.arg (s.finish - s.start)) :=
  (rfl)

variable (T)

/-- The identification of states of a polygonal table: `(x, v)` and `(y, w)` are identified when
they are equal, or when `x = y` lies in the relative interior of a side `S` and `w = σ_S v`. -/
def PhaseRel (p q : T.carrier × Circle) : Prop :=
  p = q ∨ (p.1 = q.1 ∧ ∃ s : T.Side, (p.1 : ℂ) ∈ T.sideInterior s ∧
    q.2 = Billiard.directionReflection s.direction p.2)

variable {T}

/-- A point lies in the relative interior of at most one side. -/
private theorem eq_of_mem_sideInterior {x : ℂ} {s t : T.Side} (hs : x ∈ T.sideInterior s)
    (ht : x ∈ T.sideInterior t) : s = t :=
  by_contra fun hst => Set.disjoint_left.1 (T.disjoint_sideInterior hst) hs ht

theorem PhaseRel.symm {p q : T.carrier × Circle} (h : T.PhaseRel p q) : T.PhaseRel q p := by
  rcases h with rfl | ⟨h₁, s, hs, h₂⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨h₁.symm, s, h₁ ▸ hs, ?_⟩
    rw [h₂, Billiard.directionReflection_directionReflection]

theorem PhaseRel.trans {p q r : T.carrier × Circle} (hpq : T.PhaseRel p q)
    (hqr : T.PhaseRel q r) : T.PhaseRel p r := by
  rcases hpq with rfl | ⟨h₁, s, hs, h₂⟩
  · exact hqr
  rcases hqr with rfl | ⟨h₁', s', hs', h₂'⟩
  · exact Or.inr ⟨h₁, s, hs, h₂⟩
  obtain rfl := eq_of_mem_sideInterior hs (h₁ ▸ hs')
  refine Or.inl (Prod.ext (h₁.trans h₁') ?_)
  rw [h₂', h₂, Billiard.directionReflection_directionReflection]

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

theorem PhaseSpace.surjective_mk : Function.Surjective (PhaseSpace.mk (T := T)) :=
  Quotient.mk_surjective

theorem PhaseSpace.continuous_mk : Continuous (PhaseSpace.mk (T := T)) :=
  continuous_quotient_mk'

theorem PhaseSpace.measurable_mk : Measurable (PhaseSpace.mk (T := T)) :=
  measurable_quotient_mk' (s := T.phaseSetoid)

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
        {p, (p.1, Billiard.directionReflection s.direction p.2)} := by
      intro q hq
      rcases PhaseSpace.mk_eq_mk.1 hq with rfl | ⟨h₁, t, ht, h₂⟩
      · exact Or.inl rfl
      · obtain rfl := eq_of_mem_sideInterior hs (h₁ ▸ ht)
        refine Or.inr (Prod.ext h₁ ?_)
        rw [h₂, Billiard.directionReflection_directionReflection]
    exact (encard_le_encard hsub).trans ((encard_insert_le _ _).trans (by norm_num))
  · have hsub : {q | PhaseSpace.mk q = PhaseSpace.mk p} ⊆ {p} := by
      intro q hq
      rcases PhaseSpace.mk_eq_mk.1 hq with rfl | ⟨h₁, t, ht, -⟩
      · rfl
      · exact (hp ⟨t, h₁ ▸ ht⟩).elim
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
  rfl

/-- Time reversal is an involution. -/
theorem PhaseSpace.flip_involutive : Function.Involutive (PhaseSpace.flip (T := T)) := by
  intro z
  obtain ⟨p, rfl⟩ := PhaseSpace.surjective_mk z
  simp

/-- Time reversal is continuous. -/
theorem PhaseSpace.continuous_flip : Continuous (PhaseSpace.flip (T := T)) :=
  Continuous.quotient_map' (continuous_fst.prodMk continuous_snd.neg) fun _ _ => PhaseRel.neg

variable (T)

/-- **The Liouville probability measure** `μ_P` on the phase space: the image of the normalised
product `(2π area P)⁻¹ Leb_P ⊗ dθ` of the area measure on the table and the arclength measure on
directions. -/
def liouville : Measure T.PhaseSpace :=
  ((ENNReal.ofReal (2 * π) * volume T.carrier)⁻¹ •
    ((volume.comap ((↑) : T.carrier → ℂ)).prod circleArcLength)).map PhaseSpace.mk

/-- The area of a polygonal table is positive and finite. -/
theorem volume_carrier_pos : 0 < volume T.carrier :=
  (measure_mono interior_subset).trans_lt' <|
    isOpen_interior.measure_pos _ T.isConnected_interior.nonempty

theorem volume_carrier_lt_top : volume T.carrier < ∞ :=
  T.isCompact_carrier.measure_lt_top

instance : IsProbabilityMeasure T.liouville := by
  constructor
  rw [liouville, Measure.map_apply PhaseSpace.measurable_mk MeasurableSet.univ, preimage_univ,
    smul_apply, ← univ_prod_univ, Measure.prod_prod,
    comap_subtypeVal_apply T.isCompact_carrier.isClosed.measurableSet, image_univ,
    Subtype.range_coe, circleArcLength_univ, smul_eq_mul, mul_comm (volume T.carrier)]
  exact ENNReal.inv_mul_cancel
    (mul_ne_zero (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne' T.volume_carrier_pos.ne')
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top T.volume_carrier_lt_top.ne)

end PolygonalTable

end TauCeti
