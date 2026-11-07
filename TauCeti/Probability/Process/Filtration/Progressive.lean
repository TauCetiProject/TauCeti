/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Predictable
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# The progressive sigma algebra

The progressive sigma algebra of a filtration is the sigma algebra on time × sample space
whose sets are measurable on every initial time interval using the information available at
that interval's endpoint. Measurability for this sigma algebra is equivalent to the native
`IsProgressive` predicate. This permits progressive processes to be treated as measurable
functions, for example when forming time-product almost-everywhere equivalence classes.

We prove monotonicity in the filtration, inclusion of the predictable sigma algebra, and
inclusion in the ambient product sigma algebra when countably many initial intervals cover
time. Restriction to a finite horizon is characterized by testing only earlier endpoints.
No measure, completion, or right continuity of the filtration is required.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §1.
-/

public section

open Set
open scoped NNReal

namespace MeasureTheory.Filtration

variable {ι Ω E : Type*} [MeasurableSpace ι] [m : MeasurableSpace Ω]

section Preorder

variable [Preorder ι]

/-- The sigma algebra of sets measurable on each initial time interval with the endpoint's
information. For nonnegative time, these initial intervals are `[0,t]`. -/
@[instance_reducible]
def progressive (F : Filtration ι m) : MeasurableSpace (ι × Ω) :=
  ⨅ t, MeasurableSpace.map (fun p : Iic t × Ω => ((p.1 : ι), p.2))
    (Subtype.instMeasurableSpace.prod (F t))

/-- A progressive set has measurable preimages on all initial time intervals. -/
@[simp]
theorem measurableSet_progressive_iff (F : Filtration ι m) {s : Set (ι × Ω)} :
    MeasurableSet[F.progressive] s ↔
      ∀ t, MeasurableSet[Subtype.instMeasurableSpace.prod (F t)]
        ((fun p : Iic t × Ω => ((p.1 : ι), p.2)) ⁻¹' s) := by
  simp only [MeasurableSpace.measurableSet_iInf, MeasurableSpace.map_def]

/-- Measurability for the progressive sigma algebra is precisely progressive measurability
of the associated process. -/
theorem measurable_progressive_iff (F : Filtration ι m) [MeasurableSpace E]
    {f : ι × Ω → E} :
    Measurable[F.progressive] f ↔ IsProgressive F (Function.curry f) := by
  simp only [Measurable, measurableSet_progressive_iff, IsProgressive]
  exact ⟨fun h t s hs => h hs t, fun h s hs t => h t hs⟩

/-- The inclusion of an initial time interval into the progressive measurable space. -/
theorem measurable_inclusion_progressive (F : Filtration ι m) (t : ι) :
    Measurable[Subtype.instMeasurableSpace.prod (F t), F.progressive]
      (fun p : Iic t × Ω => ((p.1 : ι), p.2)) :=
  Measurable.of_le_map (iInf_le _ t)

/-- Enlarging the filtration enlarges its progressive sigma algebra. -/
theorem progressive_mono {F G : Filtration ι m} (h : F ≤ G) :
    F.progressive ≤ G.progressive := by
  intro s hs
  rw [measurableSet_progressive_iff] at hs ⊢
  exact fun t => (MeasurableSpace.prod_mono le_rfl (h t)) _ (hs t)

/-- A sigma algebra is contained in the progressive sigma algebra exactly when every
initial-interval inclusion is measurable into it. -/
theorem le_progressive_iff (F : Filtration ι m) {m' : MeasurableSpace (ι × Ω)} :
    m' ≤ F.progressive ↔ ∀ t,
      Measurable[Subtype.instMeasurableSpace.prod (F t), m']
        (fun p : Iic t × Ω => ((p.1 : ι), p.2)) := by
  simp only [progressive, le_iInf_iff, measurable_iff_le_map]

end Preorder

/-- Every predictable set is progressive. -/
theorem predictable_le_progressive [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι]
    [OpensMeasurableSpace ι] [OrderClosedTopology ι] (F : Filtration ι m) :
    F.predictable ≤ F.progressive :=
  (F.le_progressive_iff).2 fun _ => measurable_inclusion_predictable

/-- Progressive sets are ambient-product measurable if countably many measurable initial
intervals cover time. -/
theorem progressive_le_prod_of_cover [Preorder ι] (F : Filtration ι m) (a : ℕ → ι)
    (ha : ∀ n, MeasurableSet (Iic (a n))) (hcover : ∀ t, ∃ n, t ≤ a n) :
    F.progressive ≤ (inferInstance : MeasurableSpace ι).prod m := by
  intro s hs
  rw [measurableSet_progressive_iff] at hs
  have hpiece (n : ℕ) : MeasurableSet (s ∩ (Iic (a n) ×ˢ univ)) := by
    have he := (MeasurableEmbedding.subtype_coe (ha n)).prodMap
      (MeasurableEmbedding.id (mα := m))
    have hm : MeasurableSet[(inferInstance : MeasurableSpace (Iic (a n))).prod m]
        ((Prod.map (Subtype.val : Iic (a n) → ι) id) ⁻¹' s) :=
      (MeasurableSpace.prod_mono le_rfl (F.le (a n))) _ (hs (a n))
    simpa only [image_preimage_eq_inter_range, range_prodMap, Subtype.range_coe, range_id]
      using he.measurableSet_image.mpr hm
  have heq : s = ⋃ n, s ∩ (Iic (a n) ×ˢ univ) := by
    ext p
    simp only [mem_iUnion, mem_inter_iff, mem_prod, mem_Iic, mem_univ, and_true]
    exact ⟨fun hp => let ⟨n, hn⟩ := hcover p.1; ⟨n, hp, hn⟩, fun ⟨_, hp, _⟩ => hp⟩
  rw [heq]
  exact MeasurableSet.iUnion hpiece

/-- In nonnegative real time, progressive sets are measurable for the ambient product
sigma algebra. -/
theorem progressive_le_prod (F : Filtration ℝ≥0 m) :
    F.progressive ≤ (inferInstance : MeasurableSpace ℝ≥0).prod m := by
  apply F.progressive_le_prod_of_cover (fun n => n) (fun _ => measurableSet_Iic)
  exact fun t => exists_nat_ge t

/-- Restricting the progressive sigma algebra to a finite horizon gives exactly the sets
whose restrictions to all shorter initial intervals are measurable at their endpoints. -/
theorem measurableSet_comap_progressive_iff [LinearOrder ι] [MeasurableInf ι]
    (F : Filtration ι m) (T : ι)
    {s : Set (Iic T × Ω)} :
    MeasurableSet[F.progressive.comap (fun p : Iic T × Ω => ((p.1 : ι), p.2))] s ↔
      ∀ t (ht : t ≤ T), MeasurableSet[Subtype.instMeasurableSpace.prod (F t)]
        ((fun p : Iic t × Ω =>
          (⟨(p.1 : ι), mem_Iic.mpr ((mem_Iic.mp p.1.prop).trans ht)⟩, p.2)) ⁻¹' s) := by
  constructor
  · rintro ⟨u, hu, rfl⟩ t ht
    exact (F.measurableSet_progressive_iff.1 hu) t
  · intro h
    let cap : ι × Ω → Iic T × Ω := fun p => (⟨min p.1 T, min_le_right _ _⟩, p.2)
    refine ⟨cap ⁻¹' s, F.measurableSet_progressive_iff.2 (fun t => ?_), ?_⟩
    · obtain ht | ht := le_total t T
      · convert h t ht using 1
        ext p
        simp only [mem_preimage, cap, min_eq_left (p.1.prop.trans ht)]
      · have hsT : MeasurableSet[Subtype.instMeasurableSpace.prod (F T)] s := h T le_rfl
        have hst := (MeasurableSpace.prod_mono le_rfl (F.mono ht)) _ hsT
        exact hst.preimage (((measurable_subtype_coe.comp measurable_fst).inf_const T).subtype_mk
          |>.prodMk measurable_snd)
    · ext p
      simp only [mem_preimage, cap, min_eq_left p.1.prop]

end MeasureTheory.Filtration

namespace MeasureTheory.IsProgressive

variable {Ω E : Type*} [m : MeasurableSpace Ω] [MeasurableSpace E]
    {F : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → E}

/-- A progressively measurable process in nonnegative real time is jointly measurable for
the ambient time-product sigma algebra. -/
protected theorem measurable (h : IsProgressive F X) : Measurable (Function.uncurry X) :=
  ((F.measurable_progressive_iff (f := Function.uncurry X)).2 h).mono
    F.progressive_le_prod le_rfl

end MeasureTheory.IsProgressive
