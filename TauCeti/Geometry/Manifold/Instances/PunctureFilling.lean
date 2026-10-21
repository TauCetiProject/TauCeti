/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Topology.PunctureFilling

/-!
# The charted-space structure on a puncture filling

Let `E` be a space charted over `ℂ` and let `φ i : 𝔻* → E` be open embeddings of the punctured
unit disc `𝔻* = ball 0 1 \ {0}`. Their puncture filling `TauCeti.PunctureFilling φ` adds the
centre of each punctured disc. It is again locally homeomorphic to `ℂ`
(`TauCeti.PunctureFilling.chartedSpace`): at a point of `E` the chart is the chart of `E` there,
and at an added point `center φ i` it is the inverse of the filled disc `disc φ i`, which sends
`center φ i` to `0`.

Away from the added points, the chart at `center φ i` is the inverse of `φ i` read as a chart of
`E`, `TauCeti.PunctureFilling.puncturedDiscChart`. When every such chart is compatible with the
charts of `E` for a structure groupoid closed under restriction, the charts of the filling are
compatible for that groupoid too (`TauCeti.PunctureFilling.hasGroupoid`); in particular, filling
the punctures of a `C^n` manifold along punctured discs which are `C^n` diffeomorphisms onto
their images gives a `C^n` manifold (`TauCeti.PunctureFilling.isManifold`). No removable
singularity theorem is needed: the only chart containing `center φ i` is the chart at that
point, so every other transition map lives inside `E`.

This is how the compactification of a finite cover of a punctured Riemann surface receives its
charts: `E` carries the charts pulled back along the covering map, and the punctured discs are the
components of the preimages of punctured discs about the punctures. The charts are holomorphically
compatible once these components are biholomorphic to `𝔻*`.

## Main declarations

* `TauCeti.PunctureFilling.chartedSpace`: the charted space `PunctureFilling φ` over `ℂ`, with
  preferred charts `TauCeti.PunctureFilling.chartAt_incl` and
  `TauCeti.PunctureFilling.chartAt_center`.
* `TauCeti.PunctureFilling.puncturedDiscChart`: the inverse of a punctured disc, as a chart of
  `E`.
* `TauCeti.PunctureFilling.hasGroupoid`, `TauCeti.PunctureFilling.isManifold`: compatibility of
  the charts of the filling.

## Implementation notes

The charts are assembled by hand, as Mathlib assembles those of a disjoint union
(`ChartedSpace.sum`), rather than through `TauCeti.chartedSpaceOfIsOpenEmbedding`: that
construction picks the piece containing a point by choice, so the chart at a point of `E` could be
a filled disc rather than the chart of `E`, and its gluing condition asks for maps defined on all
of the unit disc, which `φ i` is not.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §1.2.7 (Lemma 1.80: the charts at the added points).
* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer 1981,
  §8, Theorem 8.4.
-/

public section

noncomputable section

open Metric Set Topology

open scoped ContDiff Manifold

namespace TauCeti

/-- The unit disc of `ℂ`, as a subtype. -/
local notation "𝔻" => Set.Elem (ball (0 : ℂ) 1)

/-- The punctured unit disc of `ℂ`, as a subtype. -/
local notation "𝔻*" => Set.Elem (ball (0 : ℂ) 1 \ {0})

variable {E ι : Type*} [TopologicalSpace E] {φ : ι → 𝔻* → E}

namespace PunctureFilling

/-- The punctured unit disc is an open subset of `ℂ`. -/
private theorem isOpen_puncturedDisc : IsOpen (ball (0 : ℂ) 1 \ {0}) :=
  isOpen_ball.sdiff isClosed_singleton

/-- The punctured unit disc is nonempty. -/
private theorem nonempty_puncturedDisc : Nonempty 𝔻* :=
  ⟨⟨1 / 2, by norm_num [mem_ball, dist_zero_right]⟩⟩

/-- The inverse of an open embedding `φ i : 𝔻* → E` of the punctured unit disc, as a chart of `E`
with values in `ℂ`: its source is the image of `φ i` and its target is `𝔻*`. -/
def puncturedDiscChart {i : ι} (hi : IsOpenEmbedding (φ i)) : OpenPartialHomeomorph E ℂ :=
  have := nonempty_puncturedDisc
  (isOpen_puncturedDisc.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph _).lift_openEmbedding hi

variable {i : ι} (hi : IsOpenEmbedding (φ i))

@[simp]
theorem puncturedDiscChart_source : (puncturedDiscChart hi).source = range (φ i) := by
  simp [puncturedDiscChart]

@[simp]
theorem puncturedDiscChart_target : (puncturedDiscChart hi).target = ball (0 : ℂ) 1 \ {0} := by
  simp only [puncturedDiscChart, OpenPartialHomeomorph.lift_openEmbedding_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_coe]

@[simp]
theorem puncturedDiscChart_apply (w : 𝔻*) : puncturedDiscChart hi (φ i w) = w := by
  have := nonempty_puncturedDisc
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ hi

@[simp]
theorem puncturedDiscChart_symm_apply (w : 𝔻*) : (puncturedDiscChart hi).symm w = φ i w := by
  have := nonempty_puncturedDisc
  rw [puncturedDiscChart, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

/-! ### The charts -/

variable (hφ : ∀ i, IsOpenEmbedding (φ i))

/-- The inclusion of the unit disc into `ℂ`, as an open partial homeomorphism. -/
private def unitDiscChart : OpenPartialHomeomorph 𝔻 ℂ :=
  isOpen_ball.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph _

/-- The chart at the added point `center φ i`: the inverse of the `i`-th filled disc. -/
private def centerChart (i : ι) : OpenPartialHomeomorph (PunctureFilling φ) ℂ :=
  unitDiscChart.lift_openEmbedding (isOpenEmbedding_disc (fun j => (hφ j).continuous) (hφ i))

variable [ChartedSpace ℂ E]

/-- The chart at a point `incl φ x` of `E`: the chart of `E` at `x`. -/
private def inclChart (x : E) : OpenPartialHomeomorph (PunctureFilling φ) ℂ :=
  (chartAt ℂ x).lift_openEmbedding (isOpenEmbedding_incl fun j => (hφ j).continuous)

open Classical in
/-- The preferred chart at a point of the puncture filling. -/
private def chart (y : PunctureFilling φ) : OpenPartialHomeomorph (PunctureFilling φ) ℂ :=
  if h : ∃ x, incl φ x = y then inclChart hφ h.choose
  else centerChart hφ (by rwa [← compl_range_incl] : y ∈ range (center φ)).choose

private theorem chart_incl (x : E) : chart hφ (incl φ x) = inclChart hφ x := by
  have h : ∃ x', incl φ x' = incl φ x := ⟨x, rfl⟩
  rw [chart, dite_eq_left h, incl_injective h.choose_spec]

private theorem chart_center (i : ι) : chart hφ (center φ i) = centerChart hφ i := by
  have h : ¬∃ x, incl φ x = center φ i := fun ⟨x, hx⟩ => incl_ne_center x i hx
  rw [chart, dite_eq_right h]
  generalize_proofs hy
  exact congrArg _ (center_injective hy.choose_spec)

/-- **The puncture filling is locally homeomorphic to `ℂ`.** If `E` is charted over `ℂ` and the
punctured discs `φ i` are open embeddings, the chart at a point of `E` is the chart of `E` there,
and the chart at the added point `center φ i` is the inverse of the filled disc `disc φ i`. -/
@[instance_reducible]
def chartedSpace : ChartedSpace ℂ (PunctureFilling φ) where
  atlas := range (chart hφ)
  chartAt := chart hφ
  mem_chart_source y := by
    induction y using PunctureFilling.induction with
    | incl x => exact chart_incl hφ x ▸ mem_image_of_mem _ (mem_chart_source ℂ x)
    | center i => exact chart_center hφ i ▸ ⟨0, mem_univ _, disc_zero i⟩
  chart_mem_atlas y := mem_range_self y

/-- The chart of the puncture filling at a point of `E` is the chart of `E` at that point. -/
theorem chartAt_incl (x : E) :
    @chartAt ℂ _ _ _ (chartedSpace hφ) (incl φ x) =
      (chartAt ℂ x).lift_openEmbedding (isOpenEmbedding_incl fun j => (hφ j).continuous) :=
  chart_incl hφ x

/-- The chart of the puncture filling at the added point `center φ i` is the inverse of the
`i`-th filled disc. -/
theorem chartAt_center (i : ι) :
    @chartAt ℂ _ _ _ (chartedSpace hφ) (center φ i) =
      (isOpen_ball.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph _).lift_openEmbedding
        (isOpenEmbedding_disc (fun j => (hφ j).continuous) (hφ i)) :=
  chart_center hφ i

@[simp]
theorem chartAt_incl_source (x : E) :
    (@chartAt ℂ _ _ _ (chartedSpace hφ) (incl φ x)).source = incl φ '' (chartAt ℂ x).source := by
  rw [chartAt_incl, OpenPartialHomeomorph.lift_openEmbedding_source]

@[simp]
theorem chartAt_incl_target (x : E) :
    (@chartAt ℂ _ _ _ (chartedSpace hφ) (incl φ x)).target = (chartAt ℂ x).target := by
  rw [chartAt_incl, OpenPartialHomeomorph.lift_openEmbedding_target]

@[simp]
theorem chartAt_incl_apply_incl (x y : E) :
    @chartAt ℂ _ _ _ (chartedSpace hφ) (incl φ x) (incl φ y) = chartAt ℂ x y := by
  rw [chartAt_incl, OpenPartialHomeomorph.lift_openEmbedding_apply]

@[simp]
theorem chartAt_incl_symm_apply (x : E) (z : ℂ) :
    (@chartAt ℂ _ _ _ (chartedSpace hφ) (incl φ x)).symm z = incl φ ((chartAt ℂ x).symm z) := by
  rw [chartAt_incl, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply]

@[simp]
theorem chartAt_center_source (i : ι) :
    (@chartAt ℂ _ _ _ (chartedSpace hφ) (center φ i)).source = range (disc φ i) := by
  rw [chartAt_center, OpenPartialHomeomorph.lift_openEmbedding_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, image_univ]

@[simp]
theorem chartAt_center_target (i : ι) :
    (@chartAt ℂ _ _ _ (chartedSpace hφ) (center φ i)).target = ball (0 : ℂ) 1 := by
  rw [chartAt_center, OpenPartialHomeomorph.lift_openEmbedding_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_coe]

@[simp]
theorem chartAt_center_apply_disc (i : ι) (z : 𝔻) :
    @chartAt ℂ _ _ _ (chartedSpace hφ) (center φ i) (disc φ i z) = z := by
  rw [chartAt_center, OpenPartialHomeomorph.lift_openEmbedding_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_apply]

@[simp]
theorem chartAt_center_apply_center (i : ι) :
    @chartAt ℂ _ _ _ (chartedSpace hφ) (center φ i) (center φ i) = 0 := by
  simpa using chartAt_center_apply_disc hφ i 0

@[simp]
theorem chartAt_center_symm_apply (i : ι) (z : 𝔻) :
    (@chartAt ℂ _ _ _ (chartedSpace hφ) (center φ i)).symm z = disc φ i z := by
  rw [chartAt_center, OpenPartialHomeomorph.lift_openEmbedding_symm, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

/-- The atlas of the puncture filling consists of the charts of `E` and the inverses of the filled
discs. -/
theorem mem_atlas_iff {e : OpenPartialHomeomorph (PunctureFilling φ) ℂ} :
    e ∈ @atlas ℂ _ _ _ (chartedSpace hφ) ↔
      (∃ x, e = @chartAt ℂ _ _ _ (chartedSpace hφ) (incl φ x)) ∨
        ∃ i, e = @chartAt ℂ _ _ _ (chartedSpace hφ) (center φ i) := by
  constructor
  · rintro ⟨y, rfl⟩
    induction y using PunctureFilling.induction with
    | incl x => exact Or.inl ⟨x, rfl⟩
    | center i => exact Or.inr ⟨i, rfl⟩
  · rintro (⟨x, rfl⟩ | ⟨i, rfl⟩) <;> exact mem_range_self _

/-! ### Compatibility of the charts -/

/-- The chart `C` of the puncture filling restricts on `E` to the chart `A` of `E`: over the
points of `E`, `C` is `A` read through the inclusion. -/
private structure RestrictsTo (C : OpenPartialHomeomorph (PunctureFilling φ) ℂ)
    (A : OpenPartialHomeomorph E ℂ) : Prop where
  symm_apply : ∀ z ∈ A.target, z ∈ C.target ∧ C.symm z = incl φ (A.symm z)
  mem_target : ∀ z ∈ C.target, C.symm z ∈ range (incl φ) → z ∈ A.target
  source_inter : C.source ∩ range (incl φ) = incl φ '' A.source
  apply : ∀ x ∈ A.source, C (incl φ x) = A x

omit [ChartedSpace ℂ E] in
/-- Over points of `E`, the transition map between two charts of the puncture filling is the
transition map between the charts of `E` they restrict to. -/
private theorem RestrictsTo.symm_trans_eqOnSource
    {C C' : OpenPartialHomeomorph (PunctureFilling φ) ℂ} {A A' : OpenPartialHomeomorph E ℂ}
    (h : RestrictsTo C A) (h' : RestrictsTo C' A')
    (hE : ∀ z ∈ (C.symm ≫ₕ C').source, C.symm z ∈ range (incl φ)) :
    C.symm ≫ₕ C' ≈ A.symm ≫ₕ A' := by
  have hsource : (C.symm ≫ₕ C').source = (A.symm ≫ₕ A').source := by
    ext z
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    constructor
    · intro hz
      have hA := h.mem_target z hz.1 (hE z hz)
      refine ⟨hA, (incl_injective (φ := φ)).mem_set_image.1 ?_⟩
      rw [← h'.source_inter, ← (h.symm_apply z hA).2]
      exact ⟨hz.2, hE z hz⟩
    · rintro ⟨hA, hA'⟩
      refine ⟨(h.symm_apply z hA).1, ?_⟩
      have := h'.source_inter ▸ mem_image_of_mem (incl φ) hA'
      rw [(h.symm_apply z hA).2]
      exact this.1
  refine ⟨hsource, fun z hz => ?_⟩
  rw [hsource] at hz
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [(h.symm_apply z hz.1).2, h'.apply _ (by simpa using hz.2)]

private theorem restrictsTo_chartAt_center (i : ι) :
    RestrictsTo (@chartAt ℂ _ _ _ (chartedSpace hφ) (center φ i)) (puncturedDiscChart (hφ i)) := by
  refine ⟨fun z hz => ?_, fun z hz hzE => ?_, ?_, ?_⟩
  · rw [puncturedDiscChart_target] at hz
    refine ⟨by simpa using hz.1, ?_⟩
    have h := chartAt_center_symm_apply hφ i (inclusion sdiff_subset (⟨z, hz⟩ : 𝔻*))
    rw [disc_inclusion] at h
    exact h.trans (congrArg _ (puncturedDiscChart_symm_apply (hφ i) ⟨z, hz⟩).symm)
  · rw [chartAt_center_target] at hz
    rw [puncturedDiscChart_target]
    refine ⟨hz, fun h0 => ?_⟩
    rw [mem_singleton_iff] at h0
    subst h0
    have h := chartAt_center_symm_apply hφ i 0
    rw [disc_zero, unitBall.coe_zero] at h
    obtain ⟨x, hx⟩ := h ▸ hzE
    exact incl_ne_center x i hx
  · rw [chartAt_center_source, puncturedDiscChart_source]
    ext y
    constructor
    · rintro ⟨⟨z, rfl⟩, x, hx⟩
      obtain ⟨w, rfl, rfl⟩ := disc_eq_incl_iff.1 hx.symm
      exact ⟨φ i w, mem_range_self w, (disc_inclusion i w).symm⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨⟨_, disc_inclusion i w⟩, mem_range_self _⟩
  · intro x hx
    rw [puncturedDiscChart_source] at hx
    obtain ⟨w, rfl⟩ := hx
    rw [← disc_inclusion]
    exact (chartAt_center_apply_disc hφ i _).trans (puncturedDiscChart_apply (hφ i) w).symm

private theorem restrictsTo_chartAt_incl (x : E) :
    RestrictsTo (@chartAt ℂ _ _ _ (chartedSpace hφ) (incl φ x)) (chartAt ℂ x) := by
  rw [chartAt_incl]
  exact {
    symm_apply := fun z hz => ⟨hz, rfl⟩
    mem_target := fun z hz _ => hz
    source_inter := inter_eq_left.2 (image_subset_range _ _)
    apply := fun _ _ => OpenPartialHomeomorph.lift_openEmbedding_apply _ _ }

omit [TopologicalSpace E] in
/-- A point lying on two different filled discs lies in `E`. -/
private theorem mem_range_incl_of_mem_range_disc {i j : ι} (hij : i ≠ j) {y : PunctureFilling φ}
    (hi : y ∈ range (disc φ i)) (hj : y ∈ range (disc φ j)) : y ∈ range (incl φ) := by
  induction y using PunctureFilling.induction with
  | incl x => exact mem_range_self x
  | center k =>
    obtain ⟨z, hz⟩ := hi
    obtain ⟨z', hz'⟩ := hj
    exact (hij ((disc_eq_center_iff.1 hz).2.trans (disc_eq_center_iff.1 hz').2.symm)).elim

/-- Two charts of the puncture filling overlap only inside `E`, unless both are the chart at the
same added point. -/
private theorem chartAt_symm_mem_range_incl {y y' : PunctureFilling φ}
    (hyy : ¬∃ i, y = center φ i ∧ y' = center φ i) {z : ℂ}
    (hz : z ∈ ((@chartAt ℂ _ _ _ (chartedSpace hφ) y).symm ≫ₕ
      @chartAt ℂ _ _ _ (chartedSpace hφ) y').source) :
    (@chartAt ℂ _ _ _ (chartedSpace hφ) y).symm z ∈ range (incl φ) := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, mem_inter_iff,
    mem_preimage] at hz
  induction y using PunctureFilling.induction with
  | incl x => exact (chartAt_incl_symm_apply hφ x z).symm ▸ mem_range_self _
  | center i =>
    have hy : (@chartAt ℂ _ _ _ (chartedSpace hφ) (center φ i)).symm z ∈ range (disc φ i) := by
      rw [← chartAt_center_source hφ]
      exact OpenPartialHomeomorph.map_target _ hz.1
    induction y' using PunctureFilling.induction with
    | incl x' =>
      rw [chartAt_incl_source] at hz
      exact image_subset_range _ _ hz.2
    | center j =>
      have hij : i ≠ j := by
        rintro rfl
        exact hyy ⟨i, rfl, rfl⟩
      rw [chartAt_center_source] at hz
      exact mem_range_incl_of_mem_range_disc hij hy hz.2

/-- **The charts of a puncture filling are compatible** for a structure groupoid `G` closed under
restriction, as soon as the charts of `E` are and the inverse of every punctured disc `φ i` is
compatible with them. -/
theorem hasGroupoid (G : StructureGroupoid ℂ) [ClosedUnderRestriction G] [HasGroupoid E G]
    (hG : ∀ i, puncturedDiscChart (hφ i) ∈ G.maximalAtlas E) :
    @HasGroupoid ℂ _ (PunctureFilling φ) _ (chartedSpace hφ) G := by
  let := chartedSpace hφ
  have key : ∀ y : PunctureFilling φ, ∃ A ∈ G.maximalAtlas E, RestrictsTo (chartAt ℂ y) A := by
    intro y
    induction y using PunctureFilling.induction with
    | incl x => exact ⟨_, G.chart_mem_maximalAtlas x, restrictsTo_chartAt_incl hφ x⟩
    | center i => exact ⟨_, hG i, restrictsTo_chartAt_center hφ i⟩
  refine ⟨?_⟩
  rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
  by_cases hyy : ∃ i, y = center φ i ∧ y' = center φ i
  · obtain ⟨i, rfl, rfl⟩ := hyy
    refine G.mem_of_eqOnSource ?_ (OpenPartialHomeomorph.symm_trans_self _)
    exact StructureGroupoid.le_iff.1 ((closedUnderRestriction_iff_id_le G).1 inferInstance) _
      (idRestrGroupoid_mem _)
  obtain ⟨A, hA, hyA⟩ := key y
  obtain ⟨A', hA', hyA'⟩ := key y'
  exact G.mem_of_eqOnSource (G.compatible_of_mem_maximalAtlas hA hA')
    (hyA.symm_trans_eqOnSource hyA' fun _ => chartAt_symm_mem_range_incl hφ hyy)

/-- **Filling the punctures of a `C^n` manifold gives a `C^n` manifold**, as soon as the punctured
discs `φ i` are `C^n` diffeomorphisms onto their images, that is, their inverses belong to the
maximal atlas of `E`. -/
theorem isManifold {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {I : ModelWithCorners 𝕜 F ℂ} {n : ℕ∞ω} [IsManifold I n E]
    (hI : ∀ i, puncturedDiscChart (hφ i) ∈ IsManifold.maximalAtlas I n E) :
    @IsManifold 𝕜 _ F _ _ ℂ _ I n (PunctureFilling φ) _ (chartedSpace hφ) :=
  letI := chartedSpace hφ
  haveI := hasGroupoid hφ (contDiffGroupoid n I) hI
  IsManifold.mk' I n _

end PunctureFilling

end TauCeti
