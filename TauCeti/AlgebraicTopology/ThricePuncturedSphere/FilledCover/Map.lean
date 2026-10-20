/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Basic
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.SphereCharts

/-!
# The map from a filled cover to the sphere

Extend a finite cover of the thrice-punctured sphere over its filled points by sending each
added centre to its puncture. In a filled disc the extension is the power map followed by the
inverse standard coordinate on the sphere. This formula proves continuity at the centres;
compactness of the filled cover then gives properness. For a nonempty cover the extension is
surjective.

Exactly the original cover lies over the unpunctured sphere, and the extension there is the
original projection. In particular the fibre of the extension over a point of `ℂ ∖ {0, 1}` is
the fibre of the original cover, the fibre over a puncture `q` consists of the added points over
`q`, and off the marked points the extension is a covering map.
Continuity and density also characterize the extension uniquely.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, §1.2.7, Lemma 1.80.
* O. Forster, *Lectures on Riemann Surfaces*, Theorem 8.4.

The construction uses `PunctureFilling.extend` and its final-topology universal property.
-/

public noncomputable section

namespace TauCeti.FilledCover

open Filter Function Metric Set Topology ThricePuncturedSphere
open scoped OnePoint

variable {E : Type*} [TopologicalSpace E] (p : E → ThricePuncturedSphere)

/-- The extension of the covering projection to the filled cover, taking each added centre to
its puncture in the Riemann sphere. -/
def fillMap : FilledCover p → OnePoint ℂ :=
  PunctureFilling.extend (toOnePoint ∘ p) (fun i => (FilledPoint.sigmaEquiv p i).1.toOnePoint)

@[simp] theorem fillMap_incl (x : E) :
    fillMap p (PunctureFilling.incl (chart p) x) = toOnePoint (p x) :=
  PunctureFilling.extend_incl _ _ _

@[simp] theorem fillMap_center (i : FilledPoint p) :
    fillMap p (PunctureFilling.center (chart p) i) = (FilledPoint.sigmaEquiv p i).1.toOnePoint :=
  PunctureFilling.extend_center _ _ _

/-- The original cover is exactly the part of the filled cover lying over the unpunctured
sphere. -/
@[simp] theorem preimage_range_toOnePoint :
    fillMap p ⁻¹' range toOnePoint = range (PunctureFilling.incl (chart p)) := by
  ext y
  induction y using PunctureFilling.induction with
  | incl x => simp
  | center i =>
    rw [mem_preimage, fillMap_center, range_toOnePoint]
    generalize (FilledPoint.sigmaEquiv p i).1 = q
    cases q <;> simp

/-- The fibre of the extended projection over a puncture `q` consists of the added points, one for
each connected component of `p ⁻¹' D_q*`. -/
theorem fillMap_preimage_puncture (q : Puncture) :
    fillMap p ⁻¹' {q.toOnePoint} =
      range fun c ↦ PunctureFilling.center (chart p) ((FilledPoint.sigmaEquiv p).symm ⟨q, c⟩) := by
  ext y
  induction y using PunctureFilling.induction with
  | incl x =>
    -- A point of the original cover lies over `ℂ ∖ {0, 1}`, away from the punctures.
    refine iff_of_false (fun h ↦ ?_) fun ⟨c, hc⟩ ↦ PunctureFilling.center_ne_incl _ _ hc
    have hx : toOnePoint (p x) ∈ markedᶜ := range_toOnePoint ▸ mem_range_self _
    rw [mem_preimage, fillMap_incl, mem_singleton_iff] at h
    exact hx (h ▸ by cases q <;> simp)
  | center i =>
    simp only [mem_preimage, fillMap_center, mem_singleton_iff, mem_range,
      PunctureFilling.center_inj, Equiv.symm_apply_eq]
    obtain ⟨q', c⟩ := FilledPoint.sigmaEquiv p i
    refine ⟨fun h ↦ ?_, fun ⟨c', hc'⟩ ↦ by rw [← hc']⟩
    obtain rfl : q' = q := by
      cases q <;> cases q' <;> simp_all
    exact ⟨c, rfl⟩

variable {p} (hp : IsCoveringMap p) {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
include hp hfin

/-- On a punctured filling chart, the projection is the power map followed by the inverse
sphere coordinate at the corresponding puncture. -/
theorem toOnePoint_comp_chart (i : FilledPoint p) (w : ↥(ball (0 : ℂ) 1 \ {0})) :
    toOnePoint (p (chart p i w)) =
      (FilledPoint.sigmaEquiv p i).1.sphereCoordInv ((w : ℂ) ^ degree p i) := by
  obtain ⟨hw, -, hcoord⟩ := exists_coe_coord_chart_eq_pow hp hfin i w
  rw [← hcoord, Puncture.sphereCoordInv_coord]

/-- The extension has the same power-map formula on the whole filled disc, including zero. -/
theorem fillMap_disc (i : FilledPoint p) (w : ↥(ball (0 : ℂ) 1)) :
    fillMap p (PunctureFilling.disc (chart p) i w) =
      (FilledPoint.sigmaEquiv p i).1.sphereCoordInv ((w : ℂ) ^ degree p i) := by
  by_cases hw : w = 0
  · subst w
    simp [degree_ne_zero hp hfin i]
  · have hw' : (w : ℂ) ≠ 0 := fun h => hw (Subtype.ext h)
    let w' : ↥(ball (0 : ℂ) 1 \ {0}) := ⟨w, w.2, hw'⟩
    have hdisc := PunctureFilling.disc_inclusion (φ := chart p) i w'
    rw [hdisc, fillMap_incl]
    exact toOnePoint_comp_chart hp hfin i w'

/-- The extended covering projection is continuous, including at the filled points. -/
@[continuity, fun_prop] theorem continuous_fillMap : Continuous (fillMap p) := by
  refine PunctureFilling.continuous_iff.2 ⟨?_, fun i => ?_⟩
  · simpa only [Function.comp_def, fillMap_incl] using
      isOpenEmbedding_toOnePoint.continuous.comp hp.continuous
  · have h : Continuous (fun w : ↥(ball (0 : ℂ) 1) =>
        (FilledPoint.sigmaEquiv p i).1.sphereCoordInv ((w : ℂ) ^ degree p i)) :=
      ((FilledPoint.sigmaEquiv p i).1.continuous_sphereCoordInv).comp
      (continuous_subtype_val.pow (degree p i))
    exact h.congr (fun w => (fillMap_disc hp hfin i w).symm)

/-- Compactness of the filled finite cover makes the extended projection proper. -/
theorem isProperMap_fillMap : IsProperMap (fillMap p) := by
  let := compactSpace hp hfin
  exact (continuous_fillMap hp hfin).isProperMap

omit hp hfin in
/-- The extension of a surjective map hits every point of the sphere. -/
theorem surjective_fillMap (hp : Surjective p) : Surjective (fillMap p) := by
  have hq (q : Puncture) : ∃ y, fillMap p y = q.toOnePoint := by
    let z := q.coord.symm puncturedDiscBasepoint
    obtain ⟨x, hx⟩ := hp z
    let i := (FilledPoint.sigmaEquiv p).symm
      ⟨q, ConnectedComponents.mk
        (⟨x, by simpa only [Set.mem_preimage, hx] using z.2⟩ : p ⁻¹' q.neighborhood)⟩
    exact ⟨PunctureFilling.center (chart p) i, by simp [i]⟩
  intro y
  induction y using OnePoint.rec with
  | infty => simpa using hq .inf
  | coe z =>
    by_cases h0 : z = 0
    · subst z; simpa using hq .zero
    by_cases h1 : z = 1
    · subst z; simpa using hq .one
    obtain ⟨x, hx⟩ := hp ⟨z, h0, h1⟩
    exact ⟨PunctureFilling.incl (chart p) x, by simp [hx]⟩

/-- The unpunctured part of the filled cover is canonically the original covering space. -/
def unpuncturedHomeomorph : E ≃ₜ (fillMap p ⁻¹' range toOnePoint) :=
  ((PunctureFilling.isOpenEmbedding_incl
    (fun i => (isOpenEmbedding_chart hp hfin i).continuous)).isEmbedding.toHomeomorph).trans
      (Homeomorph.setCongr (preimage_range_toOnePoint p).symm)

@[simp] theorem coe_unpuncturedHomeomorph (x : E) :
    (unpuncturedHomeomorph hp hfin x : FilledCover p) = PunctureFilling.incl (chart p) x := by
  simp [unpuncturedHomeomorph, Homeomorph.setCongr]

/-- Over the unpunctured sphere, the extension is a covering map: under the canonical
identifications of source and target it is the original cover. -/
theorem isCoveringMap_restrictPreimage_fillMap :
    IsCoveringMap ((range toOnePoint).restrictPreimage (fillMap p)) := by
  apply (IsCoveringMap.comp_homeomorph_iff (unpuncturedHomeomorph hp hfin)).mp
  convert hp.homeomorph_comp isOpenEmbedding_toOnePoint.isEmbedding.toHomeomorph using 1
  funext x
  apply Subtype.ext
  simp

omit hp hfin in
/-- The fibre of the extended projection over a point `z` of `ℂ ∖ {0, 1}` is the fibre of `p`
over `z`: no added point lies over `z`. -/
theorem fillMap_preimage_toOnePoint (z : ThricePuncturedSphere) :
    fillMap p ⁻¹' {toOnePoint z} = PunctureFilling.incl (chart p) '' (p ⁻¹' {z}) := by
  ext y
  induction y using PunctureFilling.induction with
  | incl x => simp [Subtype.ext_iff]
  | center i =>
    have h : PunctureFilling.center (chart p) i ∉ fillMap p ⁻¹' range toOnePoint := by
      rw [preimage_range_toOnePoint]
      rintro ⟨x, hx⟩
      exact PunctureFilling.incl_ne_center x i hx
    refine iff_of_false (fun hz => h ⟨z, (mem_singleton_iff.1 hz).symm⟩) ?_
    rintro ⟨x, -, hx⟩
    exact PunctureFilling.incl_ne_center x i hx

omit hp hfin in
/-- The fibre of the extended projection over a point `z` of `ℂ ∖ {0, 1}` has as many points as
the fibre of `p` over `z`. -/
theorem natCard_fillMap_preimage_toOnePoint (z : ThricePuncturedSphere) :
    Nat.card (fillMap p ⁻¹' {toOnePoint z}) = Nat.card (p ⁻¹' {z}) := by
  rw [fillMap_preimage_toOnePoint, Nat.card_image_of_injective PunctureFilling.incl_injective]

/-- **Off the marked points, the extended projection is a covering map.** -/
theorem isCoveringMapOn_fillMap : IsCoveringMapOn (fillMap p) markedᶜ := by
  rw [← range_toOnePoint]
  refine .of_isCoveringMap_restrictPreimage _ isOpenEmbedding_toOnePoint.isOpen_range ?_
    (isCoveringMap_restrictPreimage_fillMap hp hfin)
  rw [preimage_range_toOnePoint]
  exact PunctureFilling.isOpen_range_incl

/-- A continuous extension of the projection to the filled cover is unique. -/
theorem fillMap_unique {f : FilledCover p → OnePoint ℂ} (hf : Continuous f)
    (hext : ∀ x, f (PunctureFilling.incl (chart p) x) = toOnePoint (p x)) :
    f = fillMap p := by
  apply (PunctureFilling.denseRange_incl (φ := chart p)).equalizer hf (continuous_fillMap hp hfin)
  funext x
  exact (hext x).trans (fillMap_incl p x).symm

end TauCeti.FilledCover
