/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero.Quotient
public import TauCeti.LinearAlgebra.LinearMap.Range

/-!
# Mapping cones and cokernels of differential modules

The cone of an injective chain map `f : (M, d) → (N, e)` computes the homology of its cokernel
`N ⧸ range f` (`LinearMap.mappingConeQuotientHomologyEquiv`). The comparison projects a cone
cycle `(a, b)` to the class of `b` in the cokernel.
A homotopy `h` between two injective chain maps `f` and `g` gives the explicit shear
`(a, b) ↦ (a, b + h a)` between their cones (`LinearEquiv.skewProd`), and therefore an
equivalence between the homologies of their cokernels
(`LinearMap.quotientHomologyEquivOfHomotopy`). If `e c = f a`, it sends the class of `c` to the
class of `c - h a`.

These constructions use the square-zero mapping cone `LinearMap.mappingCone`.
They apply to differential modules without requiring a grading or a splitting of
the quotient map. For example, they compare the complexes obtained by setting either of two
chain-homotopic polynomial variables to zero, when both variables act injectively.

## References

C. Weibel, *An Introduction to Homological Algebra*, Section 1.5 (mapping cones).
-/

public section

namespace LinearMap

variable {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  (d : M →ₗ[S] M) (hd : d ∘ₗ d = 0) (e : N →ₗ[S] N) (he : e ∘ₗ e = 0)
  (f : M →ₗ[S] N) (hf : f ∘ₗ d = e ∘ₗ f)

/-- The projection from the mapping cone to the cokernel sends `(a, b)` to the class of `b`. -/
def mappingConeQuotientProjection : M × N →ₗ[S] N ⧸ range f :=
  (range f).mkQ ∘ₗ snd S M N

/-- Evaluation of the mapping-cone projection. -/
@[simp]
theorem mappingConeQuotientProjection_apply (x : M × N) :
    mappingConeQuotientProjection f x = Submodule.Quotient.mk x.2 := (rfl)

/-- The cone projection commutes with the induced differential on the cokernel. -/
theorem mappingConeQuotientProjection_comp :
    mappingConeQuotientProjection f ∘ₗ mappingCone d e f =
      (range f).mapQ (range f) e (range_le_comap_range_of_comp_eq f hf) ∘ₗ
        mappingConeQuotientProjection f := by
  apply LinearMap.ext
  intro x
  simp only [comp_apply, mappingCone_apply, mappingConeQuotientProjection_apply,
    Submodule.mapQ_apply, Submodule.Quotient.mk_add]
  rw [(Submodule.Quotient.mk_eq_zero (range f)).mpr (mem_range_self _ x.1), zero_add]

variable {d e f} in
/-- The second coordinate of a cone cycle `(a, b)` is a cycle modulo `range f`:
`e b = f (-a)`. -/
theorem apply_snd_mem_range_of_mem_ker_mappingCone {x : M × N}
    (hx : x ∈ ker (mappingCone d e f)) : e x.2 ∈ range f := by
  have hz : f x.1 + e x.2 = 0 := by
    simpa only [mappingCone_apply, Prod.snd_zero] using congrArg Prod.snd (mem_ker.mp hx)
  exact ⟨-x.1, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_right hz).symm⟩

variable {d e f} in
include he hf in
/-- If `f` is an injective chain map and `e c = f a`, then `(-a, c)` is a cycle of the mapping
cone. -/
theorem mk_neg_mem_ker_mappingCone (hinj : Function.Injective f) {c : N} {a : M}
    (hc : e c = f a) : (-a, c) ∈ ker (mappingCone d e f) := by
  simp only [mem_ker, mappingCone_apply, map_neg, neg_neg,
    apply_eq_zero_of_apply_eq he hf hinj hc, hc, neg_add_cancel, Prod.mk_zero_zero]

/-- The cone of an injective chain map computes the homology of its cokernel. -/
theorem homologyMap_mappingConeQuotientProjection_bijective (hinj : Function.Injective f) :
    Function.Bijective (homologyMap (mappingConeQuotientProjection f)
      (mappingCone_comp_self f hd he hf)
      (e.mapQ_comp_mapQ_eq_zero he (range f) (range_le_comap_range_of_comp_eq f hf))
      (mappingConeQuotientProjection_comp d e f hf)) := by
  constructor
  · rw [homologyMap_injective_iff]
    rintro ⟨a, b⟩ hz hb
    have hz' : -d a = 0 ∧ f a + e b = 0 := by
      simpa only [mem_ker, mappingCone_apply, Prod.mk_eq_zero] using hz
    rw [mappingConeQuotientProjection_apply, Submodule.mk_mem_range_mapQ_iff] at hb
    obtain ⟨w, hw⟩ := hb
    obtain ⟨u, hu⟩ := mem_range.mp hw
    have ha : a = -d u := by
      apply hinj
      have hdu : e (f u) = f (d u) := (congr($hf u)).symm
      have hee : e (e w) = 0 := by simpa using congr($he w)
      have h := congrArg e hu
      simp only [map_sub, hee, sub_zero, hdu] at h
      rw [map_neg, h]
      exact eq_neg_of_add_eq_zero_left hz'.2
    refine ⟨(u, w), ?_⟩
    apply Prod.ext
    · simpa only [mappingCone_apply] using ha.symm
    · simpa only [mappingCone_apply] using (eq_sub_iff_add_eq.mp hu)
  · rw [homologyMap_surjective_iff]
    intro q hq
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (range f) q
    obtain ⟨a, ha⟩ := (Submodule.mk_mem_ker_mapQ_iff b).mp hq
    refine ⟨(-a, b), mk_neg_mem_ker_mappingCone he hf hinj ha.symm, ?_⟩
    simp

/-- Homology of the mapping cone of an injective chain map is the homology of the
quotient by its range. The forward map is induced by projection onto the second coordinate. -/
noncomputable def mappingConeQuotientHomologyEquiv (hinj : Function.Injective f) :
    (mappingCone d e f).homology (mappingCone_comp_self f hd he hf) ≃ₗ[S]
      e.quotientHomology he (range f) (range_le_comap_range_of_comp_eq f hf) :=
  LinearEquiv.ofBijective _
    (homologyMap_mappingConeQuotientProjection_bijective d hd e he f hf hinj)

/-- The cone-to-quotient comparison on a representing cone cycle `(a, b)` is the class of `b`. -/
@[simp]
theorem mappingConeQuotientHomologyEquiv_mk (hinj : Function.Injective f)
    (z : ker (mappingCone d e f)) :
    mappingConeQuotientHomologyEquiv d hd e he f hf hinj (Submodule.Quotient.mk z) =
      quotientHomologyClass he (range_le_comap_range_of_comp_eq f hf) z.1.2
        (apply_snd_mem_range_of_mem_ker_mappingCone z.2) := by
  rw [mappingConeQuotientHomologyEquiv, LinearEquiv.ofBijective_apply, homologyMap_mk,
    quotientHomologyClass_def]
  simp only [mappingConeQuotientProjection_apply]

/-- The inverse cone-to-quotient comparison sends the class of `c`, where `e c = f a`, to the
class of the cone cycle `(-a, c)`. -/
theorem mappingConeQuotientHomologyEquiv_symm_quotientHomologyClass
    (hinj : Function.Injective f) (c : N) (a : M) (hc : e c = f a) :
    (mappingConeQuotientHomologyEquiv d hd e he f hf hinj).symm
        (quotientHomologyClass he (range_le_comap_range_of_comp_eq f hf) c
          (mem_range.mpr ⟨a, hc.symm⟩)) =
      Submodule.Quotient.mk ⟨(-a, c), mk_neg_mem_ker_mappingCone he hf hinj hc⟩ := by
  rw [LinearEquiv.symm_apply_eq, mappingConeQuotientHomologyEquiv_mk]

variable (g h : M →ₗ[S] N) (hg : g ∘ₗ d = e ∘ₗ g)
  (hh : f - g = e ∘ₗ h + h ∘ₗ d)

include hh in
/-- The shear `(a, b) ↦ (a, b + h a)` intertwines the cone differentials of homotopic chain
maps. -/
theorem skewProd_comp_mappingCone :
    ((LinearEquiv.refl S M).skewProd (LinearEquiv.refl S N) h).toLinearMap ∘ₗ mappingCone d e f =
      mappingCone d e g ∘ₗ ((LinearEquiv.refl S M).skewProd (LinearEquiv.refl S N) h).toLinearMap
    := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simp only [comp_apply, LinearEquiv.coe_coe, mappingCone_apply, LinearEquiv.skewProd_apply,
      LinearEquiv.refl_apply]
  · have hx : f x.1 - g x.1 = e (h x.1) + h (d x.1) := congr($hh x.1)
    simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.skewProd_apply,
      LinearEquiv.refl_apply, mappingCone_apply, map_add, map_neg]
    have hfx : f x.1 = g x.1 + e (h x.1) + h (d x.1) := by
      rw [sub_eq_iff_eq_add] at hx
      rw [hx]
      abel
    rw [hfx]
    abel

include he hf hh in
/-- If `f` is injective, `f` and `g` are homotopic through `h`, and `e c = f a`, then
`e (c - h a) = g a`. -/
theorem apply_sub_eq_of_homotopy (hinj : Function.Injective f) {c : N} {a : M}
    (hc : e c = f a) : e (c - h a) = g a := by
  have hx : f a - g a = e (h a) + h (d a) := congr($hh a)
  rw [apply_eq_zero_of_apply_eq he hf hinj hc, map_zero, add_zero] at hx
  rw [map_sub, hc, ← hx, sub_sub_cancel]

/-- Homotopic injective chain maps have isomorphic cokernel homologies.
The comparison factors through their mapping cones and uses the specified homotopy `h`. -/
noncomputable def quotientHomologyEquivOfHomotopy
    (hfi : Function.Injective f) (hgi : Function.Injective g) :
    e.quotientHomology he (range f) (range_le_comap_range_of_comp_eq f hf) ≃ₗ[S]
      e.quotientHomology he (range g) (range_le_comap_range_of_comp_eq g hg) :=
  (mappingConeQuotientHomologyEquiv d hd e he f hf hfi).symm.trans
    ((((LinearEquiv.refl S M).skewProd (LinearEquiv.refl S N) h).homologyEquiv
      (mappingCone_comp_self f hd he hf) (mappingCone_comp_self g hd he hg)
      (skewProd_comp_mappingCone d e f g h hh)).trans
        (mappingConeQuotientHomologyEquiv d hd e he g hg hgi))

/-- If `e c = f a`, the homotopy comparison sends the class of `c` modulo `range f` to the class
of `c - h a` modulo `range g`. -/
theorem quotientHomologyEquivOfHomotopy_quotientHomologyClass
    (hfi : Function.Injective f) (hgi : Function.Injective g) (c : N) (a : M) (hc : e c = f a) :
    quotientHomologyEquivOfHomotopy d hd e he f hf g h hg hh hfi hgi
        (quotientHomologyClass he (range_le_comap_range_of_comp_eq f hf) c
          (mem_range.mpr ⟨a, hc.symm⟩)) =
      quotientHomologyClass he (range_le_comap_range_of_comp_eq g hg) (c - h a)
        (mem_range.mpr ⟨a, (apply_sub_eq_of_homotopy d e he f hf g h hh hfi hc).symm⟩) := by
  rw [quotientHomologyEquivOfHomotopy, LinearEquiv.trans_apply,
    mappingConeQuotientHomologyEquiv_symm_quotientHomologyClass d hd e he f hf hfi c a hc,
    LinearEquiv.trans_apply,
    LinearEquiv.homologyEquiv_mk, mappingConeQuotientHomologyEquiv_mk]
  congr 1
  simp [sub_eq_add_neg]

/-- The inverse homotopy comparison is the comparison along the reversed homotopy `-h`. -/
@[simp]
theorem quotientHomologyEquivOfHomotopy_symm
    (hfi : Function.Injective f) (hgi : Function.Injective g) :
    (quotientHomologyEquivOfHomotopy d hd e he f hf g h hg hh hfi hgi).symm =
      quotientHomologyEquivOfHomotopy d hd e he g hg f (-h) hf
        (by rw [comp_neg, neg_comp, ← neg_add, ← hh, neg_sub]) hgi hfi := by
  ext x
  rw [LinearEquiv.symm_apply_eq]
  obtain ⟨c, hc, rfl⟩ := exists_quotientHomologyClass_eq he x
  obtain ⟨a, ha⟩ := mem_range.mp hc
  rw [quotientHomologyEquivOfHomotopy_quotientHomologyClass (hc := ha.symm),
    quotientHomologyEquivOfHomotopy_quotientHomologyClass (hc := ?_)]
  · congr 1
    rw [LinearMap.neg_apply, sub_neg_eq_add, add_sub_cancel_right]
  · have hx : f a - g a = e (h a) + h (d a) := congr($hh a)
    rw [apply_eq_zero_of_apply_eq he hg hgi ha.symm, map_zero, add_zero] at hx
    rw [LinearMap.neg_apply, sub_neg_eq_add, map_add, ← ha, ← hx, add_sub_cancel]

end LinearMap
