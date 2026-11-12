/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero.Quotient

/-!
# Mapping cones and quotients of differential modules

The cone of an injective chain endomorphism computes the homology of its cokernel.
The comparison projects a cone cycle `(a, b)` to the class of `b` in the cokernel.
A homotopy between two chain endomorphisms gives an explicit shear between their
cones, and therefore an equivalence between the homologies of their cokernels.

These constructions use the square-zero mapping cone `LinearMap.mappingCone`.
They apply to differential modules without requiring a grading or a splitting of
the quotient map. For example, they compare complexes obtained by setting two
chain-homotopic polynomial variables to zero.

## References

C. Weibel, *An Introduction to Homological Algebra*, Section 1.5 (mapping cones).
-/

public section

namespace LinearMap

variable {S M : Type*} [Ring S] [AddCommGroup M] [Module S M]
  (d : M →ₗ[S] M) (hd : d ∘ₗ d = 0)
  (f : M →ₗ[S] M) (hf : f ∘ₗ d = d ∘ₗ f)

include hf in
/-- A chain endomorphism has a differential-stable range. -/
theorem range_le_comap_of_commute : range f ≤ (range f).comap d := by
  rintro _ ⟨x, rfl⟩
  exact ⟨d x, congr($hf x)⟩

/-- The projection from the mapping cone to the cokernel sends `(a, b)` to the class of `b`. -/
def mappingConeQuotientProjection : M × M →ₗ[S] M ⧸ range f :=
  (range f).mkQ ∘ₗ snd S M M

/-- Evaluation of the mapping-cone projection. -/
@[simp]
theorem mappingConeQuotientProjection_apply (x : M × M) :
    mappingConeQuotientProjection f x = Submodule.Quotient.mk x.2 := (rfl)

/-- The cone projection commutes with the induced differential on the cokernel. -/
theorem mappingConeQuotientProjection_comp :
    mappingConeQuotientProjection f ∘ₗ mappingCone d d f =
      (range f).mapQ (range f) d (range_le_comap_of_commute d f hf) ∘ₗ
        mappingConeQuotientProjection f := by
  apply LinearMap.ext
  intro x
  simp only [comp_apply, mappingCone_apply, mappingConeQuotientProjection_apply,
    Submodule.mapQ_apply, Submodule.Quotient.mk_add]
  rw [(Submodule.Quotient.mk_eq_zero (range f)).mpr (mem_range_self _ x.1), zero_add]

/-- The cone of an injective chain endomorphism computes the homology of its cokernel. -/
theorem bijective_homologyMap_mappingConeQuotientProjection (hinj : Function.Injective f) :
    Function.Bijective (homologyMap (mappingConeQuotientProjection f)
      (mappingCone_comp_self f hd hd hf)
      (d.mapQ_comp_mapQ_eq_zero hd (range f) (range_le_comap_of_commute d f hf))
      (mappingConeQuotientProjection_comp d f hf)) := by
  constructor
  · rw [homologyMap_injective_iff]
    rintro ⟨a, b⟩ hz hb
    have hz' : -d a = 0 ∧ f a + d b = 0 := by
      simpa only [mem_ker, mappingCone_apply, Prod.mk_eq_zero] using hz
    obtain ⟨q, hq⟩ := hb
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective (range f) q
    have hbc : b - d c ∈ range f := by
      apply (Submodule.Quotient.eq (range f)).mp
      exact hq.symm
    obtain ⟨u, hu⟩ := hbc
    have ha : a = -d u := by
      apply hinj
      have hdu : d (f u) = f (d u) := (congr($hf u)).symm
      have hdd : d (d c) = 0 := by simpa using congr($hd c)
      have h := congrArg d hu
      simp only [map_sub, hdd, sub_zero, hdu] at h
      rw [map_neg, h]
      exact eq_neg_of_add_eq_zero_left hz'.2
    refine ⟨(u, c), ?_⟩
    apply Prod.ext
    · simpa only [mappingCone_apply] using ha.symm
    · simpa only [mappingCone_apply] using (eq_sub_iff_add_eq.mp hu)
  · rw [homologyMap_surjective_iff]
    intro q hq
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective (range f) q
    obtain ⟨a, ha⟩ := (Submodule.mk_mem_ker_mapQ_iff b).mp hq
    have hda : d a = 0 := by
      apply hinj
      have h := congrArg d ha
      rw [← comp_apply, ← hf, comp_apply] at h
      have hdd : d (d b) = 0 := by simpa using congr($hd b)
      simpa only [map_zero] using h.trans hdd
    refine ⟨(-a, b), ?_, ?_⟩
    · simp only [mem_ker, mappingCone_apply, map_neg, hda, neg_zero, ha,
        neg_add_cancel, Prod.mk_zero_zero]
    · simp

/-- Homology of the mapping cone of an injective chain endomorphism is the homology of the
quotient by its range. The forward map is induced by projection onto the second coordinate. -/
noncomputable def mappingConeQuotientHomologyEquiv (hinj : Function.Injective f) :
    (mappingCone d d f).homology (mappingCone_comp_self f hd hd hf) ≃ₗ[S]
      d.quotientHomology hd (range f) (range_le_comap_of_commute d f hf) :=
  LinearEquiv.ofBijective _ (bijective_homologyMap_mappingConeQuotientProjection d hd f hf hinj)

/-- The cone-to-quotient comparison on a representing cone cycle. -/
@[simp]
theorem mappingConeQuotientHomologyEquiv_mk (hinj : Function.Injective f)
    (z : ker (mappingCone d d f)) :
    mappingConeQuotientHomologyEquiv d hd f hf hinj (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨Submodule.Quotient.mk z.1.2, by
        have hcomm := congr($(mappingConeQuotientProjection_comp d f hf) z.1)
        rw [comp_apply, mem_ker.mp z.2, map_zero, comp_apply,
          mappingConeQuotientProjection_apply] at hcomm
        exact hcomm.symm⟩ :=
  homologyMap_mk _ _ _ _ z

variable (g h : M →ₗ[S] M) (hg : g ∘ₗ d = d ∘ₗ g)
  (hh : f - g = d ∘ₗ h + h ∘ₗ d)

/-- The shear `(a, b) ↦ (a, b + h a)` identifies cones of homotopic endomorphisms. -/
def mappingConeHomotopyEquiv (h : M →ₗ[S] M) : (M × M) ≃ₗ[S] (M × M) where
  toFun x := (x.1, x.2 + h x.1)
  invFun x := (x.1, x.2 - h x.1)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by ext <;> simp [add_add_add_comm]
  map_smul' r x := by ext <;> simp [smul_add]

/-- Evaluation of the homotopy shear. -/
@[simp]
theorem mappingConeHomotopyEquiv_apply (x : M × M) :
    mappingConeHomotopyEquiv h x = (x.1, x.2 + h x.1) := (rfl)

/-- Evaluation of the inverse homotopy shear. -/
@[simp]
theorem mappingConeHomotopyEquiv_symm_apply (x : M × M) :
    (mappingConeHomotopyEquiv h).symm x = (x.1, x.2 - h x.1) := (rfl)

include hh in
/-- The shear intertwines the two mapping-cone differentials. -/
theorem mappingConeHomotopyEquiv_comp :
    (mappingConeHomotopyEquiv h).toLinearMap ∘ₗ mappingCone d d f =
      mappingCone d d g ∘ₗ (mappingConeHomotopyEquiv h).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simp only [comp_apply, LinearEquiv.coe_coe, mappingCone_apply,
      mappingConeHomotopyEquiv_apply]
  · have hx : f x.1 - g x.1 = d (h x.1) + h (d x.1) := congr($hh x.1)
    simp only [comp_apply, LinearEquiv.coe_coe, mappingConeHomotopyEquiv_apply,
      mappingCone_apply, map_add, map_neg]
    have hfx : f x.1 = g x.1 + d (h x.1) + h (d x.1) := by
      rw [sub_eq_iff_eq_add] at hx
      rw [hx]
      abel
    rw [hfx]
    abel

/-- Homotopic injective chain endomorphisms have isomorphic cokernel homologies.
The comparison factors through their mapping cones and uses the specified homotopy `h`. -/
noncomputable def quotientHomologyEquivOfHomotopy
    (hfi : Function.Injective f) (hgi : Function.Injective g) :
    d.quotientHomology hd (range f) (range_le_comap_of_commute d f hf) ≃ₗ[S]
      d.quotientHomology hd (range g) (range_le_comap_of_commute d g hg) :=
  (mappingConeQuotientHomologyEquiv d hd f hf hfi).symm.trans
    (((mappingConeHomotopyEquiv h).homologyEquiv
      (mappingCone_comp_self f hd hd hf) (mappingCone_comp_self g hd hd hg)
      (mappingConeHomotopyEquiv_comp d f g h hh)).trans
        (mappingConeQuotientHomologyEquiv d hd g hg hgi))

/-- The quotient comparison on a cone cycle. In particular it fixes the class of an
actual cycle of `d`, represented by `(0, b)` in either cone. -/
theorem quotientHomologyEquivOfHomotopy_quotientHomologyClass
    (hfi : Function.Injective f) (hgi : Function.Injective g)
    (z : ker (mappingCone d d f)) :
    quotientHomologyEquivOfHomotopy d hd f hf g h hg hh hfi hgi
        (quotientHomologyClass hd (range_le_comap_of_commute d f hf) z.1.2 (by
          have hz : f z.1.1 + d z.1.2 = 0 := by
            simpa only [mappingCone_apply, Prod.snd_zero] using congrArg Prod.snd (mem_ker.mp z.2)
          exact ⟨-z.1.1, by simpa only [map_neg] using (eq_neg_of_add_eq_zero_right hz).symm⟩)) =
      quotientHomologyClass hd (range_le_comap_of_commute d g hg)
        (z.1.2 + h z.1.1) (by
          have hc := congr($(mappingConeHomotopyEquiv_comp d f g h hh) z.1)
          rw [comp_apply, mem_ker.mp z.2, map_zero, comp_apply] at hc
          have hz : g z.1.1 + d (z.1.2 + h z.1.1) = 0 :=
            by simpa only [mappingCone_apply, LinearEquiv.coe_coe, mappingConeHomotopyEquiv_apply,
              Prod.snd_zero] using
              (congrArg Prod.snd hc).symm
          exact ⟨-z.1.1, by simpa only [map_neg] using (eq_neg_of_add_eq_zero_right hz).symm⟩) := by
  have hclass := mappingConeQuotientHomologyEquiv_mk d hd f hf hfi z
  rw [quotientHomologyClass_def, ← hclass]
  unfold quotientHomologyEquivOfHomotopy
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply,
    LinearEquiv.homologyEquiv_mk, mappingConeQuotientHomologyEquiv_mk]
  simp only [mappingConeHomotopyEquiv_apply, quotientHomologyClass_def]

end LinearMap
