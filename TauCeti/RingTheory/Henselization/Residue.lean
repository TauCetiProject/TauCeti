/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Algebra

/-!
# The closed fibre of a henselization

The henselization of a pair has the same quotient by its extended ideal as the original ring.
This identifies the closed fibre before proving that the colimit pair is henselian.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R]

private def reducedAlgHom (I : Ideal R) (B : Neighbourhood.{u, u} I) :
    (R ⧸ I) →ₐ[R] (B.obj ⧸ I.map (algebraMap R B.obj)) where
  toRingHom := reducedMap I B.obj
  commutes' r := reducedMap_mk I B.obj r

private noncomputable def residueEquiv (I : Ideal R) (B : Neighbourhood.{u, u} I) :
    (R ⧸ I) ≃ₐ[R] (B.obj ⧸ I.map (algebraMap R B.obj)) :=
  AlgEquiv.ofBijective (reducedAlgHom I B) ((isNeighbourhood_iff I B.obj).mp B.property).2

@[simp]
private theorem residueEquiv_mk (I : Ideal R) (B : Neighbourhood.{u, u} I) (r : R) :
    residueEquiv I B (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map (algebraMap R B.obj)) (algebraMap R B.obj r) := by
  exact reducedMap_mk I B.obj r

private noncomputable def residueMap (I : Ideal R) (B : Neighbourhood.{u, u} I) :
    B.obj →ₐ[R] R ⧸ I :=
  (residueEquiv I B).symm.toAlgHom.comp
    (Ideal.Quotient.mkₐ R (I.map (algebraMap R B.obj)))

@[simp]
private theorem residueMap_apply (I : Ideal R) (B : Neighbourhood.{u, u} I) (b : B.obj) :
    residueMap I B b =
      (residueEquiv I B).symm
        (Ideal.Quotient.mk (I.map (algebraMap R B.obj)) b) :=
  (rfl)

private theorem residueMap_naturality (I : Ideal R) {B C : Neighbourhood.{u, u} I}
    (f : B ⟶ C) : (residueMap I C).comp f.hom.hom = residueMap I B := by
  apply AlgHom.ext
  intro b
  have h := quotient_mk_eq_of_reducedMap_surjective I
    ((isNeighbourhood_iff I B.obj).mp B.property).2.2
    ((residueMap I C).comp f.hom.hom) (residueMap I B) b
  rw [Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self, Ideal.Quotient.eq,
    Ideal.mem_bot, sub_eq_zero] at h
  exact h

private noncomputable def residueCocone (I : Ideal R) :
    Cocone ((IsNeighbourhood I).ι) where
  pt := CommAlgCat.of R (R ⧸ I)
  ι :=
    { app := fun B ↦ CommAlgCat.ofHom (residueMap I B)
      naturality := fun _ _ f ↦ CommAlgCat.hom_ext (residueMap_naturality I f) }

private noncomputable def residueDesc (I : Ideal R) : algebra I →ₐ[R] R ⧸ I :=
  desc I (residueCocone I)

@[simp]
private theorem residueDesc_stage (I : Ideal R) (B : Neighbourhood.{u, u} I) :
    (residueDesc I).comp (stage I B) = residueMap I B := by
  exact desc_comp_stage I (residueCocone I) B

private theorem residueDesc_surjective (I : Ideal R) : Function.Surjective (residueDesc I) := by
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨algebraMap R (algebra I) r, (residueDesc I).commutes r⟩

private theorem ker_residueDesc (I : Ideal R) :
    RingHom.ker (residueDesc I) = extended I := by
  apply le_antisymm
  · intro x hx
    obtain ⟨B, b, rfl⟩ := exists_stage_eq I x
    have hb : residueMap I B b = 0 := by
      rw [RingHom.mem_ker] at hx
      rw [← DFunLike.congr_fun (residueDesc_stage I B) b]
      exact hx
    have hq : Ideal.Quotient.mk (I.map (algebraMap R B.obj)) b = 0 := by
      apply (residueEquiv I B).symm.injective
      rw [map_zero, ← residueMap_apply]
      exact hb
    have hbI : b ∈ I.map (algebraMap R B.obj) := Ideal.Quotient.eq_zero_iff_mem.mp hq
    rw [← map_stage_map_algebraMap I B]
    exact Ideal.mem_map_of_mem _ hbI
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hr

/-- An element belongs to the extended ideal of the henselization exactly when it comes from
the extended ideal at some étale neighbourhood. -/
theorem mem_extended_iff_exists_stage (I : Ideal R) (x : algebra I) :
    x ∈ extended I ↔
      ∃ (B : Neighbourhood.{u, u} I) (b : B.obj),
        b ∈ I.map (algebraMap R B.obj) ∧ stage I B b = x := by
  constructor
  · intro hx
    have hxker : x ∈ RingHom.ker (residueDesc I) := by
      rw [ker_residueDesc I]
      exact hx
    obtain ⟨B, b, hb⟩ := exists_stage_eq I x
    refine ⟨B, b, ?_, hb⟩
    have hzero : residueMap I B b = 0 := by
      rw [RingHom.mem_ker] at hxker
      calc
        residueMap I B b = residueDesc I (stage I B b) :=
          (DFunLike.congr_fun (residueDesc_stage I B) b).symm
        _ = residueDesc I x := congrArg (residueDesc I) hb
        _ = 0 := hxker
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (residueEquiv I B).symm.injective
    rw [map_zero, ← residueMap_apply]
    exact hzero
  · rintro ⟨B, b, hb, rfl⟩
    rw [← map_stage_map_algebraMap I B]
    exact Ideal.mem_map_of_mem _ hb

/-- The canonical map from the quotient of a ring by an ideal to the quotient of its
henselization by the extended ideal is bijective. -/
theorem quotient_bijective (I : Ideal R) :
    Function.Bijective (reducedMap I (algebra I)) := by
  let e : (algebra I ⧸ extended I) ≃ₐ[R] (R ⧸ I) :=
    (Ideal.quotientEquivAlgOfEq R (ker_residueDesc I).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (residueDesc_surjective I))
  have e_mk (a : algebra I) : e (Ideal.Quotient.mk (extended I) a) = residueDesc I a := by
    dsimp only [e]
    simp only [AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
      Ideal.quotientKerAlgEquivOfSurjective_mk]
  have he : reducedMap I (algebra I) = e.symm.toRingEquiv.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    apply e.injective
    rw [RingHom.comp_apply, reducedMap_mk, e_mk]
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    calc
      residueDesc I (algebraMap R (algebra I) r) = Ideal.Quotient.mk I r :=
        (residueDesc I).commutes r
      _ = e (e.symm (Ideal.Quotient.mk I r)) := (e.apply_symm_apply _).symm
  rw [he]
  exact e.symm.bijective

/-- An element of `R` maps into the extended ideal of the henselization exactly when it lies
in `I`. -/
@[simp]
theorem comap_extended (I : Ideal R) : (extended I).comap (algebraMap R (algebra I)) = I :=
  le_antisymm (fun _ hr ↦ mem_of_algebraMap_mem_map_of_reducedMap_injective I
    (quotient_bijective I).1 hr) Ideal.le_comap_map

/-- The extension of a maximal ideal to the henselization is a maximal ideal: the quotient by
it is the residue field `R ⧸ I`. -/
instance isMaximal_extended (I : Ideal R) [I.IsMaximal] : (extended I).IsMaximal := by
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact (RingEquiv.ofBijective _ (quotient_bijective I)).symm.toMulEquiv.isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mp ‹_›)

end TauCeti.Henselization
