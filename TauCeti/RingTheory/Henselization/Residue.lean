/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Algebra
public import TauCeti.RingTheory.Ideal.Quotient.Colimit

/-!
# The closed fibre of a henselization

The henselization of a pair has the same quotient by its extended ideal as the original ring
(`quotientEquiv`), giving a canonical surjective `R`-algebra map `toQuotient` onto `R ⧸ I` with
kernel `extended I`. This identifies the closed fibre before proving that the colimit pair is
henselian, by applying `Ideal.quotientColimitEquiv` to the small-model neighbourhood diagram.

## Main declarations

* `TauCeti.Henselization.quotientEquiv`: the canonical `R`-algebra isomorphism
  `(R ⧸ I) ≃ₐ[R] (algebra I ⧸ extended I)`.
* `TauCeti.Henselization.quotient_bijective`: bijectivity of `reducedMap I (algebra I)`.
* `TauCeti.Henselization.toQuotient`: the canonical surjective `R`-algebra map
  `algebra I →ₐ[R] R ⧸ I` with kernel `extended I`.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02)
-/

public section

open CategoryTheory Limits

universe u

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R]

/-- The canonical `R`-algebra isomorphism `(R ⧸ I) ≃ₐ[R] (algebra I ⧸ extended I)` induced by the
structure map of the henselization. -/
noncomputable def quotientEquiv (I : Ideal R) :
    (R ⧸ I) ≃ₐ[R] (algebra I ⧸ extended I) :=
  (I.quotientColimitEquiv (diagram I) (fun B ↦ by
    have he : algebraMap (R ⧸ I)
        ((diagram I).obj B ⧸ I.map (algebraMap R ((diagram I).obj B))) =
        reducedMap I ((diagram I).obj B) := by
      apply Ideal.Quotient.ringHom_ext
      apply RingHom.ext
      intro r
      simp only [RingHom.comp_apply, reducedMap_mk,
        Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.mk_algebraMap]
    rw [he]
    exact ((isNeighbourhood_iff I _).mp
      ((equivSmallModel (Neighbourhood.{u, u} I)).inverse.obj B).property).2)).trans
    (Ideal.quotientEquivAlg _ _
      (CommAlgCat.algEquivOfIso (algebraIsoColimitDiagram I).symm) (by
        rw [Ideal.map_map]
        exact congrArg (I.map ·) (algebraIsoColimitDiagram I).inv.hom.comp_algebraMap.symm))

/-- `quotientEquiv I` sends the class of `r` to the class of `algebraMap R (algebra I) r`. -/
@[simp]
theorem quotientEquiv_mk (I : Ideal R) (r : R) :
    quotientEquiv I (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (extended I) (algebraMap R (algebra I) r) := by
  simp [quotientEquiv]

/-- The canonical map from the quotient of a ring by an ideal to the quotient of its
henselization by the extended ideal is bijective. -/
theorem quotient_bijective (I : Ideal R) :
    Function.Bijective (reducedMap I (algebra I)) := by
  have he : reducedMap I (algebra I) = (quotientEquiv I).toRingEquiv.toRingHom := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro r
    simp [reducedMap_mk]
  rw [he]
  exact (quotientEquiv I).bijective

/-- The canonical surjective `R`-algebra map `algebra I →ₐ[R] R ⧸ I` factoring the quotient map
modulo `extended I` through `(quotientEquiv I).symm`. -/
noncomputable def toQuotient (I : Ideal R) : algebra I →ₐ[R] R ⧸ I :=
  (quotientEquiv I).symm.toAlgHom.comp (Ideal.Quotient.mkₐ R (extended I))

/-- The inverse of `quotientEquiv I` sends the class modulo `extended I` of `x` to
`toQuotient I x`. -/
@[simp]
theorem quotientEquiv_symm_mk (I : Ideal R) (x : algebra I) :
    (quotientEquiv I).symm (Ideal.Quotient.mk (extended I) x) = toQuotient I x := by
  simp [toQuotient]

/-- Composing `toQuotient I` with `quotientEquiv I` recovers the quotient map modulo
`extended I`. -/
@[simp]
theorem quotientEquiv_toQuotient (I : Ideal R) (x : algebra I) :
    quotientEquiv I (toQuotient I x) = Ideal.Quotient.mk (extended I) x :=
  (quotientEquiv I).apply_symm_apply _

/-- `toQuotient I` is surjective. -/
theorem toQuotient_surjective (I : Ideal R) : Function.Surjective (toQuotient I) :=
  (quotientEquiv I).symm.surjective.comp Ideal.Quotient.mk_surjective

/-- The kernel of `toQuotient I` is the extended ideal `extended I`. -/
@[simp]
theorem ker_toQuotient (I : Ideal R) : RingHom.ker (toQuotient I) = extended I := by
  ext x
  rw [RingHom.mem_ker, ← (quotientEquiv I).map_eq_zero_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- `toQuotient I` is the unique `R`-algebra map `algebra I →ₐ[R] R ⧸ I`. -/
theorem eq_toQuotient (I : Ideal R) (f : algebra I →ₐ[R] R ⧸ I) : f = toQuotient I :=
  hom_ext fun B ↦ B.property.algHom_ext (by simp [Ideal.Quotient.algebraMap_eq])

/-- An element belongs to the extended ideal of the henselization exactly when it comes from
the extended ideal at some étale neighbourhood. -/
theorem mem_extended_iff_exists_stage (I : Ideal R) (x : algebra I) :
    x ∈ extended I ↔
      ∃ (B : Neighbourhood.{u, u} I) (b : B.obj),
        b ∈ I.map (algebraMap R B.obj) ∧ stage I B b = x := by
  constructor
  · intro hx
    obtain ⟨B, b, rfl⟩ := exists_stage_eq I x
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_of_reducedMap_surjective I
      ((isNeighbourhood_iff I B.obj).mp B.property).2.2 b
    have hsub : stage I B b - algebraMap R (algebra I) r ∈ extended I := by
      rw [← map_stage_map_algebraMap I B]
      simpa using Ideal.mem_map_of_mem (stage I B).toRingHom hr
    have hrI : r ∈ I := mem_of_algebraMap_mem_map_of_reducedMap_injective I
      (quotient_bijective I).1 (by simpa using (extended I).sub_mem hx hsub)
    refine ⟨B, b, ?_, rfl⟩
    simpa using (I.map (algebraMap R B.obj)).add_mem hr (Ideal.mem_map_of_mem _ hrI)
  · rintro ⟨B, b, hb, rfl⟩
    rw [← map_stage_map_algebraMap I B]
    exact Ideal.mem_map_of_mem _ hb

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
