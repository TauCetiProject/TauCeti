/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Ideal.Over

/-!
# Colimits of algebras with a fixed residue ring

Fix an ideal `I` of a commutative ring `R`. If the canonical maps `R / I → B / IB` are
isomorphisms for every algebra in a diagram, the same holds for its colimit. No filteredness
or nonemptiness assumption on the diagram is needed. This gives the residue-ring
identification in constructions by colimits of étale neighbourhoods.

Use `TauCeti.bijective_algebraMap_quotient_colimit I D hD` for bijectivity and
`TauCeti.quotientColimitEquiv I D hD` for the corresponding algebra equivalence, where
`hD` gives bijectivity of the canonical residue map at each object of `D`.

The proof constructs compatible residue maps to `R / I` and descends them through the
colimit. Maps into an algebra annihilated by `I` are unique whenever `R / I → B / IB` is
surjective.

## References

* [Stacks Project, Tag 0A02](https://stacks.math.columbia.edu/tag/0A02), the residue-ring
  identification in the construction of the henselization of a pair.
-/

public section

open CategoryTheory Limits

universe u v w t

namespace TauCeti

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- If `R / I → B / IB` is surjective, algebra maps from `B` to an algebra annihilated
by `I` are unique. -/
theorem algHom_ext_of_surjective_algebraMap_quotient (B : Type v) [CommRing B] [Algebra R B]
    (hB : Function.Surjective (algebraMap (R ⧸ I) (B ⧸ I.map (algebraMap R B))))
    {S : Type w} [Semiring S] [Algebra R S]
    (hI : I ≤ RingHom.ker (algebraMap R S)) (f g : B →ₐ[R] S) : f = g := by
  have kills (a : B →ₐ[R] S) : ∀ b ∈ I.map (algebraMap R B), a b = 0 := by
    intro b hb
    apply (Ideal.map_le_iff_le_comap.mpr ?_ : I.map (algebraMap R B) ≤
      RingHom.ker a.toRingHom) hb
    intro r hr
    simpa using hI hr
  let f' := Ideal.Quotient.liftₐ _ f (kills f)
  let g' := Ideal.Quotient.liftₐ _ g (kills g)
  have he : f' = g' := by
    apply AlgHom.ext
    intro b
    obtain ⟨r, rfl⟩ := hB b
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    simp [f', g']
  exact AlgHom.ext fun b ↦ congrArg (fun a ↦ a (Ideal.Quotient.mk _ b)) he

variable {J : Type v} [Category.{t} J] (D : J ⥤ CommAlgCat.{u} R) [HasColimit D]
    (hD : ∀ j, Function.Bijective
      (algebraMap (R ⧸ I) (D.obj j ⧸ I.map (algebraMap R (D.obj j)))))

include hD

/-- The compatible residue maps of the diagram. -/
private noncomputable def residueCocone : Cocone D where
  pt := CommAlgCat.of R (R ⧸ I)
  ι :=
    { app j := CommAlgCat.ofHom <|
        (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I)
          (D.obj j ⧸ I.map (algebraMap R (D.obj j)))) (by
            simpa only [IsScalarTower.coe_toAlgHom'] using hD j)).symm.toAlgHom.comp
          (Ideal.Quotient.mkₐ R _)
      naturality j k f := by
        apply CommAlgCat.hom_ext
        exact algHom_ext_of_surjective_algebraMap_quotient I (D.obj j) (hD j).2
          (by simp) _ _ }

/-- The residue map induced by the colimit universal property. -/
private noncomputable def colimitToResidue : ↑(colimit D) →ₐ[R] R ⧸ I :=
  (colimit.desc D (residueCocone I D hD)).hom

/-- Descend the colimit residue map through the extended ideal. -/
private noncomputable def quotientToResidue :
    (↑(colimit D) ⧸ I.map (algebraMap R ↑(colimit D))) →ₐ[R] R ⧸ I :=
  Ideal.Quotient.liftₐ _ (colimitToResidue I D hD) (by
    intro a ha
    apply (Ideal.map_le_iff_le_comap.mpr ?_ : I.map (algebraMap R ↑(colimit D)) ≤
      RingHom.ker (colimitToResidue I D hD).toRingHom) ha
    intro r hr
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mpr hr))

@[simp]
private theorem quotientToResidue_mk (a : ↑(colimit D)) :
    quotientToResidue I D hD (Ideal.Quotient.mk _ a) = colimitToResidue I D hD a :=
  (rfl)

private theorem quotientToResidue_leftInverse :
    Function.LeftInverse (quotientToResidue I D hD)
      (algebraMap (R ⧸ I) (↑(colimit D) ⧸ I.map (algebraMap R ↑(colimit D)))) := by
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.mk_algebraMap]
  exact (quotientToResidue I D hD).commutes r

/-- Colimits preserve the property that the canonical residue-algebra map is bijective. -/
theorem bijective_algebraMap_quotient_colimit : Function.Bijective
    (algebraMap (R ⧸ I) (↑(colimit D) ⧸ I.map (algebraMap R ↑(colimit D)))) := by
  have he : (IsScalarTower.toAlgHom R (R ⧸ I)
      (↑(colimit D) ⧸ I.map (algebraMap R ↑(colimit D)))).comp (colimitToResidue I D hD) =
      Ideal.Quotient.mkₐ R _ := by
    have he' : CommAlgCat.ofHom ((IsScalarTower.toAlgHom R (R ⧸ I)
        (↑(colimit D) ⧸ I.map (algebraMap R ↑(colimit D)))).comp (colimitToResidue I D hD)) =
        CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (I.map (algebraMap R ↑(colimit D)))) := by
      apply colimit.hom_ext
      intro j
      apply CommAlgCat.hom_ext
      exact algHom_ext_of_surjective_algebraMap_quotient I (D.obj j) (hD j).2 (by
        intro r hr
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hr)) _ _
    exact congrArg CommAlgCat.Hom.hom he'
  refine ⟨(quotientToResidue_leftInverse I D hD).injective, ?_⟩
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact ⟨colimitToResidue I D hD a, congrArg (fun f ↦ f a) he⟩

/-- The canonical residue-algebra equivalence for a colimit of algebras with residue ring
`R / I`. -/
noncomputable def quotientColimitEquiv :
    (R ⧸ I) ≃ₐ[R] ↑(colimit D) ⧸ I.map (algebraMap R ↑(colimit D)) :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I)
    (↑(colimit D) ⧸ I.map (algebraMap R ↑(colimit D)))) (by
      simpa only [IsScalarTower.coe_toAlgHom'] using
        bijective_algebraMap_quotient_colimit I D hD)

/-- The forward colimit residue equivalence is the canonical residue-algebra map. -/
@[simp]
theorem quotientColimitEquiv_toAlgHom :
    (quotientColimitEquiv I D hD).toAlgHom =
      IsScalarTower.toAlgHom R (R ⧸ I)
        (↑(colimit D) ⧸ I.map (algebraMap R ↑(colimit D))) := by
  simp [quotientColimitEquiv]

/-- The colimit residue equivalence is the structure map on representatives. -/
@[simp]
theorem quotientColimitEquiv_mk (r : R) :
    quotientColimitEquiv I D hD (Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map (algebraMap R ↑(colimit D))) (algebraMap R ↑(colimit D) r) :=
  (rfl)

/-- The inverse colimit residue equivalence agrees with the inverse residue equivalence at
each stage. -/
@[simp]
theorem quotientColimitEquiv_symm_mk_ι (j : J) (b : D.obj j) :
    (quotientColimitEquiv I D hD).symm
        (Ideal.Quotient.mk _ ((colimit.ι D j).hom b)) =
      (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I)
        (D.obj j ⧸ I.map (algebraMap R (D.obj j)))) (by
          simpa only [IsScalarTower.coe_toAlgHom'] using hD j)).symm
        (Ideal.Quotient.mk _ b) := by
  have hleft : Function.LeftInverse (quotientToResidue I D hD)
      (quotientColimitEquiv I D hD) := quotientToResidue_leftInverse I D hD
  have hinv : (quotientColimitEquiv I D hD).symm
      (Ideal.Quotient.mk _ ((colimit.ι D j).hom b)) =
      colimitToResidue I D hD ((colimit.ι D j).hom b) := by
    simpa only [AlgEquiv.apply_symm_apply, quotientToResidue_mk] using
      (hleft ((quotientColimitEquiv I D hD).symm
        (Ideal.Quotient.mk _ ((colimit.ι D j).hom b)))).symm
  rw [hinv]
  exact congrArg (fun f ↦ f.hom b) (colimit.ι_desc (residueCocone I D hD) j)

end TauCeti
