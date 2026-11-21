/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine.Scaling
public import TauCeti.AlgebraicGeometry.AbelianVariety.Albanese
import TauCeti.AlgebraicGeometry.AbelianVariety.MorphismGroup
import TauCeti.AlgebraicGeometry.Rigidity.Relative
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Rational curves in abelian varieties

Every morphism from the native projective line over a field to an abelian variety is
constant. Consequently, every pointed morphism is the identity section, and the trivial
abelian variety has the Albanese property for the projective line with any rational base point.

For scaling `s`, rigidity makes the defect `(s ≫ f) * (pr₁ ≫ f)⁻¹` depend only on the Laurent
parameter. The fixed section `[0 : 1]` makes that defect trivial. The dense orbit of `[1 : 1]`
then determines `f` globally. The native rigidity theorem works over arbitrary fields, so
no algebraic-closure descent is needed.

## Main declarations

* `projectiveLine.eq_toUnit_comp`: a morphism equals its constant value at any rational point.
* `projectiveLine.existsUnique_constant`: the unique constant through which a morphism factors.
* `projectiveLine.eq_one_of_comp_eq_one`: a pointed morphism is trivial.
* `AbelianVariety.isAlbanese_projectiveLine`: the trivial abelian variety is an Albanese variety.

## References

* The Stacks Project, Tag 0BF6 (the rigidity lemma).
* J. S. Milne, *Jacobian varieties*, Section 6 (the Albanese universal property).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace projectiveLine

section Ring

variable {k : Type u} [CommRing k]

/-- The Laurent-parameter scheme as an object over the coefficient scheme. -/
private noncomputable abbrev torusOver (k : Type u) [CommRing k] : Over (Spec (.of k)) :=
  Over.mk (scalingToBase k)

/-- The native infinity section as a morphism in the over category. -/
private noncomputable def infinityOver (k : Type u) [CommRing k] :
    𝟙_ (Over (Spec (.of k))) ⟶ toOver k :=
  Over.homMk (infinitySection k) (infinitySection_over k)

/-- The section `[1 : 1]` as a morphism in the over category. -/
private noncomputable def oneOver (k : Type u) [CommRing k] :
    𝟙_ (Over (Spec (.of k))) ⟶ toOver k :=
  Over.homMk (polynomialPoint k (RingHom.id k) 1 1) (by
    simpa using polynomialPoint_over k (RingHom.id k) 1 1)

/-- The parameter section at one as a morphism in the over category. -/
private noncomputable def unitOver (k : Type u) [CommRing k] :
    𝟙_ (Over (Spec (.of k))) ⟶ torusOver k :=
  Over.homMk (scalingUnit k) (scalingUnit_over k)

/-- The torus chart as a morphism in the over category. -/
private noncomputable def torusInclusionOver (k : Type u) [CommRing k] :
    torusOver k ⟶ toOver k :=
  Over.homMk (torusInclusion k) (torusInclusion_over k)

/-- The scaling family as a morphism in the over category. -/
private noncomputable def scalingOver (k : Type u) [CommRing k] :
    toOver k ⊗ torusOver k ⟶ toOver k :=
  Over.homMk (scaling k) (scaling_over k)

private lemma scalingOver_at_unit :
    lift (𝟙 (toOver k)) (toUnit (toOver k) ≫ unitOver k) ≫ scalingOver k =
      𝟙 (toOver k) := by
  apply Over.OverMorphism.ext
  exact scaling_at_unit k

private lemma scalingOver_fixes_infinity :
    lift (toUnit (torusOver k) ≫ infinityOver k) (𝟙 (torusOver k)) ≫ scalingOver k =
      toUnit (torusOver k) ≫ infinityOver k := by
  apply Over.OverMorphism.ext
  exact scaling_fixes_infinity k

private lemma scalingOver_at_one :
    lift (toUnit (torusOver k) ≫ oneOver k) (𝟙 (torusOver k)) ≫ scalingOver k =
      torusInclusionOver k := by
  apply Over.OverMorphism.ext
  exact scaling_at_one k

end Ring

variable {k : Type u} [Field k]

private lemma scalingOver_comp (A : AbelianVariety k) (f : toOver k ⟶ A.toOver) :
    scalingOver k ≫ f = fst (toOver k) (torusOver k) ≫ f := by
  have : IsProper (toOver k).hom :=
    SymmetricAlgebra.instIsProperOver k (Fin 2 → k)
  have : GeometricallyIntegral (toOver k).hom := geometricallyIntegral k
  have : LocallyOfFiniteType (torusOver k).hom := scalingToBase_locallyOfFiniteType k
  have : GeometricallyIntegral (torusOver k).hom := scalingToBase_geometricallyIntegral k
  let d : toOver k ⊗ torusOver k ⟶ A.toOver :=
    (scalingOver k ≫ f) * (fst (toOver k) (torusOver k) ≫ f)⁻¹
  have hd : lift (𝟙 (toOver k)) (toUnit (toOver k) ≫ unitOver k) ≫ d =
      toUnit (toOver k) ≫ η[A.toOver] := by
    simp only [d, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      scalingOver_at_unit, lift_fst, Category.id_comp, mul_inv_cancel, Hom.one_def]
  have h := eq_snd_comp_lift_comp d (infinityOver k) (unitOver k) η[A.toOver] hd
  have hf : lift (toUnit (torusOver k) ≫ infinityOver k) (𝟙 (torusOver k)) ≫ d = 1 := by
    simp only [d, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc,
      scalingOver_fixes_infinity, lift_fst, mul_inv_cancel]
  have hd1 : d = 1 := by rw [h, hf, MonObj.comp_one]
  exact mul_inv_eq_one.mp hd1

/-- Every morphism from the native projective line to an abelian variety is its constant value at
any rational point. -/
lemma eq_toUnit_comp (A : AbelianVariety k) (f : toOver k ⟶ A.toOver)
    (p : 𝟙_ (Over (Spec (.of k))) ⟶ toOver k) :
    f = toUnit (toOver k) ≫ p ≫ f := by
  have hinv := scalingOver_comp A f
  have ht : torusInclusionOver k ≫ f = toUnit (torusOver k) ≫ oneOver k ≫ f := by
    have h := congrArg (fun g ↦
      lift (toUnit (torusOver k) ≫ oneOver k) (𝟙 (torusOver k)) ≫ g) hinv
    simpa only [← Category.assoc, scalingOver_at_one, lift_fst] using h
  have hc : f = toUnit (toOver k) ≫ oneOver k ≫ f := by
    apply Over.OverMorphism.ext
    apply ext_of_isSchemeTheoreticallyDominant (torusInclusion k) A.toOver.hom
    · exact (Over.w f).trans (Over.w (toUnit (toOver k) ≫ oneOver k ≫ f)).symm
    · have he := congrArg Over.Hom.left ht
      simp only [Over.comp_left, Over.toUnit_left, toOver_hom] at he ⊢
      simp only [torusInclusionOver, torusOver, Over.homMk_left] at he
      rw [torusInclusion_over_assoc]
      exact he
  have hp : p ≫ f = oneOver k ≫ f := by
    have h := congrArg (fun g ↦ p ≫ g) hc
    simpa only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp] using h
  rw [hp]
  exact hc

/-- Every morphism from the native projective line to an abelian variety factors through a unique
constant. -/
lemma existsUnique_constant (A : AbelianVariety k) (f : toOver k ⟶ A.toOver) :
    ∃! c : 𝟙_ (Over (Spec (.of k))) ⟶ A.toOver, f = toUnit (toOver k) ≫ c := by
  refine ⟨infinityOver k ≫ f, eq_toUnit_comp A f (infinityOver k), ?_⟩
  intro c hc
  have h := congrArg (fun g ↦ infinityOver k ≫ g) hc
  simpa only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp] using h.symm

/-- Every pointed morphism from the native projective line to an abelian variety is trivial. -/
lemma eq_one_of_comp_eq_one (A : AbelianVariety k)
    {p : 𝟙_ (Over (Spec (.of k))) ⟶ toOver k} (f : toOver k ⟶ A.toOver)
    (hf : p ≫ f = η[A.toOver]) : f = 1 := by
  rw [eq_toUnit_comp A f p, hf]
  rfl

end projectiveLine

namespace AbelianVariety

variable {k : Type u} [Field k]

open scoped TauCeti.AlgebraicGeometry.AbelianVariety.Hom

/-- The trivial abelian variety has the Albanese property for the native projective line with any
rational base point. -/
lemma isAlbanese_projectiveLine (p : 𝟙_ (Over (Spec (.of k))) ⟶ projectiveLine.toOver k) :
    IsAlbanese p (1 : projectiveLine.toOver k ⟶ (trivial k).toOver) where
  comp_eq_one := by rw [MonObj.comp_one]; rfl
  existsUnique_fac A f hf := by
    have h := projectiveLine.eq_one_of_comp_eq_one A f hf
    refine ⟨1, ?_, fun φ _ ↦ Subsingleton.elim _ _⟩
    simp [h]

end AbelianVariety

end TauCeti.AlgebraicGeometry
