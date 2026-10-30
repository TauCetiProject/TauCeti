/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import Mathlib.AlgebraicGeometry.Fiber
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import TauCeti.AlgebraicGeometry.Morphisms.Syntomic.Fiber
import TauCeti.CategoryTheory.MorphismProperty.Limits

/-!
# Nodality of syntomic curves is detected on fibres

A morphism syntomic of relative dimension one is at worst nodal exactly when each of its
fibres over a residue field `Spec κ(y)` is at worst nodal. Equivalently, it suffices that every
base change to a field is at worst nodal.

The singular-locus half of the nodal criterion is fibrewise: the formation of the relative
singular subscheme `Sing(X/S)` commutes with base change
(`AlgebraicGeometry.Scheme.isPullback_singularLocus_subschemeι`), and a morphism locally of finite
type is formally unramified as soon as its base changes to fields are
(`AlgebraicGeometry.Scheme.Hom.formallyUnramified_of_formallyUnramified_baseChange_field`). Hence
the singular subscheme `Sing(X/S) → S` is unramified exactly when every singular subscheme
`Sing(X_s/κ(s)) → Spec κ(s)` is.

Over a field `k`, the criterion asks that `X → Spec k` be syntomic of relative dimension one and
that its singular subscheme, cut out by the first Fitting ideal of `Ω_{X/k}`, be unramified over
`k`. Thus the theorem below reduces nodality of a syntomic family to nodality of the curves over
the residue fields of its base.

Syntomicity is itself detected on fibres for flat morphisms locally of finite presentation
(`TauCeti.AlgebraicGeometry.syntomicOfRelativeDimension_iff_flat_and_fiberToSpecResidueField`).
Combining the two gives the fibrewise criterion: a morphism is at worst nodal of relative dimension
one exactly when it is flat and locally of finite presentation and its fibres over the residue
fields are at worst nodal curves. Such fibres have pure dimension one
(`TauCeti.AlgebraicGeometry.PureRelativeDimension.of_syntomicOfRelativeDimension`).

## Main results

* `AtWorstNodalOfRelativeDimensionOne.of_baseChange_field`: a syntomic
  morphism of relative dimension one is at worst nodal if all its base changes to fields are.
* `atWorstNodalOfRelativeDimensionOne_iff_syntomic_and_fiberToSpecResidueField`: a morphism is
  at worst nodal of relative dimension one exactly when it is syntomic of relative dimension one
  and all its fibres over residue fields are at worst nodal.
* `atWorstNodalOfRelativeDimensionOne_iff_flat_and_fiberToSpecResidueField`: a morphism is at
  worst nodal of relative dimension one exactly when it is flat and locally of finite presentation
  and all its fibres over residue fields are at worst nodal.

## References

* [Stacks Project, Lemma 53.20.1, Tag 0C58](https://stacks.math.columbia.edu/tag/0C58): the
  equivalence of the fibrewise definition of families of nodal curves with the singular-locus
  criterion.
* The Stacks Project, Tag 02G8 (the fibre criterion for unramified morphisms).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- Over an affine base, a syntomic curve is at worst nodal if all its base changes along
field-valued points of the base are at worst nodal. -/
private theorem affineAtWorstNodalOfRelativeDimensionOne_of_baseChange_field
    {R : Type u} [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
    [hf : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R))]
    (h : ∀ (K : Type u) [Field K] [Algebra R K],
      AtWorstNodalOfRelativeDimensionOne
        (pullback.snd (X ↘ Spec (.of R)) (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    AffineAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of R)) := by
  have : Flat (X ↘ Spec (.of R)) := SyntomicOfRelativeDimension.flat 1 _
  have : LocallyOfFinitePresentation (X ↘ Spec (.of R)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 _
  refine AffineAtWorstNodalOfRelativeDimensionOne.mk hf ?_
  refine { toFormallyUnramified :=
    Scheme.Hom.formallyUnramified_of_formallyUnramified_baseChange_field _ fun K _ s ↦ ?_ }
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  algebraize [φ.hom]
  have hφ : φ = CommRingCat.ofHom (algebraMap R K) := by
    ext
    simp [RingHom.algebraMap_toAlgebra]
  rw [hφ]
  -- The base change `X'` of `X` to `K` is at worst nodal over `Spec K`.
  let X' := pullback (X ↘ Spec (.of R)) (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  let _ : X'.Over (Spec (.of K)) := ⟨pullback.snd _ _⟩
  have hK := (atWorstNodalOfRelativeDimensionOne_iff_of_isAffine _ (Iso.refl _)).mp (h K)
  simp only [Iso.refl_hom, Category.comp_id] at hK
  -- The structure morphism `X' ↘ Spec K` of the base change is `pullback.snd` by construction.
  replace hK : AffineAtWorstNodalOfRelativeDimensionOne (X' ↘ Spec (.of K)) := hK
  have : SyntomicOfRelativeDimension 1 (X' ↘ Spec (.of K)) := hK.syntomic
  have : Flat (X' ↘ Spec (.of K)) := SyntomicOfRelativeDimension.flat 1 _
  have : LocallyOfFinitePresentation (X' ↘ Spec (.of K)) :=
    SyntomicOfRelativeDimension.locallyOfFinitePresentation 1 _
  -- Its singular subscheme is the base change of `Sing(X/R)` along `Spec K ⟶ Spec R`.
  have H : IsPullback (pullback.fst _ _) (X' ↘ Spec (.of K)) (X ↘ Spec (.of R))
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := IsPullback.of_hasPullback _ _
  have hs := (Scheme.isPullback_singularLocus_subschemeι H).flip.paste_vert H
  -- Fixing the universe lets instance search find isomorphism invariance.
  have : MorphismProperty.RespectsIso @FormallyUnramified.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hu : FormallyUnramified (hs.isoPullback.hom ≫
      pullback.snd ((X.singularLocus R).subschemeι ≫ (X ↘ Spec (.of R)))
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
    rw [IsPullback.isoPullback_hom_snd]
    exact hK.unramified_singularLocus.toFormallyUnramified
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @FormallyUnramified.{u})
    hs.isoPullback.hom _).mp hu

/-- A morphism syntomic of relative dimension one is at worst nodal if its base change along every
field-valued point of the target is at worst nodal. -/
theorem AtWorstNodalOfRelativeDimensionOne.of_baseChange_field
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SyntomicOfRelativeDimension 1 f]
    (h : ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Y),
      AtWorstNodalOfRelativeDimensionOne (pullback.snd f s)) :
    AtWorstNodalOfRelativeDimensionOne f := by
  wlog hY : ∃ R, Y = Spec R generalizing X Y with H
  · rw [IsZariskiLocalAtTarget.iff_of_openCover
      (P := @AtWorstNodalOfRelativeDimensionOne) Y.affineCover]
    intro i
    refine H (pullback.snd f (Y.affineCover.f i)) (fun K _ s ↦ ?_) ⟨_, rfl⟩
    exact MorphismProperty.pullback_snd_pullback_snd (P := @AtWorstNodalOfRelativeDimensionOne)
      f _ _ _ (𝟙 _) (by simp) (h K (s ≫ Y.affineCover.f i))
  obtain ⟨R, rfl⟩ := hY
  refine (atWorstNodalOfRelativeDimensionOne_iff_of_isAffine (R := R) f (Iso.refl _)).mpr ?_
  simp only [Iso.refl_hom, Category.comp_id]
  let _ : X.Over (Spec (.of R)) := ⟨f⟩
  have : SyntomicOfRelativeDimension 1 (X ↘ Spec (.of R)) := ‹SyntomicOfRelativeDimension 1 f›
  exact affineAtWorstNodalOfRelativeDimensionOne_of_baseChange_field fun K _ _ ↦ h K _

/-- **The fibrewise criterion for nodality of syntomic curves.** A morphism is at worst nodal of
relative dimension one exactly when it is syntomic of relative dimension one and each of its fibres
`f.fiber y ⟶ Spec κ(y)` over a residue field is at worst nodal. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_syntomic_and_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AtWorstNodalOfRelativeDimensionOne f ↔
      SyntomicOfRelativeDimension 1 f ∧
        ∀ y : Y, AtWorstNodalOfRelativeDimensionOne (f.fiberToSpecResidueField y) := by
  refine ⟨fun hf ↦ ⟨hf.syntomic, fun y ↦ MorphismProperty.pullback_snd _ _ hf⟩, ?_⟩
  rintro ⟨hf, h⟩
  refine AtWorstNodalOfRelativeDimensionOne.of_baseChange_field f fun K _ s ↦ ?_
  rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K Y s]
  exact MorphismProperty.pullback_snd_comp f _ _ (h _)

/-- **The fibrewise criterion for nodal curves.** A morphism is at worst nodal of relative
dimension one exactly when it is flat and locally of finite presentation and each of its fibres
`f.fiber y ⟶ Spec κ(y)` over a residue field is at worst nodal. -/
theorem atWorstNodalOfRelativeDimensionOne_iff_flat_and_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AtWorstNodalOfRelativeDimensionOne f ↔ Flat f ∧ LocallyOfFinitePresentation f ∧
      ∀ y : Y, AtWorstNodalOfRelativeDimensionOne (f.fiberToSpecResidueField y) := by
  rw [atWorstNodalOfRelativeDimensionOne_iff_syntomic_and_fiberToSpecResidueField,
    syntomicOfRelativeDimension_iff_flat_and_fiberToSpecResidueField]
  exact ⟨fun ⟨⟨hfl, hfp, _⟩, h⟩ ↦ ⟨hfl, hfp, h⟩,
    fun ⟨hfl, hfp, h⟩ ↦ ⟨⟨hfl, hfp, fun y ↦ (h y).syntomic⟩, h⟩⟩

end TauCeti.AlgebraicGeometry
