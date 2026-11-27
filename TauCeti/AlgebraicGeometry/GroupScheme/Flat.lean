/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.Geometrically.Reduced
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Equivariance
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Fiber
import TauCeti.AlgebraicGeometry.RationalPoint.Image
import TauCeti.CategoryTheory.Comma.Over
import TauCeti.CategoryTheory.Monoidal.Grp.Translation

/-!
# Flatness of surjective homomorphisms over a field

A surjective finite-type homomorphism of group schemes over a field is faithfully flat when
the target is geometrically reduced and locally of finite type over the field. Over an
algebraically closed field, surjectivity lifts rational points, so translations by source
points act transitively on the closed points of the target. Flatness on the generic flat open
then extends to the whole target by `Scheme.Hom.flat_of_transitive_closedPoints_of_finiteType`.
Over an arbitrary field, flatness descends from its algebraic closure.

For a finite, locally finitely presented surjective homomorphism over an arbitrary base, the
field theorem implies flatness by the fibrewise criterion, provided the source is flat and
the target is geometrically reduced and locally of finite type over the base.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 1.65(a).
* The Stacks Project, Tags 052A and 02L2, generic flatness and faithfully flat descent.
-/

public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory Topology
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Over.Hom

universe u

section Field

variable {k : Type u} [Field k] {G H : Over (Spec (.of k))}
  [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
  [QuasiCompact f.left] [LocallyOfFiniteType f.left] [Surjective f.left]
  [LocallyOfFiniteType H.hom]

private theorem flat_left_of_surjective_of_isAlgClosed [IsAlgClosed k] [IsReduced H.left] :
    Flat f.left := by
  let : JacobsonSpace H.left := LocallyOfFiniteType.jacobsonSpace H.hom
  let : IsLocallyNoetherian H.left := LocallyOfFiniteType.isLocallyNoetherian H.hom
  refine f.left.flat_of_transitive_closedPoints_of_finiteType
    (fun a ↦ (Over.forget _).mapIso (TauCeti.leftTranslation a))
    (fun a ↦ (Over.forget _).mapIso (TauCeti.leftTranslation (a ≫ f)))
    (fun a ↦ congrArg Over.Hom.left (TauCeti.leftTranslation_hom_comp f a)) ?_
  intro y z hy hz
  let y₀ : 𝟙_ _ ⟶ H := Over.homMk _ (pointOfClosedPoint_comp H.hom y hy)
  let z₀ : 𝟙_ _ ⟶ H := Over.homMk _ (pointOfClosedPoint_comp H.hom z hz)
  obtain ⟨a, ha⟩ := (f.left.exists_comp_eq_iff_mem_range (z₀ / y₀).left).mpr
    ((surjective_iff f.left).mp inferInstance _)
  let a₀ : 𝟙_ _ ⟶ G := Over.homMk a (by
    rw [← Over.w f, ← Category.assoc, ha]
    exact Over.w (z₀ / y₀))
  have ha₀ : a₀ ≫ f = z₀ / y₀ := Over.OverMorphism.ext ha
  have htranslate : y₀ ≫ (TauCeti.leftTranslation (a₀ ≫ f)).hom = z₀ := by simp [ha₀]
  let q : (𝟙_ (Over (Spec (.of k)))).left := IsLocalRing.closedPoint k
  have hy₀ : y₀.left q = y := pointOfClosedPoint_apply H.hom y hy q
  have hz₀ : z₀.left q = z := pointOfClosedPoint_apply H.hom z hz q
  refine ⟨a₀, ?_⟩
  simpa only [Functor.mapIso_hom, Over.forget_map, Over.comp_left, Scheme.Hom.comp_apply, hy₀, hz₀]
    using congrArg (fun g : (𝟙_ _ : Over (Spec (.of k))) ⟶ H ↦ g.left q) htranslate

/-- A surjective finite-type homomorphism over a field is flat if the target group scheme
is geometrically reduced and locally of finite type over the field. -/
theorem flat_left_of_surjective [GeometricallyReduced H.hom] : Flat f.left := by
  let p := Spec.algebraMap k (AlgebraicClosure k)
  let F := Over.pullback p
  let : QuasiCompact (F.map f).left := MorphismProperty.overPullbackMap p f ‹_›
  let : LocallyOfFiniteType (F.map f).left := MorphismProperty.overPullbackMap p f ‹_›
  let : Surjective (F.map f).left := MorphismProperty.overPullbackMap p f ‹_›
  let : LocallyOfFiniteType (F.obj H).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd H.hom p))
  exact MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact
    (Over.isPullback_pullback_map_left p f) (flat_left_of_surjective_of_isAlgClosed (F.map f))

end Field

/-- A finite, locally finitely presented, surjective homomorphism over an arbitrary base is flat
if the source is flat and the target is geometrically reduced and locally of finite type over
the base. -/
theorem flat_left_of_finite_of_surjective {S : Scheme.{u}} {G H : Over S} [GrpObj G] [GrpObj H]
    (f : G ⟶ H) [IsMonHom f] [Flat G.hom] [GeometricallyReduced H.hom] [LocallyOfFiniteType H.hom]
    [IsFinite f.left] [LocallyOfFinitePresentation f.left] [Surjective f.left] : Flat f.left := by
  let : Flat (f.left ≫ H.hom) := (Over.w f).symm ▸ inferInstanceAs (Flat G.hom)
  refine f.left.flat_of_flat_pullback_fiberι H.hom fun s ↦ ?_
  let p := S.fromSpecResidueField s
  let F := Over.pullback p
  let : IsFinite (F.map f).left := MorphismProperty.overPullbackMap p f ‹_›
  let : Surjective (F.map f).left := MorphismProperty.overPullbackMap p f ‹_›
  let : LocallyOfFiniteType (F.obj H).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd H.hom p))
  let : GeometricallyReduced (F.obj H).hom :=
    inferInstanceAs (GeometricallyReduced (pullback.snd H.hom p))
  have hf : Flat (F.map f).left := flat_left_of_surjective (k := S.residueField s) (F.map f)
  have h := (Over.isPullback_pullback_map_left p f).flip
  -- The fibre inclusion is the first projection of the pullback along the residue field.
  have : Flat (pullback.snd f.left (pullback.fst H.hom p)) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  exact this

end CategoryTheory.Over.Hom
