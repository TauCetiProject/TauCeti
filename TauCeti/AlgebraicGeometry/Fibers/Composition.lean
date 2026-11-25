/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Fibres of a composite morphism

For morphisms of schemes `j : Y ⟶ X` and `f : X ⟶ S` and a point `s` of `S`, the
scheme-theoretic fibre `(j ≫ f)⁻¹(s) = Y ×_S Spec κ(s)` maps to the fibre `f⁻¹(s)` over
`Spec κ(s)`, and this map is the base change of `j` along the embedding `f⁻¹(s) ⟶ X` of the
fibre. Hence a closed immersion `j` induces closed immersions of fibres. This is how properties
tested on the fibres of `f` restrict to closed subschemes of `X`.

The file also records that the fibres of a proper morphism are proper over their residue fields,
and that the embedding of a fibre is an isomorphism when `Spec κ(s) ⟶ S` is one.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.fiberCompMap j f s : (j ≫ f).fiber s ⟶ f.fiber s`: the map of
  fibres over `s`, compatible with the embeddings into `Y` and `X`
  (`Scheme.Hom.fiberCompMap_fiberι`) and with the maps to `Spec κ(s)`
  (`Scheme.Hom.fiberCompMap_fiberToSpecResidueField`);
* `AlgebraicGeometry.Scheme.Hom.isPullback_fiberCompMap`: the square formed by
  `fiberCompMap j f s`, `j` and the two fibre embeddings is cartesian;
* `AlgebraicGeometry.Scheme.Hom.isProper_fiberToSpecResidueField`: the fibres of a proper morphism
  are proper over the residue fields.
* `AlgebraicGeometry.Scheme.Hom.isIso_fiberι`: the embedding `f⁻¹(s) ⟶ X` of a fibre is an
  isomorphism when `Spec κ(s) ⟶ S` is one, for instance over the spectrum of a field.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y S : Scheme.{u}}

/-- The fibres of a proper morphism are proper over the residue fields. -/
instance isProper_fiberToSpecResidueField (f : X ⟶ S) [IsProper f] (s : S) :
    IsProper (f.fiberToSpecResidueField s) :=
  inferInstanceAs (IsProper (pullback.snd _ _))

/-- The embedding `f⁻¹(s) ⟶ X` of the fibre of `f : X ⟶ S` over `s` is an isomorphism when
`Spec κ(s) ⟶ S` is one: it is the base change of `Spec κ(s) ⟶ S` along `f`. -/
instance isIso_fiberι (f : X ⟶ S) (s : S) [IsIso (S.fromSpecResidueField s)] :
    IsIso (f.fiberι s) := by
  unfold Scheme.Hom.fiberι
  exact pullback_fst_iso_of_right_iso _ _

/-- The fibre over `s` of a composite `j ≫ f` maps to the fibre of `f` over `s`. It is the base
change of `j` along the embedding of the fibre of `f` (`Scheme.Hom.isPullback_fiberCompMap`). -/
def fiberCompMap (j : Y ⟶ X) (f : X ⟶ S) (s : S) : (j ≫ f).fiber s ⟶ f.fiber s :=
  pullback.map _ _ _ _ j (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The map of fibres `fiberCompMap j f s` lies over `j`. -/
@[reassoc (attr := simp)]
lemma fiberCompMap_fiberι (j : Y ⟶ X) (f : X ⟶ S) (s : S) :
    j.fiberCompMap f s ≫ f.fiberι s = (j ≫ f).fiberι s ≫ j :=
  pullback.lift_fst _ _ _

/-- The map of fibres `fiberCompMap j f s` lies over `Spec κ(s)`. -/
@[reassoc (attr := simp)]
lemma fiberCompMap_fiberToSpecResidueField (j : Y ⟶ X) (f : X ⟶ S) (s : S) :
    j.fiberCompMap f s ≫ f.fiberToSpecResidueField s = (j ≫ f).fiberToSpecResidueField s :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The fibre over `s` of a composite `j ≫ f` is the base change of `j` along the embedding of
the fibre of `f` over `s`. -/
theorem isPullback_fiberCompMap (j : Y ⟶ X) (f : X ⟶ S) (s : S) :
    IsPullback (j.fiberCompMap f s) ((j ≫ f).fiberι s) (f.fiberι s) j := by
  refine .of_right (h₁₂ := f.fiberToSpecResidueField s) (h₂₂ := f) ?_
    (fiberCompMap_fiberι j f s) (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip
  rw [fiberCompMap_fiberToSpecResidueField]
  exact (IsPullback.of_hasPullback (j ≫ f) (S.fromSpecResidueField s)).flip

/-- A closed immersion `j` induces closed immersions of the fibres of `j ≫ f` into those of
`f`. -/
instance isClosedImmersion_fiberCompMap (j : Y ⟶ X) [IsClosedImmersion j] (f : X ⟶ S) (s : S) :
    IsClosedImmersion (j.fiberCompMap f s) :=
  MorphismProperty.of_isPullback (isPullback_fiberCompMap j f s).flip ‹_›

end AlgebraicGeometry.Scheme.Hom
