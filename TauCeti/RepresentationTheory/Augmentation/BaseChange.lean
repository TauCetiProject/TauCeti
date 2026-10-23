/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Augmentation.Projection
public import TauCeti.Algebra.MonoidAlgebra.ScalarExtension
import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact

/-!
# Scalar extension of the augmentation representation

Extending the coefficients of a sum-zero vector gives another sum-zero vector. This map
is equivariant for the permutation action and exhibits the
augmentation representation over the new ring as the base change of the old one.

In particular, the integral sum-zero permutation lattice spans its real counterpart.
This supplies the standard lattice for comparing logarithmic unit representations by
Tate's lattice lemma.

Augmentation splits as a map of modules after choosing an index, even when it does not
split equivariantly. Mathlib's `IsBaseChange.of_right_exact` then applies without a flatness
hypothesis.
-/

public noncomputable section

namespace TauCeti

section ScalarMap

variable (R S : Type*) [CommSemiring R] [Semiring S] [Algebra R S]
  (G X : Type*) [Monoid G] [MulAction G X]

/-- Extend the coefficients of a sum-zero permutation vector along `R → S`. -/
def augmentationScalarMap :
    (augmentationSubrepresentation R G X).toSubmodule →ₗ[R]
      (augmentationSubrepresentation S G X).toSubmodule :=
  ((monoidAlgebraScalarMap R S X).comp
    (augmentationSubrepresentation R G X).toSubmodule.subtype).codRestrict
      ((augmentationSubrepresentation S G X).toSubmodule.restrictScalars R)
      fun (v : (augmentationSubrepresentation R G X).toSubmodule) => by
        simpa using congrArg (algebraMap R S) (mem_augmentationSubrepresentation_iff.mp v.2)

/-- The underlying free-module vector is obtained by extending every coefficient. -/
@[simp]
theorem coe_augmentationScalarMap
    (v : (augmentationSubrepresentation R G X).toSubmodule) :
    (augmentationScalarMap R S G X v : MonoidAlgebra S X) =
      monoidAlgebraScalarMap R S X v :=
  (rfl)

/-- Scalar extension of augmentation vectors commutes with the permutation action. -/
@[simp]
theorem augmentationScalarMap_action (g : G)
    (v : (augmentationSubrepresentation R G X).toSubmodule) :
    augmentationScalarMap R S G X
        ((augmentationSubrepresentation R G X).toRepresentation g v) =
      (augmentationSubrepresentation S G X).toRepresentation g
        (augmentationScalarMap R S G X v) := by
  apply Subtype.ext
  simp only [coe_augmentationScalarMap, Subrepresentation.toRepresentation_apply,
    LinearMap.restrict_apply]
  apply MonoidAlgebra.coeff_injective
  have hcoeff (w : MonoidAlgebra R X) :
      (monoidAlgebraScalarMap R S X w).coeff =
        Finsupp.mapRange (algebraMap R S) (map_zero _) w.coeff := by
    ext x
    simp
  simpa [Representation.ofMulAction_def, hcoeff] using
    (Finsupp.mapDomain_mapRange (g • ·) (v : MonoidAlgebra R X).coeff
      (algebraMap R S) (map_zero _) (map_add _)).symm

end ScalarMap

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  (G X : Type*) [Monoid G] [MulAction G X]

/-- Scalar extension commutes with the augmentation representation. No flatness, finiteness
or nonemptiness assumption is required. -/
theorem isBaseChange_augmentationScalarMap :
    IsBaseChange S (augmentationScalarMap R S G X) := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · have : Subsingleton (MonoidAlgebra R X) := MonoidAlgebra.coeff_injective.subsingleton
    have : Subsingleton (MonoidAlgebra S X) := MonoidAlgebra.coeff_injective.subsingleton
    exact IsBaseChange.of_equiv (LinearEquiv.ofSubsingleton _ _) fun _ => Subsingleton.elim _ _
  · let x₀ := Classical.arbitrary X
    -- Project along a single basis vector. This splitting need not respect the group action.
    refine IsBaseChange.of_right_exact S (Algebra.linearMap R S)
      (monoidAlgebraScalarMap R S X) (augmentationScalarMap R S G X)
      (f := LinearMap.toSpanSingleton R _ (MonoidAlgebra.single x₀ 1))
      (g := augmentationProjection R G X x₀)
      (f' := LinearMap.toSpanSingleton S _ (MonoidAlgebra.single x₀ 1))
      (g' := augmentationProjection S G X x₀)
      ?_ ?_ (IsBaseChange.linearMap R S) (isBaseChange_monoidAlgebraScalarMap R S X)
      (exact_toSpanSingleton_augmentationProjection R G X x₀)
      (augmentationProjection_surjective R G X x₀)
      (exact_toSpanSingleton_augmentationProjection S G X x₀)
      (augmentationProjection_surjective S G X x₀)
    · apply LinearMap.ext
      intro r
      simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply,
        LinearMap.restrictScalars_apply, Algebra.linearMap_apply,
        LinearMap.map_smul_of_tower, monoidAlgebraScalarMap_single, map_one,
        algebraMap_smul]
    · apply LinearMap.ext
      intro v
      apply Subtype.ext
      simp only [LinearMap.comp_apply, coe_augmentationScalarMap, coe_augmentationProjection,
        LinearMap.restrictScalars_apply, map_sub, LinearMap.map_smul_of_tower,
        monoidAlgebraScalarMap_single, map_one, sumCoords_monoidAlgebraScalarMap,
        algebraMap_smul]

end TauCeti
