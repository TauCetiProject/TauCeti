/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ResidueField

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The scheme of generic points

For an arbitrary scheme, its scheme of generic points is the disjoint union of the spectra of
the residue fields at its component-generic points. Its structural morphism is a dominant
monomorphism, and the pullback along a morphism has image the points mapping to component-generic
points. This construction follows M. Temkin, *Tame distillation and desingularization by
p-alterations* (2017), §4.1.1, using Mathlib's `genericPoints`, scheme coproducts, and canonical
morphisms from spectra of residue fields.

## Main results

* `AlgebraicGeometry.Scheme.genericPointScheme`: the disjoint union of the residue-field
  spectra at the component-generic points of an arbitrary scheme.
* `AlgebraicGeometry.Scheme.fromGenericPointScheme`: its dominant monomorphism to the scheme.
* `AlgebraicGeometry.Scheme.Hom.range_pullback_fst_fromGenericPointScheme`: the first projection
  from its pullback has image the points mapping to component-generic points.
-/

public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- The disjoint union of the spectra of the residue fields at the component-generic points. -/
noncomputable abbrev genericPointScheme (X : Scheme.{u}) : Scheme.{u} :=
  ∐ fun x : genericPoints X ↦ Spec (X.residueField x)

/-- For an irreducible scheme, each generic-point summand is the whole generic-point scheme. -/
instance (X : Scheme.{u}) [IrreducibleSpace X] (x : genericPoints X) :
    IsIso (Sigma.ι (fun x : genericPoints X ↦ Spec (X.residueField x)) x) := by
  have : Subsingleton (genericPoints X) := by
    rw [genericPoints_eq_singleton]
    infer_instance
  let : Unique (genericPoints X) := uniqueOfSubsingleton x
  rw [Subsingleton.elim x default, ← coproductUniqueIso_inv]
  infer_instance

/-- The canonical morphism from the scheme of generic points to the original scheme. -/
noncomputable def fromGenericPointScheme (X : Scheme.{u}) : X.genericPointScheme ⟶ X :=
  Sigma.desc fun x ↦ X.fromSpecResidueField x

/-- On each component the structural morphism is the canonical residue-field morphism. -/
@[reassoc (attr := simp)]
theorem ι_fromGenericPointScheme (X : Scheme.{u}) (x : genericPoints X) :
    Sigma.ι (fun x : genericPoints X ↦ Spec (X.residueField x)) x ≫
      X.fromGenericPointScheme = X.fromSpecResidueField x := by
  unfold fromGenericPointScheme
  exact Sigma.ι_comp_desc _ x

/-- Every point of a residue-field component maps to its indexing generic point. -/
@[simp]
theorem fromGenericPointScheme_ι_apply (X : Scheme.{u})
    (x : genericPoints X) (t : Spec (X.residueField x)) :
    X.fromGenericPointScheme
      (Sigma.ι (fun x : genericPoints X ↦ Spec (X.residueField x)) x t) = x := by
  rw [← Hom.comp_apply, ι_fromGenericPointScheme, fromSpecResidueField_apply]

private theorem fromGenericPointScheme_comp_sigmaMk (X : Scheme.{u}) :
    ⇑X.fromGenericPointScheme ∘ sigmaMk _ =
      Subtype.val ∘ (Sigma.fst : (Σ x : genericPoints X, Spec (X.residueField x)) → _) := by
  funext ⟨x, t⟩
  simp

/-- The image of the scheme of generic points is precisely the set of component-generic points. -/
@[simp]
theorem range_fromGenericPointScheme (X : Scheme.{u}) :
    range X.fromGenericPointScheme = genericPoints X := by
  rw [← (sigmaMk _).surjective.range_comp (⇑X.fromGenericPointScheme),
    fromGenericPointScheme_comp_sigmaMk, Sigma.fst_surjective.range_comp, Subtype.range_val]

/-- The structural morphism from the scheme of generic points is a monomorphism. -/
instance (X : Scheme.{u}) : Mono X.fromGenericPointScheme := by
  have : SurjectiveOnStalks X.fromGenericPointScheme :=
    IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) fun _ ↦ inferInstance
  apply SurjectiveOnStalks.mono_of_injective
  apply Function.Injective.of_comp_right (g := sigmaMk _) _ (sigmaMk _).surjective
  rw [fromGenericPointScheme_comp_sigmaMk]
  exact Subtype.val_injective.comp Sigma.fst_injective

/-- The scheme of generic points has dense image in the original scheme. -/
instance (X : Scheme.{u}) : IsDominant X.fromGenericPointScheme := by
  rw [isDominant_iff, DenseRange, range_fromGenericPointScheme, dense_iff_closure_eq]
  exact genericPoints.closure

end Scheme

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}}

/-- The actual pullback of the target's generic-point scheme has as image the points lying
over component-generic points. -/
@[simp]
theorem range_pullback_fst_fromGenericPointScheme (f : X ⟶ Y) :
    range (pullback.fst f Y.fromGenericPointScheme) = f ⁻¹' genericPoints Y := by
  rw [Scheme.Pullback.range_fst, Scheme.range_fromGenericPointScheme]

end AlgebraicGeometry.Scheme.Hom
