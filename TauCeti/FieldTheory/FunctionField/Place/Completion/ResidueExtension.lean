/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Extension

/-!
# Residue extensions under completion

For a place `P'` of an integral extension `F' / F`, completion identifies not only
its residue field and the residue field of the place below, but also the embedding
between them. The two completion isomorphisms form a commutative square with the
original and completed residue embeddings.

Consequently the full relative residue degree and separability of the residue
extension are unchanged by completion. No finiteness or separability assumption
on the fields or their residues is needed. In particular, the degree here includes
any inseparable factor; this is the residue degree occurring in local different
and discriminant formulas.

The algebra structure of the completed valuation-ring extension is explicit, as
in `TauCeti.Place.completionIntegersExtensionAlgebra`. This is the intrinsic-place
counterpart of `IsDedekindDomain.HeightOneSpectrum.algebraMap_residueFieldEquivAdicCompletion`
and `IsDedekindDomain.HeightOneSpectrum.finrank_residueField_adicCompletion`: it uses
the chosen place completions directly, without choosing affine models or identifying
them with adic completions.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §3.
-/

public section

namespace TauCeti.Place

open IsLocalRing

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P' : Place k' F')

/-- The canonical residue-field identifications commute with the embedding induced
by the extension of valuation rings. -/
@[simp]
theorem residueFieldEquivCompletion_algebraMap
    (x : (P'.restrict k F).ResidueField) :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    P'.residueFieldEquivCompletion
        (algebraMap (P'.restrict k F).ResidueField P'.ResidueField x) =
      algebraMap (P'.restrict k F).completionPlace.ResidueField
        P'.completionPlace.ResidueField ((P'.restrict k F).residueFieldEquivCompletion x) := by
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  obtain ⟨x, rfl⟩ := residue_surjective x
  simp only [ResidueField.algebraMap_residue, residueFieldEquivCompletion_apply_residue,
    algebraMap_completionIntegersExtensionAlgebra,
    completionIntegersExtension_completionIntegersEmbedding]

/-- The residue embeddings commute with the canonical completion isomorphisms,
expressed as an equality of ring homomorphisms. -/
theorem algebraMap_comp_residueFieldEquivCompletion :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    (algebraMap (P'.restrict k F).completionPlace.ResidueField
      P'.completionPlace.ResidueField).comp
        (P'.restrict k F).residueFieldEquivCompletion.toRingHom =
      P'.residueFieldEquivCompletion.toRingHom.comp
        (algebraMap (P'.restrict k F).ResidueField P'.ResidueField) := by
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  exact RingHom.ext fun x ↦
    (P'.residueFieldEquivCompletion_algebraMap (k := k) (F := F) x).symm

/-- Completion preserves the full relative residue degree, including its inseparable
factor. The completed residue-field algebra is induced by the canonical local map
of completed valuation rings. -/
@[simp]
theorem finrank_residueField_completion :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    Module.finrank (P'.restrict k F).completionPlace.ResidueField
      P'.completionPlace.ResidueField = relativeDegree k F P' := by
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  rw [relativeDegree_def]
  exact (Algebra.finrank_eq_of_equiv_equiv
    (P'.restrict k F).residueFieldEquivCompletion.toRingEquiv
    P'.residueFieldEquivCompletion.toRingEquiv
    (P'.algebraMap_comp_residueFieldEquivCompletion (k := k) (F := F))).symm

/-- Completion preserves, rather than repairs, separability of the residue extension.
In particular, an inseparable residue extension remains inseparable after completion. -/
@[simp]
theorem isSeparable_residueField_completion_iff :
    letI := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
    Algebra.IsSeparable (P'.restrict k F).completionPlace.ResidueField
      P'.completionPlace.ResidueField ↔
        Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField := by
  let := (P'.restrict k F).completionIntegersExtensionAlgebra P' rfl
  exact (Algebra.IsSeparable.iff_of_equiv_equiv
    (P'.restrict k F).residueFieldEquivCompletion.toRingEquiv
    P'.residueFieldEquivCompletion.toRingEquiv
    (P'.algebraMap_comp_residueFieldEquivCompletion (k := k) (F := F))).symm

end TauCeti.Place
