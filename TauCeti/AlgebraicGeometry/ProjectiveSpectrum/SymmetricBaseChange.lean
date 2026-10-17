/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
public import TauCeti.LinearAlgebra.SymmetricAlgebra.BaseChange

/-!
# Projective spectra of scalar-extended symmetric algebras

The graded equivalence between `S ⊗[R] Sym(M)` and `Sym(S ⊗[R] M)` induces an isomorphism
of their projective spectra, contravariantly. This compares the two graded presentations
and is an input to constructing algebraic families of projective linear transformations.

The convention is `Proj(Sym M)`: `M` is the module of linear homogeneous coordinates.
For the projective space of lines in a finite locally free module `V`, take `M = V∨`.
No finite generation or freeness is needed for the comparison of projective spectra.

One side is `Proj` of the scalar-extended graded ring. Composing with `Proj.baseChangeIso`
gives `Proj.symmetricAlgebraBaseChangeIso`, identifying the scheme fiber product over
`Spec R` for arbitrary coefficient extensions, with lemmas for both projections.
The construction combines `Proj.mapIso` with the graded symmetric-algebra base-change maps.
The comparison commutes with `Proj.toSpecZero`, and the degree-zero comparison preserves
the scalar copy of `S` in both presentations.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§7.d–7.f, projective actions and homogeneous spaces.
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti.SymmetricAlgebra
open scoped TensorProduct

namespace AlgebraicGeometry.Proj

universe u

variable (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The canonical graded symmetric-algebra base-change equivalence induces an isomorphism of
projective spectra. The tensor-product grading places `S` in degree zero. -/
noncomputable def symmetricAlgebraScalarTensorIso :
    Proj (homogeneousSubmodule S (S ⊗[R] M)) ≅
      Proj (fun n ↦ (homogeneousSubmodule R M n).baseChange S) :=
  mapIso scalarTensorGradedAlgHom.toGradedRingHom
    scalarTensorGradedAlgHomSymm.toGradedRingHom
    scalarTensorGradedAlgHom_rightInverse
    scalarTensorGradedAlgHom_leftInverse

/-- The forward projective morphism pulls back coordinates by the scalar-extension
equivalence. -/
@[simp]
theorem symmetricAlgebraScalarTensorIso_hom :
    (symmetricAlgebraScalarTensorIso R S M).hom =
      map scalarTensorGradedAlgHom.toGradedRingHom
        (HomogeneousIdeal.irrelevant_le_map_of_surjective _
          scalarTensorGradedAlgHom_rightInverse.surjective) := by
  rw [symmetricAlgebraScalarTensorIso, mapIso_hom]

/-- The inverse projective morphism pulls back coordinates by the inverse scalar-extension
equivalence. -/
@[simp]
theorem symmetricAlgebraScalarTensorIso_inv :
    (symmetricAlgebraScalarTensorIso R S M).inv =
      map scalarTensorGradedAlgHomSymm.toGradedRingHom
        (HomogeneousIdeal.irrelevant_le_map_of_surjective _
          scalarTensorGradedAlgHom_leftInverse.surjective) := by
  rw [symmetricAlgebraScalarTensorIso, mapIso_inv]

/-- The projective comparison lies over the induced comparison of degree-zero rings. -/
-- Use the comparison square before simplifying the isomorphism into `Proj.map`.
@[reassoc (attr := simp↓)]
theorem symmetricAlgebraScalarTensorIso_hom_toSpecZero :
    (symmetricAlgebraScalarTensorIso R S M).hom ≫
        toSpecZero (fun n ↦ (homogeneousSubmodule R M n).baseChange S) =
      toSpecZero (homogeneousSubmodule S (S ⊗[R] M)) ≫
        Spec.map (CommRingCat.ofHom
          scalarTensorGradedAlgHom.toGradedRingHom.gradedZeroRingHom) := by
  rw [symmetricAlgebraScalarTensorIso_hom, map_toSpecZero]

/-- The scalar-extended symmetric-algebra presentation identifies projective space with
its scheme fiber product after arbitrary extension of coefficients. -/
noncomputable def symmetricAlgebraBaseChangeIso :
    Proj (homogeneousSubmodule S (S ⊗[R] M)) ≅
      pullback (toSpecCoeff (homogeneousSubmodule R M))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  symmetricAlgebraScalarTensorIso R S M ≪≫ baseChangeIso (homogeneousSubmodule R M) S

/-- The projective projection of the comparison is the scalar-tensor comparison followed
by the projective coefficient projection. -/
@[reassoc (attr := simp)]
theorem symmetricAlgebraBaseChangeIso_hom_fst :
    (symmetricAlgebraBaseChangeIso R S M).hom ≫ pullback.fst _ _ =
      (symmetricAlgebraScalarTensorIso R S M).hom ≫
        baseChangeProjection (homogeneousSubmodule R M) S := by
  simp [symmetricAlgebraBaseChangeIso]

/-- The parameter projection of the comparison is the coefficient structure morphism. -/
@[reassoc (attr := simp)]
theorem symmetricAlgebraBaseChangeIso_hom_snd :
    (symmetricAlgebraBaseChangeIso R S M).hom ≫ pullback.snd _ _ =
      toSpecCoeff (homogeneousSubmodule S (S ⊗[R] M)) := by
  simp only [symmetricAlgebraBaseChangeIso, Iso.trans_hom, Category.assoc,
    baseChangeIso_hom_snd, toSpecCoeff_def,
    symmetricAlgebraScalarTensorIso_hom_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp,
    scalarTensorGradedAlgHom_gradedZeroRingHom_comp_algebraMap]

/-- The inverse comparison preserves the parameter projection. -/
@[reassoc (attr := simp)]
theorem symmetricAlgebraBaseChangeIso_inv_toSpecCoeff :
    (symmetricAlgebraBaseChangeIso R S M).inv ≫
        toSpecCoeff (homogeneousSubmodule S (S ⊗[R] M)) = pullback.snd _ _ := by
  rw [← symmetricAlgebraBaseChangeIso_hom_snd R S M, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Proj
