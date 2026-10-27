/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Node.SingularLocus
public import TauCeti.RingTheory.Node.Branches
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Etale.Pi
import Mathlib.Algebra.Ring.Fin
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The branch scheme of a split node

The inverse image of the singular subscheme of `Spec R[x,y]/(xy)` in its branch algebra
`Spec (R[t] × R[t])` is `Spec (R × R)`. Its morphism to the actual singular subscheme is
finite étale of degree two. This calculation retains the singular scheme structure over
arbitrary commutative bases, including nonreduced rings.

Over an integrally closed domain the branch inclusion is the normalization inclusion, by
`NodeAlgebra.isIntegralClosure_branchFractionMap` in `TauCeti.RingTheory.Node.Normalization`.
Thus the pullback also describes the inverse image of the singular subscheme in that
normalization. Over a general base the theorem concerns the branch inclusion only.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46, especially Lemma 53.19.4.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace TauCeti.NodeAlgebra

universe u

variable (R : Type u) [CommRing R]

/-- The two branch origins form the inverse image of the origin under the branch inclusion. -/
theorem isPullback_branchValues :
    IsPullback (Spec.map (CommRingCat.ofHom (branchValues R).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R (R × R))))
      (Spec.map (CommRingCat.ofHom (branchMap R).toRingHom))
      (Spec.map (CommRingCat.ofHom (origin R).toRingHom)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_branchValues R)

/-- The direct structural morphism of the split node chart, used by its singular locus. -/
local instance (priority := high) splitNodeSpecOverSpec :
    (Spec (.of (NodeAlgebra R 0))).Over (Spec (.of R)) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R 0)))

local instance : Flat (Spec (.of (NodeAlgebra R 0)) ↘ Spec (.of R)) := flat_spec 0
local instance : LocallyOfFinitePresentation
    (Spec (.of (NodeAlgebra R 0)) ↘ Spec (.of R)) := locallyOfFinitePresentation_spec 0
local instance : TauCeti.AlgebraicGeometry.PureRelativeDimension 1
    (Spec (.of (NodeAlgebra R 0)) ↘ Spec (.of R)) := pureRelativeDimension_spec 0

/-- The singular subscheme of the split node is the base itself. -/
def splitSingularLocusIso :
    ((Spec (.of (NodeAlgebra R 0))).singularLocus R).subscheme ≅ Spec (.of R) :=
  singularLocusIso (0 : R) ≪≫ Scheme.Spec.mapIso
    ((Ideal.quotEquivOfEq (by simp : Ideal.span {(0 : R)} = ⊥)).trans
      (RingEquiv.quotientBot R)).toCommRingCatIso.symm.op

/-- Under the split singular-locus identification, its inclusion is the origin point. -/
@[reassoc (attr := simp)]
theorem splitSingularLocusIso_inv_subschemeι :
    (splitSingularLocusIso R).inv ≫
      ((Spec (.of (NodeAlgebra R 0))).singularLocus R).subschemeι =
        Spec.map (CommRingCat.ofHom (origin R).toRingHom) := by
  simp only [splitSingularLocusIso, Iso.trans_inv, Category.assoc,
    singularLocusIso_inv_subschemeι]
  simp only [Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h : ((Ideal.quotientEquivAlgOfEq R
      (by simp : Ideal.span {(0 : R)} = ⊥)).trans
        (AlgEquiv.quotientBot R R)).toAlgHom.comp (evalZero (0 : R)) = origin R := by
    ext <;> simp
  exact congrArg AlgHom.toRingHom h

/-- The branch scheme over the singular subscheme of the split node. Its source is
`Spec (R × R)`, with one copy of the base for each branch. -/
def branchSchemeToSingularLocus :
    Spec (.of (R × R)) ⟶ ((Spec (.of (NodeAlgebra R 0))).singularLocus R).subscheme :=
  Spec.map (CommRingCat.ofHom (algebraMap R (R × R))) ≫ (splitSingularLocusIso R).inv

/-- The branch-scheme morphism is the diagonal algebra map under the singular-locus
identification. -/
@[reassoc (attr := simp)]
theorem branchSchemeToSingularLocus_comp_iso :
    branchSchemeToSingularLocus R ≫ (splitSingularLocusIso R).hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (R × R))) := by
  simp [branchSchemeToSingularLocus]

/-- The branch scheme is the scheme-theoretic inverse image of the actual relative singular
subscheme under the branch inclusion. -/
theorem isPullback_branchSchemeToSingularLocus :
    IsPullback (Spec.map (CommRingCat.ofHom (branchValues R).toRingHom))
      (branchSchemeToSingularLocus R)
      (Spec.map (CommRingCat.ofHom (branchMap R).toRingHom))
      ((Spec (.of (NodeAlgebra R 0))).singularLocus R).subschemeι := by
  refine (isPullback_branchValues R).of_iso (Iso.refl _) (Iso.refl _)
    (splitSingularLocusIso R).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp [branchSchemeToSingularLocus]
  · simp
  · simp

/-- The two branches vary étale over the singular subscheme. -/
instance etale_branchSchemeToSingularLocus : Etale (branchSchemeToSingularLocus R) := by
  let e : (Fin 2 → R) ≃ₐ[R] R × R :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo fun _ : Fin 2 ↦ R) (by intro r; rfl)
  have : Algebra.Etale R (R × R) := Algebra.Etale.of_equiv e
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  dsimp only [branchSchemeToSingularLocus]
  infer_instance

/-- The branch scheme is finite over the singular subscheme. -/
instance isFinite_branchSchemeToSingularLocus : IsFinite (branchSchemeToSingularLocus R) := by
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  dsimp only [branchSchemeToSingularLocus]
  infer_instance

/-- There are two branches over every point of the singular subscheme, counted by the
rank of the finite étale morphism. -/
theorem finrank_branchSchemeToSingularLocus
    (s : ((Spec (.of (NodeAlgebra R 0))).singularLocus R).subscheme) :
    (branchSchemeToSingularLocus R).finrank s = 2 := by
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) := by
    rw [← branchSchemeToSingularLocus_comp_iso]
    infer_instance
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) := by
    rw [← branchSchemeToSingularLocus_comp_iso]
    infer_instance
  have h : IsPullback (𝟙 (Spec (.of (R × R)))) (branchSchemeToSingularLocus R)
      (Spec.map (CommRingCat.ofHom (algebraMap R (R × R))))
      (splitSingularLocusIso R).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ h]
  have : Nontrivial R := ((splitSingularLocusIso R).hom s).nontrivial
  exact (Scheme.Hom.finrank_SpecMap_algebraMap R (R × R)
    ((splitSingularLocusIso R).hom s)).trans (by simp [Module.finrank_prod]; rfl)

end TauCeti.NodeAlgebra
