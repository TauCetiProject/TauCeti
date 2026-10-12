/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.RootDatum

/-!
# Integral adjoint root lines of the special linear group

The diagonal torus of `SL_{r+1}` acts on its tangent Lie algebra by conjugation. Over any
commutative base ring, its root character `ε_i - ε_j` has exactly the matrix-unit line
`R E_ij` as its eigenspace. The assertion uses the universal torus point over its coordinate
ring, rather than just rational points: distinct characters remain distinguishable in
small characteristic and over nonreduced rings.

`adDerivation_universalDiagonalTorus_eq_iff` characterizes every character's eigenspace by
vanishing of matrix entries of the wrong weight. `adDerivation_universalDiagonalTorus_root_iff`
identifies each root eigenspace with the span of the normalized matrix unit in the existing
tangent-matrix equivalence. In particular, this supplies the integral root-line calculation
needed to normalize root vectors in a pinning.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1 and Example 21.2.
* B. Conrad, *Reductive Group Schemes*, §5.1 (root spaces and pinnings).
* The entrywise character comparison follows
  `TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Classification`, here applied to
  the tangent Lie functor over arbitrary commutative rings.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] {r : ℕ}

private theorem pointInCounitAlgebra_universalDiagonalTorus :
    Derivation.pointInCounitAlgebra
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))
        (toConv ((diagonalTorusCoordinateMap r R).hom :
          coordinateHopfAlgebra R (r + 1) →ₐ[R]
            MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))) =
      (Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R (r + 1))
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))).symm
          (diagonalTorusPoints r R _ (toConv (AlgHom.id R _))) := by
  apply WithConv.ofConv_injective
  ext h
  rw [Derivation.pointInCounitAlgebra_apply,
    Bialgebra.CounitAlgebra.pointsMulEquiv_symm_apply,
    Bialgebra.CounitAlgebra.algEquivSelf_symm_apply, diagonalTorusPoints_apply,
    CommHopfAlgCat.mapPointsFunctor_app_apply_apply]
  rw [AlgHom.id_apply]
  -- The remaining coercion is the algebra-hom component of the categorical morphism.
  rfl

/-- A tangent vector transforms by the character `α` of the diagonal torus exactly
when all its entries of a different character vanish. The action is tested at the universal
torus point, after extending the coefficients to the torus coordinate algebra. -/
theorem adDerivation_universalDiagonalTorus_eq_iff
    (α : Multiplicative (ULift.{u} (Fin r) →₀ ℤ))
    (d : Derivation R (coordinateHopfAlgebra R (r + 1))
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R (r + 1)) R)) :
    Derivation.adDerivation
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))
        ((Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R (r + 1))
          (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))).symm
          (diagonalTorusPoints r R _ (toConv (AlgHom.id R _))))
        (Derivation.mapValue (Algebra.ofId R _) d) =
      MonoidAlgebra.single α (1 : R) • Derivation.mapValue (Algebra.ofId R _) d ↔
    ∀ i j : Fin (r + 1),
      SplitTorus.weightCharacter (diagonalTorusWeight r i - diagonalTorusWeight r j) ≠ α →
        (tangentMatrix (r + 1) d : Matrix (Fin (r + 1)) (Fin (r + 1)) R) i j = 0 := by
  rw [tangentMatrix_apply_coe]
  have hπ := congrArg (fun f => f.hom)
    (coordinateMap_comp_diagonalTorusCoordinateMap r R)
  -- Use the coefficient ring consistently while identifying its counit-valued universal point.
  have hpoint := pointInCounitAlgebra_universalDiagonalTorus (R := R) (r := r)
  simpa only [hpoint] using
    HopfIdeal.adDerivation_universalWeightTorus_eq_iff (definingHopfIdeal R (r + 1))
      (diagonalTorusWeight r) (diagonalTorusCoordinateMap r R).hom hπ α d

/-- The adjoint eigenspace of every root of `SL_{r+1}` over any commutative base ring is
exactly the line spanned by its normalized matrix unit. The tangent-matrix equivalence
identifies this with a line in the tangent Lie algebra of the group scheme. -/
@[simp]
theorem adDerivation_universalDiagonalTorus_root_iff
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (d : Derivation R (coordinateHopfAlgebra R (r + 1))
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R (r + 1)) R)) :
    Derivation.adDerivation
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))
        ((Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R (r + 1))
          (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))).symm
          (diagonalTorusPoints r R _ (toConv (AlgHom.id R _))))
        (Derivation.mapValue (Algebra.ofId R _) d) =
      MonoidAlgebra.single (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) (1 : R) •
        Derivation.mapValue (Algebra.ofId R _) d ↔
      tangentMatrix (r + 1) d ∈
        R ∙ LieAlgebra.SpecialLinear.single p.1.1 p.1.2 p.2 (1 : R) := by
  classical
  rw [adDerivation_universalDiagonalTorus_eq_iff]
  simp only [ne_eq, weightCharacter_diagonalTorusWeight_sub_eq_root_iff]
  constructor
  · intro h
    rw [Submodule.mem_span_singleton]
    refine ⟨(tangentMatrix (r + 1) d : Matrix (Fin (r + 1)) (Fin (r + 1)) R) p.1.1 p.1.2, ?_⟩
    apply Subtype.ext
    ext a b
    simp only [SetLike.val_smul, LieAlgebra.SpecialLinear.val_single, Matrix.smul_apply,
      Matrix.single_apply, smul_eq_mul]
    by_cases hab : a = p.1.1 ∧ b = p.1.2
    · obtain ⟨rfl, rfl⟩ := hab
      simp
    · have hab' : ¬ (p.1.1 = a ∧ p.1.2 = b) := by tauto
      simp [hab', h a b hab]
  · intro h a b hab
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    have hentry := congrArg
      (fun X : LieAlgebra.SpecialLinear.sl (Fin (r + 1)) R =>
        (X : Matrix (Fin (r + 1)) (Fin (r + 1)) R) a b) hc
    have hab' : ¬ (p.1.1 = a ∧ p.1.2 = b) := by tauto
    simpa [SetLike.val_smul, LieAlgebra.SpecialLinear.val_single, Matrix.single_apply, hab']
      using hentry.symm

end

end TauCeti.SpecialLinear
