/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

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

open WithConv

namespace TauCeti.SpecialLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] {r : ℕ}

/-- The diagonal torus acts on each matrix entry of a tangent vector through the difference
of the corresponding standard weights. -/
theorem tangentMatrix_adDerivation_diagonalTorusPoints_apply
    {B : Type*} [CommRing B] [Algebra R B]
    (s : WithConv (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) →ₐ[R] B))
    (d : Derivation R (coordinateHopfAlgebra R (r + 1))
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R (r + 1)) B))
    (i j : Fin (r + 1)) :
    (tangentMatrix (r + 1)
      (Derivation.adDerivation B
        ((Bialgebra.CounitAlgebra.pointsMulEquiv R
          (coordinateHopfAlgebra R (r + 1)) B).symm (diagonalTorusPoints r R B s)) d) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) B) i j =
      (DiagonalizableGroup.charOfPoint s.ofConv
        (SplitTorus.weightCharacter (diagonalTorusWeight r i - diagonalTorusWeight r j)) : B) *
      (tangentMatrix (r + 1) d : Matrix (Fin (r + 1)) (Fin (r + 1)) B) i j := by
  let g := (Bialgebra.CounitAlgebra.pointsMulEquiv R
    (coordinateHopfAlgebra R (r + 1)) B).symm (diagonalTorusPoints r R B s)
  have hg : Matrix.SpecialLinearGroup.toGL (counitPointsMulEquiv (r + 1) g) =
      diagGL fun k => torusCharacter (SplitTorus.pointsMulEquiv s) (diagonalTorusWeight r k) := by
    rw [counitPointsMulEquiv_eq_pointsMulEquiv, MulEquiv.apply_symm_apply]
    exact toGL_pointsMulEquiv_diagonalTorusPoints r R B s
  rw [tangentMatrix_adDerivation_coe]
  -- The adjoint formula uses determinant-one matrices; the diagonal formula is stated for
  -- their general-linear images. Both matrix coercions have explicit comparison lemmas.
  rw [← Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    ← Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    map_inv Matrix.SpecialLinearGroup.toGL, hg, ← map_inv diagGL]
  simp only [diagGL_coe, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Pi.inv_apply]
  rw [SplitTorus.charOfPoint_weightCharacter, torusCharacter_sub, div_eq_mul_inv,
    Units.val_mul]
  ring

/-- At the universal torus point, the `(i,j)` entry has coefficient `ε_i - ε_j` in the
group-algebra basis. This is valid over arbitrary commutative base rings. -/
theorem tangentMatrix_adDerivation_universalDiagonalTorus_apply
    (d : Derivation R (coordinateHopfAlgebra R (r + 1))
      (Bialgebra.CounitAlgebra R (coordinateHopfAlgebra R (r + 1)) R))
    (i j : Fin (r + 1)) :
    (tangentMatrix (r + 1)
      (Derivation.adDerivation
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))
        ((Bialgebra.CounitAlgebra.pointsMulEquiv R (coordinateHopfAlgebra R (r + 1))
          (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))).symm
          (diagonalTorusPoints r R _ (toConv (AlgHom.id R _))))
        (Derivation.mapValue (Algebra.ofId R _) d)) : Matrix (Fin (r + 1)) (Fin (r + 1))
          (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))) i j =
      MonoidAlgebra.single
        (SplitTorus.weightCharacter (diagonalTorusWeight r i - diagonalTorusWeight r j))
        ((tangentMatrix (r + 1) d : Matrix (Fin (r + 1)) (Fin (r + 1)) R) i j) := by
  rw [tangentMatrix_adDerivation_diagonalTorusPoints_apply, tangentMatrix_mapValue_coe,
    Matrix.map_apply, DiagonalizableGroup.charOfPoint_apply_coe,
    ofConv_toConv, AlgHom.id_apply, Algebra.ofId_apply]
  rw [mul_comm, ← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]

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
  let K := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ))
  have hentry (i j : Fin (r + 1)) :
      (tangentMatrix (B := K) (r + 1)
          (MonoidAlgebra.single α (1 : R) • Derivation.mapValue (Algebra.ofId R K) d) :
        Matrix (Fin (r + 1)) (Fin (r + 1))
          (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))) i j =
        MonoidAlgebra.single α
          ((tangentMatrix (r + 1) d : Matrix (Fin (r + 1)) (Fin (r + 1)) R) i j) := by
    rw [map_smul, SetLike.val_smul, Matrix.smul_apply, smul_eq_mul,
      tangentMatrix_mapValue_coe, Matrix.map_apply, Algebra.ofId_apply]
    rw [mul_comm, ← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]
  constructor
  · intro h i j hij
    have hmatrix := congrArg (fun e =>
      (tangentMatrix (r + 1) e : Matrix (Fin (r + 1)) (Fin (r + 1))
        (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)))) i j) h
    rw [tangentMatrix_adDerivation_universalDiagonalTorus_apply, hentry] at hmatrix
    by_contra hne
    exact hij (MonoidAlgebra.single_left_injective hne hmatrix)
  · intro h
    apply (tangentLieEquivSl (R := R) (r + 1)).injective
    simp only [LieEquiv.coe_toLieHom]
    -- Injectivity elaborates the coordinate algebra as its quotient presentation; expose
    -- that presentation to apply the tangent-equivalence computation rule.
    erw [tangentLieEquivSl_apply, tangentLieEquivSl_apply]
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    rw [tangentMatrix_adDerivation_universalDiagonalTorus_apply, hentry]
    by_cases hij : SplitTorus.weightCharacter
        (diagonalTorusWeight r i - diagonalTorusWeight r j) = α
    · rw [hij]
    · simp [h i j hij]

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
