/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import TauCeti.Geometry.Toric.Algebraic.FaceLocalization

/-!
# The affine toric coaction

The coordinate ring of an affine toric chart is graded by the integral character lattice.
Its grading gives the coaction of the dense torus: a monomial of character `m` maps to the
monomial of `m` on the torus tensored with the original monomial. The torus factor is the
coordinate ring of the zero cone, so this uses the same dense torus as the fan construction.

We prove the counit and coassociativity identities as equalities of algebra homomorphisms,
and equivariance of face restriction. These identities are the coordinate-ring form of the
unit and associativity laws for the affine torus action. Face equivariance allows the actions
to descend along the affine open immersions used to glue a fan scheme.

The construction uses Mathlib's monoid-algebra comultiplication and tensor-product algebra
maps. No rationality, salience, or regularity hypothesis on the cone is needed.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2--1.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open Multiplicative
open scoped TensorProduct

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- The coaction of the dense torus on the coordinate ring of an affine toric chart. The first
factor is the coordinate ring of the zero cone, and the second is the coordinate ring of the
chart. -/
noncomputable def affineCoordinateRingCoaction (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) : affineCoordinateRing hi σ →ₐ[ℂ]
      affineCoordinateRing hi (⊥ : PointedCone ℝ V) ⊗[ℂ] affineCoordinateRing hi σ :=
  (Algebra.TensorProduct.map
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (AddMonoidHom.toMultiplicative
      (AddSubmonoid.inclusion (dualSemigroup_anti hi bot_le))))
    (AlgHom.id ℂ (affineCoordinateRing hi σ))).comp
      (Bialgebra.comulAlgHom ℂ (affineCoordinateRing hi σ))

/-- The torus coaction records the character of a monomial in its first factor and retains the
monomial, including its coefficient, in its second factor. -/
@[simp]
theorem affineCoordinateRingCoaction_single (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) (m : dualSemigroup hi σ) (z : ℂ) :
    affineCoordinateRingCoaction hi σ (MonoidAlgebra.single (ofAdd m) z) =
      MonoidAlgebra.single (ofAdd (⟨m, by simp⟩ : dualSemigroup hi ⊥)) 1 ⊗ₜ[ℂ]
        MonoidAlgebra.single (ofAdd m) z := by
  simp [affineCoordinateRingCoaction, AddSubmonoid.inclusion]

/-- Evaluation at the identity of the dense torus recovers the original coordinate function. -/
@[simp]
theorem affineCoordinateRingCoaction_counit (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    ((Algebra.TensorProduct.lid ℂ (affineCoordinateRing hi σ)).toAlgHom.comp
      (Algebra.TensorProduct.map
        (Bialgebra.counitAlgHom ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))
        (AlgHom.id ℂ (affineCoordinateRing hi σ)))).comp
          (affineCoordinateRingCoaction hi σ) = AlgHom.id ℂ (affineCoordinateRing hi σ) := by
  apply MonoidAlgebra.algHom_ext
  · intro m
    simp only [AlgHom.comp_apply]
    rw [← ofAdd_toAdd m, affineCoordinateRingCoaction_single]
    simp
  · exact Subsingleton.elim _ _

/-- The two ways of coacting twice agree, after the canonical reassociation of the tensor
product. This is the coordinate-ring associativity law of the torus action. -/
theorem affineCoordinateRingCoaction_coassoc (hi : IsIntegralLattice i)
    (σ : PointedCone ℝ V) :
    ((Algebra.TensorProduct.assoc ℂ ℂ ℂ
      (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
      (affineCoordinateRing hi (⊥ : PointedCone ℝ V))
      (affineCoordinateRing hi σ)).toAlgHom.comp
        (Algebra.TensorProduct.map
          (Bialgebra.comulAlgHom ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))
          (AlgHom.id ℂ (affineCoordinateRing hi σ)))).comp
            (affineCoordinateRingCoaction hi σ) =
      (Algebra.TensorProduct.map
        (AlgHom.id ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))
        (affineCoordinateRingCoaction hi σ)).comp (affineCoordinateRingCoaction hi σ) := by
  apply MonoidAlgebra.algHom_ext
  · intro m
    simp only [AlgHom.comp_apply]
    rw [← ofAdd_toAdd m, affineCoordinateRingCoaction_single]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      affineCoordinateRingCoaction_single]
    simp
  · exact Subsingleton.elim _ _

/-- Restriction to a face is equivariant for the affine torus coactions. In particular, the
coactions agree on the coordinate rings of chart overlaps. -/
@[simp]
theorem affineCoordinateRingCoaction_comp_face (hi : IsIntegralLattice i)
    {σ τ : PointedCone ℝ V} (hτσ : τ.IsFaceOf σ) :
    (affineCoordinateRingCoaction hi τ).comp (faceAffineCoordinateRingMap hi hτσ) =
      (Algebra.TensorProduct.map
        (AlgHom.id ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V)))
        (faceAffineCoordinateRingMap hi hτσ)).comp (affineCoordinateRingCoaction hi σ) := by
  apply MonoidAlgebra.algHom_ext
  · intro m
    simp only [AlgHom.comp_apply]
    rw [← ofAdd_toAdd m, faceAffineCoordinateRingMap_single,
      affineCoordinateRingCoaction_single, affineCoordinateRingCoaction_single]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      faceAffineCoordinateRingMap_single]
  · exact Subsingleton.elim _ _

/-- On the zero cone, the torus coaction is its own multiplication comorphism. -/
@[simp]
theorem affineCoordinateRingCoaction_bot (hi : IsIntegralLattice i) :
    affineCoordinateRingCoaction hi (⊥ : PointedCone ℝ V) =
      Bialgebra.comulAlgHom ℂ (affineCoordinateRing hi (⊥ : PointedCone ℝ V)) := by
  apply MonoidAlgebra.algHom_ext
  · intro m
    rw [← ofAdd_toAdd m, affineCoordinateRingCoaction_single]
    simp
  · exact Subsingleton.elim _ _

/-- A map of lattice cones intertwines their coactions and the induced map of dense tori.
This is the coordinate-ring equivariance law for affine toric morphisms. -/
@[simp]
theorem affineCoordinateRingCoaction_comp_map
    {N' V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V'] {i' : N' →+ V'}
    (hi : IsIntegralLattice i) (hi' : IsIntegralLattice i')
    {σ : PointedCone ℝ V} {τ : PointedCone ℝ V'}
    (f : N →+ N') (g : V →ₗ[ℝ] V') (hfg : ∀ n, g (i n) = i' (f n))
    (hστ : Set.MapsTo g σ τ) :
    (affineCoordinateRingCoaction hi σ).comp
      (affineCoordinateRingMap hi hi' f g hfg hστ) =
      (Algebra.TensorProduct.map
        (affineCoordinateRingMap hi hi' f g hfg
          (σ := ⊥) (τ := ⊥) (by simp [Set.MapsTo]))
        (affineCoordinateRingMap hi hi' f g hfg hστ)).comp
          (affineCoordinateRingCoaction hi' τ) := by
  apply MonoidAlgebra.algHom_ext
  · intro m
    simp only [AlgHom.comp_apply]
    rw [← ofAdd_toAdd m, affineCoordinateRingMap_single,
      affineCoordinateRingCoaction_single, affineCoordinateRingCoaction_single]
    simp only [Algebra.TensorProduct.map_tmul, affineCoordinateRingMap_single]
    congr 2
    apply congrArg ofAdd
    apply Subtype.ext
    ext n
    simp
  · exact Subsingleton.elim _ _

end TauCeti.Toric
