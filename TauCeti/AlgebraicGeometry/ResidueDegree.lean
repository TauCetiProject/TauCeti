/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Residue degrees of scheme morphisms

This file develops the elementary functorial API for Mathlib's
`AlgebraicGeometry.Scheme.Hom.residueDegree`. For a scheme morphism `f : X ⟶ Y` and a point
`x : X`, this is the degree `[κ(x) : κ(f(x))]`, with value zero when the field extension is
infinite.

The main result is the tower law `residueDegree_comp`. It identifies the residue degree of a
composite with the product of the two successive residue degrees. We also characterize when a
residue degree is positive and when it is one. Over the spectrum of a field `k` the residue field
at the unique point is `k` itself (`bijective_Γevaluation_comp_ΓSpecIso_inv`), which identifies
residue degrees over `Spec k` with dimensions over `k`. These facts supply the residue-field
weights used in the degree and pushforward parts of Layer A of the Jacobian challenge roadmap.

The construction follows the residue-degree convention for pushforward of cycles in the
[Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4). The proofs reuse
Mathlib's residue-field maps and the field-extension tower law `Module.finrank_mul_finrank`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}}

/-- The residue degree of a composite is the product of the successive residue degrees:
`[κ(x) : κ(g(f(x)))] = [κ(f(x)) : κ(g(f(x)))] [κ(x) : κ(f(x))]`. -/
@[simp]
theorem residueDegree_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueDegree x = g.residueDegree (f x) * f.residueDegree x := by
  let : Algebra (Z.residueField (g (f x))) (Y.residueField (f x)) :=
    (g.residueFieldMap (f x)).hom.toAlgebra
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : Algebra (Z.residueField (g (f x))) (X.residueField x) :=
    ((f ≫ g).residueFieldMap x).hom.toAlgebra
  let : IsScalarTower (Z.residueField (g (f x))) (Y.residueField (f x))
      (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq' <| by
      rw [RingHom.algebraMap_toAlgebra]
      exact congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f g x)
  rw [Scheme.Hom.residueDegree]
  exact (Module.finrank_mul_finrank (Z.residueField (g (f x)))
    (Y.residueField (f x)) (X.residueField x)).symm

/-- A residue degree is positive exactly when the associated residue-field extension is finite. -/
theorem residueDegree_pos_iff (f : X ⟶ Y) (x : X) :
    0 < f.residueDegree x ↔
      (f.residueFieldMap x).hom.Finite := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [Scheme.Hom.residueDegree, RingHom.Finite]
  constructor
  · exact Module.finite_of_finrank_pos
  · intro h
    let : Module.Finite (Y.residueField (f x)) (X.residueField x) := h
    exact Module.finrank_pos

/-- A residue degree is nonzero exactly when the associated residue-field extension is finite. -/
theorem residueDegree_ne_zero_iff (f : X ⟶ Y) (x : X) :
    f.residueDegree x ≠ 0 ↔
      (f.residueFieldMap x).hom.Finite := by
  rw [← residueDegree_pos_iff f x, Nat.pos_iff_ne_zero]

/-- A residue-field map is bijective exactly when its residue degree is one. -/
theorem residueDegree_eq_one_iff (f : X ⟶ Y) (x : X) :
    f.residueDegree x = 1 ↔ Function.Bijective (f.residueFieldMap x) := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [Scheme.Hom.residueDegree, Algebra.finrank_eq_one_iff_bijective_algebraMap,
    RingHom.algebraMap_toAlgebra]

/-- An isomorphism of schemes has residue degree one at every point. -/
@[simp]
theorem residueDegree_eq_one_of_isIso (f : X ⟶ Y) [IsIso f] (x : X) :
    f.residueDegree x = 1 :=
  (residueDegree_eq_one_iff f x).mpr (ConcreteCategory.bijective_of_isIso _)

/-- The residue field of the spectrum of a field `k` at its unique point is `k` itself:
evaluating the global function corresponding to an element of `k` at that point is bijective.
This identifies residue degrees over `Spec k` with dimensions over `k`. -/
theorem bijective_Γevaluation_comp_ΓSpecIso_inv (k : Type u) [Field k] (p : Spec (.of k)) :
    Function.Bijective ((Spec (.of k)).Γevaluation p ∘ (Scheme.ΓSpecIso (.of k)).inv) := by
  have : p.asIdeal.IsPrime := p.isPrime
  have : p.asIdeal.IsMaximal := by
    rw [Ideal.eq_bot_of_prime p.asIdeal]
    exact Ideal.bot_isMaximal
  have h : (Spec (.of k)).Γevaluation p ∘ (Scheme.ΓSpecIso (.of k)).inv =
      (Scheme.Spec.residueFieldIso (.of k) p).inv ∘ algebraMap k p.asIdeal.ResidueField := by
    funext c
    exact (ConcreteCategory.congr_hom (Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) p) c).symm
  rw [h, IsScalarTower.algebraMap_eq k (k ⧸ p.asIdeal) p.asIdeal.ResidueField,
    RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso _).comp
    ((p.asIdeal.bijective_algebraMap_quotient_residueField).comp
      ⟨(algebraMap k (k ⧸ p.asIdeal)).injective, Ideal.Quotient.mk_surjective⟩)

end AlgebraicGeometry

end TauCeti
