/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.StarAlgebra.GNS.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# C*-norms from faithful positive functionals

A faithful positive functional on a finite-dimensional unital complex star algebra makes the
algebra a C*-algebra under the operator norm of left multiplication on its algebraic GNS space.
In particular, this constructs the C*-norm on finite-dimensional quotients equipped with a
faithful positive trace, without presupposing an algebra norm.

The functional need not be tracial. We use `StarPositiveFunctional.GNS` and its algebraic
`StarPositiveFunctional.representation`; finite dimensionality makes the representing operators
bounded and the GNS space complete. Faithfulness makes the representation injective, so its
operator norm pulls back to a norm on the original algebra. This algebra norm differs from the
GNS Hilbert norm. All norm structures here are explicit definitions, so they can be installed
locally without changing a pre-existing norm.

## Main constructions

* `StarPositiveFunctional.regularRep`: the GNS representation by bounded operators.
* `StarPositiveFunctional.gnsNormedRing`: the operator norm pulled back along that representation.
* `StarPositiveFunctional.gnsCStarAlgebra`: the resulting complex C*-algebra structure.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Sections 4.4–4.5,
  for the application to positive trace quotients of Temperley–Lieb algebras.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti.StarPositiveFunctional

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [FiniteDimensional ℂ A] (φ : StarPositiveFunctional A)

/-- The algebraic GNS representation as a unital star representation by bounded operators.
Finite dimensionality guarantees boundedness and completeness of the GNS space. -/
def regularRep : A →⋆ₐ[ℂ] (φ.GNS →L[ℂ] φ.GNS) where
  toAlgHom := (Module.End.toContinuousLinearMap φ.GNS).toAlgHom.comp φ.representation
  map_star' a := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
    intro x y
    -- The algebra-hom composition computes to the original action on GNS vectors.
    change ⟪φ.representation (star a) x, y⟫_ℂ = ⟪x, φ.representation a y⟫_ℂ
    simpa only [star_star] using φ.inner_representation (star a) x y

/-- The bounded representation acts by left multiplication on GNS classes. -/
@[simp]
theorem regularRep_classMap (a b : A) :
    φ.regularRep a (φ.classMap b) = φ.classMap (a * b) :=
  φ.representation_classMap a b

/-- Faithfulness of the functional makes the bounded GNS representation injective. -/
theorem regularRep_injective (hfaith : ∀ x, φ (star x * x) = 0 → x = 0) :
    Function.Injective φ.regularRep := by
  have hnull : φ.nullSubmodule = ⊥ := by
    apply eq_bot_iff.mpr
    intro a ha
    exact hfaith a ((φ.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero a).mp ha)
  exact (Module.End.toContinuousLinearMap φ.GNS).injective.comp
    (φ.representation_injective_of_classMap_injective (φ.classMap_injective_iff.mpr hnull))

variable (hfaith : ∀ x, φ (star x * x) = 0 → x = 0)

/-- The algebra norm of a faithful positive functional is the operator norm of its GNS
representation. -/
-- The constructor is exposed so its underlying ring remains definitionally the original ring.
@[expose, instance_reducible]
def gnsNormedRing : NormedRing A :=
  NormedRing.induced A (φ.GNS →L[ℂ] φ.GNS) φ.regularRep (φ.regularRep_injective hfaith)

/-- The induced algebra norm is the operator norm of the GNS representation. -/
theorem gnsNormedRing_norm (a : A) :
    @norm A (φ.gnsNormedRing hfaith).toNorm a = ‖φ.regularRep a‖ := (rfl)

/-- The GNS operator norm is compatible with scalar multiplication. -/
-- Expose the constructor to preserve the given algebra and scalar action.
@[expose, instance_reducible]
def gnsNormedAlgebra :
    letI := φ.gnsNormedRing hfaith
    NormedAlgebra ℂ A := by
  letI := φ.gnsNormedRing hfaith
  exact NormedAlgebra.induced ℂ A _ φ.regularRep

/-- The GNS operator norm satisfies the C*-identity. -/
theorem gnsCStarRing :
    letI := φ.gnsNormedRing hfaith
    CStarRing A := by
  let := φ.gnsNormedRing hfaith
  exact ⟨fun a ↦ by
    simp only [gnsNormedRing_norm, map_mul, StarHomClass.map_star]
    exact (CStarRing.norm_star_mul_self (x := φ.regularRep a)).ge⟩

/-- A finite-dimensional unital complex star algebra with a faithful positive functional is a
C*-algebra under the operator norm of its GNS representation. In particular this applies to a
faithful positive trace. Completeness follows from finite dimensionality. No norm on the algebra
is assumed. -/
-- The constructor is exposed to retain the original ring, algebra and scalar action.
@[expose, instance_reducible]
def gnsCStarAlgebra : CStarAlgebra A := by
  letI := φ.gnsNormedRing hfaith
  letI := φ.gnsNormedAlgebra hfaith
  letI := φ.gnsCStarRing hfaith
  exact {
    toCompleteSpace := FiniteDimensional.complete ℂ A
    toStarModule := inferInstance }

/-- The C*-algebra structure uses the GNS operator norm. -/
theorem gnsCStarAlgebra_norm (a : A) :
    @norm A (φ.gnsCStarAlgebra hfaith).toNorm a = ‖φ.regularRep a‖ :=
  φ.gnsNormedRing_norm hfaith a

end TauCeti.StarPositiveFunctional
