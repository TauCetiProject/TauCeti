/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Shift
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Graded

/-!
# Graded Ext-Euler evaluation on zigzag vertex projectives

For a finite simple graph without isolated vertices, the vertex projectives form graded
Euler-admissible pairs. Projectivity supplies the uniform cohomological vanishing bound, while
their categorical shifted Hom spaces have finite Laurent support. The graded Ext-Euler
characteristic is therefore the projective q-Hom polynomial, and its entries are those of the
quantum Cartan matrix `(1 + q²)I + qA`.

The internal shifts here are the integer powers of the grading-shift autoequivalence of the
graded-module category. Their comparison with the explicit shifts of graded pieces preserves
the convention `χ_q(P_i,P_j) = ∑_d q⁻ᵈ dim Hom(P_i,P_j{d})`. No infinite projective resolution
or Ext-Euler assertion for arbitrary zigzag modules is involved.

These projectives belong to the relation quotient. The no-isolated-vertex hypothesis ensures
that this quotient has the ordinary zigzag conventions on every component.

## References

* Huerfano--Khovanov, *A category for the adjoint representation*, Section 3.
* Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
* Dancso--Licata, *Koszul algebras and flow lattices*, Section 2.2, for the graded Euler
  characteristic and target-shift convention.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

universe u w t

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]
  [HasExt.{t} (GradedModuleCat.{max u w} (zigzagIntegerGrade k G))]

/-- A pair of graded zigzag vertex projectives is Euler-admissible: positive Ext degrees
vanish uniformly, and degree-zero Ext has the finite support of the computed shifted Homs. -/
theorem isGradedEulerAdmissible_zigzagGradedProjective
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) :
    IsGradedEulerAdmissible.{t} k (GradedModuleCat.shift (zigzagIntegerGrade k G))
      (zigzagGradedProjective k G i) (zigzagGradedProjective k G j) := by
  apply isGradedEulerAdmissible_of_projective
  exact (hasFiniteLaurentSupport_zigzagGradedProjective_hom k G hns i j).of_equiv
    fun d ↦ (GradedModuleCat.homShiftPowEquiv (zigzagIntegerGrade k G) _ _ d).symm

/-- The graded Ext-Euler characteristic of vertex projectives is their projective q-Hom
polynomial, hence the corresponding entry of the quantum Cartan matrix. This holds for every
choice of the category's `HasExt` instance. -/
theorem gradedExtEuler_zigzagGradedProjective
    (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) :
    gradedExtEuler k (GradedModuleCat.shift (zigzagIntegerGrade k G))
      (isGradedEulerAdmissible_zigzagGradedProjective.{u, w, t} k G hns i j) =
        zigzagProjectiveQHom k G hns i j := by
  rw [gradedExtEuler_projective]
  calc
    _ = targetShiftGradedDimension k
        (fun d : ℤ ↦ (zigzagGradedProjective k G i) ⟶
          (zigzagGradedProjective k G j).shiftObj d)
        (hasFiniteLaurentSupport_zigzagGradedProjective_hom k G hns i j) :=
      targetShiftGradedDimension_congr _ _ fun d ↦
        (GradedModuleCat.homShiftPowEquiv (zigzagIntegerGrade k G) _ _ d).finrank_eq
    _ = _ := targetShiftGradedDimension_zigzagGradedProjective_hom k G hns i j

end TauCeti
