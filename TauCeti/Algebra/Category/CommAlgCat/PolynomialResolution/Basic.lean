/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.CommAlgCat.PolynomialPresentation

/-!
# Stages and operators of the polynomial resolution

The augmented polynomial stages are `B`, `R[B]`, `R[R[B]]`, and so on. Their faces
and degeneracies are iterates of the counit and comultiplication of
`CommAlgCat.polynomialComonad`, not a separate choice of polynomial presentations.
Stage zero is the original algebra, so the first face is the augmentation `R[B] → B`.

These are the basic operators for assembling an augmented simplicial algebra;
no simplicial identities, resolution or acyclicity assertion is made here.

## References

* The Stacks Project, Definition 92.3.1 (Tag 08PM), the standard polynomial resolution.
-/

public noncomputable section

open CategoryTheory MvPolynomial

universe u

namespace TauCeti.PolynomialResolution

variable {R : Type u} [CommRing R]

/-- The augmented polynomial stages, with the original algebra in stage zero.
The body is exposed so callers can use each successor stage as a polynomial ring. -/
abbrev stage (R : Type u) [CommRing R] (B : CommAlgCat.{u} R) : ℕ → CommAlgCat.{u} R
  | 0 => B
  | n + 1 => CommAlgCat.of R (MvPolynomial (stage R B n) R)

theorem stage_zero (B : CommAlgCat.{u} R) : stage R B 0 = B := rfl

theorem stage_succ (B : CommAlgCat.{u} R) (n : ℕ) :
    stage R B (n + 1) = CommAlgCat.of R (MvPolynomial (stage R B n) R) := rfl

/-- Counit faces, indexed from the outermost polynomial algebra.
For `n = 0` this is the augmentation `R[B] → B`. -/
def face (B : CommAlgCat.{u} R) :
    (n : ℕ) → Fin (n + 1) → (stage R B (n + 1) ⟶ stage R B n)
  | 0, _ => (CommAlgCat.polynomialComonad R).ε.app B
  | n + 1, i => Fin.cases
      ((CommAlgCat.polynomialComonad R).ε.app (stage R B (n + 1)))
      (fun j => (CommAlgCat.polynomialComonad R).map (face B n j)) i

/-- The outermost face is the counit of the polynomial comonad. -/
theorem face_zero (B : CommAlgCat.{u} R) (n : ℕ) :
    face B n 0 = (CommAlgCat.polynomialComonad R).ε.app (stage R B n) := by
  cases n <;> rfl

/-- Inner faces are the polynomial comonad applied to the faces one stage lower. -/
theorem face_succ (B : CommAlgCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    face B (n + 1) i.succ = (CommAlgCat.polynomialComonad R).map (face B n i) := (rfl)

@[simp] theorem face_zero_hom (B : CommAlgCat.{u} R) (n : ℕ) :
    (face B n 0).hom = aeval (id : stage R B n → stage R B n) := by
  rw [face_zero]
  exact CommAlgCat.polynomialComonad_ε_app_hom R _

@[simp] theorem face_succ_hom (B : CommAlgCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    (face B (n + 1) i.succ).hom = rename (face B n i).hom := by
  rw [face_succ]
  exact CommAlgCat.polynomialComonad_map_hom R (face B n i)

/-- Comultiplication degeneracies, indexed from the outermost polynomial algebra. -/
def degeneracy (B : CommAlgCat.{u} R) :
    (n : ℕ) → Fin (n + 1) → (stage R B (n + 1) ⟶ stage R B (n + 2))
  | 0, _ => (CommAlgCat.polynomialComonad R).δ.app B
  | n + 1, i => Fin.cases
      ((CommAlgCat.polynomialComonad R).δ.app (stage R B (n + 1)))
      (fun j => (CommAlgCat.polynomialComonad R).map (degeneracy B n j)) i

/-- The outermost degeneracy is the comultiplication of the polynomial comonad. -/
theorem degeneracy_zero (B : CommAlgCat.{u} R) (n : ℕ) :
    degeneracy B n 0 = (CommAlgCat.polynomialComonad R).δ.app (stage R B n) := by
  cases n <;> rfl

/-- Inner degeneracies are the polynomial comonad applied to those one stage lower. -/
theorem degeneracy_succ (B : CommAlgCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    degeneracy B (n + 1) i.succ =
      (CommAlgCat.polynomialComonad R).map (degeneracy B n i) := (rfl)

@[simp] theorem degeneracy_zero_hom (B : CommAlgCat.{u} R) (n : ℕ) :
    (degeneracy B n 0).hom = rename (X (R := R) : stage R B n → _) := by
  rw [degeneracy_zero]
  exact CommAlgCat.polynomialComonad_δ_app_hom R _

@[simp] theorem degeneracy_succ_hom (B : CommAlgCat.{u} R) (n : ℕ) (i : Fin (n + 1)) :
    (degeneracy B (n + 1) i.succ).hom = rename (degeneracy B n i).hom := by
  rw [degeneracy_succ]
  exact CommAlgCat.polynomialComonad_map_hom R (degeneracy B n i)

end TauCeti.PolynomialResolution
