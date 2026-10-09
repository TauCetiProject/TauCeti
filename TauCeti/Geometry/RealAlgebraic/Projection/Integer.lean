/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Projection.Delineability

/-!
# The Collins projection of integer families

A finite family `P` of polynomials with integer coefficients in the variables `X 0, …, X n`
enters cylindrical decomposition over `ℝ` by mapping its coefficients to `ℝ` and singling out the
distinguished variable `X 0` with `MvPolynomial.finSuccEquiv`. This gives the real family
`P.integerFamily` of polynomials in `X 0` over `ℝ[X 1, …, X n]`, whose fibers over a point `x`
of `ℝⁿ` are the univariate polynomials `t ↦ f (Fin.cons t x)`, `f ∈ P`
(`MvPolynomial.polynomial_eval_map_finSuccEquiv`).

The Collins projection of this real family can be computed without leaving the integers: single
out `X 0` over `ℤ` and project there. The result `P.integerProjection` is a finite family of
integer polynomials in `n` variables. The injective map `Int.castRingHom ℝ` preserves the degrees
of all reducta and of their derivatives, so the principal subresultant coefficients are taken at
the same formal bounds over `ℤ` and over `ℝ`, and the image of the integer projection is exactly
the Collins projection of the real family. Hence sign conditions on the integer projection
delineate the real family.

## Main definitions

* `Finset.integerFamily`: the real family in the distinguished variable `X 0` attached to a
  finite family of integer polynomials in `n + 1` variables.
* `Finset.integerProjection`: its Collins projection, computed over `ℤ`.

## Main results

* `Finset.image_map_integerProjection`: the image of the integer projection in `ℝ[X 1, …, X n]` is
  the Collins projection of the real family.
* `TauCeti.nonempty_delineation_integerFamily_of_signInvariant_integerProjection`:
  **integer delineability**. If every element of the integer projection is sign-invariant on a
  preconnected set `S ⊆ ℝⁿ`, the real family has a delineation over `S`.

## References

* G. E. Collins, *Quantifier elimination for real closed fields by cylindrical algebraic
  decomposition*, Lecture Notes in Computer Science 33 (1975), 134–183.
* S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
  Chapter 11.
-/

public section

open Polynomial

namespace Finset

variable {n : ℕ}

/-- The real family attached to a finite family `P` of integer polynomials in the variables
`X 0, …, X n`: map the coefficients to `ℝ` and single out the distinguished variable `X 0`. -/
noncomputable def integerFamily (P : Finset (MvPolynomial (Fin (n + 1)) ℤ)) :
    Finset (MvPolynomial (Fin n) ℝ)[X] := by
  classical
  exact P.image fun f ↦ MvPolynomial.finSuccEquiv ℝ n (f.map (Int.castRingHom ℝ))

/-- The Collins projection of a finite family `P` of integer polynomials in the variables
`X 0, …, X n`, computed over `ℤ`: single out the distinguished variable `X 0` and take the Collins
projection of the resulting family of polynomials in `X 0` over `ℤ[X 1, …, X n]`. -/
noncomputable def integerProjection (P : Finset (MvPolynomial (Fin (n + 1)) ℤ)) :
    Finset (MvPolynomial (Fin n) ℤ) :=
  (P.image (MvPolynomial.finSuccEquiv ℤ n)).collinsProjection

/-- The members of the real family of `P` are the members of `P` mapped to `ℝ`, with the
distinguished variable `X 0` singled out. -/
@[simp]
theorem mem_integerFamily {P : Finset (MvPolynomial (Fin (n + 1)) ℤ)}
    {g : (MvPolynomial (Fin n) ℝ)[X]} :
    g ∈ P.integerFamily ↔
      ∃ f ∈ P, MvPolynomial.finSuccEquiv ℝ n (f.map (Int.castRingHom ℝ)) = g := by
  classical
  simp [integerFamily]

/-- The integer projection is the Collins projection of the family obtained by singling out the
distinguished variable `X 0` over `ℤ`. -/
theorem integerProjection_def (P : Finset (MvPolynomial (Fin (n + 1)) ℤ)) :
    P.integerProjection = (P.image (MvPolynomial.finSuccEquiv ℤ n)).collinsProjection :=
  (rfl)

/-- The real family of the empty family is empty. -/
@[simp]
theorem integerFamily_empty : (∅ : Finset (MvPolynomial (Fin (n + 1)) ℤ)).integerFamily = ∅ := by
  ext
  simp

/-- The integer projection of the empty family is empty. -/
@[simp]
theorem integerProjection_empty :
    (∅ : Finset (MvPolynomial (Fin (n + 1)) ℤ)).integerProjection = ∅ := by
  simp [integerProjection_def]

/-- Enlarging a family of integer polynomials enlarges its real family. -/
@[gcongr]
theorem integerFamily_mono {P Q : Finset (MvPolynomial (Fin (n + 1)) ℤ)} (h : P ⊆ Q) :
    P.integerFamily ⊆ Q.integerFamily := by
  intro g hg
  obtain ⟨f, hf, rfl⟩ := mem_integerFamily.1 hg
  exact mem_integerFamily.2 ⟨f, h hf, rfl⟩

/-- Enlarging a family of integer polynomials enlarges its integer projection. -/
@[gcongr]
theorem integerProjection_mono {P Q : Finset (MvPolynomial (Fin (n + 1)) ℤ)} (h : P ⊆ Q) :
    P.integerProjection ⊆ Q.integerProjection :=
  collinsProjection_mono (image_subset_image h)

/-- **The integer projection computes the real projection.** Mapping the integer projection of
`P` to `ℝ` gives the Collins projection of the real family of `P`. -/
theorem image_map_integerProjection [DecidableEq (MvPolynomial (Fin n) ℝ)]
    (P : Finset (MvPolynomial (Fin (n + 1)) ℤ)) :
    P.integerProjection.image (MvPolynomial.map (Int.castRingHom ℝ)) =
      P.integerFamily.collinsProjection := by
  classical
  -- `collinsProjection_image_finSuccEquiv_map` is stated with arbitrary `DecidableEq` instances;
  -- `convert` identifies them with the ones here, leaving the two descriptions of the family.
  convert (collinsProjection_image_finSuccEquiv_map (RingHom.injective_int (Int.castRingHom ℝ))
    P).symm using 2
  · exact integerProjection_def P
  · ext
    simp

end Finset

namespace TauCeti

variable {n : ℕ} {S : Set (Fin n → ℝ)}

/-- **Integer delineability.** Let `P` be a finite family of polynomials with integer
coefficients in the variables `X 0, …, X n`. If every element of its integer projection is
sign-invariant on a preconnected set `S ⊆ ℝⁿ`, then the real family of `P` has a delineation
over `S`: its fibers over `x ∈ S` are the polynomials `t ↦ f (Fin.cons t x)`, `f ∈ P`. -/
theorem nonempty_delineation_integerFamily_of_signInvariant_integerProjection
    {P : Finset (MvPolynomial (Fin (n + 1)) ℤ)} (hS : IsPreconnected S)
    (h : ∀ q ∈ P.integerProjection,
      SignInvariant (fun x ↦ MvPolynomial.eval₂ (Int.castRingHom ℝ) x q) S) :
    Nonempty (Delineation fun (p : P.integerFamily) (x : S) ↦
      p.1.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) x.1)) := by
  classical
  exact nonempty_delineation_image_finSuccEquiv_map_of_signInvariant_collinsProjection
    (RingHom.injective_int _) hS h

end TauCeti
