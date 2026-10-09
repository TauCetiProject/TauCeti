/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.BlockSucc
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Character
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Branching

/-!
# Branching of Weyl-module characters on the diagonal torus

The character of the Weyl module of a shape `μ` on `GL (n + 1)` restricts on the diagonal
`GL n × GL 1` to

`χ_μ(diag(t, z)) = ∑_ν z ^ (|μ| - |ν|) * χ_ν(diag t)`,

where `ν` ranges over the shapes interlacing `μ` with at most `n` rows. Setting `z = 1`
gives the character identity for the upper-left block inclusion `GL n → GL (n + 1)`.
Each interlacing shape occurs once. The formula includes the empty rank and shapes with
more than `n + 1` rows, whose Weyl modules vanish.

These are identities of group characters evaluated on the diagonal torus, not isomorphisms
of restricted representations. They provide the character calculation for multiplicity-free
branching; identifying the representation summands is a separate step.

The proofs combine `TauCeti.char_weylRepOfShape_diagramOf_diagonal`, the Weyl-module
character formula, with `TauCeti.eval_snoc_diagramSchurPoly`, the Schur-polynomial branching
identity. The `FDRep` forms also apply to `TauCeti.schurFunctor` over `ℂ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15
  and Appendix A: Schur characters and branching of general linear representations.
-/

public section

namespace TauCeti

universe u

variable (k : Type u) [Field k] [CharZero k] (n : ℕ) (μ : YoungDiagram)

/-- On the diagonal `GL n × GL 1`, the Weyl character branches over interlacing shapes.
The last coordinate records the number of boxes removed from the shape. -/
theorem char_weylRepOfShape_diagonal_snoc (t : Fin n → kˣ) (z : kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k (n + 1) μ).toSubmodule)
        (weylRepOfShape k (n + 1) μ) (diagGL (Fin.snoc t z)) =
      ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
        (z : k) ^ (μ.card - ν.card) *
          Representation.character (V := ↥(weylModuleOfShape k n ν).toSubmodule)
            (weylRepOfShape k n ν) (diagGL t) := by
  classical
  have hchar (m : ℕ) (ν : YoungDiagram) (s : Fin m → kˣ) :
      Representation.character (V := ↥(weylModuleOfShape k m ν).toSubmodule)
          (weylRepOfShape k m ν) (diagGL s) =
        MvPolynomial.eval (fun i => (s i : k)) (diagramSchurPoly m k ν) := by
    have h := char_weylRepOfShape_diagramOf_diagonal k m (shapePartition ν) s
    rw [schurPoly_eq_rename, diagramOf_shapePartition] at h
    have hrename (r : ℕ) (e : Fin r ≃ Fin m) :
        MvPolynomial.rename e (diagramSchurPoly r k ν) = diagramSchurPoly m k ν := by
      have hr : r = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
      subst r
      exact isSymmetric_diagramSchurPoly m k ν e
    rw [hrename] at h
    exact h
  simp_rw [hchar]
  have hsnoc : (fun i : Fin (n + 1) => ((Fin.snoc t z : Fin (n + 1) → kˣ) i : k)) =
      Fin.snoc (fun i => (t i : k)) (z : k) :=
    Fin.comp_snoc (fun a : kˣ => (a : k)) t z
  rw [hsnoc, eval_snoc_diagramSchurPoly]

/-- The diagonal `GL n × GL 1` branching identity for the bundled Weyl module. -/
theorem char_weylFDRepOfShape_diagonal_snoc (t : Fin n → kˣ) (z : kˣ) :
    (weylFDRepOfShape k (n + 1) μ).character (diagGL (Fin.snoc t z)) =
      ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
        (z : k) ^ (μ.card - ν.card) * (weylFDRepOfShape k n ν).character (diagGL t) :=
  char_weylRepOfShape_diagonal_snoc k n μ t z

/-- On the diagonal torus, restriction along the upper-left block inclusion branches the
Weyl character as a sum over interlacing shapes, each occurring once. -/
theorem char_weylRepOfShape_glBlockSucc_diagGL (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k (n + 1) μ).toSubmodule)
        (weylRepOfShape k (n + 1) μ) (glBlockSucc k n (diagGL t)) =
      ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
        Representation.character (V := ↥(weylModuleOfShape k n ν).toSubmodule)
          (weylRepOfShape k n ν) (diagGL t) := by
  rw [glBlockSucc_diagGL, char_weylRepOfShape_diagonal_snoc]
  simp

/-- The block-restriction character identity on the diagonal torus for the bundled Weyl
module, equivalently the Schur functor over `ℂ`. -/
theorem char_weylFDRepOfShape_glBlockSucc_diagGL (t : Fin n → kˣ) :
    (weylFDRepOfShape k (n + 1) μ).character (glBlockSucc k n (diagGL t)) =
      ∑ ν ∈ YoungDiagram.interlacingShapes n μ,
        (weylFDRepOfShape k n ν).character (diagGL t) :=
  char_weylRepOfShape_glBlockSucc_diagGL k n μ t

end TauCeti
