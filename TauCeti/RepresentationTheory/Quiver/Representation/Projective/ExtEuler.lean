/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.EulerForm
public import TauCeti.RepresentationTheory.Quiver.Representation.Projective.Module

/-!
# The Ext-Euler characteristic of a vertex projective is the quiver Euler form

For a finite quiver `Q` over a field `k` the Ext-Euler characteristic

`χ(X, Y) = ∑ n, (-1)ⁿ dim_k Extⁿ(X, Y)`

of `TauCeti.extEuler` is available in the abelian category `ModuleCat (kQ)` of modules over the
path algebra. This file evaluates it on the vertex projective `Pᵢ` and identifies the value with
the combinatorial Euler form `TauCeti.eulerForm` of the two dimension vectors:

`χ(Pᵢ, Y) = ⟨dim Pᵢ, dim Y⟩ = (dim Y)ᵢ`.

Both sides are computed without any acyclicity hypothesis on `Q`: the left-hand side because all
higher `Ext` out of a projective vanishes, the right-hand side because `Pᵢ` represents evaluation
at `i`. What is needed instead is that the paths out of `i` are finite, so that `dim Pᵢ` is an
honest path count, and that the vertex space of `Y` at `i` is finite-dimensional over `k`, so that
`Hom(Pᵢ, Y)` is and the pair is Euler-admissible.

The vertex projective enters as a module rather than a representation, because it is the module
category that carries `Ext`; `TauCeti.indecProjModule` and its universal property are in
`TauCeti.RepresentationTheory.Quiver.Representation.Projective.Module`.

## Main results

* `TauCeti.isEulerAdmissible_indecProjModule`: a vertex projective is Euler-admissible against
  every module whose vertex space at `i` is finite-dimensional.
* `TauCeti.extEuler_indecProjModule`: `χ(Pᵢ, Y) = (dim Y)ᵢ`, and
  `TauCeti.extEuler_indecProjModule_eq_eulerForm`: that value is the Euler form
  `⟨dim Pᵢ, dim Y⟩`.
* `TauCeti.extEuler_indecProjModule_indecProjModule`: `χ(Pᵢ, Pⱼ)` counts the paths `j → i`, the
  path-counting Cartan matrix of the path algebra.

## References

* Ibrahim Assem, Daniel Simson and Andrzej Skowroński, *Elements of the Representation Theory of
  Associative Algebras I*, Chapter III, Section 3, for the Euler form of a path algebra and its
  homological reading.
* Harm Derksen and Jerzy Weyman, *An Introduction to Quiver Representations*, Chapter 1, for the
  identity `⟨dim M, dim N⟩ = dim Hom(M, N) - dim Ext¹(M, N)`, of which this file proves the case
  needing no `Ext¹`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian

open scoped ModuleCat

universe u v w

section Modules

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Finite Q]

/-! ### The Ext-Euler characteristic out of a vertex projective -/

/-- **A vertex projective is Euler-admissible against a module with a finite-dimensional vertex
space at `i`**: all of its higher `Ext` vanishes, and its `Hom` space is that vertex space. Only the
space at `i` is asked for, so a target that is infinite-dimensional elsewhere is admitted; for one
that is finite-dimensional overall the `Hom`-space instance of
`TauCeti.RepresentationTheory.Quiver.Representation.Projective.Module` makes
`TauCeti.isEulerAdmissible_of_projective` apply with no hypothesis at all. -/
theorem isEulerAdmissible_indecProjModule (i : Q) (Y : ModuleCat (pathAlgebra k Q))
    (hY : FiniteDimensional k (((quiverRepFunctor k Q).obj Y).obj ((Paths.of Q).obj i))) :
    IsEulerAdmissible k (indecProjModule k Q i) Y :=
  haveI := finiteDimensional_hom_indecProjModule k Q i Y hY
  isEulerAdmissible_of_projective k _ _

/-- **Projective evaluation in quiver coordinates**: `χ(Pᵢ, Y)` is the `i`-th coordinate of the
dimension vector of `Y`. -/
@[simp]
theorem extEuler_indecProjModule (i : Q) {Y : ModuleCat (pathAlgebra k Q)}
    (h : IsEulerAdmissible k (indecProjModule k Q i) Y) :
    extEuler k h = dimVector ((quiverRepFunctor k Q).obj Y) i := by
  rw [extEuler_projective k h, finrank_hom_indecProjModule]

-- Not `@[simp]`: its left-hand side is an instance of that of `TauCeti.extEuler_indecProjModule`,
-- which already rewrites it, so tagging this would be a `simpNF` violation.
/-- **The Cartan pairing of two vertex projectives**: `χ(Pᵢ, Pⱼ)` counts the paths `j → i`. -/
theorem extEuler_indecProjModule_indecProjModule (i j : Q)
    (h : IsEulerAdmissible k (indecProjModule k Q i) (indecProjModule k Q j)) :
    extEuler k h = Nat.card (Quiver.Path j i) := by
  rw [extEuler_indecProjModule k Q i h, dimVector_eq_of_iso (indecProjModuleIso k Q j),
    dimVector_indecProjRep]

end Modules

section EulerForm

variable (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q] [Fintype Q]
  [∀ a b : Q, Fintype (a ⟶ b)]

/-! ### Comparison with the Euler form of the quiver -/

/-- **The Ext-Euler characteristic of a vertex projective is the quiver Euler form.** For a
`kQ`-module `Y` Euler-admissible against `Pᵢ`, `χ(Pᵢ, Y)` is the Euler form `⟨dim Pᵢ, dim Y⟩` of
the two dimension vectors. -/
theorem extEuler_indecProjModule_eq_eulerForm (i : Q) [∀ a : Q, Finite (Quiver.Path i a)]
    {Y : ModuleCat (pathAlgebra k Q)} (h : IsEulerAdmissible k (indecProjModule k Q i) Y) :
    extEuler k h
      = eulerForm Q (fun a ↦ (dimVector (indecProjRep k Q i) a : ℤ))
          (fun a ↦ (dimVector ((quiverRepFunctor k Q).obj Y) a : ℤ)) := by
  rw [eulerForm_dimVector_indecProjRep, extEuler_indecProjModule]

end EulerForm

end TauCeti
