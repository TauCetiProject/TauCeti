/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.ProjectiveDimension
public import TauCeti.RepresentationTheory.Quiver.Representation.VertexSimpleModule
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.RingTheory.Finiteness.Small

/-!
# Short projective resolutions over acyclic path algebras

Every finite-length module over the path algebra of a finite acyclic quiver has
projective dimension at most one. Indeed, every simple module is a vertex simple,
whose first-arrow resolution has length one, and this bound is preserved by
extensions. In particular the result applies to every module finite-dimensional over
the coefficient field.

The standard free presentation therefore has projective kernel and is a length-one
projective resolution. Its terms need not be finitely generated. These resolutions
allow Ext computations to stop at degree one.

The simple-module classification and first-arrow resolutions are those of
`TauCeti.RepresentationTheory.Quiver.Representation.VertexSimpleModule`.
See Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative
Algebras I*, Chapter III, Section 2.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe v w x

variable (k : Type (max v w)) (Q : Type v) [Field k] [Quiver.{w} Q]
  [Finite Q] [∀ i j : Q, Finite (i ⟶ j)]

/-- Every finite-length module over an acyclic path algebra has projective dimension
at most one. The coefficient field need not be algebraically closed. -/
theorem hasProjectiveDimensionLT_two_pathAlgebra (hQ : Quiver.IsAcyclic Q)
    (M : ModuleCat.{max v w x} (pathAlgebra k Q))
    (hM : IsFiniteLength (pathAlgebra k Q) M) :
    HasProjectiveDimensionLT M 2 := by
  apply M.hasProjectiveDimensionLT_of_isFiniteLength 2 _ hM
  intro S hS
  let _ : IsSimpleModule (pathAlgebra k Q) S := hS
  -- The vertex-simple classification uses modules in the ring's universe. A simple
  -- module is cyclic, so shrink it there and transport the bound back afterwards.
  have : Small.{max v w} S := Module.Finite.small (pathAlgebra k Q) S
  let S' := ModuleCat.of (pathAlgebra k Q) (Shrink.{max v w} S)
  let eS : S' ≃ₗ[pathAlgebra k Q] S := Shrink.linearEquiv (pathAlgebra k Q) S
  have : IsSimpleModule (pathAlgebra k Q) S' := IsSimpleModule.congr eS
  obtain ⟨i, ⟨e⟩⟩ := exists_iso_vertexSimpleModule_of_simple k Q hQ S'
  let _ := hasProjectiveDimensionLT_two_vertexSimpleModule k i
  let _ := hasProjectiveDimensionLT_of_iso e.symm 2
  exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv eS 1

/-- A finite-dimensional module over an acyclic path algebra has projective dimension
at most one. -/
theorem hasProjectiveDimensionLT_two_pathAlgebra_of_finiteDimensional
    (hQ : Quiver.IsAcyclic Q) (M : ModuleCat.{max v w x} (pathAlgebra k Q))
    [FiniteDimensional k M] :
    HasProjectiveDimensionLT M 2 := by
  have : IsNoetherian (pathAlgebra k Q) M := isNoetherian_of_tower k inferInstance
  have : IsArtinian (pathAlgebra k Q) M := isArtinian_of_tower k inferInstance
  exact hasProjectiveDimensionLT_two_pathAlgebra k Q hQ M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

/-- The standard free presentation of a finite-length module over an acyclic path
algebra has projective kernel, so it is a projective resolution of length one. -/
theorem projective_projectiveShortComplex_X₁_pathAlgebra (hQ : Quiver.IsAcyclic Q)
    (M : ModuleCat.{max v w x} (pathAlgebra k Q))
    (hM : IsFiniteLength (pathAlgebra k Q) M) :
    Projective M.projectiveShortComplex.X₁ := by
  have h₂ : Projective M.projectiveShortComplex.X₂ := inferInstance
  have h₃ := hasProjectiveDimensionLT_two_pathAlgebra k Q hQ M hM
  have h₁ := ((M.shortExact_projectiveShortComplex).hasProjectiveDimensionLT_X₃_iff 0 h₂).mp h₃
  exact projective_iff_hasProjectiveDimensionLT_one.mpr h₁

end TauCeti
