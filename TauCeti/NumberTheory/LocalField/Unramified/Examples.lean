/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.ZMod
public import TauCeti.NumberTheory.LocalField.Unramified.Character
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Noncommutative counterexample for pointwise products of unramified characters

Over a noncommutative coefficient ring such as `M₂(𝔽₃)`, the pointwise product of two continuous
characters of `Kˣ` need not be a homomorphism, because products depend on commutation of the
character values (`TauCeti.exists_monoidHom_mul_unramifiedCharacter_iff`).

## Main results

* `TauCeti.exists_unramifiedCharacter_matrix_mul_not_monoidHom`: over `M₂(𝔽₃)`, there exist
  unramified characters whose pointwise product is not a group homomorphism on `Kˣ`.
-/

public section

noncomputable section

namespace TauCeti

/-- The upper-triangular unipotent unit `A = !![1, 1; 0, 1]` in `M₂(𝔽₃)ˣ`. -/
private def matA : (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ where
  val := !![(1 : ZMod 3), 1; 0, 1]
  inv := !![(1 : ZMod 3), 2; 0, 1]
  val_inv := by decide
  inv_val := by decide

/-- The lower-triangular unipotent unit `B = !![1, 0; 1, 1]` in `M₂(𝔽₃)ˣ`. -/
private def matB : (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ where
  val := !![(1 : ZMod 3), 0; 1, 1]
  inv := !![(1 : ZMod 3), 0; 2, 1]
  val_inv := by decide
  inv_val := by decide

/-- **Pointwise products can fail to be characters over noncommutative coefficients.** Over
`M₂(𝔽₃)`, for any nonarchimedean local field `K`, the pointwise product of the unramified
characters sending a uniformizer to `!![1, 1; 0, 1]` and `!![1, 0; 1, 1]` is not a homomorphism
on `Kˣ`, because these matrices do not commute. -/
theorem exists_unramifiedCharacter_matrix_mul_not_monoidHom (K : Type*) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    ∃ a b : (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ,
      ¬ ∃ δ : Kˣ →* (Matrix (Fin 2) (Fin 2) (ZMod 3))ˣ,
        ∀ x : Kˣ, δ x = unramifiedCharacter K a x * unramifiedCharacter K b x := by
  refine ⟨matA, matB, ?_⟩
  rw [exists_monoidHom_mul_unramifiedCharacter_iff]
  intro hcomm
  have h : (matA : Matrix (Fin 2) (Fin 2) (ZMod 3)) * matB =
      (matB : Matrix (Fin 2) (Fin 2) (ZMod 3)) * matA := by
    simpa [Units.val_mul] using congrArg Units.val hcomm.eq
  exact absurd h (by decide)

end TauCeti
