/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.RepresentationTheory.Symmetric.Standard
import TauCeti.RingTheory.RootsOfUnity.Basic
-- Non-public: eigenvectors for distinct eigenvalues are linearly independent.
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenvectors of the three-cycle on the standard representation of `S₃`

Let `V₃ = {(z₀, z₁, z₂) : z₀ + z₁ + z₂ = 0}` be the standard representation
`TauCeti.standardRepresentation k (Fin 3)` of `S₃`, and let `τ = (0 1 2) = finRotate 3`. For a
primitive cube root of unity `ζ` in the field `k`, the vector

`v_ζ = δ₀ + ζ² δ₁ + ζ δ₂`

has coordinate sum `1 + ζ + ζ² = 0`, so lies in `V₃`, and `τ v_ζ = ζ v_ζ`. Eigenvectors for
distinct primitive cube roots of unity are linearly independent, so for a primitive cube root of
unity `ζ` the vectors `v_ζ` and `v_{ζ²}` form an eigenbasis of `τ` on `V₃`.

## Main definitions

* `TauCeti.symmetricGroupThreeEigenvector`: the vector `v_ζ`.

## Main results

* `TauCeti.standardRepresentation_finRotate_symmetricGroupThreeEigenvector`: `τ v_ζ = ζ v_ζ`.
* `TauCeti.symmetricGroupThreeEigenvector_ne_zero`: `v_ζ ≠ 0`.
* `TauCeti.linearIndependent_symmetricGroupThreeEigenvector`: `v_ζ` and `v_ζ'` are linearly
  independent for distinct primitive cube roots of unity `ζ` and `ζ'`.
-/

public section

open MonoidAlgebra

namespace TauCeti

variable {k : Type*} [Field k] {ζ : k}

/-- **The eigenvector `v_ζ = δ₀ + ζ² δ₁ + ζ δ₂` of the three-cycle `(0 1 2)`** on the standard
module of `S₃`, for a primitive cube root of unity `ζ`. Its coordinates sum to
`1 + ζ² + ζ = 0`. -/
noncomputable def symmetricGroupThreeEigenvector (hζ : IsPrimitiveRoot ζ 3) :
    (augmentationSubrepresentation k (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule :=
  ⟨single 0 1 + ζ ^ 2 • single 1 1 + ζ • single 2 1, by
    rw [toSubmodule_augmentationSubrepresentation, LinearMap.mem_ker]
    simp only [← MonoidAlgebra.basis_apply, map_add, map_smul, Module.Basis.sumCoords_self_apply,
      smul_eq_mul, mul_one]
    linear_combination hζ.one_add_add_sq⟩

/-- The coordinates of `v_ζ`. -/
@[simp]
theorem coe_symmetricGroupThreeEigenvector (hζ : IsPrimitiveRoot ζ 3) :
    (symmetricGroupThreeEigenvector hζ : MonoidAlgebra k (Fin 3)) =
      single 0 1 + ζ ^ 2 • single 1 1 + ζ • single 2 1 :=
  (rfl)

/-- **`τ v_ζ = ζ v_ζ`**: the three-cycle `τ = (0 1 2)` acts on `v_ζ` by `ζ`. -/
@[simp]
theorem standardRepresentation_finRotate_symmetricGroupThreeEigenvector
    (hζ : IsPrimitiveRoot ζ 3) :
    standardRepresentation k (Fin 3) (finRotate 3) (symmetricGroupThreeEigenvector hζ) =
      ζ • symmetricGroupThreeEigenvector hζ := by
  rw [← toRepresentation_augmentationSubrepresentation,
    Subrepresentation.toRepresentation_apply_coe]
  simp only [coe_symmetricGroupThreeEigenvector, Submodule.coe_smul, map_add, map_smul,
    Representation.ofMulAction_single, Equiv.Perm.smul_def, finRotate_apply, Fin.isValue,
    Fin.reduceAdd]
  linear_combination (norm := module)
    hζ.pow_eq_one • (-(single 1 1) : MonoidAlgebra k (Fin 3))

/-- `v_ζ` is nonzero: its coefficient at `0` is `1`. -/
@[simp]
theorem symmetricGroupThreeEigenvector_ne_zero (hζ : IsPrimitiveRoot ζ 3) :
    symmetricGroupThreeEigenvector hζ ≠ 0 := by
  intro h
  have h0 := congrArg (fun v : MonoidAlgebra k (Fin 3) => v.coeff 0) (Subtype.ext_iff.mp h)
  simp at h0

/-- `v_ζ` is an eigenvector of `τ = (0 1 2)` for the eigenvalue `ζ`. -/
private theorem hasEigenvector_symmetricGroupThreeEigenvector (hζ : IsPrimitiveRoot ζ 3) :
    Module.End.HasEigenvector (standardRepresentation k (Fin 3) (finRotate 3)) ζ
      (symmetricGroupThreeEigenvector hζ) :=
  ⟨Module.End.mem_eigenspace_iff.mpr
    (standardRepresentation_finRotate_symmetricGroupThreeEigenvector hζ),
    symmetricGroupThreeEigenvector_ne_zero hζ⟩

/-- **Eigenvectors of `τ` for distinct eigenvalues are linearly independent**: `v_ζ` and `v_ζ'`
are linearly independent for distinct primitive cube roots of unity `ζ` and `ζ'`. -/
theorem linearIndependent_symmetricGroupThreeEigenvector (hζ : IsPrimitiveRoot ζ 3) {ζ' : k}
    (hζ' : IsPrimitiveRoot ζ' 3) (hne : ζ ≠ ζ') :
    LinearIndependent k
      ![symmetricGroupThreeEigenvector hζ, symmetricGroupThreeEigenvector hζ'] := by
  refine Module.End.eigenvectors_linearIndependent' _ ![ζ, ζ'] ?_ _ <|
    Fin.forall_fin_two.mpr ⟨hasEigenvector_symmetricGroupThreeEigenvector hζ,
      hasEigenvector_symmetricGroupThreeEigenvector hζ'⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

end TauCeti
