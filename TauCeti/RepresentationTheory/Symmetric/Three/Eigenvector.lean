/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.RepresentationTheory.Symmetric.Standard

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
    have h : 1 + ζ + ζ ^ 2 = 0 := by
      simpa [Finset.sum_range_succ] using hζ.geom_sum_eq_zero (by norm_num)
    linear_combination h⟩

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
  have h0 : finRotate 3 • (0 : Fin 3) = 1 := by decide
  have h1 : finRotate 3 • (1 : Fin 3) = 2 := by decide
  have h2 : finRotate 3 • (2 : Fin 3) = 0 := by decide
  simp only [coe_symmetricGroupThreeEigenvector, Submodule.coe_smul, map_add, map_smul,
    Representation.ofMulAction_single, h0, h1, h2]
  linear_combination (norm := module)
    hζ.pow_eq_one • (-(single 1 1) : MonoidAlgebra k (Fin 3))

/-- **Eigenvectors of `τ` for distinct eigenvalues are linearly independent**: `v_ζ` and `v_ζ'`
are linearly independent for distinct primitive cube roots of unity `ζ` and `ζ'`. -/
theorem linearIndependent_symmetricGroupThreeEigenvector (hζ : IsPrimitiveRoot ζ 3) {ζ' : k}
    (hζ' : IsPrimitiveRoot ζ' 3) (hne : ζ ≠ ζ') :
    LinearIndependent k
      ![symmetricGroupThreeEigenvector hζ, symmetricGroupThreeEigenvector hζ'] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hc (i : Fin 3) :
      s * (symmetricGroupThreeEigenvector hζ : MonoidAlgebra k (Fin 3)).coeff i +
        t * (symmetricGroupThreeEigenvector hζ' : MonoidAlgebra k (Fin 3)).coeff i = 0 := by
    simpa [-coe_symmetricGroupThreeEigenvector] using
      congrArg (fun v : MonoidAlgebra k (Fin 3) => v.coeff i) (Subtype.ext_iff.mp hst)
  have h0 := hc 0
  have h2 := hc 2
  simp only [coe_symmetricGroupThreeEigenvector, coeff_add, coeff_smul, coeff_single,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at h0 h2
  norm_num at h0 h2
  have hs : s * (ζ - ζ') = 0 := by linear_combination h2 - ζ' * h0
  have hs0 : s = 0 := (mul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr hne)
  refine ⟨hs0, ?_⟩
  simpa [hs0] using h0

end TauCeti
