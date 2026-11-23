/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Instances.Matrix
import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo

/-!
# Trace and determinant of rank-two representations

For a commutative ring `A`, an invertible `2 × 2` matrix `g` satisfies `g + det g • g⁻¹ = tr g • 1`
(Cayley–Hamilton, since `det g • g⁻¹` is the adjugate `tr g • 1 - g`). Multiplying by `h` and taking
traces gives the identity

`det g * tr (g⁻¹ h) - tr g * tr h + tr (g h) = 0`,

which, with `tr 1 = 2`, `tr (g h) = tr (h g)` and multiplicativity of `det`, is what the pair
`(T, δ) = (tr ∘ ρ, det ∘ ρ)` of a representation `ρ : Γ →* GL₂(A)` satisfies. The pair determines
the characteristic polynomials and conversely, `charpoly g = X ^ 2 - tr g • X + det g`. For
continuous representations into `GL₂(A)` with `A` a Hausdorff topological ring, agreement of the
pairs on a dense subset of `Γ` gives agreement everywhere.

## Main results

* `Matrix.trace_adjugate_mul_fin_two`: `tr (adj M * N) = tr M * tr N - tr (M * N)`.
* `Matrix.GeneralLinearGroup.det_mul_trace_inv_mul_sub_trace_mul_trace_add_trace_mul`:
  `det g * tr (g⁻¹ h) - tr g * tr h + tr (g h) = 0` in `GL₂(A)`.
* `Matrix.charpoly_eq_charpoly_iff_fin_two`: two `2 × 2` matrices have the same characteristic
  polynomial exactly when they have the same trace and determinant.
* `Matrix.GeneralLinearGroup.charpoly_eq_of_dense`: continuous representations
  `ρ ρ' : Γ →* GL₂(A)` whose traces and determinants agree on a dense subset have the same
  characteristic polynomials everywhere.

## References

* G. Chenevier, arXiv:0809.0415v2, Lemma 1.9, p. 11, for the identity in rank two.
-/

public section

open Polynomial

namespace Matrix

variable {A : Type*} [CommRing A]

/-- For `2 × 2` matrices, `tr (adj M * N) = tr M * tr N - tr (M * N)`, as `adj M = tr M • 1 - M`. -/
theorem trace_adjugate_mul_fin_two (M N : Matrix (Fin 2) (Fin 2) A) :
    (adjugate M * N).trace = M.trace * N.trace - (M * N).trace := by
  rw [adjugate_fin_two_eq_trace_smul_one_sub, sub_mul, smul_mul_assoc, one_mul, trace_sub,
    trace_smul, smul_eq_mul]

/-- Two `2 × 2` matrices have the same characteristic polynomial exactly when they have the same
trace and the same determinant. -/
theorem charpoly_eq_charpoly_iff_fin_two (M N : Matrix (Fin 2) (Fin 2) A) :
    M.charpoly = N.charpoly ↔ M.trace = N.trace ∧ M.det = N.det := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨htr, hdet⟩ ↦ ?_⟩
  · rw [trace_eq_neg_charpoly_coeff, trace_eq_neg_charpoly_coeff, h]
  · rw [det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, h]
  · nontriviality A
    rw [charpoly_fin_two, charpoly_fin_two, htr, hdet]

namespace GeneralLinearGroup

/-- **The rank-two trace identity.** For `g h ∈ GL₂(A)`,
`det g * tr (g⁻¹ h) - tr g * tr h + tr (g h) = 0`. -/
theorem det_mul_trace_inv_mul_sub_trace_mul_trace_add_trace_mul (g h : GL (Fin 2) A) :
    (g : Matrix (Fin 2) (Fin 2) A).det * ((g⁻¹ : GL (Fin 2) A) * h : Matrix (Fin 2) (Fin 2) A).trace
      - (g : Matrix (Fin 2) (Fin 2) A).trace * (h : Matrix (Fin 2) (Fin 2) A).trace
      + ((g : Matrix (Fin 2) (Fin 2) A) * h).trace = 0 := by
  -- `det g • g⁻¹` is the adjugate of `g`.
  have hadj : (g : Matrix (Fin 2) (Fin 2) A).det • ((g⁻¹ : GL (Fin 2) A) : Matrix _ _ A) =
      adjugate (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [coe_units_inv, inv_def, smul_smul,
      Ring.mul_inverse_cancel _ ((isUnit_iff_isUnit_det _).1 g.isUnit), one_smul]
  rw [← smul_eq_mul, ← trace_smul, ← smul_mul_assoc, hadj, trace_adjugate_mul_fin_two]
  ring

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [TopologicalSpace A] [IsTopologicalRing A]
  [T2Space A]

/-- **Recognition on a dense subset in rank two.** Two continuous representations
`ρ ρ' : Γ →* GL₂(A)` into a Hausdorff topological ring whose traces and determinants agree on a
dense subset of `Γ` have the same characteristic polynomial at every element. -/
theorem charpoly_eq_of_dense {ρ ρ' : Γ →* GL (Fin 2) A} (hρ : Continuous ρ)
    (hρ' : Continuous ρ') {S : Set Γ} (hS : Dense S)
    (htr : ∀ g ∈ S,
      (ρ g : Matrix (Fin 2) (Fin 2) A).trace = (ρ' g : Matrix (Fin 2) (Fin 2) A).trace)
    (hdet : ∀ g ∈ S,
      (ρ g : Matrix (Fin 2) (Fin 2) A).det = (ρ' g : Matrix (Fin 2) (Fin 2) A).det) (g : Γ) :
    (ρ g : Matrix (Fin 2) (Fin 2) A).charpoly = (ρ' g : Matrix (Fin 2) (Fin 2) A).charpoly := by
  have hc := Units.continuous_val.comp hρ
  have hc' := Units.continuous_val.comp hρ'
  rw [charpoly_eq_charpoly_iff_fin_two]
  exact ⟨congrFun (hc.matrix_trace.ext_on hS hc'.matrix_trace htr) g,
    congrFun (hc.matrix_det.ext_on hS hc'.matrix_det hdet) g⟩

end GeneralLinearGroup

end Matrix
