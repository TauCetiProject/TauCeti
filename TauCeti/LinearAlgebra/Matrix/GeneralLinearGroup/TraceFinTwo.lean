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
import TauCeti.LinearAlgebra.Matrix.Charpoly.FinTwo

/-!
# Trace and determinant of rank-two representations

For a commutative ring `A`, an invertible `2 × 2` matrix `g` satisfies `g + det g • g⁻¹ = tr g • 1`
(Cayley–Hamilton, since `det g • g⁻¹` is the adjugate `tr g • 1 - g`). Multiplying by `h` and taking
traces gives the identity

`det g * tr (g⁻¹ h) - tr g * tr h + tr (g h) = 0`,

which, with `tr 1 = 2`, `tr (g h) = tr (h g)` and multiplicativity of `det`, is what the pair
`(T, δ) = (tr ∘ ρ, det ∘ ρ)` of a representation `ρ : Γ →* GL₂(A)` satisfies. The pair determines
the characteristic polynomials and conversely (`Matrix.charpoly_eq_charpoly_iff_fin_two`). For
continuous maps into `GL₂(A)` with `A` a Hausdorff topological ring, such as continuous
representations, agreement of the pairs on a dense subset of `Γ` gives agreement everywhere.

## Main results

* `Matrix.GeneralLinearGroup.det_mul_trace_inv_mul_sub_trace_mul_trace_add_trace_mul_fin_two`:
  `det g * tr (g⁻¹ h) - tr g * tr h + tr (g h) = 0` in `GL₂(A)`.
* `Matrix.GeneralLinearGroup.charpoly_eq_of_dense_fin_two`: continuous maps
  `ρ ρ' : Γ → GL₂(A)` whose traces and determinants agree on a dense subset have the same
  characteristic polynomials everywhere.

## References

* G. Chenevier, arXiv:0809.0415v2, Lemma 1.9, p. 11, for the identity in rank two.
-/

public section

open Polynomial

namespace Matrix

namespace GeneralLinearGroup

variable {A : Type*} [CommRing A]

/-- **The rank-two trace identity.** For `g h ∈ GL₂(A)`,
`det g * tr (g⁻¹ h) - tr g * tr h + tr (g h) = 0`. -/
theorem det_mul_trace_inv_mul_sub_trace_mul_trace_add_trace_mul_fin_two (g h : GL (Fin 2) A) :
    (g : Matrix (Fin 2) (Fin 2) A).det * ((g⁻¹ : GL (Fin 2) A) * h : Matrix (Fin 2) (Fin 2) A).trace
      - (g : Matrix (Fin 2) (Fin 2) A).trace * (h : Matrix (Fin 2) (Fin 2) A).trace
      + ((g : Matrix (Fin 2) (Fin 2) A) * h).trace = 0 := by
  have key := trace_adjugate_mul_fin_two (g : Matrix (Fin 2) (Fin 2) A) h
  -- `adj g = det g • g⁻¹`.
  rw [adjugate_eq_det_smul_of_mul_eq_one (Units.mul_inv g), smul_mul_assoc, trace_smul,
    smul_eq_mul] at key
  linear_combination key

variable {Γ : Type*} [TopologicalSpace Γ] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]

/-- **Recognition on a dense subset in rank two.** Two continuous maps `ρ ρ' : Γ → GL₂(A)` into a
Hausdorff topological ring, such as continuous representations, whose traces and determinants agree
on a dense subset of `Γ` have the same characteristic polynomial at every point. -/
theorem charpoly_eq_of_dense_fin_two {ρ ρ' : Γ → GL (Fin 2) A} (hρ : Continuous ρ)
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
