/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Alternating area and conormals in dimension two

If a linear functional annihilates a tangent vector, contracting an alternating area form
with two other vectors changes by the same factor as their values under that functional.
This identity proves that an induced boundary orientation is independent of the inward field.
No compatibility between the topology and the module structure is required.
-/

public section
namespace ContinuousAlternatingMap

/-- The complementary basis vector gives the exact coordinate face sign. -/
theorem apply_pair_basis_rev {R E : Type*} [CommRing R] [TopologicalSpace R]
    [AddCommGroup E] [Module R E] [TopologicalSpace E] (A : E [⋀^Fin 2]→L[R] R)
    (B : Module.Basis (Fin 2) R E) (i : Fin 2) (w : E) :
    A ![w, B i.rev] = (-1 : R) ^ i.val * (B.repr w) i * A B := by
  rw [apply_eq_det_mul A B]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  fin_cases i <;> simp [Module.Basis.repr_self]

variable {𝕜 E : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- The transverse case of `apply_pair_mul_apply_eq`. -/
private theorem apply_pair_mul_apply_eq_of_ne_zero (hE : Module.finrank 𝕜 E = 2)
    (A : E [⋀^Fin 2]→L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜) {u W W' : E}
    (hLu : L u = 0) (hLW : L W ≠ 0) :
    A ![W', u] * L W = A ![W, u] * L W' := by
  by_cases hu : u = 0
  · subst u
    have hz (z : E) : A ![z, 0] = 0 := A.map_coord_zero 1 rfl
    rw [hz, hz, zero_mul, zero_mul]
  have hli : LinearIndependent 𝕜 ![u, W] := by
    rw [LinearIndependent.pair_iff' hu]
    intro a ha
    have h := congrArg L ha
    rw [map_smul, hLu, smul_zero] at h
    exact hLW h.symm
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simpa using hE.symm)
  have hB : (B : Fin 2 → E) = ![u, W] :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hB0 : B 0 = u := by rw [hB]; rfl
  have hB1 : B 1 = W := by rw [hB]; rfl
  have hrepr : W' = (B.repr W') 0 • u + (B.repr W') 1 • W := by
    have h := B.sum_repr W'
    rw [Fin.sum_univ_two, hB0, hB1] at h
    exact h.symm
  have hL : L W' = (B.repr W') 1 * L W := by
    conv_lhs => rw [hrepr]
    rw [map_add, map_smul, map_smul, hLu, smul_zero, zero_add, smul_eq_mul]
  have hA (w : E) : A ![w, u] = -((B.repr w) 1 * A B) := by
    simpa [hB0] using A.apply_pair_basis_rev B 1 w
  have hW : B.repr W 1 = 1 := by rw [← hB1, Module.Basis.repr_self, Finsupp.single_eq_same]
  rw [hL, hA, hA, hW]
  ring

/-- Area contractions and conormal values have the same ratio. -/
theorem apply_pair_mul_apply_eq (hE : Module.finrank 𝕜 E = 2)
    (A : E [⋀^Fin 2]→L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜) {u W W' : E} (hLu : L u = 0) :
    A ![W', u] * L W = A ![W, u] * L W' := by
  by_cases hLW : L W = 0
  · by_cases hLW' : L W' = 0
    · rw [hLW, hLW', mul_zero, mul_zero]
    · exact (apply_pair_mul_apply_eq_of_ne_zero hE A L hLu hLW').symm
  · exact apply_pair_mul_apply_eq_of_ne_zero hE A L hLu hLW

end ContinuousAlternatingMap
