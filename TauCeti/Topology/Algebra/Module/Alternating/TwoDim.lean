/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.Alternating.Basic
/-!
# Alternating area and conormals in dimension two

In dimension two, if `L u = 0`, then an alternating area form `A` satisfies
`A ![W', u] * L W = A ![W, u] * L W'` for all `W, W'`, including when either
functional value vanishes. This is the linear-algebra input for showing that an induced
boundary orientation does not depend on the choice of inward transverse vector.
No compatibility between the topology and the module structure is required.
-/

public section
namespace ContinuousAlternatingMap

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
    have hremove : (1 : Fin 2).removeNth (B : Fin 2 → E) = ![u] := by
      ext i
      fin_cases i
      simpa [Fin.removeNth] using hB0
    simpa [hremove] using A.toAlternatingMap.map_vecCons_removeNth_basis B w 1
  have hW : B.repr W 1 = 1 := by rw [← hB1, Module.Basis.repr_self, Finsupp.single_eq_same]
  rw [hL, hA, hA, hW]
  ring

/-- In dimension two, if `L u = 0`, then
`A ![W', u] * L W = A ![W, u] * L W'` for all `W, W'`.
This cross-multiplied proportionality identity also holds when functional values vanish. -/
theorem apply_pair_mul_apply_eq (hE : Module.finrank 𝕜 E = 2)
    (A : E [⋀^Fin 2]→L[𝕜] 𝕜) (L : E →L[𝕜] 𝕜) {u W W' : E} (hLu : L u = 0) :
    A ![W', u] * L W = A ![W, u] * L W' := by
  by_cases hLW : L W = 0
  · by_cases hLW' : L W' = 0
    · rw [hLW, hLW', mul_zero, mul_zero]
    · exact (apply_pair_mul_apply_eq_of_ne_zero hE A L hLu hLW').symm
  · exact apply_pair_mul_apply_eq_of_ne_zero hE A L hLu hLW

end ContinuousAlternatingMap
