/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel.Component

/-!
# Two components of `Γ₀` over `ℤ` are different subgroups of `GL₂(ℚ)`

Over `A = ℤ` with fraction field `ℚ` and unit level, the upper unipotent matrix
`(1, 1/2; 0, 1)` lies in the component group `Γ₀(ℤ, 2ℤ)`, whose upper-right entries range over
`(2ℤ)⁻¹ = ½ℤ`, but not in the principal component `Γ₀(ℤ, ℤ)`, whose upper-right entries are
integers. So the component groups of different fractional ideals are in general different
subgroups of `GL₂(K)`, although they are conjugate when the ideals differ by a principal factor
(`TauCeti.Gamma0Component.map_conj_diagGL`).
-/

public section

namespace TauCeti

open FractionalIdeal
open scoped nonZeroDivisors

/-- The upper unipotent matrix `(1, 1/2; 0, 1)` of `GL₂(ℚ)`, with inverse `(1, -1/2; 0, 1)`. -/
def upperUnipotentHalf : GL (Fin 2) ℚ :=
  ⟨!![1, 1 / 2; 0, 1], !![1, -1 / 2; 0, 1], by ext i j; fin_cases i <;> fin_cases j <;> norm_num,
    by ext i j; fin_cases i <;> fin_cases j <;> norm_num⟩

/-- `(1, 1/2; 0, 1)` lies in the component group `Γ₀(ℤ, 2ℤ)` of unit level. -/
theorem upperUnipotentHalf_mem_Gamma0Component_two :
    upperUnipotentHalf ∈ Gamma0Component (⊤ : Ideal ℤ) (spanSingleton ℤ⁰ (2 : ℚ)) := by
  refine Gamma0Component.mem_iff.mpr ⟨by simp [upperUnipotentHalf],
    by simp [upperUnipotentHalf], ?_, by simp [upperUnipotentHalf, FractionalIdeal.zero_mem], 1,
    by simp [upperUnipotentHalf, Matrix.det_fin_two]⟩
  rw [spanSingleton_inv, mem_spanSingleton]
  exact ⟨1, by norm_num [upperUnipotentHalf]⟩

/-- `(1, 1/2; 0, 1)` does not lie in the principal component group `Γ₀(ℤ, ℤ)` of unit level:
its upper-right entry is not an integer. -/
theorem upperUnipotentHalf_not_mem_Gamma0Component_one :
    upperUnipotentHalf ∉ Gamma0Component (⊤ : Ideal ℤ) (1 : FractionalIdeal ℤ⁰ ℚ) := by
  rw [Gamma0Component.mem_iff]
  rintro ⟨-, -, h, -⟩
  rw [inv_eq, FractionalIdeal.div_one, mem_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hn : (n : ℚ) * 2 = 1 := by
    rw [show (n : ℚ) = 1 / 2 by simpa [upperUnipotentHalf] using hn]
    norm_num
  norm_cast at hn
  omega

end TauCeti
