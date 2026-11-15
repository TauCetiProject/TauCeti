/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Primitive

/-!
# Primitive vectors from rational saturation

A vector in a free integral submodule of a rational vector space is primitive
if the only rational multiples lying in that submodule are its integer multiples.
This criterion turns integral normalization of a rational line into an integral
coordinate taking its specified generator to one.
-/

public section

namespace Submodule

/-- A normalized generator of the intersection with a rational line is primitive. -/
theorem isPrimitive_of_forall_smul_mem {V : Type*} [AddCommGroup V] [Module ℚ V]
    (M : Submodule ℤ V) [Module.Free ℤ M] {v : M}
    (h : ∀ q : ℚ, q • (v : V) ∈ M → ∃ n : ℤ, (n : ℚ) = q) :
    TauCeti.IsPrimitive v := by
  have hv : v ≠ 0 := by
    intro hv
    obtain ⟨n, hn⟩ := h (1 / 2) (by simp [hv])
    have hden := congrArg Rat.den hn
    norm_num at hden
  obtain ⟨d, w, hd, hp, hvw⟩ := TauCeti.exists_eq_zsmul_isPrimitive hv
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hval : (v : V) = d • (w : V) := congrArg Subtype.val hvw
  have hw : (d : ℚ)⁻¹ • (v : V) = (w : V) := by
    rw [hval, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hdq, one_smul]
  obtain ⟨n, hn⟩ := h (d : ℚ)⁻¹ (hw.symm ▸ w.2)
  have hnd : n * d = 1 := by
    exact_mod_cast (show (n : ℚ) * d = 1 by rw [hn, inv_mul_cancel₀ hdq])
  have hd1 : d = 1 := by
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hnd with h | h <;> omega
  subst d
  have hvw' : v = w := by simpa only [one_zsmul] using hvw
  rwa [hvw']

end Submodule
