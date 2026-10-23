/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Topology.Algebra.Module.Equiv.SMul

/-!
# Normalizing continuous linear equivalences

Rescaling a continuous linear equivalence `T` between normed spaces by a nonzero scalar does not
change `‖T‖ * ‖T⁻¹‖`. Using Mathlib's `rescale_to_shell`, every equivalence from a nonzero space
can be rescaled to have norm at most `1`, with its inverse then of norm at most
`‖c‖ * ‖T‖ * ‖T⁻¹‖` for any scalar `c` with `1 < ‖c‖`. This bounds both operators at once, as
needed in compactness arguments over the set of equivalences.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Given a scalar with `1 < ‖c‖`, every continuous linear equivalence `T` from a nonzero space
can be rescaled, without changing `‖T‖ * ‖T⁻¹‖`, to have norm at most `1` and inverse of norm at
most `‖c‖ * ‖T‖ * ‖T⁻¹‖`. -/
theorem exists_norm_le_one_and_norm_symm_le [Nontrivial E] {c : 𝕜} (hc : 1 < ‖c‖)
    (T : E ≃L[𝕜] F) :
    ∃ U : E ≃L[𝕜] F, ‖(U : E →L[𝕜] F)‖ ≤ 1 ∧
      ‖(U.symm : F →L[𝕜] E)‖ ≤ ‖c‖ * (‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖) ∧
      ‖(U : E →L[𝕜] F)‖ * ‖(U.symm : F →L[𝕜] E)‖ =
        ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ := by
  have hT : (T : E →L[𝕜] F) ≠ 0 := fun h ↦ by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact hx (T.injective (by simpa using congr($h x)))
  obtain ⟨d, hd, hlt, hge, -⟩ := rescale_to_shell hc one_pos hT
  obtain ⟨U, hU, hUs⟩ := T.exists_coe_eq_smul hd
  have hd' : 0 < ‖d‖ := norm_pos_iff.2 hd
  rw [norm_smul] at hlt hge
  refine ⟨U, by rw [hU, norm_smul]; exact hlt.le, ?_, ?_⟩
  · rw [hUs, norm_smul, norm_inv, ← mul_assoc]
    gcongr
    rw [inv_le_iff_one_le_mul₀ hd']
    calc 1 = ‖c‖ * ‖c‖⁻¹ := (mul_inv_cancel₀ (by positivity)).symm
      _ ≤ ‖c‖ * (‖d‖ * ‖(T : E →L[𝕜] F)‖) := by gcongr; simpa [one_div] using hge
      _ = _ := by ring
  · rw [hU, hUs, norm_smul, norm_smul, norm_inv]
    field_simp

end ContinuousLinearEquiv
