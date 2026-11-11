/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Topology.Algebra.Module.Equiv.Pi
public import TauCeti.Topology.Algebra.Module.Equiv.SMul

/-!
# Normalizing continuous linear equivalences

The file also bounds the inverse of a continuous linear equivalence from a quadratic lower
bound on the equivalence itself.

Rescaling a continuous linear equivalence `T` between normed spaces by a nonzero scalar does not
change `‖T‖ * ‖T⁻¹‖`. Using Mathlib's `rescale_to_shell`, every equivalence
can be rescaled to have norm at most `1`, with its inverse then of norm at most
`‖c‖ * ‖T‖ * ‖T⁻¹‖` for any scalar `c` with `1 < ‖c‖`. This bounds both operators at once, as
needed in compactness arguments over the set of equivalences.

For finite index types `S` and `T`, the splitting `ContinuousLinearEquiv.sumPiEquivProdPi` of a
family indexed by `S ⊕ T` into its restrictions to `S` and to `T` preserves the sup norms
(`ContinuousLinearEquiv.norm_sumPiEquivProdPi_apply`), so it and its inverse have operator norm
at most `1`.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Given a scalar with `1 < ‖c‖`, every continuous linear equivalence `T` can be rescaled, without
changing `‖T‖ * ‖T⁻¹‖`, to have norm at most `1` and inverse of norm at most
`‖c‖ * ‖T‖ * ‖T⁻¹‖`. -/
theorem exists_norm_le_one_and_norm_symm_le {c : 𝕜} (hc : 1 < ‖c‖)
    (T : E ≃L[𝕜] F) :
    ∃ U : E ≃L[𝕜] F, ‖(U : E →L[𝕜] F)‖ ≤ 1 ∧
      ‖(U.symm : F →L[𝕜] E)‖ ≤ ‖c‖ * (‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖) ∧
      ‖(U : E →L[𝕜] F)‖ * ‖(U.symm : F →L[𝕜] E)‖ =
        ‖(T : E →L[𝕜] F)‖ * ‖(T.symm : F →L[𝕜] E)‖ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : Subsingleton F := T.toEquiv.symm.subsingleton
    refine ⟨T, ?_, ?_, ?_⟩ <;>
      simp [ContinuousLinearMap.opNorm_subsingleton]
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

section SumPi

variable {S T : Type*} [Fintype S] [Fintype T] {A : S ⊕ T → Type*}
  [∀ st, SeminormedAddCommGroup (A st)]

/-- Splitting a family indexed by `S ⊕ T` into its restrictions to `S` and to `T` preserves the
sup norm. -/
theorem norm_sumPiEquivProdPi_apply (R : Type*) [Semiring R] [∀ st, Module R (A st)]
    (x : (st : S ⊕ T) → A st) : ‖sumPiEquivProdPi R S T A x‖ = ‖x‖ := by
  rw [sumPiEquivProdPi_apply, Prod.norm_def]
  refine le_antisymm (max_le ?_ ?_) ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun st ↦ ?_)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun s ↦ norm_le_pi_norm x _
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun t ↦ norm_le_pi_norm x _
  · cases st with
    | inl s => exact (norm_le_pi_norm (fun s ↦ x (.inl s)) s).trans (le_max_left _ _)
    | inr t => exact (norm_le_pi_norm (fun t ↦ x (.inr t)) t).trans (le_max_right _ _)

/-- Gluing a family on `S` and a family on `T` into a family on `S ⊕ T` preserves the sup norm. -/
theorem norm_sumPiEquivProdPi_symm_apply (R : Type*) [Semiring R] [∀ st, Module R (A st)]
    (p : ((s : S) → A (.inl s)) × ((t : T) → A (.inr t))) :
    ‖(sumPiEquivProdPi R S T A).symm p‖ = ‖p‖ := by
  rw [← norm_sumPiEquivProdPi_apply R, apply_symm_apply]

variable [∀ st, NormedSpace 𝕜 (A st)]

/-- The splitting `sumPiEquivProdPi` has operator norm at most `1`. -/
theorem opNorm_sumPiEquivProdPi_le :
    ‖(sumPiEquivProdPi 𝕜 S T A :
      ((st : S ⊕ T) → A st) →L[𝕜] ((s : S) → A (.inl s)) × ((t : T) → A (.inr t)))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    rw [coe_coe, norm_sumPiEquivProdPi_apply, one_mul]

/-- The inverse of the splitting `sumPiEquivProdPi` has operator norm at most `1`. -/
theorem opNorm_sumPiEquivProdPi_symm_le :
    ‖((sumPiEquivProdPi 𝕜 S T A).symm :
      ((s : S) → A (.inl s)) × ((t : T) → A (.inr t)) →L[𝕜] (st : S ⊕ T) → A st)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p ↦ by
    rw [coe_coe, norm_sumPiEquivProdPi_symm_apply, one_mul]

end SumPi

end ContinuousLinearEquiv

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A quadratic lower bound `λ ‖y‖ ^ 2 ≤ ‖e y‖ ^ 2` with `0 < λ` on a continuous linear
equivalence `e` bounds its inverse: `‖e⁻¹ x‖ ≤ ‖x‖ / √λ`. -/
theorem norm_symm_apply_le_inv_sqrt_mul_norm (e : E ≃L[𝕜] F) {lam : ℝ} (hlam : 0 < lam)
    (h : ∀ y, lam * ‖y‖ ^ 2 ≤ ‖e y‖ ^ 2) (x : F) : ‖e.symm x‖ ≤ (√lam)⁻¹ * ‖x‖ := by
  -- `√λ ‖y‖ ≤ ‖e y‖`, applied to `y = e⁻¹ x`.
  have hx := h (e.symm x)
  rw [e.apply_symm_apply] at hx
  rw [← Real.sqrt_inv]
  refine Real.le_sqrt_mul_of_sq_le_mul (norm_nonneg x) ?_
  rw [inv_mul_eq_div, le_div_iff₀ hlam, mul_comm]
  exact hx

end ContinuousLinearEquiv
