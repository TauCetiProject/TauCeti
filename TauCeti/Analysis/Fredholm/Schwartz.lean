/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.Surjective
public import TauCeti.Analysis.Normed.Operator.NonlinearRightInverse
public import TauCeti.Analysis.Normed.Module.Quotient
public import TauCeti.Analysis.Fredholm.ClosedRange

/-!
# Compact perturbations of surjections

The functional-analytic Schwartz lemma used in the finite-dimensionality proof for cohomology
on compact Riemann surfaces: a compact perturbation of a surjective map between Banach spaces
has closed range of finite codimension. The kernel of the surjection need not be finite
or complemented.

The proof uses the compact-operator quotient estimate and bounded nonlinear right inverses.
These lower-level APIs require neither Fredholm hypotheses nor complemented kernels. No
approximation property or finite-rank operator-norm approximation is assumed.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14.
-/

public noncomputable section

open Set
open scoped NNReal Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Schwartz's lemma.** A compact perturbation of a surjection between real or complex
Banach spaces has finite-dimensional cokernel, without any hypothesis on its kernel. -/
theorem cofg_range_add_of_surjective_of_isCompactOperator [CompleteSpace E] [CompleteSpace F]
    (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    (T + K).range.CoFG := by
  let R := T.nonlinearRightInverseOfSurjective (LinearMap.range_eq_top.2 hT)
  have hR : 0 < (R.nnnorm : ℝ) := by
    exact_mod_cast T.nonlinearRightInverseOfSurjective_nnnorm_pos
      (LinearMap.range_eq_top.2 hT)
  let a : ℝ := ((R.nnnorm : ℝ) * 2)⁻¹
  have ha : 0 < a := inv_pos.2 (mul_pos hR (by norm_num))
  obtain ⟨W, hW, hsmall⟩ := exists_finiteDimensional_quotient_norm_le K hK (half_pos ha)
  have : FiniteDimensional 𝕜 W := hW
  have : IsClosed (W : Set F) := W.closed_of_finiteDimensional
  let A := W.mkQL.comp T
  let B := W.mkQL.comp (T + K)
  let Q : A.NonlinearRightInverse := R.comp W.quotientRightInverse
  have hd : B - A = W.mkQL.comp K := by
    ext x
    simp [A, B]
  have hp : ‖B - A‖ < (Q.nnnorm : ℝ)⁻¹ := by
    rw [hd]
    simpa only [Q, NonlinearRightInverse.comp_nnnorm, Submodule.quotientRightInverse_nnnorm,
      NNReal.coe_mul, NNReal.coe_ofNat, a] using
      hsmall.trans_lt (half_lt_self ha)
  have hs : Function.Surjective B := surjective_of_norm_sub_lt_inv_rightInverse A B Q hp
  have hm : Submodule.map W.mkQ (T + K).range = ⊤ := by
    have hr : LinearMap.range (B : E →ₗ[𝕜] F ⧸ W) = ⊤ := LinearMap.range_eq_top.2 hs
    simpa only [B, toLinearMap_comp, Submodule.toLinearMap_mkQL, LinearMap.range_comp] using hr
  have hsup : W ⊔ (T + K).range = ⊤ := (Submodule.map_mkQ_eq_top _ _).1 hm
  have hm' : Submodule.map (T + K).range.mkQ W = ⊤ :=
    (Submodule.map_mkQ_eq_top _ _).2 (by simpa only [sup_comm] using hsup)
  let L : W →ₗ[𝕜] F ⧸ (T + K).range := (T + K).range.mkQ.comp W.subtype
  have hL : Function.Surjective L := by
    apply LinearMap.range_eq_top.1
    dsimp only [L]
    rw [LinearMap.range_comp, Submodule.range_subtype]
    exact hm'
  exact Module.Finite.of_surjective L hL

/-- A compact perturbation of a surjection between real or complex Banach spaces has closed
range. The finite-dimensional cokernel, rather than a kernel complement, supplies closedness. -/
theorem isClosed_range_add_of_surjective_of_isCompactOperator [CompleteSpace E] [CompleteSpace F]
    (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    IsClosed ((T + K).range : Set F) := by
  have := cofg_range_add_of_surjective_of_isCompactOperator T K hT hK
  exact (T + K).isClosed_range_of_finite_coker

end ContinuousLinearMap
