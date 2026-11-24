/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.Surjective
public import TauCeti.Analysis.Normed.Operator.NonlinearRightInverse
public import TauCeti.Analysis.Normed.Module.Quotient
public import TauCeti.Analysis.Fredholm.ClosedRange
public import TauCeti.Topology.Algebra.LinearMapCompletion
import TauCeti.LinearAlgebra.Prod

/-!
# Compact perturbations of surjections

The functional-analytic Schwartz lemma used in the finite-dimensionality proof for cohomology
on compact Riemann surfaces: a compact perturbation of a surjective map between Banach spaces over
a complete nontrivially normed field has closed range of finite codimension. The kernel of the
surjection need not be finite or complemented.

In the cohomological application the lemma is used in a second form: for a continuous linear map
`δ : E →L[𝕜] F` between Banach spaces and a compact continuous linear map `r : G →L[𝕜] F` from a
normed space `G` that need not be complete, if every `y` is `r g + δ e`, then the range of `δ` has
finite codimension and is closed. Here `δ`
is the coboundary of cochains and `r` restricts cocycles to a relatively compact refinement, so
surjectivity of `(g, e) ↦ r g + δ e` says that every cocycle on the refinement is cohomologous to
a restricted one.

## Main statements

* `ContinuousLinearMap.cofg_range_add_of_surjective_of_isCompactOperator`: Schwartz's lemma.
* `ContinuousLinearMap.isClosed_range_add_of_surjective_of_isCompactOperator`: the range of a
  compact perturbation of a surjection is closed.
* `ContinuousLinearMap.exists_finset_forall_eq_add_sub_of_surjective_of_isCompactOperator`: the
  same finiteness elementwise, as finitely many vectors spanning modulo the range.
* `ContinuousLinearMap.cofg_range_right_of_surjective_coprod_of_isCompactOperator_left` and
  `ContinuousLinearMap.isClosed_range_right_of_surjective_coprod_of_isCompactOperator_left`: the
  cohomological form.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14 (Lemma 14.8 and Theorem 14.9).
* L. Schwartz, *Homomorphismes et applications complètement continues*, C. R. Acad. Sci. Paris
  237 (1953), 1355–1357.
-/

/- The cohomological statements are adapted from split 1 of the formalization
lookahead/ModularForms/finite-dimensional-h1-structure-sheaf; their proofs here are new. -/

public noncomputable section

open Set
open scoped NNReal Topology

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Schwartz's lemma.** A compact perturbation of a surjection between Banach spaces over a
complete nontrivially normed field has finite-dimensional cokernel, without any hypothesis on its
kernel. -/
theorem cofg_range_add_of_surjective_of_isCompactOperator [CompleteSpace E] [CompleteSpace F]
    (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    (T + K).range.CoFG := by
  let R := T.nonlinearRightInverseOfSurjective (LinearMap.range_eq_top.2 hT)
  have hR : 0 < (R.nnNorm : ℝ) := by
    exact_mod_cast T.nonlinearRightInverseOfSurjective_nnNorm_pos
      (LinearMap.range_eq_top.2 hT)
  let a : ℝ := ((R.nnNorm : ℝ) * 2)⁻¹
  have ha : 0 < a := inv_pos.2 (mul_pos hR (by norm_num))
  obtain ⟨W, hW, hsmall⟩ := exists_finiteDimensional_quotient_norm_le K hK (half_pos ha)
  have : FiniteDimensional 𝕜 W := hW
  have : IsClosed (W : Set F) := W.isClosed_of_finiteDimensional
  let A := W.mkQL.comp T
  let B := W.mkQL.comp (T + K)
  let Q : A.NonlinearRightInverse := R.comp W.quotientRightInverse
  have hd : B - A = W.mkQL.comp K := by
    ext x
    simp [A, B]
  have hp : ‖B - A‖ < (Q.nnNorm : ℝ)⁻¹ := by
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

/-- A compact perturbation of a surjection between Banach spaces over a complete nontrivially
normed field has closed range. The finite-dimensional cokernel, rather than a kernel complement,
supplies closedness. -/
theorem isClosed_range_add_of_surjective_of_isCompactOperator [CompleteSpace E] [CompleteSpace F]
    (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    IsClosed ((T + K).range : Set F) := by
  have := cofg_range_add_of_surjective_of_isCompactOperator T K hT hK
  exact (T + K).isClosed_range_of_finite_coker

/-- **Schwartz's lemma, spanning form.** If `T` is a surjection and `K` a compact operator
between Banach spaces over a complete nontrivially normed field, finitely many vectors span `F`
modulo the range of `T - K`: every `y` is `b + (T x - K x)` with `b` in their span. -/
theorem exists_finset_forall_eq_add_sub_of_surjective_of_isCompactOperator [CompleteSpace E]
    [CompleteSpace F] (T K : E →L[𝕜] F) (hT : Function.Surjective T) (hK : IsCompactOperator K) :
    ∃ s : Finset F, ∀ y, ∃ b ∈ Submodule.span 𝕜 (s : Set F), ∃ x, y = b + (T x - K x) := by
  have hS := cofg_range_add_of_surjective_of_isCompactOperator T (-K) hT hK.neg
  obtain ⟨B, hB⟩ := Submodule.exists_isCompl (T + -K).range
  obtain ⟨s, rfl⟩ := hS.fg_of_isCompl hB
  refine ⟨s, fun y ↦ ?_⟩
  obtain ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩ :=
    Submodule.mem_sup.mp (hB.sup_eq_top ▸ Submodule.mem_top (x := y))
  exact ⟨b, hb, x, by simp [add_comm, sub_eq_add_neg]⟩

open UniformSpace in
/-- **Schwartz's lemma, cohomological form.** Let `δ : E →L[𝕜] F` be a continuous linear map
between Banach spaces and `r : G →L[𝕜] F` a compact continuous linear map. If every point of `F`
is of the form `r g + δ e`, then the range of `δ` has finite codimension. The source `G` of `r`
need not be complete. -/
theorem cofg_range_right_of_surjective_coprod_of_isCompactOperator_left [CompleteSpace E]
    [CompleteSpace F] (r : G →L[𝕜] F) (δ : E →L[𝕜] F) (h : Function.Surjective (r.coprod δ))
    (hr : IsCompactOperator r) : δ.range.CoFG := by
  let r' : Completion G →L[𝕜] F := r.fromCompletion
  have hcomp : r' ∘L Completion.toComplL = r := by
    ext x
    exact r.fromCompletion_apply_coe x
  have h' : Function.Surjective (r'.coprod δ) :=
    LinearMap.surjective_coprod_of_comp_left (h := (Completion.toComplL : G →L[𝕜] _).toLinearMap)
      (by rwa [← toLinearMap_comp, hcomp])
  have hK : IsCompactOperator (-(r'.comp (fst 𝕜 (Completion G) E))) :=
    (hr.fromCompletion.comp_clm (fst 𝕜 _ E)).neg
  have hδ : r'.coprod δ + -(r'.comp (fst 𝕜 (Completion G) E)) = δ.comp (snd 𝕜 _ E) := by
    rw [← comp_fst_add_comp_snd]
    abel
  simpa [hδ, LinearMap.range_comp] using
    cofg_range_add_of_surjective_of_isCompactOperator _ _ h' hK

/-- Let `δ : E →L[𝕜] F` be a continuous linear map between Banach spaces and `r : G →L[𝕜] F` a
compact continuous linear map. If every point of `F` is of the form `r g + δ e`, then the range of
`δ` is closed. The source `G` of `r` need not be complete. -/
theorem isClosed_range_right_of_surjective_coprod_of_isCompactOperator_left [CompleteSpace E]
    [CompleteSpace F] (r : G →L[𝕜] F) (δ : E →L[𝕜] F)
    (h : Function.Surjective (r.coprod δ)) (hr : IsCompactOperator r) :
    IsClosed (δ.range : Set F) := by
  have := cofg_range_right_of_surjective_coprod_of_isCompactOperator_left r δ h hr
  exact δ.isClosed_range_of_finite_coker

end ContinuousLinearMap
