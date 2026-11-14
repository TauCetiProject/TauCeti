/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Embedding
public import TauCeti.Analysis.Normed.Lp.HahnBanach

/-!
# Pietsch's embedding identity

Over `ℝ` or `ℂ`, the Gelfand numbers of `T : E →L[𝕜] F` are the approximation numbers of
`J ∘L T`, where `J` is evaluation on the closed unit ball of the continuous dual of `F`
(`ContinuousLinearMap.singularValue_dualBallEmbedding_comp`). Thus Gelfand numbers become
approximation numbers after placing the target in its canonical `ℓ∞` space. More generally, the
same identity holds for every linear isometry `J` of `F` into a scalar-valued `ℓ∞` space
(`ContinuousLinearMap.singularValue_linearIsometry_lpInfty_comp`).

The lower bound holds over every nontrivially normed field, for every linear isometry into any
target (`ContinuousLinearMap.gelfandNumber_le_singularValue_linearIsometry_comp`). For the reverse
bound, which uses Hahn–Banach and hence needs `ℝ` or `ℂ`, extend the restriction of `J ∘L T`
from an admissible subspace without increasing its norm. Subtracting this extension leaves an
operator factoring through the finite-dimensional quotient. Neither space needs to be complete.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped ENNReal NNReal

namespace ContinuousLinearMap

section LowerBound

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Gelfand numbers are bounded by approximation numbers after any isometric embedding
of the target. -/
theorem gelfandNumber_le_singularValue_linearIsometry_comp (T : E →L[𝕜] F) (J : F →ₗᵢ[𝕜] G)
    (n : ℕ) : T.gelfandNumber n ≤ (J.toContinuousLinearMap ∘L T).singularValue n := by
  have hJ : T.gelfandNumber n ≤ (J.toContinuousLinearMap ∘L T).gelfandNumber n :=
    le_gelfandNumber_iff.mpr fun M _ hM ↦ (T.gelfandNumber_le hM).trans_eq <| by
      rw [comp_assoc, ← NNReal.coe_inj, coe_nnNorm, coe_nnNorm, J.norm_toContinuousLinearMap_comp]
  refine hJ.trans (le_singularValue_iff.mpr fun R hR ↦ ?_)
  simpa [gelfandNumber_eq_zero_of_rank_le hR] using
    R.gelfandNumber_add_le (J.toContinuousLinearMap ∘L T - R) n

end LowerBound

section Embedding

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Gelfand numbers are the approximation numbers after any isometric embedding of the target
into a scalar-valued `ℓ∞` space. -/
theorem singularValue_linearIsometry_lpInfty_comp (T : E →L[𝕜] F)
    (J : F →ₗᵢ[𝕜] lp (fun _ : ι ↦ 𝕜) ∞) (n : ℕ) :
    (J.toContinuousLinearMap ∘L T).singularValue n = T.gelfandNumber n := by
  refine le_antisymm (le_gelfandNumber_iff.mpr fun M _ hM ↦ ?_)
    (T.gelfandNumber_le_singularValue_linearIsometry_comp J n)
  let JT := J.toContinuousLinearMap ∘L T
  obtain ⟨U, hU, hnorm⟩ := M.exists_extension_lpInfty_norm_eq (JT ∘L M.subtypeL)
  let R := JT - U
  have hker : M ≤ LinearMap.ker R.toLinearMap := by
    intro x hx
    have h := congrArg (fun f ↦ f (⟨x, hx⟩ : M)) hU
    simpa [R] using sub_eq_zero.mpr h.symm
  have hR : R.rank ≤ n := by
    let L := M.liftQ R.toLinearMap hker
    have hL : R.toLinearMap = L.comp M.mkQ := (M.liftQ_mkQ R.toLinearMap hker).symm
    have h : L.rank ≤ n := Cardinal.lift_le_nat_iff.mp
      ((lift_rank_range_le L).trans (Cardinal.lift_le_nat_iff.mpr hM))
    rw [hL]
    exact (LinearMap.rank_comp_le_left M.mkQ L).trans h
  calc
    JT.singularValue n ≤ ‖JT - R‖₊ := singularValue_le_nnnorm_sub _ hR
    _ = ‖U‖₊ := by simp [R]
    _ = ‖T ∘L M.subtypeL‖₊ := by
      rw [← NNReal.coe_inj, coe_nnNorm, coe_nnNorm, hnorm, comp_assoc]
      exact J.norm_toContinuousLinearMap_comp

end Embedding

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Pietsch's embedding identity.** Gelfand numbers are the approximation numbers after
evaluation on the dual unit ball of the target. -/
@[simp]
theorem singularValue_dualBallEmbedding_comp (T : E →L[𝕜] F) (n : ℕ) :
    ((TauCeti.dualBallEmbedding 𝕜 F).toContinuousLinearMap ∘L T).singularValue n =
      T.gelfandNumber n :=
  T.singularValue_linearIsometry_lpInfty_comp _ n

end ContinuousLinearMap
