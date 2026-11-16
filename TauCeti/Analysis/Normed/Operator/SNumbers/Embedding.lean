/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.SNumbers.Gelfand
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Basic
public import TauCeti.Analysis.Normed.Module.Dual.Embedding
public import TauCeti.Analysis.Normed.Module.HahnBanach

/-!
# Pietsch's embedding identity

The Gelfand numbers of `T : E →L[𝕜] F` are the approximation numbers of `J ∘L T`, where
`J` is evaluation on the closed unit ball of the continuous dual of `F`. Thus Gelfand
numbers become approximation numbers after placing the target in its canonical `ℓ∞` space.

The lower bound holds for every linear isometry into any target. For the reverse bound,
extend the restriction of `J ∘L T` from an admissible subspace without increasing its norm.
Subtracting this extension leaves an operator factoring through the finite-dimensional
quotient. Neither space needs to be complete.

## References

* A. Pietsch, *s-Numbers of operators in Banach spaces*, Studia Math. 51 (1974), §4.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press (1987), Chapter 2.
-/

public section

open scoped NNReal

namespace ContinuousLinearMap

section LowerBound

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Gelfand numbers are bounded by approximation numbers after any isometric embedding
of the target. -/
theorem gelfandNumber_le_singularValue_comp (T : E →L[𝕜] F) (J : F →ₗᵢ[𝕜] G) (n : ℕ) :
    T.gelfandNumber n ≤ (J.toContinuousLinearMap ∘L T).singularValue n := by
  refine le_singularValue_iff.mpr fun R hR ↦ ?_
  have hrank : Module.rank 𝕜 (E ⧸ LinearMap.ker R.toLinearMap) ≤ n := by
    have h := R.toLinearMap.quotKerEquivRange.lift_rank_eq
    exact Cardinal.lift_le_nat_iff.mp (h.trans_le (Cardinal.lift_le_nat_iff.mpr hR))
  refine (T.gelfandNumber_le hrank).trans (opNNNorm_le_bound _ _ fun x ↦ ?_)
  have hx : R x = 0 := x.2
  have h : ‖T x‖ ≤ ‖J.toContinuousLinearMap ∘L T - R‖ * ‖x‖ := by
    simpa [hx, Submodule.norm_coe] using
      (J.toContinuousLinearMap ∘L T - R).le_opNorm (x : E)
  exact_mod_cast h

end LowerBound

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Pietsch's embedding identity.** Gelfand numbers are the approximation numbers after
evaluation on the dual unit ball of the target. -/
theorem singularValue_dualBallEmbedding_comp (T : E →L[𝕜] F) (n : ℕ) :
    ((TauCeti.dualBallEmbedding 𝕜 F).toContinuousLinearMap ∘L T).singularValue n =
      T.gelfandNumber n := by
  let J := (TauCeti.dualBallEmbedding 𝕜 F).toContinuousLinearMap
  refine le_antisymm (le_gelfandNumber_iff.mpr fun M _ hM ↦ ?_)
    (T.gelfandNumber_le_singularValue_comp _ n)
  obtain ⟨U, hU, hnorm⟩ := M.exists_extension_lpInfty ((J ∘L T) ∘L M.subtypeL)
  let R := J ∘L T - U
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
    (J ∘L T).singularValue n ≤ ‖J ∘L T - R‖₊ := singularValue_le_nnnorm_sub _ hR
    _ = ‖U‖₊ := by simp [R]
    _ = ‖T ∘L M.subtypeL‖₊ := by
      rw [hnorm, comp_assoc, ← NNReal.coe_inj, coe_nnNorm, coe_nnNorm]
      exact (TauCeti.dualBallEmbedding 𝕜 F).norm_toContinuousLinearMap_comp

end ContinuousLinearMap
