/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.Normed.Lp.MapCLM

/-!
# Adjoints of direct sums of operators on Hilbert sums

For Hilbert spaces `E i`, the space `lp E 2` is their Hilbert direct sum, with inner product
`⟪x, y⟫ = ∑' i, ⟪x i, y i⟫`. A uniformly bounded family `T i : E i →L[𝕜] F i` of operators between
Hilbert spaces has the direct sum `⊕ T i = lp.mapCLM 2 T hK hTK : lp E 2 →L[𝕜] lp F 2`, whose
coordinate, algebraic and norm laws are in `TauCeti.Analysis.Normed.Lp.MapCLM`.

This file proves that the adjoint of a direct sum is the direct sum of the adjoints,
`(⊕ T i)† = ⊕ (T i)†`. Together with the additive and multiplicative laws, this makes
`T ↦ ⊕ T i` compatible with the star operation on bounded operators, so that direct sums of
star representations are star representations; in particular `⊕ T i` is self-adjoint exactly when
every summand is. For the ampliation `lp.ampliation ι 2 T` of a single operator this reads
`(⊕ T)† = ⊕ T†`, and its matrix coefficients are the sums `∑' i, ⟪η i, T (ξ i)⟫`.

## Main results

* `lp.adjoint_mapCLM`: `(⊕ T i)† = ⊕ (T i)†`.
* `lp.star_mapCLM`: the same identity for families of endomorphisms, stated with `star`.
* `lp.isSelfAdjoint_mapCLM_iff`: `⊕ T i` is self-adjoint iff every `T i` is.
* `lp.inner_ampliation_apply`, `lp.adjoint_ampliation`: matrix coefficients and adjoints of
  ampliations.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §II.1.
-/

public section

open scoped ENNReal InnerProduct InnerProductSpace lp

namespace lp

variable {ι 𝕜 : Type*} [RCLike 𝕜] {E F : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)] [∀ i, CompleteSpace (F i)]

/-- **Adjoint of a direct sum.** The adjoint of the direct sum `⊕ T i` on the Hilbert sums is the
direct sum of the adjoints, `(⊕ T i)† = ⊕ (T i)†`. -/
theorem adjoint_mapCLM (T : ∀ i, E i →L[𝕜] F i) {K L : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (hL : 0 ≤ L) (hTL : ∀ i, ‖(T i)†‖ ≤ L) :
    (mapCLM 2 T hK hTK)† = mapCLM 2 (fun i ↦ (T i)†) hL hTL := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y ↦ ?_).symm
  simp [lp.inner_eq_tsum, ContinuousLinearMap.adjoint_inner_left]

/-- **Star of a direct sum.** For families of endomorphisms, `star (⊕ T i) = ⊕ star (T i)`. -/
theorem star_mapCLM (T : ∀ i, E i →L[𝕜] E i) {K L : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) (hL : 0 ≤ L) (hTL : ∀ i, ‖star (T i)‖ ≤ L) :
    star (mapCLM 2 T hK hTK) = mapCLM 2 (fun i ↦ star (T i)) hL hTL := by
  simp only [ContinuousLinearMap.star_eq_adjoint] at hTL ⊢
  exact adjoint_mapCLM T hK hTK hL hTL

/-- A direct sum of endomorphisms is self-adjoint exactly when every summand is. -/
theorem isSelfAdjoint_mapCLM_iff (T : ∀ i, E i →L[𝕜] E i) {K : ℝ} (hK : 0 ≤ K)
    (hTK : ∀ i, ‖T i‖ ≤ K) :
    IsSelfAdjoint (mapCLM 2 T hK hTK) ↔ ∀ i, IsSelfAdjoint (T i) := by
  have hTK' : ∀ i, ‖star (T i)‖ ≤ K := fun i ↦ (norm_star (T i)).trans_le (hTK i)
  simp only [isSelfAdjoint_iff, star_mapCLM T hK hTK hK hTK', mapCLM_inj, funext_iff]

section Ampliation

variable {ι 𝕜 X Y : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]

/-- The matrix coefficients of an ampliation are the sums of the matrix coefficients of the
operator over the coordinates. -/
theorem inner_ampliation_apply (T : X →L[𝕜] Y) (x : ℓ²(ι, X)) (y : ℓ²(ι, Y)) :
    ⟪y, ampliation ι 2 T x⟫_𝕜 = ∑' i, ⟪y i, T (x i)⟫_𝕜 := by
  simp [lp.inner_eq_tsum]

variable [CompleteSpace X] [CompleteSpace Y]

/-- **Adjoint of an ampliation.** `(⊕ T)† = ⊕ T†`. -/
@[simp]
theorem adjoint_ampliation (T : X →L[𝕜] Y) : (ampliation ι 2 T)† = ampliation ι 2 (T†) := by
  rw [ampliation_eq_mapCLM, ampliation_eq_mapCLM]
  exact adjoint_mapCLM (fun _ ↦ T) (norm_nonneg T) (fun _ ↦ le_rfl) (norm_nonneg (T†))
    fun _ ↦ le_rfl

/-- **Star of an ampliation.** `star (⊕ T) = ⊕ star T`. -/
@[simp]
theorem star_ampliation (T : X →L[𝕜] X) : star (ampliation ι 2 T) = ampliation ι 2 (star T) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_ampliation]

end Ampliation

end lp
