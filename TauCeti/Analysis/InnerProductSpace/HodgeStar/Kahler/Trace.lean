/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Power
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.PowTrace
import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The trace identity for the normalized Kähler powers

Let `J` be an orthogonal almost complex structure on a real inner product space `V` of dimension
`2n`, with Kähler form `ω(u, w) = ⟪J u, w⟫`, and let `u₁, …, uₙ` be a basis that is orthonormal
for the Hermitian metric of `J`. For every real two-form `α`,

`α ∧ ω ^ (n - 1) / (n - 1)! = (∑ᵢ α(uᵢ, J uᵢ)) · ω ^ n / n!`

(`TauCeti.AlmostComplexStructure.pairedWedge_kahlerPowerForm`), that is,
`n α ∧ ω ^ (n - 1) = (tr_ω α) ω ^ n` with `tr_ω α = ∑ᵢ α(uᵢ, J uᵢ)`. When `α` is invariant under
`J`, the sum is the trace `∑ᵢ Re H_α(uᵢ, uᵢ)` of its Hermitian form, the sum of the eigenvalues of
`α` relative to the metric; for `α = ω` it is `n`.

Both sides are forms of top degree, so they agree once they agree on the basis
`(u₁, J u₁, …, uₙ, J uₙ)` (`ContinuousAlternatingMap.apply_eq_det_mul`). There the left side is
`∑ᵢ α(uᵢ, J uᵢ)` by the value of a two-form wedged with a power of `ω` on a symplectic basis
(`ContinuousAlternatingMap.pairedWedge_wedgePow_apply_finProdFinEquiv`), and `ω ^ n / n!` is one
(`TauCeti.AlmostComplexStructure.kahlerPowerForm_apply_complexRealFrame`).

## Main results

* `TauCeti.AlmostComplexStructure.pairedWedge_kahlerPowerForm_apply_complexRealFrame`: the value
  of `α ∧ ω ^ m / m!` on the frame of `m + 1` Hermitian-orthonormal vectors is
  `∑ᵢ α(uᵢ, J uᵢ)`.
* `TauCeti.AlmostComplexStructure.pairedWedge_kahlerPowerForm`: the trace identity in top degree.
-/

public section

noncomputable section

open Module ContinuousAlternatingMap
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

namespace TauCeti.AlmostComplexStructure

variable {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
include hJ

/-- The value of `α ∧ ω ^ m / m!` on the frame `(u₀, J u₀, …, uₘ, J uₘ)` of a family that is
orthonormal for the Hermitian metric of `J` is `∑ᵢ α(uᵢ, J uᵢ)`. -/
theorem pairedWedge_kahlerPowerForm_apply_complexRealFrame {m : ℕ} {u : Fin (m + 1) → V}
    (hu : Orthonormal ℝ u) (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) (α : V [⋀^Fin 2]→L[ℝ] ℝ) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (J.kahlerPowerForm m) α (J.complexRealFrame u) = ∑ i, α ![u i, J (u i)] := by
  have hω (a b : V) : alternatingFormEquiv V 2 J.kahlerForm ![a, b] = ⟪J a, b⟫ := by
    rw [alternatingFormEquiv_apply, inner_kahlerForm_ιMulti hJ]
  have h := pairedWedge_wedgePow_apply_finProdFinEquiv (alternatingFormEquiv V 2 J.kahlerForm) α
    (fun p : Fin (m + 1) × Fin 2 ↦ ![u p.1, J (u p.1)] p.2) (fun i j ↦ by simpa [hω] using hJu i j)
    (fun i j ↦ by simpa [hω, hJ] using (orthonormal_iff_ite.1 hu) i j)
    (fun i j ↦ by simpa [hω, hJ, real_inner_comm] using hJu j i)
  rw [kahlerPowerForm_def, pairedWedge_smul_left, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  have hframe : J.complexRealFrame u = fun r : Fin (2 * (m + 1)) ↦
      (fun p : Fin (m + 1) × Fin 2 ↦ ![u p.1, J (u p.1)] p.2)
        (finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 (m + 1)) r)) := by
    rw [complexRealFrame_eq_comp]
    rfl
  rw [hframe, h]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

/-- **The trace identity** `n α ∧ ω ^ (n - 1) = (tr_ω α) ω ^ n`, normalized: on a space of
dimension `2 (m + 1)` with a basis `u` that is orthonormal for the Hermitian metric of `J`,
`α ∧ ω ^ m / m! = (∑ᵢ α(uᵢ, J uᵢ)) · ω ^ (m + 1) / (m + 1)!`. -/
theorem pairedWedge_kahlerPowerForm {m : ℕ} (hm : finrank ℝ V = 2 * (m + 1))
    {u : Fin (m + 1) → V} (hu : Orthonormal ℝ u) (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0)
    (α : V [⋀^Fin 2]→L[ℝ] ℝ) :
    pairedWedge (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ).continuous₂
        (J.kahlerPowerForm m) α = (∑ i, α ![u i, J (u i)]) • J.kahlerPowerForm (m + 1) := by
  have hon := (orthonormal_complexRealFrame_iff hJ).2 ⟨hu, hJu⟩
  let B : Basis (Fin (2 * (m + 1))) ℝ V :=
    basisOfOrthonormalOfCardEqFinrank hon (by simp [hm])
  ext v
  rw [apply_eq_det_mul _ B v, ContinuousAlternatingMap.smul_apply,
    apply_eq_det_mul (J.kahlerPowerForm (m + 1)) B v]
  have hB : (B : Fin (2 * (m + 1)) → V) = J.complexRealFrame u :=
    coe_basisOfOrthonormalOfCardEqFinrank _ _
  rw [hB, pairedWedge_kahlerPowerForm_apply_complexRealFrame hJ hu hJu,
    kahlerPowerForm_apply_complexRealFrame hJ hu hJu, smul_eq_mul]
  ring

end TauCeti.AlmostComplexStructure
