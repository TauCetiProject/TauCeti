/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Power
public import TauCeti.Topology.Algebra.Module.Alternating.Wedge.Pow.Trace
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.Specializations
public import TauCeti.Analysis.InnerProductSpace.RelativeEigenvalues.HermitianForm
public import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex

/-!
# The trace identity for the normalized Kähler powers

Let `J` be an orthogonal almost complex structure on a real inner product space `V` of dimension
`2n`, with Kähler form `ω(u, w) = ⟪J u, w⟫`, and let `u₁, …, uₙ` be a basis that is orthonormal
for the Hermitian metric of `J`. For every real two-form `α`,

`α ∧ ω ^ (n - 1) / (n - 1)! = (∑ᵢ α(uᵢ, J uᵢ)) · ω ^ n / n!`

(`TauCeti.AlmostComplexStructure.wedge_kahlerPowerForm`), that is,
`n α ∧ ω ^ (n - 1) = (tr_ω α) ω ^ n` with `tr_ω α = ∑ᵢ α(uᵢ, J uᵢ)`. When `α` is invariant under
`J`, the sum is the trace `∑ᵢ Re H_α(uᵢ, uᵢ)` of its Hermitian form, the sum of the eigenvalues of
`α` relative to the metric; for `α = ω` it is `n`.

Both sides are forms of top degree, so the left side is its value on the basis
`(u₁, J u₁, …, uₙ, J uₙ)` times `ω ^ n / n!`
(`TauCeti.AlmostComplexStructure.eq_smul_kahlerPowerForm`). That value is `∑ᵢ α(uᵢ, J uᵢ)` by the
value of a two-form wedged with a power of `ω` on a symplectic basis
(`ContinuousAlternatingMap.pairedWedge_wedgePow_apply_finProdFinEquiv`).

On a complex inner product space `E` of dimension `n`, with `J` multiplication by `i` and the real
inner product `Re ⟪·, ·⟫_ℂ`, a two-form `α` of type (1,1) has the eigenvalues `λ[α]` of its
Hermitian form `H_α` relative to the inner product, and their sum is `∑ᵢ α(uᵢ, i uᵢ)` for any
orthonormal basis `u` (`ContinuousAlternatingMap.sum_relEigenvalues_hermitianSesqForm`). So the
trace identity reads `n α ∧ ω ^ (n - 1) = (∑ⱼ λⱼ[α]) ω ^ n`
(`TauCeti.AlmostComplexStructure.nsmul_wedge_wedgePow_ofComplexModule`).

## Main results

* `TauCeti.AlmostComplexStructure.wedge_kahlerPowerForm_apply_complexRealFrame`: the value
  of `α ∧ ω ^ m / m!` on the frame of `m + 1` Hermitian-orthonormal vectors is
  `∑ᵢ α(uᵢ, J uᵢ)`.
* `TauCeti.AlmostComplexStructure.wedge_kahlerPowerForm`: the trace identity in top degree.
* `TauCeti.AlmostComplexStructure.wedge_kahlerPowerForm_ofComplexModule`: on a complex inner
  product space, `α ∧ ω ^ (n - 1) / (n - 1)! = (∑ⱼ λⱼ[α]) · ω ^ n / n!` for `α` of type (1,1).
* `TauCeti.AlmostComplexStructure.nsmul_wedge_wedgePow_ofComplexModule`: the same identity
  without the factorials, `n α ∧ ω ^ (n - 1) = (∑ⱼ λⱼ[α]) ω ^ n`.

## References

* G. Székelyhidi, *Fully non-linear elliptic equations on compact Hermitian manifolds*,
  J. Differential Geom. 109 (2018), Section 2.
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
theorem wedge_kahlerPowerForm_apply_complexRealFrame {m : ℕ} {u : Fin (m + 1) → V}
    (hu : Orthonormal ℝ u) (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0) (α : V [⋀^Fin 2]→L[ℝ] ℝ) :
    wedge (J.kahlerPowerForm m) α (J.complexRealFrame u) = ∑ i, α ![u i, J (u i)] := by
  -- The frame vectors `b (i, 0)` and `b (i, 1)` reduce to `u i` and `J (u i)`.
  have h := pairedWedge_wedgePow_apply_finProdFinEquiv (alternatingFormEquiv V 2 J.kahlerForm) α
    (fun p : Fin (m + 1) × Fin 2 ↦ ![u p.1, J (u p.1)] p.2)
    (alternatingFormEquiv_kahlerForm_vecCons_eq_zero hJ hJu)
    (alternatingFormEquiv_kahlerForm_vecCons_apply hJ hu)
    (alternatingFormEquiv_kahlerForm_vecCons_apply_apply_eq_zero hJ hJu)
  rw [wedge_def, kahlerPowerForm_def, pairedWedge_smul_left, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, complexRealFrame_def, h]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp

/-- **The trace identity** `n α ∧ ω ^ (n - 1) = (tr_ω α) ω ^ n`, normalized: on a space of
dimension `2 (m + 1)` with a basis `u` that is orthonormal for the Hermitian metric of `J`,
`α ∧ ω ^ m / m! = (∑ᵢ α(uᵢ, J uᵢ)) · ω ^ (m + 1) / (m + 1)!`. -/
theorem wedge_kahlerPowerForm {m : ℕ} (hm : finrank ℝ V = 2 * (m + 1))
    {u : Fin (m + 1) → V} (hu : Orthonormal ℝ u) (hJu : ∀ i j, ⟪J (u i), u j⟫ = 0)
    (α : V [⋀^Fin 2]→L[ℝ] ℝ) :
    wedge (J.kahlerPowerForm m) α = (∑ i, α ![u i, J (u i)]) • J.kahlerPowerForm (m + 1) := by
  rw [eq_smul_kahlerPowerForm hJ hm hu hJu (wedge (J.kahlerPowerForm m) α),
    wedge_kahlerPowerForm_apply_complexRealFrame hJ hu hJu]

omit hJ

section Complex

/-! ### The trace identity through the eigenvalues of a (1,1)-form -/

attribute [local instance] InnerProductSpace.complexToReal

open Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {α : E [⋀^Fin 2]→L[ℝ] ℝ} (hα : ∀ u v : E, α ![I • u, I • v] = α ![u, v])
include hα

/-- **The trace identity through eigenvalues**, normalized: on a complex inner product space of
dimension `m + 1`, with `ω` the Kähler form of multiplication by `i`, a real two-form `α` of type
(1,1) satisfies `α ∧ ω ^ m / m! = (∑ⱼ λⱼ[α]) · ω ^ (m + 1) / (m + 1)!`, where `λ[α]` are the
eigenvalues of the Hermitian form `H_α` relative to the inner product. -/
theorem wedge_kahlerPowerForm_ofComplexModule {m : ℕ} (hm : finrank ℂ E = m + 1) :
    wedge ((ofComplexModule E).kahlerPowerForm m) α =
      (∑ j, (isSymm_hermitianSesqForm hα).relEigenvalues hm j) •
        (ofComplexModule E).kahlerPowerForm (m + 1) := by
  let b : OrthonormalBasis (Fin (m + 1)) ℂ E := (stdOrthonormalBasis ℂ E).reindex (finCongr hm)
  have hbR : Orthonormal ℝ (b : Fin (m + 1) → E) := b.orthonormal.real
  have hm' : finrank ℝ E = 2 * (m + 1) := by rw [finrank_real_of_complex, hm]
  rw [ContinuousAlternatingMap.sum_relEigenvalues_hermitianSesqForm hα hm b,
    wedge_kahlerPowerForm real_inner_ofComplexModule_ofComplexModule hm' hbR
      b.orthonormal.real_inner_ofComplexModule_eq_zero α]
  simp only [ofComplexModule_apply]

/-- **The trace identity through eigenvalues** `n α ∧ ω ^ (n - 1) = (∑ⱼ λⱼ[α]) ω ^ n` on a
complex inner product space of dimension `n = m + 1`, for `ω` the Kähler form of multiplication by
`i` and a real two-form `α` of type (1,1), with `λ[α]` the eigenvalues of `H_α` relative to the
inner product. -/
theorem nsmul_wedge_wedgePow_ofComplexModule {m : ℕ} (hm : finrank ℂ E = m + 1) :
    (m + 1) • wedge ((alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow m) α =
      (∑ j, (isSymm_hermitianSesqForm hα).relEigenvalues hm j) •
        (alternatingFormEquiv E 2 (ofComplexModule E).kahlerForm).wedgePow (m + 1) := by
  have h := wedge_kahlerPowerForm_ofComplexModule hα hm
  rw [kahlerPowerForm_def, kahlerPowerForm_def, wedge_smul_left, smul_smul] at h
  have hf : (m.factorial : ℝ) ≠ 0 := by positivity
  have h' := congrArg (fun φ ↦ ((m + 1).factorial : ℝ) • φ) h
  simp only [smul_smul, Nat.factorial_succ, Nat.cast_mul] at h'
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  convert h' using 2
  · field_simp
  · field_simp

end Complex

end TauCeti.AlmostComplexStructure
