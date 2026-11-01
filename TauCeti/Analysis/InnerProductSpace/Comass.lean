/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.Normed.Module.Alternating.Dual
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.InnerProductSpace.ExteriorPower
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard

/-!
# Comass of forms and mass of `k`-vectors

Let `E` be a finite-dimensional real inner product space. Mathlib equips the `k`-vectors
`⋀[ℝ]^k E` with the Gram inner product, `⟪v₁ ∧ ⋯ ∧ vₖ, w₁ ∧ ⋯ ∧ wₖ⟫ = det ⟪vⱼ, wᵢ⟫`, so that
`‖v₁ ∧ ⋯ ∧ vₖ‖` is the `k`-dimensional volume of the parallelepiped spanned by the `vᵢ`. This file
relates that norm to the two norms of geometric measure theory.

* The *comass* of a form `ω : E [⋀^Fin k]→L[ℝ] F` is the supremum of `‖ω v‖` over the families `v`
  whose wedge `v₁ ∧ ⋯ ∧ vₖ` has norm at most one. It is the native operator norm of `ω`:
  `ContinuousAlternatingMap.opNorm_le_iff_le_mul_norm_ιMulti`. One direction is Hadamard's
  inequality `exteriorPower.norm_ιMulti_le_prod_norm`; the other writes `v` in an orthonormal
  basis of its span, where `ω` is a multiple of the determinant. Thus the operator norm used for
  the mass of currents is Federer's comass, and no second norm on forms is needed.
* The *mass* of a `k`-vector `ξ` is the dual norm of the comass: the norm of `ξ` as a functional
  on forms, through `exteriorPower.formDualEquiv`. It agrees with the inner product norm on
  wedges of vectors (`exteriorPower.norm_formDualEquiv_ιMulti`) and is compared with it in general
  by
  `‖ξ‖ ≤ ‖ξ‖_mass ≤ √(n choose k) ‖ξ‖` with `n = finrank ℝ E`
  (`exteriorPower.norm_le_norm_formDualEquiv`, `exteriorPower.norm_formDualEquiv_le`). Dually the
  comass of the form `v ↦ ⟪η, v₁ ∧ ⋯ ∧ vₖ⟫` is at most `‖η‖`
  (`TauCeti.norm_alternatingFormEquiv_le`).

## Main results

* `ContinuousAlternatingMap.le_opNorm_mul_norm_ιMulti`: `‖ω v‖ ≤ ‖ω‖ * ‖v₁ ∧ ⋯ ∧ vₖ‖`.
* `ContinuousAlternatingMap.opNorm_le_iff_le_mul_norm_ιMulti`: the operator norm is the comass.
* `exteriorPower.norm_formDualEquiv_ιMulti`: the mass of a wedge of vectors is its volume.
* `exteriorPower.norm_le_norm_formDualEquiv`, `exteriorPower.norm_formDualEquiv_le`: the mass of
  `k`-vectors is comparable with the inner product norm.

## References

* H. Federer, *Geometric Measure Theory*, §1.8.1.
-/

public section

noncomputable section

open Module exteriorPower
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace ContinuousAlternatingMap

/-- The comass bound for real-valued forms: `|ω v| ≤ ‖ω‖ * ‖v₁ ∧ ⋯ ∧ vₖ‖`. -/
private theorem abs_apply_le_opNorm_mul_norm_ιMulti (ω : E [⋀^Fin k]→L[ℝ] ℝ) (v : Fin k → E) :
    |ω v| ≤ ‖ω‖ * ‖ιMulti ℝ k v‖ := by
  -- On the span `W` of an independent family `v`, with an orthonormal basis `b`, the form is
  -- `ω b` times the determinant in `b`, and the determinant of `v` has absolute value
  -- `‖v₁ ∧ ⋯ ∧ vₖ‖`.
  by_cases hv : LinearIndependent ℝ v
  swap
  · have hω : ω v = 0 := by
      simpa [coe_toAlternatingMap] using ω.toAlternatingMap.map_linearDependent v hv
    rw [hω, abs_zero]
    positivity
  set W := Submodule.span ℝ (Set.range v)
  let w : Fin k → W := fun i ↦ ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  let b : OrthonormalBasis (Fin k) ℝ W := (stdOrthonormalBasis ℝ W).reindex
    (finCongr (by simpa using finrank_span_eq_card hv))
  let f : W [⋀^Fin k]→ₗ[ℝ] ℝ := ω.toAlternatingMap.compLinearMap W.subtype
  have hf : ω v = f b * b.toBasis.det w := by
    simpa [f, w, mul_comm] using DFunLike.congr_fun (f.eq_smul_basis_det b.toBasis) w
  have hb : |f b| ≤ ‖ω‖ := by
    have hbi (i : Fin k) : ‖(b i : E)‖ = 1 := by rw [Submodule.norm_coe, b.norm_eq_one]
    simpa [f, hbi] using ω.le_opNorm (fun i ↦ (b i : E))
  have hdet : |b.toBasis.det w| = ‖ιMulti ℝ k v‖ := by
    have hgram : Matrix.gram ℝ w = Matrix.gram ℝ v := by
      ext i j
      simp [Matrix.gram, w]
    rw [← Real.norm_eq_abs]
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
    rw [norm_ιMulti_sq, ← hgram, b.det_gram_eq_norm_det_sq w]
    simp
  rw [hf, abs_mul, ← hdet]
  gcongr

/-- The value of a form on `(v₁, …, vₖ)` is bounded by its operator norm times the volume
`‖v₁ ∧ ⋯ ∧ vₖ‖`, which may be much smaller than `‖v₁‖ ⋯ ‖vₖ‖`. -/
theorem le_opNorm_mul_norm_ιMulti (ω : E [⋀^Fin k]→L[ℝ] F) (v : Fin k → E) :
    ‖ω v‖ ≤ ‖ω‖ * ‖ιMulti ℝ k v‖ := by
  obtain ⟨g, hg, hgv⟩ := exists_dual_vector'' ℝ (ω v)
  have hgω : ‖g.compContinuousAlternatingMap ω‖ ≤ ‖ω‖ :=
    (g.norm_compContinuousAlternatingMap_le ω).trans (mul_le_of_le_one_left (norm_nonneg ω) hg)
  calc ‖ω v‖ = g (ω v) := by simpa using hgv.symm
    _ ≤ |g.compContinuousAlternatingMap ω v| := le_abs_self _
    _ ≤ ‖g.compContinuousAlternatingMap ω‖ * ‖ιMulti ℝ k v‖ :=
      abs_apply_le_opNorm_mul_norm_ιMulti _ v
    _ ≤ ‖ω‖ * ‖ιMulti ℝ k v‖ := by gcongr

/-- **The operator norm of a form is its comass**: `‖ω‖ ≤ C` exactly when
`‖ω v‖ ≤ C ‖v₁ ∧ ⋯ ∧ vₖ‖` for every family `v`, so `‖ω‖` is the supremum of `‖ω v‖` over the
families whose wedge has norm at most one. -/
theorem opNorm_le_iff_le_mul_norm_ιMulti {ω : E [⋀^Fin k]→L[ℝ] F} {C : ℝ} (hC : 0 ≤ C) :
    ‖ω‖ ≤ C ↔ ∀ v : Fin k → E, ‖ω v‖ ≤ C * ‖ιMulti ℝ k v‖ := by
  refine ⟨fun h v ↦ (ω.le_opNorm_mul_norm_ιMulti v).trans (by gcongr), fun h ↦ ?_⟩
  exact ω.opNorm_le_bound hC fun v ↦ (h v).trans (by gcongr; exact norm_ιMulti_le_prod_norm v)

end ContinuousAlternatingMap

namespace TauCeti

/-- The comass of the form `v ↦ ⟪η, v₁ ∧ ⋯ ∧ vₖ⟫` is at most the norm of `η`. -/
theorem norm_alternatingFormEquiv_le (η : ⋀[ℝ]^k E) : ‖alternatingFormEquiv E k η‖ ≤ ‖η‖ :=
  (alternatingFormEquiv E k η).opNorm_le_bound (norm_nonneg η) fun v ↦ by
    rw [alternatingFormEquiv_apply, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (by gcongr; exact norm_ιMulti_le_prod_norm v)

end TauCeti

namespace exteriorPower

/-- A `k`-vector `ξ` pairs with the form `v ↦ ⟪η, v₁ ∧ ⋯ ∧ vₖ⟫` to `⟪η, ξ⟫`. -/
@[simp]
theorem formDualEquiv_alternatingFormEquiv (ξ η : ⋀[ℝ]^k E) :
    formDualEquiv ℝ E k ξ (TauCeti.alternatingFormEquiv E k η) = ⟪η, ξ⟫ := by
  rw [formDualEquiv_apply]
  suffices h : continuousAlternatingMapLinearEquiv ℝ E k ℝ (TauCeti.alternatingFormEquiv E k η) =
      innerₗ (⋀[ℝ]^k E) η from congr($h ξ)
  ext v
  simp

/-- The inner product norm of a `k`-vector is at most its mass, the norm of `ξ` as a functional
on forms. -/
theorem norm_le_norm_formDualEquiv (ξ : ⋀[ℝ]^k E) : ‖ξ‖ ≤ ‖formDualEquiv ℝ E k ξ‖ := by
  rcases (norm_nonneg ξ).eq_or_lt with h | h
  · rw [← h]
    exact norm_nonneg (formDualEquiv ℝ E k ξ)
  refine le_of_mul_le_mul_right ?_ h
  calc ‖ξ‖ * ‖ξ‖ = formDualEquiv ℝ E k ξ (TauCeti.alternatingFormEquiv E k ξ) := by
        rw [formDualEquiv_alternatingFormEquiv, real_inner_self_eq_norm_mul_norm]
    _ ≤ ‖formDualEquiv ℝ E k ξ‖ * ‖TauCeti.alternatingFormEquiv E k ξ‖ :=
      (Real.le_norm_self _).trans ((formDualEquiv ℝ E k ξ).le_opNorm _)
    _ ≤ ‖formDualEquiv ℝ E k ξ‖ * ‖ξ‖ := by gcongr; exact TauCeti.norm_alternatingFormEquiv_le ξ

/-- **The mass of a simple `k`-vector is its volume**: as a functional on forms, `v₁ ∧ ⋯ ∧ vₖ` has
norm `‖v₁ ∧ ⋯ ∧ vₖ‖`. -/
@[simp]
theorem norm_formDualEquiv_ιMulti (v : Fin k → E) :
    ‖formDualEquiv ℝ E k (ιMulti ℝ k v)‖ = ‖ιMulti ℝ k v‖ := by
  refine le_antisymm ?_ (norm_le_norm_formDualEquiv _)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ω ↦ ?_
  rw [formDualEquiv_ιMulti_apply, mul_comm]
  exact ω.le_opNorm_mul_norm_ιMulti v

/-- The mass of a `k`-vector is at most `√(n choose k)` times its inner product norm, where
`n = finrank ℝ E`. -/
theorem norm_formDualEquiv_le (ξ : ⋀[ℝ]^k E) :
    ‖formDualEquiv ℝ E k ξ‖ ≤ √((finrank ℝ E).choose k) * ‖ξ‖ := by
  set B := (stdOrthonormalBasis ℝ E).exteriorPower k
  -- Each vector of the orthonormal basis `B` of `⋀ᵏ E` is a wedge of vectors, so has mass one.
  have hB (s) : ‖formDualEquiv ℝ E k (B s)‖ = 1 := by
    have : B s = ιMulti_family ℝ k (stdOrthonormalBasis ℝ E) s := by
      rw [← B.coe_toBasis, OrthonormalBasis.toBasis_exteriorPower, coe_basis,
        OrthonormalBasis.coe_toBasis]
    rw [← B.norm_eq_one s, this, ιMulti_family, norm_formDualEquiv_ιMulti]
  have hcard : Fintype.card (Set.powersetCard (Fin (finrank ℝ E)) k) = (finrank ℝ E).choose k := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  -- Cauchy–Schwarz and Parseval bound the `ℓ¹` norm of the coefficients of `ξ` in `B`.
  have hsum : ∑ s, |⟪B s, ξ⟫| ≤ √((finrank ℝ E).choose k) * ‖ξ‖ := by
    rw [← Real.sqrt_sq (norm_nonneg ξ), ← B.sum_sq_norm_inner_right ξ,
      ← Real.sqrt_mul (by positivity), ← hcard]
    refine Real.le_sqrt_of_sq_le ?_
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun s ↦ |⟪B s, ξ⟫|)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ω ↦ ?_
  have hω (s) : |formDualEquiv ℝ E k (B s) ω| ≤ ‖ω‖ := by
    simpa [hB, Real.norm_eq_abs] using (formDualEquiv ℝ E k (B s)).le_opNorm ω
  calc ‖formDualEquiv ℝ E k ξ ω‖ = |∑ s, ⟪B s, ξ⟫ * formDualEquiv ℝ E k (B s) ω| := by
        conv_lhs => rw [← B.sum_repr' ξ]
        simp [Real.norm_eq_abs]
    _ ≤ ∑ s, |⟪B s, ξ⟫| * ‖ω‖ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
      rw [abs_mul]
      gcongr
      exact hω s
    _ = (∑ s, |⟪B s, ξ⟫|) * ‖ω‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := by gcongr

end exteriorPower
