/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Factoring finitely many vectors through orthogonal vectors

Given finitely many vectors `vᵣ = (v k r)ₖ ∈ 𝕜^κ` over `𝕜 = ℝ` or `ℂ`, indexed by `r` in a
finite type `ι`, the normalized Gram–Schmidt process produces vectors `eₜ ∈ 𝕜^κ`, `t ∈ ι`, that
are pairwise orthogonal, each a unit vector or zero, and span every `vᵣ`. Writing
`vᵣ = ∑ t, ⟪eₜ, vᵣ⟫ eₜ` gives a factorization `v k r = ∑ t, e t k * v' t r` with
`∑ t r, ‖v' t r‖² = ∑ k r, ‖v k r‖²` (Parseval's identity for each `vᵣ`).

## Main declarations

* `InnerProductSpace.exists_orthogonal_factor`: the factorization `v = e v'`.
-/

public section

open scoped InnerProductSpace

namespace InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The factorization of `exists_orthogonal_factor` for vectors indexed by `Fin n`, where the
Gram–Schmidt process applies. -/
private theorem exists_orthogonal_factor_fin {κ : Type*} [Fintype κ] {n : ℕ} (v : κ → Fin n → 𝕜) :
    ∃ (e : Fin n → κ → 𝕜) (v' : Fin n → Fin n → 𝕜),
      (∀ k r, v k r = ∑ t, e t k * v' t r) ∧
      (∀ t t', t ≠ t' → ∑ k, e t k * star (e t' k) = 0) ∧
      (∀ t, ∑ k, ‖e t k‖ ^ 2 ≤ 1) ∧
      ∑ t, ∑ r, ‖v' t r‖ ^ 2 = ∑ k, ∑ r, ‖v k r‖ ^ 2 := by
  let c : Fin n → EuclideanSpace 𝕜 κ := fun r => WithLp.toLp 2 fun k => v k r
  let E := InnerProductSpace.gramSchmidtNormed 𝕜 c
  have horth (t t' : Fin n) (h : t ≠ t') : ⟪E t', E t⟫_𝕜 = 0 := by
    simp [E, InnerProductSpace.gramSchmidtNormed, inner_smul_left, inner_smul_right,
      InnerProductSpace.gramSchmidt_orthogonal 𝕜 c h.symm]
  have hnorm (t : Fin n) : ‖E t‖ ^ 2 • E t = E t := by
    by_cases h : E t = 0
    · simp [h]
    · rw [InnerProductSpace.gramSchmidtNormed_unit_length' h, one_pow, one_smul]
  have hrec (r : Fin n) : c r = ∑ t, ⟪E t, c r⟫_𝕜 • E t := by
    have hmem : c r ∈ Submodule.span 𝕜 (Set.range E) := by
      rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]
      exact Submodule.subset_span ⟨r, rfl⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hmem
    have hcoef (t : Fin n) : ⟪E t, c r⟫_𝕜 = a t * ((‖E t‖ ^ 2 : ℝ) : 𝕜) := by
      rw [← ha, inner_sum, Finset.sum_eq_single t]
      · rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
        norm_cast
      · exact fun t' _ h => by rw [inner_smul_right, horth t' t h, mul_zero]
      · simp
    calc c r = ∑ t, a t • E t := ha.symm
      _ = _ := Finset.sum_congr rfl fun t _ => by
        rw [hcoef t, mul_smul, ← RCLike.real_smul_eq_coe_smul, hnorm]
  have hparseval (r : Fin n) : ∑ t, ‖⟪E t, c r⟫_𝕜‖ ^ 2 = ‖c r‖ ^ 2 := by
    have h := congrArg (fun z => ⟪c r, z⟫_𝕜) (hrec r)
    simp only [inner_sum, inner_smul_right, ← inner_conj_symm (c r) (E _),
      RCLike.mul_conj, inner_self_eq_norm_sq_to_K] at h
    exact_mod_cast h.symm
  refine ⟨fun t k => E t k, fun t r => ⟪E t, c r⟫_𝕜, fun k r => ?_, fun t t' h => ?_,
    fun t => ?_, ?_⟩
  · have := congrArg (fun z : EuclideanSpace 𝕜 κ => z k) (hrec r)
    simpa [c, mul_comm] using this
  · simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct] using horth t t' h
  · rw [← EuclideanSpace.norm_sq_eq]
    by_cases h : E t = 0
    · simp [h]
    · rw [InnerProductSpace.gramSchmidtNormed_unit_length' h, one_pow]
  · rw [Finset.sum_comm]
    simp_rw [hparseval, EuclideanSpace.norm_sq_eq, c]
    exact Finset.sum_comm

/-- **Gram–Schmidt factorization** of vectors `vᵣ = (v k r)ₖ ∈ 𝕜^κ` indexed by a finite type `ι`:
`v k r = ∑ t, e t k * v' t r` for pairwise orthogonal vectors `e t` of norm at most `1`, with
`∑ t r, ‖v' t r‖² = ∑ k r, ‖v k r‖²`. -/
theorem exists_orthogonal_factor {κ ι : Type*} [Fintype κ] [Fintype ι] (v : κ → ι → 𝕜) :
    ∃ (e : ι → κ → 𝕜) (v' : ι → ι → 𝕜),
      (∀ k r, v k r = ∑ t, e t k * v' t r) ∧
      (∀ t t', t ≠ t' → ∑ k, e t k * star (e t' k) = 0) ∧
      (∀ t, ∑ k, ‖e t k‖ ^ 2 ≤ 1) ∧
      ∑ t, ∑ r, ‖v' t r‖ ^ 2 = ∑ k, ∑ r, ‖v k r‖ ^ 2 := by
  classical
  let σ := Fintype.equivFin ι
  obtain ⟨e, v', hv, he, he₁, hv'⟩ := exists_orthogonal_factor_fin fun k i => v k (σ.symm i)
  refine ⟨fun t => e (σ t), fun t r => v' (σ t) (σ r), fun k r => ?_,
    fun t t' h => he _ _ (σ.injective.ne h), fun t => he₁ _, ?_⟩
  · rw [← σ.symm_apply_apply r, hv, ← σ.sum_comp]
    simp
  · calc ∑ t, ∑ r, ‖v' (σ t) (σ r)‖ ^ 2 = ∑ t, ∑ r, ‖v' t r‖ ^ 2 :=
          (Finset.sum_congr rfl fun t _ => σ.sum_comp fun r => ‖v' (σ t) r‖ ^ 2).trans
            (σ.sum_comp fun t => ∑ r, ‖v' t r‖ ^ 2)
      _ = ∑ k, ∑ r, ‖v k (σ.symm r)‖ ^ 2 := hv'
      _ = _ := Finset.sum_congr rfl fun k _ => σ.symm.sum_comp fun r => ‖v k r‖ ^ 2

end InnerProductSpace
