/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# Uniform ellipticity of continuous positive-definite matrix fields on compact sets

A continuous matrix field `a : X → Matrix ι ι ℝ` on a compact set `K` whose quadratic form is
pointwise strictly positive on nonzero vectors is uniformly elliptic on `K`: the quadratic form
`(x, ξ) ↦ ξᵀ a(x) ξ` attains a positive minimum `λ` on the compact product `K × Sⁿ⁻¹`, and the
operator norm of `matrixBilinearForm (a x)` attains a finite maximum on `K`. No symmetry of `a` is
required (`TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact`); in particular, every continuous
field of positive-definite matrices on a compact set is uniformly elliptic
(`TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact_of_posDef`).

## Main results

* `TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact`: a continuous matrix field on a compact set
  whose quadratic form is strictly positive away from zero is uniformly elliptic there.
* `TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact_of_posDef`: the symmetric specialization to
  positive-definite matrices (`Matrix.PosDef`).
* `TauCeti.PDE.exists_uniformlyEllipticOn_of_subset_isCompact_of_posDef`: restriction to any subset
  of a compact set on which the matrix field is continuous and positive definite.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), Chapter 3.
-/

public section

open Matrix Metric Set

namespace TauCeti.PDE

variable {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Uniform ellipticity on a compact set.** Let `a : X → Matrix ι ι ℝ` be continuous on a compact
set `K`, and suppose `ξᵀ a(x) ξ > 0` for every `x ∈ K` and every nonzero `ξ`. Then there exist
constants `0 < λ ≤ Λ` such that `a` is uniformly elliptic on `K`. No symmetry of `a` is assumed. -/
theorem exists_uniformlyEllipticOn_of_isCompact {K : Set X} (hK : IsCompact K)
    {a : X → Matrix ι ι ℝ} (ha : ContinuousOn a K)
    (hpos : ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ ι, ξ ≠ 0 → 0 < (a x).toQuadraticForm' ξ) :
    ∃ lam Lam : ℝ, UniformlyEllipticOn K a lam Lam := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, 1, uniformlyEllipticOn_iff.2 ⟨zero_lt_one, le_rfl, fun _ hx ↦ hx.elim⟩⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨1, 1, uniformlyEllipticOn_iff.2
      ⟨zero_lt_one, le_rfl, fun x _ ↦ ⟨fun ξ ↦ ?_, fun η ξ ↦ ?_⟩⟩⟩
    · rw [Subsingleton.elim ξ 0]
      simp
    · rw [Subsingleton.elim η 0, Subsingleton.elim ξ 0]
      simp
  -- On `K × Sⁿ⁻¹` the quadratic form is continuous and positive, so it attains a positive minimum.
  set S : Set (EuclideanSpace ℝ ι) := sphere 0 1
  have hSne : S.Nonempty := by
    obtain ⟨i⟩ := hι
    exact ⟨EuclideanSpace.single i (1 : ℝ), by simp [S]⟩
  have hKS : IsCompact (K ×ˢ S) := hK.prod (isCompact_sphere 0 1)
  let q : X × EuclideanSpace ℝ ι → ℝ := fun p ↦ matrixBilinearForm (a p.1) p.2 p.2
  have hq_cont : ContinuousOn q (K ×ˢ S) := by
    have hB : ContinuousOn (fun p : X × EuclideanSpace ℝ ι ↦ matrixBilinearForm (a p.1)) (K ×ˢ S) :=
      (continuous_matrixBilinearForm.comp_continuousOn ha).comp continuous_fst.continuousOn
        fun _ hp ↦ hp.1
    exact (hB.clm_apply continuous_snd.continuousOn).clm_apply continuous_snd.continuousOn
  obtain ⟨⟨x₀, ξ₀⟩, ⟨hx₀, hξ₀⟩, hmin⟩ := hKS.exists_isMinOn (hKne.prod hSne) hq_cont
  have hξ₀_norm : ‖ξ₀‖ = 1 := by simpa [S] using hξ₀
  have hξ₀_ne : ξ₀ ≠ 0 := fun h ↦ by simp [h] at hξ₀_norm
  set lam := q (x₀, ξ₀)
  have hlam : 0 < lam := by
    dsimp [lam, q]
    rw [matrixBilinearForm_self]
    exact hpos x₀ hx₀ ξ₀ hξ₀_ne
  -- The sum of absolute values of entries is continuous on `K`, bounding the operator norm.
  let s : X → ℝ := fun x ↦ ∑ i, ∑ j, |a x i j|
  have hs_cont : ContinuousOn s K :=
    (by fun_prop : Continuous fun A : Matrix ι ι ℝ ↦ ∑ i, ∑ j, |A i j|).comp_continuousOn ha
  obtain ⟨x₁, -, hmax⟩ := hK.exists_isMaxOn hKne hs_cont
  set Lam := max lam (s x₁)
  refine ⟨lam, Lam, uniformlyEllipticOn_iff.2 ⟨hlam, le_max_left _ _,
    fun x hx ↦ ⟨fun ξ ↦ ?_, fun η ξ ↦ ?_⟩⟩⟩
  · by_cases hξ : ξ = 0
    · simp [hξ]
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hu : ‖ξ‖⁻¹ • ξ ∈ S := by
      simp [S, norm_smul, inv_mul_cancel₀ hn.ne']
    have hle : lam ≤ q (x, ‖ξ‖⁻¹ • ξ) := hmin ⟨hx, hu⟩
    dsimp [q] at hle
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
      matrixBilinearForm_self] at hle
    have hsq : 0 < ‖ξ‖ ^ 2 := sq_pos_of_pos hn
    have hmul := mul_le_mul_of_nonneg_right hle hsq.le
    calc lam * ‖ξ‖ ^ 2 ≤ ‖ξ‖⁻¹ * (‖ξ‖⁻¹ * (a x).toQuadraticForm' ξ) * ‖ξ‖ ^ 2 := hmul
      _ = (a x).toQuadraticForm' ξ := by field_simp [hn.ne']
  · have hM : ‖matrixBilinearForm (a x)‖ ≤ Lam :=
      (norm_matrixBilinearForm_le_sum_abs (a x)).trans ((hmax hx).trans (le_max_right _ _))
    have h := (matrixBilinearForm (a x)).le_opNorm₂ η ξ
    rw [matrixBilinearForm_apply, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hM (norm_nonneg η)) (norm_nonneg ξ))

/-- **Continuous positive-definite matrix fields on compact sets are uniformly elliptic.** -/
theorem exists_uniformlyEllipticOn_of_isCompact_of_posDef {K : Set X} (hK : IsCompact K)
    {a : X → Matrix ι ι ℝ} (ha : ContinuousOn a K) (hpos : ∀ x ∈ K, (a x).PosDef) :
    ∃ lam Lam : ℝ, UniformlyEllipticOn K a lam Lam := by
  refine exists_uniformlyEllipticOn_of_isCompact hK ha fun x hx ξ hξ ↦ ?_
  have hξ' : ξ.ofLp ≠ 0 := fun h ↦ hξ (by simpa using congrArg (WithLp.toLp 2) h)
  simpa only [Matrix.toQuadraticForm'_apply, star_trivial] using
    (hpos x hx).dotProduct_mulVec_pos hξ'

/-- A matrix field continuous and positive definite on a compact superset `K` of `Ω` is uniformly
elliptic on `Ω`. -/
theorem exists_uniformlyEllipticOn_of_subset_isCompact_of_posDef {Ω K : Set X} (hK : IsCompact K)
    (hΩK : Ω ⊆ K) {a : X → Matrix ι ι ℝ} (ha : ContinuousOn a K)
    (hpos : ∀ x ∈ K, (a x).PosDef) :
    ∃ lam Lam : ℝ, UniformlyEllipticOn Ω a lam Lam := by
  obtain ⟨lam, Lam, h⟩ := exists_uniformlyEllipticOn_of_isCompact_of_posDef hK ha hpos
  exact ⟨lam, Lam, h.mono_set hΩK⟩

end TauCeti.PDE
