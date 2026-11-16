/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Analysis.PDE.Ellipticity.Basic

/-!
# Uniform ellipticity on compact sets

A continuous matrix field `a : X → Matrix n n ℝ` on a compact set `K` whose quadratic form is
strictly positive on every nonzero vector at every point of `K` is uniformly elliptic on `K`
(`TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact`). The lower ellipticity constant is the
minimum of the quadratic form on the compact product `K × S`, where `S` is the unit sphere of
`EuclideanSpace ℝ n`, and the upper constant comes from compactness of `K` applied to the
continuous entrywise `ℓ¹` sum `x ↦ ∑ i, ∑ j, |a x i j|`. In particular, a continuous field of
positive-definite matrices on a compact set is uniformly elliptic
(`TauCeti.PDE.exists_uniformlyEllipticOn_of_posDef`).

## Main results

* `TauCeti.PDE.exists_uniformlyEllipticOn_of_isCompact`: continuous pointwise-positive quadratic
  form on a compact set implies `UniformlyEllipticOn`.
* `TauCeti.PDE.exists_uniformlyEllipticOn_of_posDef`: continuous positive-definite matrix field
  on a compact set implies `UniformlyEllipticOn`.
-/

public section

open Metric Set
open scoped Matrix

namespace TauCeti.PDE

variable {X : Type*} [TopologicalSpace X] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Continuous strictly positive matrix fields are uniformly elliptic on compact sets.** Let
`a : X → Matrix n n ℝ` be continuous on a compact set `K` with `0 < ξᵀ a(x) ξ` for every `x ∈ K`
and every nonzero `ξ`. Then `a` is uniformly elliptic on `K` with some positive constants `λ ≤ Λ`.
Symmetry of `a` is not required. -/
theorem exists_uniformlyEllipticOn_of_isCompact {K : Set X} {a : X → Matrix n n ℝ}
    (hK : IsCompact K) (ha : ContinuousOn a K)
    (hpos : ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ n, ξ ≠ 0 → 0 < (a x).toQuadraticForm' ξ) :
    ∃ lam Lam, UniformlyEllipticOn K a lam Lam := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, 1, UniformlyEllipticOn.of_bounds one_pos le_rfl (fun _ hx ↦ hx.elim)
      (fun _ hx ↦ hx.elim)⟩
  cases isEmpty_or_nonempty n with
  | inl _ =>
    refine ⟨1, 1, UniformlyEllipticOn.of_bounds one_pos le_rfl (fun _ _ ξ ↦ ?_)
      (fun _ _ η ξ ↦ ?_)⟩
    · simp [Subsingleton.elim ξ 0]
    · simp [Subsingleton.elim η 0]
  | inr hne =>
    obtain ⟨i₀⟩ := hne
    set S : Set (EuclideanSpace ℝ n) := sphere 0 1
    have hSne : S.Nonempty := ⟨EuclideanSpace.single i₀ 1, by simp [S]⟩
    -- The quadratic form is continuous on the compact product `K × S` and strictly positive there.
    let q : X × EuclideanSpace ℝ n → ℝ := fun p ↦ matrixBilinearForm (a p.1) p.2 p.2
    have hq_cont : ContinuousOn q (K ×ˢ S) :=
      ((ha.matrixBilinearForm.comp (continuousOn_fst (s := K ×ˢ S)) fun _ hp ↦ hp.1).clm_apply
        continuousOn_snd).clm_apply continuousOn_snd
    obtain ⟨⟨x₀, ξ₀⟩, ⟨hx₀, hξ₀⟩, hmin⟩ :=
      (hK.prod (isCompact_sphere (0 : EuclideanSpace ℝ n) 1)).exists_isMinOn
        (hKne.prod hSne) hq_cont
    set lam := q (x₀, ξ₀)
    have hξ₀_ne : ξ₀ ≠ 0 := by
      intro h0
      have h1 : ‖ξ₀‖ = 1 := by simpa [S, mem_sphere_zero_iff_norm] using hξ₀
      simp [h0] at h1
    have hlam : 0 < lam := by
      have h := hpos x₀ hx₀ ξ₀ hξ₀_ne
      rwa [← matrixBilinearForm_self] at h
    -- Compactness of `K` bounds the entrywise `ℓ¹` sum, hence the bilinear operator norm.
    have hsum_cont : ContinuousOn (fun x ↦ ∑ i : n, ∑ j : n, |a x i j|) K :=
      continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
        (continuousOn_pi.1 (continuousOn_pi.1 ha i) j).abs
    obtain ⟨x₁, _, hmax⟩ := hK.exists_isMaxOn hKne hsum_cont
    set M := ∑ i : n, ∑ j : n, |a x₁ i j|
    refine ⟨lam, max lam M, UniformlyEllipticOn.of_bounds hlam (le_max_left _ _) ?_ ?_⟩
    · intro x hx ξ
      rw [← matrixBilinearForm_self]
      by_cases hξ : ξ = 0
      · simp [hξ]
      · have hnorm_pos : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
        set u : EuclideanSpace ℝ n := ‖ξ‖⁻¹ • ξ
        have huS : u ∈ S := by
          simp [S, u, norm_smul, inv_mul_cancel₀ hnorm_pos.ne']
        have hle : lam ≤ q (x, u) := hmin (mk_mem_prod hx huS)
        have hscale : q (x, u) = (‖ξ‖⁻¹) ^ 2 * matrixBilinearForm (a x) ξ ξ := by
          simp only [q, u, map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
          ring
        rw [hscale] at hle
        have hsq : 0 < ‖ξ‖ ^ 2 := sq_pos_of_pos hnorm_pos
        have := mul_le_mul_of_nonneg_left hle hsq.le
        have hcancel : ‖ξ‖ ^ 2 * ((‖ξ‖⁻¹) ^ 2 * matrixBilinearForm (a x) ξ ξ) =
            matrixBilinearForm (a x) ξ ξ := by
          field_simp [hnorm_pos.ne']
        linarith
    · intro x hx η ξ
      rw [← matrixBilinearForm_apply, ← Real.norm_eq_abs]
      calc ‖matrixBilinearForm (a x) η ξ‖
          ≤ ‖matrixBilinearForm (a x)‖ * ‖η‖ * ‖ξ‖ :=
            ContinuousLinearMap.le_opNorm₂ (matrixBilinearForm (a x)) η ξ
        _ ≤ max lam M * ‖η‖ * ‖ξ‖ := by
            gcongr
            exact (norm_matrixBilinearForm_le_sum_abs (a x)).trans
              ((hmax hx).trans (le_max_right _ _))

/-- **Continuous positive-definite matrix fields are uniformly elliptic on compact sets.** -/
theorem exists_uniformlyEllipticOn_of_posDef {K : Set X} {a : X → Matrix n n ℝ}
    (hK : IsCompact K) (ha : ContinuousOn a K) (hpos : ∀ x ∈ K, (a x).PosDef) :
    ∃ lam Lam, UniformlyEllipticOn K a lam Lam :=
  exists_uniformlyEllipticOn_of_isCompact hK ha fun x hx ξ hξ ↦
    (hpos x hx).toQuadraticForm' ξ (by
      intro h0
      exact hξ (WithLp.ofLp_injective 2 (by simpa using h0)))

end TauCeti.PDE
