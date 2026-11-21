/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Northcott
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.CompactResolvent
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Diagonal.Basic
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.InnerProductSpace.LinearPMap.Spectral.Cutoff

/-!
# Reed–Simon compact-resolvent criterion for diagonal operators

A real diagonal operator `b.diagonalPMap lam` in a Hilbert basis `b` has compact resolvent iff
`i ↦ |lam i|` satisfies the Northcott property (`HilbertBasis.hasCompactResolvent_diagonalPMap_iff`,
Reed–Simon Theorem XIII.64).
-/

public section

noncomputable section

open Filter LinearPMap Topology
open scoped ENNReal InnerProductSpace lp

section CompactResolvent

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Reed–Simon criterion for diagonal operators.** A diagonal partial linear map with real
entries `lam : ι → ℝ` in a Hilbert basis has compact resolvent if and only if `i ↦ |lam i|` is
Northcott (only finitely many entries lie in any bounded interval). -/
theorem HilbertBasis.hasCompactResolvent_diagonalPMap_iff (b : HilbertBasis ι ℂ H) (lam : ι → ℝ) :
    (b.diagonalPMap fun i ↦ (lam i : ℂ)).HasCompactResolvent ↔ Northcott fun i ↦ |lam i| := by
  set A := b.diagonalPMap fun i ↦ (lam i : ℂ)
  have hA : IsSelfAdjoint A := b.isSelfAdjoint_diagonalPMap (by ext i; simp)
  have hb : ∀ i, ∃ hi : b i ∈ A.domain, A ⟨b i, hi⟩ = (lam i : ℂ) • b i := fun i ↦
    ⟨b.self_mem_diagonalPMap_domain _ i, b.diagonalPMap_apply_self _ i⟩
  constructor
  · intro h
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      h.northcott_norm_of_orthonormal b.orthonormal hb
  · intro hN
    rw [hA.hasCompactResolvent_iff_isCompactOperator_resolvent (z := Complex.I) (by simp)]
    have hnorm (i : ι) : 1 ≤ ‖Complex.I - (lam i : ℂ)‖ := by
      simpa using Complex.abs_im_le_norm (Complex.I - (lam i : ℂ))
    let m : ℓ^∞(ι, ℂ) := ⟨fun i ↦ (Complex.I - (lam i : ℂ))⁻¹, memℓp_infty ⟨1, by
      rintro _ ⟨i, rfl⟩
      dsimp only
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (hnorm i)⟩⟩
    have hm (i : ι) : m i = (Complex.I - (lam i : ℂ))⁻¹ := rfl
    have hR : A.resolvent Complex.I = b.diagonal m := by
      refine b.ext_inner_apply b fun i j ↦ ?_
      rw [LinearPMap.resolvent_apply_of_apply_eq_smul hA.I_mem_resolventSet
        ⟨b j, (hb j).1⟩ (hb j).2, b.diagonal_apply_self]
    rw [hR, b.isCompactOperator_diagonal_iff, tendsto_zero_iff_norm_tendsto_zero,
      Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_cofinite]
    refine (hN.finite_le ε⁻¹).subset fun i hi ↦ ?_
    simp only [Set.mem_ofPred_eq, Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _),
      not_lt] at hi
    rw [hm, norm_inv] at hi
    have hre : |lam i| ≤ ‖Complex.I - (lam i : ℂ)‖ := by
      simpa using Complex.abs_re_le_norm (Complex.I - (lam i : ℂ))
    exact hre.trans ((le_inv_comm₀ hε (zero_lt_one.trans_le (hnorm i))).1 hi)

end CompactResolvent
