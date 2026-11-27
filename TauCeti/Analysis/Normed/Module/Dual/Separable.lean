/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Topology.Algebra.Module.Basic
import TauCeti.Analysis.Normed.Module.Dual.Submodule

/-!
# Spaces with a separable dual

A real or complex normed space whose dual is separable is itself separable. The converse fails:
`ℓ¹` is separable while its dual `ℓ^∞` is not.

Separability of the dual is the hypothesis of the theorem that separable dual spaces have the
Radon–Nikodým property. Its proof tests dual-valued functions against a countable dense subset of
the predual, whose existence is the theorem proved here.

For a dense sequence `yₙ` of functionals, pick unit vectors `xₙ` with `‖yₙ‖ / 2 ≤ ‖yₙ xₙ‖`. A
nonzero functional `f` vanishing on the closed span of the `xₙ` would be close to some `yₙ`, which
is impossible since `f xₙ = 0`; by the Hahn–Banach theorem the closed span of the `xₙ` is therefore
the whole space.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Springer,
  2011, Theorem 3.26.
-/

public section

open TopologicalSpace

namespace TauCeti

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A real or complex normed space whose dual is separable is separable. -/
theorem separableSpace_of_separableSpace_strongDual [SeparableSpace (StrongDual 𝕜 E)] :
    SeparableSpace E := by
  obtain ⟨y, hy⟩ := exists_dense_seq (StrongDual 𝕜 E)
  -- Each `y n` nearly attains its norm, up to a factor `2`, on the closed unit ball.
  have hx (n : ℕ) : ∃ x : E, ‖x‖ ≤ 1 ∧ ‖y n‖ / 2 ≤ ‖y n x‖ := by
    rcases eq_or_ne (y n) 0 with h | h
    · exact ⟨0, by simp, by simp [h]⟩
    · obtain ⟨x, hx₁, hx⟩ := (y n).exists_lt_apply_of_lt_opNorm
        (half_lt_self (norm_pos_iff.2 h))
      exact ⟨x, hx₁.le, hx.le⟩
  choose x hx₁ hxy using hx
  set K := (Submodule.span 𝕜 (Set.range x)).topologicalClosure
  -- A functional vanishing on `K` is far from every `y n`, so it is zero.
  have hK : ∀ z, z ∈ K := by
    by_contra! ⟨z, hz⟩
    obtain ⟨f, hf₀, hfz⟩ :=
      Submodule.exists_dual_forall_mem_eq_zero_eq_one
        (Submodule.span 𝕜 (Set.range x)).isClosed_topologicalClosure hz
    have hf : 0 < ‖f‖ := norm_pos_iff.2 fun h ↦ by simp [h] at hfz
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hy f (‖f‖ / 3) (by positivity)
    have hfx : f (x n) = 0 :=
      hf₀ _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨n, rfl⟩))
    have h₁ : ‖y n (x n)‖ ≤ ‖f‖ / 3 :=
      calc ‖y n (x n)‖ = ‖(y n - f) (x n)‖ := by simp [hfx]
        _ ≤ ‖y n - f‖ * ‖x n‖ := (y n - f).le_opNorm _
        _ ≤ ‖f‖ / 3 * 1 := by
          gcongr
          · rw [← dist_eq_norm, dist_comm]
            exact hn.le
          · exact hx₁ n
        _ = ‖f‖ / 3 := mul_one _
    have h₂ : ‖f‖ - ‖y n‖ < ‖f‖ / 3 := by
      have := norm_sub_norm_le f (y n)
      rw [← dist_eq_norm] at this
      linarith
    linarith [hxy n]
  have hsep : IsSeparable (K : Set E) := by
    have : ProperSpace 𝕜 := FiniteDimensional.proper_rclike 𝕜 𝕜
    rw [Submodule.topologicalClosure_coe]
    exact (Set.countable_range x).isSeparable.span.closure
  rw [show (K : Set E) = Set.univ from Set.eq_univ_of_forall hK] at hsep
  exact isSeparable_univ_iff.1 hsep

end TauCeti
