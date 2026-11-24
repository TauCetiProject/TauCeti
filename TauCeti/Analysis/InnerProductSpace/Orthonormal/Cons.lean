/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Adjoining an orthonormal pair to an orthonormal family of pairs

A family of orthonormal pairs `(q k, p k)`, indexed by `Fin r`, is recorded as the single family
`Sum.elim q p`. Prepending a pair `(q₀, p₀)` with `Fin.cons` keeps it orthonormal exactly when the
new pair is orthonormal and orthogonal to every old vector. This is the inductive step when planes
spanned by orthonormal pairs are split off one at a time, as in the real normal form of commuting
skew-symmetric maps.

## Main results

* `TauCeti.orthonormal_sum_elim_cons_iff`: `Sum.elim (Fin.cons q₀ q) (Fin.cons p₀ p)` is
  orthonormal if and only if `(q₀, p₀)` is orthonormal, orthogonal to every `q k` and `p k`, and
  `Sum.elim q p` is orthonormal.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Prepending a pair `(q₀, p₀)` to a family of pairs `(q k, p k)` gives an orthonormal family
`Sum.elim (Fin.cons q₀ q) (Fin.cons p₀ p)` if and only if `(q₀, p₀)` is orthonormal, both vectors
are orthogonal to every `q k` and `p k`, and `Sum.elim q p` is orthonormal. -/
theorem orthonormal_sum_elim_cons_iff {r : ℕ} {q₀ p₀ : E} {q p : Fin r → E} :
    Orthonormal 𝕜 (Sum.elim (Fin.cons q₀ q : Fin (r + 1) → E) (Fin.cons p₀ p)) ↔
      (‖q₀‖ = 1 ∧ ‖p₀‖ = 1 ∧ ⟪q₀, p₀⟫_𝕜 = 0) ∧
      (∀ k, ⟪q₀, q k⟫_𝕜 = 0 ∧ ⟪p₀, q k⟫_𝕜 = 0 ∧ ⟪q₀, p k⟫_𝕜 = 0 ∧ ⟪p₀, p k⟫_𝕜 = 0) ∧
      Orthonormal 𝕜 (Sum.elim q p) := by
  constructor
  · intro hv
    have h (i j) (hij : i ≠ j) := hv.2 hij
    refine ⟨⟨hv.1 (.inl 0), hv.1 (.inr 0), h (.inl 0) (.inr 0) Sum.inl_ne_inr⟩,
      fun k ↦ ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa using h (.inl 0) (.inl k.succ) (by simp [(Fin.succ_ne_zero k).symm])
    · simpa using h (.inr 0) (.inl k.succ) Sum.inr_ne_inl
    · simpa using h (.inl 0) (.inr k.succ) Sum.inl_ne_inr
    · simpa using h (.inr 0) (.inr k.succ) (by simp [(Fin.succ_ne_zero k).symm])
    · convert hv.comp (Sum.map Fin.succ Fin.succ) (Sum.map_injective.2 ⟨Fin.succ_injective _,
        Fin.succ_injective _⟩) using 1
      ext (k | k) <;> rfl
  · rintro ⟨⟨hq₀, hp₀, hqp₀⟩, hqp, hon⟩
    have honE := orthonormal_iff_ite.1 hon
    have hqq (k l : Fin r) : ⟪q k, q l⟫_𝕜 = if k = l then 1 else 0 := by
      simpa using honE (.inl k) (.inl l)
    have hqp' (k l : Fin r) : ⟪q k, p l⟫_𝕜 = 0 := by simpa using honE (.inl k) (.inr l)
    have hpq (k l : Fin r) : ⟪p k, q l⟫_𝕜 = 0 := by simpa using honE (.inr k) (.inl l)
    have hpp (k l : Fin r) : ⟪p k, p l⟫_𝕜 = if k = l then 1 else 0 := by
      simpa using honE (.inr k) (.inr l)
    have hpq₀ : ⟪p₀, q₀⟫_𝕜 = 0 := inner_eq_zero_symm.1 hqp₀
    have hq (k) : ⟪q k, q₀⟫_𝕜 = 0 ∧ ⟪q k, p₀⟫_𝕜 = 0 :=
      ⟨inner_eq_zero_symm.1 (hqp k).1, inner_eq_zero_symm.1 (hqp k).2.1⟩
    have hp (k) : ⟪p k, q₀⟫_𝕜 = 0 ∧ ⟪p k, p₀⟫_𝕜 = 0 :=
      ⟨inner_eq_zero_symm.1 (hqp k).2.2.1, inner_eq_zero_symm.1 (hqp k).2.2.2⟩
    rw [orthonormal_iff_ite]
    rintro (k | k) (l | l) <;> cases k using Fin.cases <;> cases l using Fin.cases <;>
      simp [hq₀, hp₀, hqp₀, hpq₀, hq, hp, hqp, hqq, hqp', hpq, hpp, (Fin.succ_ne_zero _).symm]

end TauCeti
