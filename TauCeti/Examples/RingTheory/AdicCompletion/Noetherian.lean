/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.AdicCompletion.Noetherian

/-!
# Examples of Noetherian adic completions

The completions of `ℤ` along `(p)` and of `k[t]` along `(t)` are Noetherian by the completion
instance. The polynomial ring `k[X₀, X₁, …]` is complete for the finitely generated zero ideal but
is not Noetherian, so the hypothesis that `R ⧸ I` be Noetherian cannot be dropped from
`Ideal.isNoetherianRing_of_isAdicComplete`.
-/

open MvPolynomial

-- The completion of `ℤ` along the principal ideal `(p)` is Noetherian.
example (p : ℤ) : IsNoetherianRing (AdicCompletion (Ideal.span {p} : Ideal ℤ) ℤ) := inferInstance

-- The `t`-adic completion of `k[t]` is Noetherian.
example (k : Type*) [Field k] :
    IsNoetherianRing
      (AdicCompletion (Ideal.span {Polynomial.X} : Ideal (Polynomial k)) (Polynomial k)) :=
  inferInstance

-- Completeness for a finitely generated ideal alone does not give noetherianity:
-- `k[X₀, X₁, …]` is complete for the zero ideal, but the chain `(X₀, …, Xₙ₋₁)` never stabilizes.
example (k : Type*) [Field k] :
    IsAdicComplete (⊥ : Ideal (MvPolynomial ℕ k)) (MvPolynomial ℕ k) ∧
      (⊥ : Ideal (MvPolynomial ℕ k)).FG ∧ ¬ IsNoetherianRing (MvPolynomial ℕ k) := by
  refine ⟨inferInstance, Submodule.fg_bot, fun h ↦ ?_⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr h
    ⟨fun n ↦ Ideal.span (X '' Set.Iio n), fun _ _ hmn ↦
      Ideal.span_mono (Set.image_mono (Set.Iio_subset_Iio hmn))⟩
  have hX : (X N : MvPolynomial ℕ k) ∈ Ideal.span (X '' Set.Iio N) := by
    have hN' : Ideal.span (X '' Set.Iio N) = Ideal.span (X '' Set.Iio (N + 1)) :=
      hN (N + 1) N.le_succ
    rw [hN']
    exact Ideal.subset_span ⟨N, Nat.lt_succ_self N, rfl⟩
  -- Evaluating `Xᵢ` at `0` for `i < N` and at `1` otherwise kills the ideal but not `X N`.
  have hker : Ideal.span (X '' Set.Iio N) ≤
      RingHom.ker (aeval (R := k) fun i : ℕ ↦ if i < N then (0 : k) else 1) :=
    Ideal.span_le.mpr (by rintro _ ⟨i, hi, rfl⟩; simp_all)
  simpa using hker hX
