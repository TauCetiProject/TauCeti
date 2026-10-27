/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.Quotient
public import TauCeti.NumberTheory.Padics.Distribution.AnalyticStage
import Mathlib.FieldTheory.Finite.Basic

/-!
# Torsion and analytic-stage transitions

For a coefficient vector with values in a complete ultrametric `ℤ_p`-module, raising the
analytic level need not be injective. If `p • e = 0`, the level-zero coefficient vector
`(X^p - X) • e` re-expands to zero on every level-one disc: its constant coefficient
vanishes by Fermat's theorem, and its positive-degree coefficients contain a factor of `p`.
The vector is nonzero whenever `e` is nonzero.

The native quotient `ℤ_p / 𝔪` by the maximal ideal supplies a concrete example. It is the
finite field `𝔽_p`, identified with `ZMod p` by `PadicInt.residueField`, equipped with its
quotient norm and bounded quotient scalar action.
-/

public section

open scoped ZeroAtInfty

namespace TauCeti.AnalyticStage

variable {p : ℕ} {E : Type*} [NormedAddCommGroup E]

/-- The level-zero coefficient vector `(X^p - X) • e`. -/
noncomputable def frobeniusSubIdCoeffs (e : E) : AnalyticStage p 0 E :=
  ZeroAtInftyContinuousMap.single (0, p) e - ZeroAtInftyContinuousMap.single (0, 1) e

/-- The coefficients of `(X^p - X) • e` are `e` in degree `p` and `-e` in degree one. -/
theorem frobeniusSubIdCoeffs_apply (e : E) (i : ZMod (p ^ 0) × ℕ) :
    frobeniusSubIdCoeffs (p := p) e i =
      (if i.2 = p then e else 0) - if i.2 = 1 then e else 0 := by
  have : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
  rcases i with ⟨a, n⟩
  simp only [frobeniusSubIdCoeffs, ZeroAtInftyContinuousMap.sub_apply,
    ZeroAtInftyContinuousMap.single_apply, Prod.mk.injEq, Subsingleton.elim a 0, true_and]

variable [hp : Fact p.Prime]

/-- The coefficient vector `(X^p - X) • e` vanishes exactly when `e` vanishes. -/
@[simp]
theorem frobeniusSubIdCoeffs_eq_zero (e : E) :
    frobeniusSubIdCoeffs (p := p) e = 0 ↔ e = 0 := by
  constructor
  · intro h
    have := congrArg (fun c : AnalyticStage p 0 E ↦ c (0, p)) h
    simpa only [frobeniusSubIdCoeffs_apply, hp.out.ne_one, ite_true, ite_false, sub_zero,
      ZeroAtInftyContinuousMap.zero_apply] using this
  · rintro rfl
    simp only [frobeniusSubIdCoeffs, ZeroAtInftyContinuousMap.single_zero, sub_self]

/-- The coefficient vector `(X^p - X) • e` has Gauss norm `‖e‖`. -/
@[simp]
theorem norm_frobeniusSubIdCoeffs (e : E) :
    ‖frobeniusSubIdCoeffs (p := p) e‖ = ‖e‖ := by
  apply le_antisymm
  · refine (ZeroAtInftyContinuousMap.norm_le (norm_nonneg e)).mpr fun i ↦ ?_
    by_cases h : i.2 = p
    · simp only [frobeniusSubIdCoeffs_apply, h, hp.out.ne_one, ite_true, ite_false, sub_zero,
        le_rfl]
    · simp only [frobeniusSubIdCoeffs_apply, h, ite_false, zero_sub, norm_neg]
      split_ifs <;> simp
  · simpa only [frobeniusSubIdCoeffs_apply, hp.out.ne_one, ite_true, ite_false, sub_zero] using
      (frobeniusSubIdCoeffs (p := p) e).norm_coe_le_norm (0, p)

variable [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E] [CompleteSpace E]
  (S : Type*) [Semiring S] [Module S E] [ContinuousConstSMul S E] [SMulCommClass ℤ_[p] S E]

/-- The coefficient vector `(X^p - X) • e` re-expands to zero if `p` annihilates `e`. -/
@[simp]
theorem transition_frobeniusSubIdCoeffs (e : E) (he : (p : ℤ_[p]) • e = 0) :
    transition S (frobeniusSubIdCoeffs (p := p) e) = 0 := by
  ext ⟨a, j⟩
  have : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
  have hsingle (n : ℕ) :
      transition S (ZeroAtInftyContinuousMap.single (0, n) e : AnalyticStage p 0 E)
          (a, j) =
        ((n.choose j : ℤ_[p]) * (a.val : ℤ_[p]) ^ (n - j) * (p : ℤ_[p]) ^ j) • e := by
    rw [transition_apply, tsum_eq_single n]
    · rw [ZeroAtInftyContinuousMap.single_apply]
      have ha : ((a.val : ZMod (p ^ 0)), n) = (0, n) :=
        Prod.ext (Subsingleton.elim _ _) rfl
      rw [ite_eq_left ha]
      simp
    · intro k hk
      simp only [ZeroAtInftyContinuousMap.single_apply, Prod.mk.injEq, hk, and_false,
        ite_false, smul_zero]
  simp only [frobeniusSubIdCoeffs, map_sub, ZeroAtInftyContinuousMap.sub_apply,
    hsingle, ZeroAtInftyContinuousMap.zero_apply]
  by_cases hj : j = 0
  · subst j
    simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul, pow_zero, mul_one,
      pow_one, ← sub_smul]
    have hdiv : (p : ℤ_[p]) ∣ (a.val : ℤ_[p]) ^ p - a.val := by
      simpa using map_dvd (Int.castRingHom ℤ_[p])
        (Int.prime_dvd_pow_self_sub hp.out (a.val : ℤ))
    obtain ⟨r, hr⟩ := hdiv
    rw [hr, mul_comm, mul_smul, he, smul_zero]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [pow_succ, mul_smul, he]

/-- The level-zero transition with coefficients in `𝔽_p = ℤ_p / 𝔪` is not injective. -/
theorem not_injective_transition_residueField :
    ¬ Function.Injective (transition (p := p) (h := 0) ℤ_[p]
      (E := ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p])) := by
  intro hinj
  have he : (p : ℤ_[p]) • (1 : ℤ_[p] ⧸ IsLocalRing.maximalIdeal ℤ_[p]) = 0 := by
    rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem,
      PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.subset_span (by simp)
  exact one_ne_zero <| (frobeniusSubIdCoeffs_eq_zero (p := p) _).mp <|
    hinj <| by simpa using transition_frobeniusSubIdCoeffs (p := p) ℤ_[p] _ he

end TauCeti.AnalyticStage
