/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Star.Module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.Algebra.Central.Basic
import TauCeti.Algebra.CentralSimple.SkolemNoether

/-!
# Involutive Skolem–Noether presentation on central simple star algebras

Refines inner conjugation (`TauCeti.exists_unit_conj_of_algEquiv`) for `α : M ≃ₐ[F] M` when
`X ↦ α (star X)` is an involution (`TauCeti.exists_unit_conj_star_of_central`), with trivial-star
(`TauCeti.exists_unit_conj_star_eq_self_or_neg_of_central`) and complex rescaling
(`TauCeti.exists_isSelfAdjoint_unit_rescale_complex`).
-/

public section

namespace TauCeti

/-- **Skolem–Noether presentation of an involution on a central simple algebra.** Given an
`F`-algebra automorphism `α` of a finite-dimensional central simple `F`-star algebra `M` such that
`X ↦ α (star X)` is an involution, `α X = u * X * u⁻¹` for a unit `u : Mˣ` satisfying
`star u = μ • u` with `star μ * μ = 1`. -/
theorem exists_unit_conj_star_of_central (F : Type*) {M : Type*} [Field F] [StarRing F]
    [Ring M] [Algebra F M] [StarRing M] [StarModule F M] [Algebra.IsCentral F M]
    [IsSimpleRing M] [FiniteDimensional F M] (α : M ≃ₐ[F] M)
    (hinvol : ∀ X : M, α (star (α (star X))) = X) :
    ∃ (u : Mˣ) (μ : F), (∀ X : M, α X = (u : M) * X * (↑u⁻¹ : M)) ∧
      star (u : M) = μ • (u : M) ∧ star μ * μ = 1 := by
  obtain ⟨u, hu⟩ := exists_unit_conj_of_algEquiv F α
  let su : Mˣ := ⟨star (u : M), star (↑u⁻¹ : M),
    by rw [← star_mul, u.inv_mul, star_one], by rw [← star_mul, u.mul_inv, star_one]⟩
  let w : Mˣ := u * su⁻¹
  have hmem : (w : M) ∈ Subalgebra.center F M := Subalgebra.mem_center_iff.mpr fun X ↦ by
    have h1 : (w : M) * X * (↑w⁻¹ : M) = X := by
      have hX := hinvol X; rw [hu, hu] at hX; simpa [w, su, mul_inv_rev, mul_assoc] using hX
    exact (by rw [← mul_one ((w : M) * X), ← w.inv_mul, ← mul_assoc, h1] : (w : M) * X = _).symm
  rw [Algebra.IsCentral.center_eq_bot F M, Algebra.mem_bot] at hmem; obtain ⟨c, hc⟩ := hmem
  have hcu : c • star (u : M) = (u : M) := by
    simpa [w, su, ← Algebra.smul_def, mul_assoc, ← star_mul, u.inv_mul] using
      (congrArg (· * (su : M)) hc.symm).symm
  have hc0 : c ≠ 0 := fun h0 ↦
    one_ne_zero (by simpa [h0] using congrArg (· * (↑u⁻¹ : M)) hcu.symm : (1 : M) = 0)
  have hsu : star (u : M) = c⁻¹ • (u : M) := (eq_inv_smul_iff₀ hc0).mpr hcu
  refine ⟨u, c⁻¹, hu, hsu, (algebraMap F M).injective <| by
    have h2 := congrArg star hsu; rw [star_star, star_smul, hsu, smul_smul, eq_comm] at h2
    simpa [Algebra.algebraMap_eq_smul_one, smul_mul_assoc] using congrArg (· * (↑u⁻¹ : M)) h2⟩

/-- Specialization of `TauCeti.exists_unit_conj_star_of_central` when the base field `F` has
trivial star: the conjugating unit `u` is either self-adjoint or skew-adjoint. -/
theorem exists_unit_conj_star_eq_self_or_neg_of_central (F : Type*) {M : Type*} [Field F]
    [StarRing F] [TrivialStar F] [Ring M] [Algebra F M] [StarRing M] [StarModule F M]
    [Algebra.IsCentral F M] [IsSimpleRing M] [FiniteDimensional F M] (α : M ≃ₐ[F] M)
    (hinvol : ∀ X : M, α (star (α (star X))) = X) :
    ∃ u : Mˣ, (star (u : M) = u ∨ star (u : M) = -u) ∧
      ∀ X : M, α X = (u : M) * X * (↑u⁻¹ : M) := by
  obtain ⟨u, μ, hu, huμ, hμsq⟩ := exists_unit_conj_star_of_central F α hinvol
  rcases mul_self_eq_one_iff.mp (by simpa using hμsq) with rfl | rfl <;>
    exact ⟨u, by simp [huμ], hu⟩

/-- Rescaling a unit `u` satisfying `star (u : M) = μ • (u : M)` (`star μ * μ = 1`) in a
complex star algebra to a self-adjoint unit `u'` inducing the same inner automorphism. -/
theorem exists_isSelfAdjoint_unit_rescale_complex {M : Type*} [Ring M] [Algebra ℂ M] [StarRing M]
    [StarModule ℂ M] (u : Mˣ) (μ : ℂ) (huμ : star (u : M) = μ • (u : M))
    (hμsq : star μ * μ = 1) :
    ∃ u' : Mˣ, IsSelfAdjoint (u' : M) ∧
      ∀ X : M, (u' : M) * X * (↑u'⁻¹ : M) = (u : M) * X * (↑u⁻¹ : M) := by
  let ζ : ℂ := if μ = -1 then Complex.I else 1 + μ
  have hζ0 : ζ ≠ 0 := by
    dsimp only [ζ]; split_ifs with h
    · exact Complex.I_ne_zero
    · exact fun h0 ↦ h (eq_neg_of_add_eq_zero_right h0)
  let u' : Mˣ := ⟨ζ • (u : M), ζ⁻¹ • (↑u⁻¹ : M),
    by simp [smul_smul, inv_mul_cancel₀ hζ0], by simp [smul_smul, mul_inv_cancel₀ hζ0]⟩
  refine ⟨u', ?_, fun X ↦ by simp [u', smul_smul, inv_mul_cancel₀ hζ0]⟩
  rw [IsSelfAdjoint, show (u' : M) = ζ • (u : M) from rfl, star_smul, huμ, smul_smul]; congr 1
  by_cases h : μ = -1
  · simp [ζ, h]
  · simp only [ζ, h, ↓reduceIte, star_add, star_one, add_mul, one_mul]
    rw [add_comm 1 μ]; simpa using congrArg (μ + ·) hμsq

end TauCeti
