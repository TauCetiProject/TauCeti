/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleRing.Defs
import Mathlib.Algebra.Central.Basic
import TauCeti.Algebra.CentralSimple.SkolemNoether

/-!
# Involutive Skolem–Noether presentation on central simple star algebras

Refines inner conjugation (`TauCeti.exists_unit_conj_of_algEquiv`) for an `F`-algebra
automorphism `α` of a finite-dimensional central simple `F`-star algebra `M` such that
`X ↦ α (star X)` is an involution (`TauCeti.exists_unit_conj_star_of_central`).
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
  have hcomm (X : M) : ((u : M) * star (↑u⁻¹ : M)) * X = X * ((u : M) * star (↑u⁻¹ : M)) := by
    have h1 : ((u : M) * star (↑u⁻¹ : M)) * X * (star (u : M) * (↑u⁻¹ : M)) = X := by
      have hX := hinvol X; rw [hu, hu, star_mul, star_mul, star_star] at hX
      simpa only [mul_assoc] using hX
    have hinv : (star (u : M) * (↑u⁻¹ : M)) * ((u : M) * star (↑u⁻¹ : M)) = 1 := by
      rw [mul_assoc (star (u : M)), ← mul_assoc (↑u⁻¹ : M), u.inv_mul, one_mul, ← star_mul,
        u.inv_mul, star_one]
    rw [← mul_one (((u : M) * star (↑u⁻¹ : M)) * X), ← hinv, ← mul_assoc, h1]
  have hmem : (u : M) * star (↑u⁻¹ : M) ∈ Subalgebra.center F M :=
    Subalgebra.mem_center_iff.mpr fun X ↦ (hcomm X).symm
  rw [Algebra.IsCentral.center_eq_bot F M, Algebra.mem_bot] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hcu : c • star (u : M) = (u : M) := by
    simpa [← Algebra.smul_def, mul_assoc, ← star_mul] using congrArg (· * star (u : M)) hc
  have hc0 : c ≠ 0 := fun h0 ↦
    one_ne_zero (by simpa [h0] using congrArg (· * (↑u⁻¹ : M)) hcu.symm : (1 : M) = 0)
  have hsu : star (u : M) = c⁻¹ • (u : M) := (eq_inv_smul_iff₀ hc0).mpr hcu
  refine ⟨u, c⁻¹, hu, hsu, (algebraMap F M).injective <| by
    have h2 := congrArg star hsu; rw [star_star, star_smul, hsu, smul_smul, eq_comm] at h2
    simpa [Algebra.algebraMap_eq_smul_one, smul_mul_assoc] using congrArg (· * (↑u⁻¹ : M)) h2⟩

end TauCeti
