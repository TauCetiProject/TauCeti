/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Basic

/-!
# Frobenius functionals on finite field extensions

Every nonzero `K`-linear functional on a finite field extension `L/K` is a Frobenius
functional. Consequently the multiplication pairing identifies `L` with its `K`-dual,
and two nonzero functionals differ by multiplication by a unique unit of `L`. This
unique scalar is the change of functional in Scharlau transfer.

The functional choice follows Scharlau, *Quadratic and Hermitian Forms*, Chapter 2,
§5, and Lam, *Introduction to Quadratic Forms over Fields*, Chapter VII, §1.
-/

public section

noncomputable section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- On a field extension, a `K`-linear functional is Frobenius exactly when it
is nonzero. Separability is unnecessary. -/
@[simp]
theorem _root_.LinearMap.isFrobeniusFunctional_iff_ne_zero (s : L →ₗ[K] K) :
    s.IsFrobeniusFunctional ↔ s ≠ 0 := by
  constructor
  · intro hs hzero
    have h : (1 : L) = 0 := hs.eq_zero_of_forall_left (a := 1) (by simp [hzero])
    exact one_ne_zero h
  · intro hs
    obtain ⟨x, hx⟩ : ∃ x : L, s x ≠ 0 := by
      by_contra h
      push Not at h
      apply hs
      ext y
      exact h y
    have hleft : ∀ a : L, (∀ b, s (a * b) = 0) → a = 0 := by
      intro a ha
      by_contra hne
      have hmul : a * (a⁻¹ * x) = x := by field_simp
      exact hx (hmul ▸ ha (a⁻¹ * x))
    exact LinearMap.isFrobeniusFunctional_iff.mpr
      ⟨hleft, fun b hb => hleft b (fun a => by simpa [mul_comm] using hb a)⟩

/-- Two nonzero `K`-linear functionals on a finite extension differ by multiplication
by a unique unit of the extension. -/
theorem _root_.LinearMap.existsUnique_unit_apply_eq_apply_mul (s t : L →ₗ[K] K)
    [FiniteDimensional K L] (hs : s ≠ 0) (ht : t ≠ 0) :
    ∃! u : Lˣ, ∀ x : L, t x = s ((u : L) * x) := by
  let e := s.isFrobeniusFunctional_iff_ne_zero.mpr hs |>.toDualEquiv
  let a := e.symm t
  have hta : e a = t := e.apply_symm_apply t
  have happly (b x : L) : e b x = s (b * x) :=
    LinearMap.IsFrobeniusFunctional.toDualEquiv_apply_apply _ b x
  have ha : a ≠ 0 := by
    intro h
    apply ht
    rw [← hta, h]
    exact e.map_zero
  refine ⟨Units.mk0 a ha, ?_, ?_⟩
  · intro x
    rw [← hta, happly]
    simp
  · intro u hu
    apply Units.ext
    apply e.injective
    calc
      e (u : L) = t := by
        ext x
        rw [happly]
        exact (hu x).symm
      _ = e a := hta.symm

end TauCeti
