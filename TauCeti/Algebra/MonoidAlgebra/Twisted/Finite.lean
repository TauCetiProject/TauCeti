/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Root-of-unity representatives of finite-group factor sets

Over an algebraically closed field, every normalized factor set of a finite group can be
rescaled to take values in the roots of unity of order dividing the group order. This gives a
finite set of representatives for the cohomology classes of factor sets, and hence finiteness
of the Schur multiplier.

The explicit rescaling comes from taking roots of the products of the rows of the factor set.
It works in arbitrary characteristic and does not require a faithful projective representation.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985), Chapter 2.
-/

public section

namespace TauCeti.IsFactorSet

variable {k G : Type*} [Field k] [IsAlgClosed k] [Group G] [Finite G]
  (α : G → G → kˣ) [IsFactorSet α]

/-- A normalized factor set of a finite group over an algebraically closed field can be
rescaled by a normalized cochain so that every value has order dividing `Nat.card G`. -/
theorem exists_rescale_pow_card_eq_one :
    ∃ c : G → kˣ, c 1 = 1 ∧ ∀ g h,
      (c g * c h * (c (g * h))⁻¹ * α g h) ^ Nat.card G = 1 := by
  classical
  let := Fintype.ofFinite G
  let b (g : G) : kˣ := ∏ t : G, α g t
  have hb (g h : G) : b (g * h) * α g h ^ Fintype.card G = b h * b g := by
    have hc := congrArg (fun f : G → kˣ ↦ ∏ t, f t)
      (funext (IsFactorSet.cocycle (α := α) g h))
    have hshift : (∏ t, α g (h * t)) = b g := Equiv.prod_comp (Equiv.mulLeft h) (α g)
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      hshift] using hc
  have hb₁ : b 1 = 1 := by simp [b, IsFactorSet.one_left]
  have hroot (g : G) : ∃ z : kˣ, z ^ Fintype.card G = (b g)⁻¹ := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((b g)⁻¹ : kˣ).val
      (Fintype.card_pos : 0 < Fintype.card G)
    have hz₀ : z ≠ 0 := by
      intro h
      exact (Units.ne_zero ((b g)⁻¹)) (by
        simpa only [h, zero_pow Fintype.card_ne_zero] using hz.symm)
    exact ⟨Units.mk0 z hz₀, Units.ext hz⟩
  choose d hd using hroot
  let c (g : G) : kˣ := if g = 1 then 1 else d g
  have hc₁ : c 1 = 1 := by simp [c]
  have hc (g : G) : c g ^ Fintype.card G = (b g)⁻¹ := by
    by_cases hg : g = 1
    · simp [c, hg, hb₁]
    · simp [c, hg, hd]
  refine ⟨c, hc₁, fun g h ↦ ?_⟩
  rw [Nat.card_eq_fintype_card, mul_pow, mul_pow, mul_pow, inv_pow, hc, hc, hc]
  rw [inv_inv]
  calc
    (b g)⁻¹ * (b h)⁻¹ * b (g * h) * α g h ^ Fintype.card G =
        (b g)⁻¹ * (b h)⁻¹ * (b (g * h) * α g h ^ Fintype.card G) := by
      ac_rfl
    _ = 1 := by rw [hb]; simp [mul_assoc]

end TauCeti.IsFactorSet
