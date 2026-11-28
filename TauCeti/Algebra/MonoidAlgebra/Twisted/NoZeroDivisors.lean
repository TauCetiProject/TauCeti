/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Twisted.Basic

/-!
# Zero divisors in twisted monoid algebras

A twisted monoid algebra over a monoid with unique products has no zero divisors whenever
its scalar semiring has none. In particular, the based quantum torus of a free abelian
lattice over a domain ring is a domain, including at finite-order parameters.
This is the algebraic input to constructing its fraction division ring.

The coefficient formula from `Twisted.Basic` uses the existing monomial basis. At a uniquely
represented product of support elements, the coefficient is the product of the two
coefficients times the factor-set unit. When the scalar semiring has no zero divisors, this
coefficient cannot vanish.

The `NoZeroDivisors` and `IsCancelMulZero` instance arguments adapt the corresponding instances
in `Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors` to the table of `TwistedMonoidAlgebra.of`.
No ordering or finite generation of the monoid is required.
-/

public section

namespace TauCeti.TwistedMonoidAlgebra

variable {k G : Type*} [CommSemiring k] [Monoid G]
  {α : G → G → kˣ} [IsFactorSet α]

/-- A unit-valued twist does not introduce zero divisors on a unique-product monoid. -/
instance [NoZeroDivisors k] [UniqueProds G] :
    NoZeroDivisors (twistedMonoidAlgebra k G α) where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} hfg := by
    contrapose! hfg
    have hf : ((basis k G α).repr f).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr ((map_ne_zero_iff _ (basis k G α).repr.injective).mpr hfg.1)
    have hg : ((basis k G α).repr g).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr ((map_ne_zero_iff _ (basis k G α).repr.injective).mpr hfg.2)
    obtain ⟨a, ha, b, hb, hab⟩ := UniqueProds.uniqueMul_of_nonempty hf hg
    have : Nontrivial k := ⟨⟨(basis k G α).repr f a, 0, Finsupp.mem_support_iff.mp ha⟩⟩
    intro heq
    have hc := repr_mul_apply_of_uniqueMul hab
    rw [heq, map_zero, Finsupp.zero_apply] at hc
    exact (mul_ne_zero (mul_ne_zero (Finsupp.mem_support_iff.mp ha)
      (Finsupp.mem_support_iff.mp hb)) (α a b).ne_zero) hc.symm

/-- An additive self-map `φ` of a twisted monoid algebra over an additively cancellative
semiring is injective if, whenever `φ g₁ = φ g₂` and `g₁` or `g₂` is nonzero, some monomial in
the union of their supports has the same coefficient in `g₁` and `g₂`. Removing that monomial
from both reduces the union of supports, which drives the induction. -/
private theorem injective_of_exists_repr_eq [IsCancelAdd k] [DecidableEq G]
    {φ : twistedMonoidAlgebra k G α → twistedMonoidAlgebra k G α}
    (hφ : ∀ x y, φ (x + y) = φ x + φ y)
    (h : ∀ g₁ g₂, φ g₁ = φ g₂ →
      (((basis k G α).repr g₁).support ∪ ((basis k G α).repr g₂).support).Nonempty →
      ∃ a ∈ ((basis k G α).repr g₁).support ∪ ((basis k G α).repr g₂).support,
        (basis k G α).repr g₁ a = (basis k G α).repr g₂ a) :
    Function.Injective φ := by
  intro g₁ g₂ eq
  induction hg : ((basis k G α).repr g₁).support ∪ ((basis k G α).repr g₂).support
    using Finset.eraseInduction generalizing g₁ g₂ with
  | _ s ih =>
  obtain hs | hs := s.eq_empty_or_nonempty <;> subst s
  · simp_all
  obtain ⟨a, ha, hc⟩ := h g₁ g₂ eq hs
  have decomp (g : twistedMonoidAlgebra k G α) :
      g = (basis k G α).repr.symm (((basis k G α).repr g).erase a) +
        (basis k G α).repr.symm (Finsupp.single a ((basis k G α).repr g a)) := by
    rw [← map_add, Finsupp.erase_add_single, LinearEquiv.symm_apply_apply]
  rw [decomp g₁, decomp g₂, hc] at eq ⊢
  rw [hφ, hφ, add_left_inj] at eq
  rw [ih a ha eq]
  simp [Finset.erase_union_distrib]

/-- Multiplication by a nonzero element of a twisted monoid algebra is cancellative over an
additively and multiplicatively cancellative semiring on a unique-product monoid. -/
instance [IsCancelAdd k] [IsCancelMulZero k] [UniqueProds G] :
    IsCancelMulZero (twistedMonoidAlgebra k G α) where
  mul_left_cancel_of_ne_zero {f} hf := by
    classical
    refine injective_of_exists_repr_eq (mul_add f) fun g₁ g₂ eq h ↦ ?_
    have hf : ((basis k G α).repr f).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr ((map_ne_zero_iff _ (basis k G α).repr.injective).mpr hf)
    obtain ⟨af, haf, ag, hag, uniq⟩ := UniqueProds.uniqueMul_of_nonempty hf h
    have h := repr_mul_apply_of_uniqueMul (uniq.mono subset_rfl Finset.subset_union_left)
    rw [eq, repr_mul_apply_of_uniqueMul (uniq.mono subset_rfl Finset.subset_union_right)] at h
    exact ⟨ag, hag, mul_left_cancel₀ (Finsupp.mem_support_iff.mp haf)
      ((Units.mul_left_inj _).mp h).symm⟩
  mul_right_cancel_of_ne_zero {f} hf := by
    classical
    refine injective_of_exists_repr_eq (fun _ _ ↦ add_mul _ _ f) fun g₁ g₂ eq h ↦ ?_
    have hf : ((basis k G α).repr f).support.Nonempty :=
      Finsupp.support_nonempty_iff.mpr ((map_ne_zero_iff _ (basis k G α).repr.injective).mpr hf)
    obtain ⟨ag, hag, af, haf, uniq⟩ := UniqueProds.uniqueMul_of_nonempty h hf
    have h := repr_mul_apply_of_uniqueMul (uniq.mono Finset.subset_union_left subset_rfl)
    rw [eq, repr_mul_apply_of_uniqueMul (uniq.mono Finset.subset_union_right subset_rfl)] at h
    exact ⟨ag, hag, mul_right_cancel₀ (Finsupp.mem_support_iff.mp haf)
      ((Units.mul_left_inj _).mp h).symm⟩

/-- A twisted monoid algebra over an additively cancellative domain semiring and a
unique-product monoid is a domain. -/
instance [IsCancelAdd k] [IsDomain k] [UniqueProds G] :
    IsDomain (twistedMonoidAlgebra k G α) where

end TauCeti.TwistedMonoidAlgebra
