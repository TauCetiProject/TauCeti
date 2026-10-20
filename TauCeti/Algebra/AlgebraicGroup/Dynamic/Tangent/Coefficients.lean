/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Representability
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent

/-!
# Coefficient criteria for dynamic tangent spaces

The tangent Lie algebra of a dynamic parabolic consists of the derivations annihilating
all negative coefficients of universal conjugation. For the dynamic unipotent subgroup,
the constant coefficient must also be annihilated. These criteria apply over arbitrary
commutative base rings and coefficient algebras, including nonreduced ones.

They express the infinitesimal extension and zero-limit conditions without choosing a
faithful matrix representation.

The proofs use the coefficient presentations of the dynamic defining ideals and
`TauCeti.HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span`.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), §§10 and 13.
-/

public section

open TauCeti TauCeti.Cocharacter

namespace BialgHom

universe u v w

variable {R : Type u} {H : Type v} {B : Type w}
variable [CommRing R] [CommRing H] [HopfAlgebra R H] [CommRing B] [Algebra R B]

/-- A tangent vector belongs to the dynamic parabolic exactly when it kills every negative
Laurent coefficient of universal conjugation. Use this as an explicit rewrite: the general
`TauCeti.HopfIdeal.mem_lieSubalgebra_iff` already simplifies tangent membership. -/
theorem mem_lieSubalgebra_parabolicDefiningHopfIdeal_iff
    (l : H →ₐc[R] LaurentPolynomial R)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ (parabolicDefiningHopfIdeal l).lieSubalgebra (B := B) ↔
      ∀ h : H, ∀ n : ℤ, n < 0 → d ((conjugationAlgHom l h).coeff n) = 0 := by
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _
    (parabolicDefiningHopfIdeal_toIdeal l)]
  constructor
  · intro hd h n hn
    exact hd _ ⟨h, n, hn, rfl⟩
  · rintro hd x ⟨h, n, hn, rfl⟩
    exact hd h n hn

/-- A tangent vector belongs to the dynamic unipotent subgroup exactly when it kills every
nonpositive Laurent coefficient of universal conjugation. Use this as an explicit rewrite: the
general
`TauCeti.HopfIdeal.mem_lieSubalgebra_iff` already simplifies tangent membership. -/
theorem mem_lieSubalgebra_unipotentDefiningHopfIdeal_iff
    (l : H →ₐc[R] LaurentPolynomial R)
    (d : Derivation R H (Bialgebra.CounitAlgebra R H B)) :
    d ∈ l.unipotentDefiningHopfIdeal.lieSubalgebra (B := B) ↔
      ∀ h : H, ∀ n : ℤ, n ≤ 0 → d ((conjugationAlgHom l h).coeff n) = 0 := by
  have hspan : (l.unipotentDefiningHopfIdeal).toIdeal =
      Ideal.span ({x | ∃ h : H, ∃ n : ℤ,
        n < 0 ∧ (conjugationAlgHom l h).coeff n = x} ∪
        {x | ∃ h : H, (conjugationAlgHom l h).coeff 0 -
          algebraMap R H (Coalgebra.counit h) = x}) := by
    rw [unipotentDefiningHopfIdeal_toIdeal, parabolicDefiningHopfIdeal_toIdeal,
      Ideal.span_union]
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _ hspan]
  constructor
  · intro hd h n hn
    rcases lt_or_eq_of_le hn with hn | rfl
    · exact hd _ (Or.inl ⟨h, n, hn, rfl⟩)
    · have hz := hd _ (Or.inr ⟨h, rfl⟩)
      simpa only [map_sub, d.map_algebraMap, sub_zero] using hz
  · intro hd x hx
    rcases hx with ⟨h, n, hn, rfl⟩ | ⟨h, rfl⟩
    · exact hd h n hn.le
    · simpa only [map_sub, d.map_algebraMap, sub_zero] using hd h 0 le_rfl

end BialgHom
