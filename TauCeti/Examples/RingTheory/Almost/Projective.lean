/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Projective
import TauCeti.RingTheory.Almost.ValuationRing
import TauCeti.NumberTheory.Padics.Complex.MaximalIdeal

/-!
# Examples of almost finite projective modules

These examples test `TauCeti.Almost.BasicSetup.IsAlmostFiniteProjective`:

* `Vⁿ` is almost finite projective for every setup, including `n = 0`;
* through the almost isomorphism `m → V`, the ideal `m` of every setup is almost finite
  projective; for a valuation domain with non-finitely-generated maximal ideal, such as
  `𝓞_ℂ_[p]`, it is not a finite projective module, so the almost notion is strictly weaker;
* `V ⧸ m` is almost finite projective for every setup, while `ℤ ⧸ 2` is not classically, since it
  is not a projective `ℤ`-module;
* for the zero setup `ℕ →₀ ℤ` is almost finite projective, but classically it is not, since it
  is not almost finitely generated.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.4.
-/

open IsLocalRing TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V] (S : BasicSetup V)

/-! ### Finite free modules -/

-- `Vⁿ` is almost finite projective for every setup, including `n = 0`.
example (n : ℕ) : S.IsAlmostFiniteProjective (Fin n → V) :=
  isAlmostFiniteProjective_of_finite_of_projective S

example : S.IsAlmostFiniteProjective (Fin 0 → V) :=
  isAlmostFiniteProjective_of_finite_of_projective S

/-! ### The ideal `m` -/

-- The ideal `m` of every setup is almost finite projective: `m → V` is an almost isomorphism.
example : S.IsAlmostFiniteProjective S.ideal :=
  S.isAlmostIso_subtype.isAlmostFiniteProjective_iff.mpr
    (isAlmostFiniteProjective_of_finite_of_projective S)

section ValuationRing

variable {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O] (h : ¬ (maximalIdeal O).FG)

-- For a valuation domain whose maximal ideal `m` is not finitely generated, `m` is almost finite
-- projective, but it is not a finitely generated, hence not a finite projective, `O`-module.
example : (ofValuationRing h).IsAlmostFiniteProjective (ofValuationRing h).ideal :=
  (isAlmostIso_subtype _).isAlmostFiniteProjective_iff.mpr
    (isAlmostFiniteProjective_of_finite_of_projective _)

example : ¬ Module.Finite O (ofValuationRing h).ideal := by
  rwa [Module.Finite.iff_fg, ofValuationRing_ideal]

-- The same for `𝓞_ℂ_[p]`.
example (p : ℕ) [Fact p.Prime] :
    (ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)).IsAlmostFiniteProjective
      (ofValuationRing (TauCeti.PadicComplexInt.not_fg_maximalIdeal p)).ideal :=
  (isAlmostIso_subtype _).isAlmostFiniteProjective_iff.mpr
    (isAlmostFiniteProjective_of_finite_of_projective _)

end ValuationRing

/-! ### Almost zero modules -/

-- `V ⧸ m` is almost finite projective for every setup.
example : S.IsAlmostFiniteProjective (V ⧸ S.ideal) :=
  S.isAlmostZero_quotient.isAlmostFiniteProjective

-- Classically `ℤ ⧸ 2` is not almost finite projective: a projective `ℤ`-module is flat, so
-- multiplication by `2` would be injective on it, whereas it is zero on `ℤ ⧸ 2`.
example : ¬ (classical ℤ).IsAlmostFiniteProjective (ZMod 2) := by
  rw [isAlmostFiniteProjective_classical_iff]
  rintro ⟨_, _⟩
  have h₂ : IsSMulRegular ℤ (2 : ℤ) := .of_ne_zero two_ne_zero
  exact one_ne_zero (h₂.of_flat (S := ZMod 2) (a₁ := 1) (a₂ := 0) (by decide))

/-! ### Infinite free modules -/

-- For the zero setup `ℕ →₀ ℤ` is almost finite projective; classically it is not, as it is not
-- almost finitely generated.
example : (zero ℤ).IsAlmostFiniteProjective (ℕ →₀ ℤ) :=
  isAlmostFiniteProjective_zero

example : ¬ (classical ℤ).IsAlmostFiniteProjective (ℕ →₀ ℤ) := fun h ↦ by
  have := almostFG_classical_iff.mp h.almostFG
  have := Module.Finite.finite_basis (Finsupp.basisSingleOne (R := ℤ) (ι := ℕ))
  exact not_finite ℕ
