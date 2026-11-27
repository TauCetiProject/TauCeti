/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers

/-!
# Period-algebra presentations of quadratic rings of integers

For any quadratic number field `K` of discriminant `D = NumberField.discr K`, Stickelberger's
congruence gives `D % 4 = 0 ∨ D % 4 = 1`, so `QuadraticAlgebra ℤ (D / 4) (D % 4)` has
discriminant `D` (`QuadraticAlgebra.discr_ediv_emod`). Comparing discriminants with the
`ℤ[θ]` / `ℤ[(1 + θ)/2]` presentations from
`TauCeti.NumberTheory.NumberField.Quadratic.RingOfIntegers` yields a `ℤ`-algebra isomorphism
`𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (D / 4) (D % 4)`
(`TauCeti.NumberField.exists_ringOfIntegers_periodAlgEquiv`).

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
* D. A. Cox, *Primes of the Form x² + ny²*, §7.
-/

public section

open Module NumberField

namespace TauCeti.NumberField

/-- **Period-algebra presentation of `𝓞 K`**: for any quadratic number field `K` of discriminant
`D = discr K`, `𝓞 K` admits a `ℤ`-algebra isomorphism onto the canonical integral quadratic algebra
`QuadraticAlgebra ℤ (D / 4) (D % 4)`. -/
theorem exists_ringOfIntegers_periodAlgEquiv {K : Type*} [Field K] [NumberField K]
    (hK : finrank ℚ K = 2) :
    Nonempty (𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (discr K / 4) (discr K % 4)) := by
  obtain ⟨θ, d, hmin, hgen, hsf⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  by_cases hd4 : d % 4 = 1
  · have hdisc : discr K = d := discr_eq_of_squarefree_of_mod_four_eq_one hmin hgen hsf hd4
    have hD4 : discr K % 4 = 0 ∨ discr K % 4 = 1 := Or.inr (hdisc.symm ▸ hd4)
    obtain ⟨e₂⟩ :=
      (QuadraticAlgebra.nonempty_algEquiv_int_iff_discr_eq (a := (d - 1) / 4) (b := 1) hD4).mpr <|
        by rw [hdisc, QuadraticAlgebra.discr_def]; omega
    exact ⟨(ringOfIntegersAlgEquivHalfGen hmin hgen hsf hd4).trans e₂⟩
  · have hdisc : discr K = 4 * d := discr_eq_four_mul_of_mod_four_ne_one hmin hgen hsf hd4
    have hD4 : discr K % 4 = 0 ∨ discr K % 4 = 1 := Or.inl (by rw [hdisc]; omega)
    obtain ⟨e₂⟩ :=
      (QuadraticAlgebra.nonempty_algEquiv_int_iff_discr_eq (a := d) (b := 0) hD4).mpr <|
        by rw [hdisc, QuadraticAlgebra.discr_def]; ring
    exact ⟨(ringOfIntegersAlgEquivGen hmin hgen hsf hd4).trans e₂⟩

end TauCeti.NumberField
