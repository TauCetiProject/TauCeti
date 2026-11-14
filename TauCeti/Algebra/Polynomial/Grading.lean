/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# The standard integer monomial-degree grading on `R[X]`

Because `R[X]` is `AddMonoidAlgebra R ℕ`, `AddMonoidAlgebra.gradeBy R (Nat.castAddMonoidHom ℤ)`
equips `R[X]` with its standard `ℤ`-indexed monomial-degree `GradedAlgebra` structure, placing
`X ^ n` in degree `n` and `⊥` in every negative degree.

## Main definitions

* `TauCeti.Polynomial.degreeGrade`: the `ℤ`-indexed monomial grading on `R[X]`.

## Main results

* `TauCeti.Polynomial.degreeGrade_eq_bot_of_neg`: negative-degree pieces vanish.
* `TauCeti.Polynomial.degreeGrade_zero_eq_span_one`: degree zero is the `R`-span of `1`.
* `TauCeti.Polynomial.X_pow_mem_degreeGrade` and `TauCeti.Polynomial.X_mem_degreeGrade_one`:
  `X ^ n` has degree `n` and `X` has degree `1`.
-/

public section

noncomputable section

namespace TauCeti.Polynomial

open _root_.Polynomial

universe u

variable (R : Type u) [CommSemiring R]

/-- The standard `ℤ`-indexed monomial-degree grading on `R[X]`, placing `X ^ n` in degree `(n : ℤ)`
and `⊥` in negative degrees. Its `GradedAlgebra` instance comes directly from
`AddMonoidAlgebra.gradeBy.gradedAlgebra`. -/
abbrev degreeGrade : ℤ → Submodule R R[X] :=
  AddMonoidAlgebra.gradeBy R (Nat.castAddMonoidHom ℤ)

variable {R} in
/-- A polynomial lies in `degreeGrade R d` exactly when every nonzero coefficient occurs in degree
`n` with `(n : ℤ) = d`. -/
theorem mem_degreeGrade_iff {d : ℤ} {f : R[X]} :
    f ∈ degreeGrade R d ↔ ∀ n : ℕ, f.coeff n ≠ 0 → (n : ℤ) = d := by
  simp [degreeGrade]

/-- All negative-degree pieces of `degreeGrade R` vanish. -/
@[simp]
theorem degreeGrade_eq_bot_of_neg {d : ℤ} (hd : d < 0) : degreeGrade R d = ⊥ := by
  refine eq_bot_iff.2 fun f hf ↦ ?_
  rw [Submodule.mem_bot]
  ext n
  rw [coeff_zero]
  by_contra hne
  have hnd := mem_degreeGrade_iff.1 hf n hne
  omega

/-- The degree-zero piece of `degreeGrade R` is the `R`-submodule spanned by `1`. -/
theorem degreeGrade_zero_eq_span_one :
    degreeGrade R 0 = Submodule.span R {(1 : R[X])} := by
  ext f
  rw [mem_degreeGrade_iff, Submodule.mem_span_singleton]
  refine ⟨fun hf ↦ ⟨f.coeff 0, ?_⟩, ?_⟩
  · ext n
    rw [AddMonoidAlgebra.coeff_smul_apply, coeff_one]
    split_ifs with hn
    · subst hn; simp
    · rw [smul_zero]
      symm
      by_contra hne
      have h0 := hf n hne
      omega
  · rintro ⟨r, rfl⟩ n hne
    rw [AddMonoidAlgebra.coeff_smul_apply, coeff_one] at hne
    split_ifs at hne with hn
    · exact mod_cast hn
    · rw [smul_zero] at hne
      exact absurd rfl hne

/-- The monomial `X ^ n` has degree `(n : ℤ)` in `degreeGrade R`. -/
theorem X_pow_mem_degreeGrade (n : ℕ) : (X ^ n : R[X]) ∈ degreeGrade R n := by
  rw [mem_degreeGrade_iff]
  intro m hm
  rw [coeff_X_pow] at hm
  split_ifs at hm with h
  · exact mod_cast h
  · exact absurd rfl hm

/-- The indeterminate `X` has degree `1` in `degreeGrade R`. -/
theorem X_mem_degreeGrade_one : (X : R[X]) ∈ degreeGrade R 1 := by
  simpa using X_pow_mem_degreeGrade R 1

end TauCeti.Polynomial
