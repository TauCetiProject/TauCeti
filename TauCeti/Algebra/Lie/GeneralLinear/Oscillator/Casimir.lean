/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.Casimir
public import TauCeti.Algebra.Lie.GeneralLinear.Oscillator.DualPair
import Mathlib.Tactic.NoncommRing

/-!
# The Casimir operators of the dual pair `(U(p, q), U(r, s))` on its Fock module

On the Fock module `MvPolynomial (I × I') K` of
`TauCeti/Algebra/Lie/GeneralLinear/Oscillator/DualPair.lean`, with `n` rows and `n'` columns,
the trace-form Casimir elements `TauCeti.glCasimir` of `gl I` and of
`gl I'` act through the row action `TauCeti.fockRowHom` and the column action
`TauCeti.fockColHom`. Both images are, after normal ordering,

`D₄ + (n + n') D₂ + c`, with `D₄ = ∑ R a c R b c' L b c L a c'` and `D₂ = ∑ R a c L a c`,

with the constants `c = n n'² / 4` for the rows and `c = n² n' / 4` for the columns. So the two
Casimir operators differ by a scalar (`TauCeti.lift_fockColHom_glCasimir`):

`Ω' = Ω + n n' (n - n') / 4`.

On a common eigenvector the two Casimir eigenvalues therefore differ by `n n' (n - n') / 4`. This
matches the parameters: if `λ'` is `λ` with the string `σ_t = ((t - 1) / 2, …, -(t - 1) / 2)`
inserted, then `|λ'|² - |ρ_{n'}|² = |λ|² - |ρ_n|² - n n' (n' - n) / 4`
(`TauCeti.sum_sq_sub_eq_of_equiv_sum` in `TauCeti/Algebra/Lie/GeneralLinear/Casimir.lean`), and
`|λ|² - |ρ|²` is the eigenvalue of `TauCeti.glCasimir` on a highest weight vector of weight
`λ - ρ` (`TauCeti.glCasimir_eigenvalue_eq_sum_sq_sub`).

## Main results

* `TauCeti.sum_mul_eq_normal_order`: normal ordering of a Casimir sum of elements `∑ c, x a c d b c`
  under the canonical commutation relations.
* `TauCeti.lift_fockRowHom_glCasimir`, `TauCeti.lift_fockColHom_glCasimir`: the Casimir operators
  on the Fock module, and their difference.
* `TauCeti.casimir_eigenvalue_fockCol_eq`: on a common eigenvector the eigenvalues differ by
  `n n' (n - n') / 4`.

## References

* A. Paul, *First occurrence for the dual pairs `(U(p, q), U(r, s))`*, Canad. J. Math. 51
  (1999), 636--657, Theorem 2.11.
* The normal ordering argument is adapted from `New.FockDualPair.centredCasimir_oscRows`,
  `New.FockDualPair.centredCasimir_swap_oscRows_eq_add` and `New.sum_mul_eq_normal_order` in
  `src/Lib/DiscreteSeries/Theta/CasimirComparison.lean` of grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). The
  parameter identity `TauCeti.sum_sq_sub_eq_of_equiv_sum` is credited in its own file.
-/

public section

namespace TauCeti

open MvPolynomial Finset Matrix

open Fintype (card)

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Normal ordering -/

section NormalOrder

variable {K A R C : Type*} [CommRing K] [Ring A] [Algebra K A] [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C]

/-- Adding a scalar `t` to the diagonal of a square array `F` adds `2 t ∑ F a a + n t²` to the
sum `∑ F a b F b a`, where `n` is the size of the array. -/
theorem sum_add_scalar_mul_add_scalar (F : R → R → A) (t : K) :
    ∑ a, ∑ b, (F a b + if a = b then t • 1 else 0) * (F b a + if b = a then t • 1 else 0) =
      ∑ a, ∑ b, F a b * F b a + (2 * t) • ∑ a, F a a + (card R * t ^ 2) • (1 : A) := by
  have h_term (a b : R) :
      (F a b + if a = b then t • 1 else 0) * (F b a + if b = a then t • 1 else 0) =
        F a b * F b a + if a = b then (2 * t) • F a a + t ^ 2 • (1 : A) else 0 := by
    obtain rfl | hab := eq_or_ne a b
    · simp only [ite_true, add_mul, mul_add, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      module
    · simp [hab, hab.symm]
  simp only [h_term, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← smul_sum, sum_const,
    card_univ, ← Nat.cast_smul_eq_nsmul K]
  module

/-- **Normal ordering.** Let `x`, `d` be arrays in an algebra with
`d r c x r c' = x r c' d r c + δ c c'`. Then the Casimir sum of the elements
`∑ c, x a c d b c + t δ a b` is `D₄ + (n + 2 t) D₂ + n t²`, where
`D₄ = ∑ x a c x b c' d b c d a c'`, `D₂ = ∑ x r c d r c`, and `n` is the number of rows. -/
theorem sum_mul_eq_normal_order (x d : R → C → A) (t : K)
    (h_comm : ∀ (r : R) (c c' : C), d r c * x r c' = x r c' * d r c + if c = c' then 1 else 0) :
    ∑ a, ∑ b, (∑ c, x a c * d b c + if a = b then t • 1 else 0) *
        (∑ c, x b c * d a c + if b = a then t • 1 else 0) =
      ∑ a, ∑ b, ∑ c, ∑ c', x a c * x b c' * d b c * d a c' +
        (card R + 2 * t) • ∑ r, ∑ c, x r c * d r c + (card R * t ^ 2) • (1 : A) := by
  have h_move (a b : R) (c c' : C) : x a c * d b c * (x b c' * d a c') =
      x a c * x b c' * d b c * d a c' + if c = c' then x a c * d a c' else 0 := by
    rw [mul_assoc, ← mul_assoc (d b c), h_comm]
    split_ifs <;> noncomm_ring
  have h_quartic : ∑ a, ∑ b, (∑ c, x a c * d b c) * ∑ c, x b c * d a c =
      ∑ a, ∑ b, ∑ c, ∑ c', x a c * x b c' * d b c * d a c' +
        (card R : K) • ∑ r, ∑ c, x r c * d r c := by
    simp only [sum_mul_sum, h_move, sum_add_distrib, sum_ite_eq, mem_univ, ite_true, sum_const,
      card_univ, Nat.cast_smul_eq_nsmul, smul_sum]
  rw [sum_add_scalar_mul_add_scalar (fun a b ↦ ∑ c, x a c * d b c), h_quartic]
  module

end NormalOrder

/-! ### The two Casimir operators -/

variable {K : Type*} [Field K] {I I' : Type*} [Fintype I] [DecidableEq I] [Fintype I']
  [DecidableEq I'] {ε : I → Bool} {ε' : I' → Bool}

/-- **The Casimir operator of `gl I` on the Fock module**, in normal order: with `n` rows and `n'`
columns it is `D₄ + (n + n') D₂ + n n'² / 4`, where `D₄ = ∑ R a c R b c' L b c L a c'` and
`D₂ = ∑ R a c L a c`. -/
theorem lift_fockRowHom_glCasimir [NeZero (2 : K)] :
    UniversalEnvelopingAlgebra.lift K (fockRowHom K ε ε') (glCasimir K I) =
      (∑ a : I, ∑ b : I, ∑ c : I', ∑ c' : I',
        oscRaise K (IsEvenPair ε ε') (a, c) * oscRaise K (IsEvenPair ε ε') (b, c') *
          oscLower K (IsEvenPair ε ε') (b, c) * oscLower K (IsEvenPair ε ε') (a, c')) +
        (card I + card I' : K) • (∑ a : I, ∑ c : I',
          oscRaise K (IsEvenPair ε ε') (a, c) * oscLower K (IsEvenPair ε ε') (a, c)) +
        (card I * card I' ^ 2 / 4 : K) • 1 := by
  rw [lift_glCasimir]
  simp only [fockRowHom_single]
  rw [sum_mul_eq_normal_order (fun a c ↦ oscRaise K (IsEvenPair ε ε') (a, c))
    (fun b c ↦ oscLower K (IsEvenPair ε ε') (b, c)) _
    fun r c c' ↦ by simp [oscLower_mul_oscRaise], mul_div_cancel₀ _ two_ne_zero]
  congr 2
  rw [div_pow]
  norm_num
  ring

/-- The Casimir operator of `gl I'` on the Fock module, in the normal order of
`TauCeti.lift_fockRowHom_glCasimir`: `D₄ + (n + n') D₂ + n² n' / 4`. -/
private theorem lift_fockColHom_glCasimir_eq [NeZero (2 : K)] :
    UniversalEnvelopingAlgebra.lift K (fockColHom K ε ε') (glCasimir K I') =
      (∑ a : I, ∑ b : I, ∑ c : I', ∑ c' : I',
        oscRaise K (IsEvenPair ε ε') (a, c) * oscRaise K (IsEvenPair ε ε') (b, c') *
          oscLower K (IsEvenPair ε ε') (b, c) * oscLower K (IsEvenPair ε ε') (a, c')) +
        (card I + card I' : K) • (∑ a : I, ∑ c : I',
          oscRaise K (IsEvenPair ε ε') (a, c) * oscLower K (IsEvenPair ε ε') (a, c)) +
        (card I ^ 2 * card I' / 4 : K) • 1 := by
  rw [lift_glCasimir]
  simp only [fockColHom_single]
  rw [sum_mul_eq_normal_order (fun c a ↦ oscRaise K (IsEvenPair ε ε') (a, c))
    (fun d a ↦ oscLower K (IsEvenPair ε ε') (a, d)) _
    fun r c c' ↦ by simp [oscLower_mul_oscRaise]]
  -- The quartic terms agree after reordering the sums and exchanging the commuting `L`s.
  have h_quartic : ∑ c : I', ∑ d : I', ∑ a : I, ∑ b : I,
      oscRaise K (IsEvenPair ε ε') (a, c) * oscRaise K (IsEvenPair ε ε') (b, d) *
        oscLower K (IsEvenPair ε ε') (a, d) * oscLower K (IsEvenPair ε ε') (b, c) =
      ∑ a : I, ∑ b : I, ∑ c : I', ∑ c' : I',
        oscRaise K (IsEvenPair ε ε') (a, c) * oscRaise K (IsEvenPair ε ε') (b, c') *
          oscLower K (IsEvenPair ε ε') (b, c) * oscLower K (IsEvenPair ε ε') (a, c') := by
    have h := sum_comm (s := (univ : Finset (I' × I'))) (t := (univ : Finset (I × I)))
      (f := fun x y ↦ oscRaise K (IsEvenPair ε ε') (y.1, x.1) *
        oscRaise K (IsEvenPair ε ε') (y.2, x.2) * oscLower K (IsEvenPair ε ε') (y.1, x.2) *
          oscLower K (IsEvenPair ε ε') (y.2, x.1))
    simp only [Fintype.sum_prod_type] at h
    rw [h]
    simp only [mul_assoc, (commute_oscLower (_, _) (_, _)).eq]
  rw [h_quartic, sum_comm (s := univ (α := I')), mul_div_cancel₀ _ two_ne_zero]
  congr 2
  · rw [add_comm (card I' : K)]
  · rw [div_pow]
    norm_num
    ring

/-- **The comparison of the Casimir operators on the Fock module.** With `n` rows and `n'`
columns, the Casimir operator of `gl I'` is that of `gl I` plus the scalar `n n' (n - n') / 4`. -/
theorem lift_fockColHom_glCasimir [NeZero (2 : K)] :
    UniversalEnvelopingAlgebra.lift K (fockColHom K ε ε') (glCasimir K I') =
      UniversalEnvelopingAlgebra.lift K (fockRowHom K ε ε') (glCasimir K I) +
        (card I * card I' * (card I - card I') / 4 : K) • 1 := by
  rw [lift_fockColHom_glCasimir_eq, lift_fockRowHom_glCasimir]
  module

/-- On a nonzero vector of the Fock module on which the Casimir operators of `gl I` and `gl I'`
act by scalars `κ` and `κ'`, these satisfy `κ' = κ + n n' (n - n') / 4`. -/
theorem casimir_eigenvalue_fockCol_eq [NeZero (2 : K)] {v : MvPolynomial (I × I') K} (hv : v ≠ 0)
    {κ κ' : K} (h : UniversalEnvelopingAlgebra.lift K (fockRowHom K ε ε') (glCasimir K I) v = κ • v)
    (h' : UniversalEnvelopingAlgebra.lift K (fockColHom K ε ε') (glCasimir K I') v = κ' • v) :
    κ' = κ + card I * card I' * (card I - card I') / 4 := by
  rw [lift_fockColHom_glCasimir, LinearMap.add_apply, h, LinearMap.smul_apply,
    one_apply_eq_self, ← add_smul] at h'
  exact smul_left_injective K hv h'.symm

end TauCeti
