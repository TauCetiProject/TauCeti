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

This is the relation between the two Casimir operators on the Fock module in route step (2) of the
roadmap target below. On the side of the parameters, if `λ'` is `λ` with the string
`σ_t = ((t - 1) / 2, …, -(t - 1) / 2)` inserted (in any blocks), then
`|λ'|² - |ρ_{n'}|² = |λ|² - |ρ_n|² - n n' (n' - n) / 4`
(`TauCeti.sum_sq_sub_eq_of_equiv_sum`), where `ρ_N = ((N - 1) / 2, …, -(N - 1) / 2)` has
`|ρ_N|² = N (N² - 1) / 12` (`TauCeti.sum_rho_sq`); and `|λ|² - |ρ|²` is the eigenvalue of
`TauCeti.glCasimir` on a highest weight vector of weight `λ - ρ`
(`TauCeti.glCasimir_eigenvalue_eq_sum_sq_sub`), so the two relations match.

## Main results

* `TauCeti.lift_fockRowHom_glCasimir`, `TauCeti.lift_fockColHom_glCasimir`: the Casimir operators
  on the Fock module, and their difference.
* `TauCeti.casimir_eigenvalue_fockCol_eq`: on a common eigenvector the eigenvalues differ by
  `n n' (n - n') / 4`.
* `TauCeti.sum_rho_sq`, `TauCeti.glCasimir_eigenvalue_eq_sum_sq_sub`,
  `TauCeti.sum_sq_sub_eq_of_equiv_sum`: the parameters.

## References

This is part of route step (2) of target 3.46a of the roadmap
`RiemannHypothesisForDirichletLFunctions/ThetaKernelsForUnitaryDualPairs`.

* A. Paul, *First occurrence for the dual pairs `(U(p, q), U(r, s))`*, Canad. J. Math. 51
  (1999), 636--657, Theorem 2.11.
* The normal ordering argument is adapted from `New.FockDualPair.centredCasimir_oscRows`,
  `New.FockDualPair.centredCasimir_swap_oscRows_eq_add`, `New.sum_mul_eq_normal_order` and
  `New.IsMatch.centred_casimirValue_eq` in `src/Lib/DiscreteSeries/Theta/CasimirComparison.lean`
  of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

namespace TauCeti

open MvPolynomial Finset Matrix

open Fintype (card)

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Normal ordering -/

section NormalOrder

variable {K A R C : Type*} [Field K] [Ring A] [Algebra K A] [Fintype R] [DecidableEq R]
  [Fintype C] [DecidableEq C]

/-- Adding a scalar `t` to the diagonal of a square array `F` adds `2 t ∑ F a a + n t²` to the
sum `∑ F a b F b a`, where `n` is the size of the array. -/
private theorem sum_add_scalar_mul_add_scalar (F : R → R → A) (t : K) :
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
private theorem sum_mul_eq_normal_order (x d : R → C → A) (t : K)
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

/-- Exchanging the two outer and the two inner summation variables of a fourfold sum. -/
private theorem sum_sum_sum_sum_comm {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (f : α → α → β → β → M) :
    ∑ c, ∑ d, ∑ a, ∑ b, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := by
  simp only [← Finset.sum_product']
  exact Finset.sum_nbij' (fun x ↦ (x.2.2.1, x.2.2.2, x.1, x.2.1))
    (fun y ↦ (y.2.2.1, y.2.2.2, y.1, y.2.1)) (by simp) (by simp) (by simp) (by simp) (by simp)

end NormalOrder

/-! ### The two Casimir operators -/

variable {K : Type*} [Field K] {I I' : Type*} [Fintype I] [DecidableEq I] [Fintype I']
  [DecidableEq I'] {ε : I → Bool} {ε' : I' → Bool}

variable (K ε ε')

/-- The operator `D₄ = ∑ R a c R b c' L b c L a c'` on the Fock module. -/
private noncomputable def fockQuartic : Module.End K (MvPolynomial (I × I') K) :=
  ∑ a : I, ∑ b : I, ∑ c : I', ∑ c' : I',
    oscRaise K (IsEvenPair ε ε') (a, c) * oscRaise K (IsEvenPair ε ε') (b, c') *
      oscLower K (IsEvenPair ε ε') (b, c) * oscLower K (IsEvenPair ε ε') (a, c')

/-- The operator `D₂ = ∑ R a c L a c` on the Fock module. -/
private noncomputable def fockQuadratic : Module.End K (MvPolynomial (I × I') K) :=
  ∑ a : I, ∑ c : I', oscRaise K (IsEvenPair ε ε') (a, c) * oscLower K (IsEvenPair ε ε') (a, c)

variable {K ε ε'}

private theorem lift_fockRowHom_glCasimir_eq [NeZero (2 : K)] :
    UniversalEnvelopingAlgebra.lift K (fockRowHom K ε ε') (glCasimir K I) =
      fockQuartic K ε ε' + (card I + card I' : K) • fockQuadratic K ε ε' +
        (card I * card I' ^ 2 / 4 : K) • 1 := by
  rw [lift_glCasimir]
  simp only [fockRowHom_single]
  rw [sum_mul_eq_normal_order (fun a c ↦ oscRaise K (IsEvenPair ε ε') (a, c))
    (fun b c ↦ oscLower K (IsEvenPair ε ε') (b, c)) _
    fun r c c' ↦ by simp [oscLower_mul_oscRaise]]
  rw [fockQuartic, fockQuadratic, mul_div_cancel₀ _ two_ne_zero]
  congr 2
  rw [div_pow, show (2 : K) ^ 2 = 4 by norm_num]
  ring

private theorem lift_fockColHom_glCasimir_eq [NeZero (2 : K)] :
    UniversalEnvelopingAlgebra.lift K (fockColHom K ε ε') (glCasimir K I') =
      fockQuartic K ε ε' + (card I + card I' : K) • fockQuadratic K ε ε' +
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
      fockQuartic K ε ε' := by
    rw [fockQuartic, sum_sum_sum_sum_comm]
    simp only [mul_assoc, (commute_oscLower (_, _) (_, _)).eq]
  rw [h_quartic, fockQuadratic, sum_comm (s := univ (α := I')), mul_div_cancel₀ _ two_ne_zero]
  congr 2
  · rw [add_comm (card I' : K)]
  · rw [div_pow, show (2 : K) ^ 2 = 4 by norm_num]
    ring

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
        (card I * card I' ^ 2 / 4 : K) • 1 :=
  lift_fockRowHom_glCasimir_eq

/-- **The comparison of the Casimir operators on the Fock module.** With `n` rows and `n'`
columns, the Casimir operator of `gl I'` is that of `gl I` plus the scalar `n n' (n - n') / 4`. -/
theorem lift_fockColHom_glCasimir [NeZero (2 : K)] :
    UniversalEnvelopingAlgebra.lift K (fockColHom K ε ε') (glCasimir K I') =
      UniversalEnvelopingAlgebra.lift K (fockRowHom K ε ε') (glCasimir K I) +
        (card I * card I' * (card I - card I') / 4 : K) • 1 := by
  rw [lift_fockColHom_glCasimir_eq, lift_fockRowHom_glCasimir_eq]
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

/-! ### The parameters -/

section Parameters

variable [CharZero K]

private theorem sum_range_sq_mul_six (N : ℕ) :
    (∑ i ∈ range N, (i : K) ^ 2) * 6 = N * (N - 1) * (2 * N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, add_mul, ih]
    push_cast
    ring

private theorem sum_range_mul_two (N : ℕ) : (∑ i ∈ range N, (i : K)) * 2 = N * (N - 1) := by
  have h := congrArg (fun m : ℕ ↦ (m : K)) (sum_range_id_mul_two N)
  rcases N with _ | N
  · simp
  · simpa using h

/-- The vector `ρ_N = ((N - 1) / 2, (N - 3) / 2, …, -(N - 1) / 2)`, half the sum of the positive
roots of `gl N`, has `|ρ_N|² = N (N² - 1) / 12`. -/
theorem sum_rho_sq (N : ℕ) :
    ∑ i : Fin N, (((N : K) - 1) / 2 - i) ^ 2 = (N : K) * (N ^ 2 - 1) / 12 := by
  have h6 := sum_range_sq_mul_six (K := K) N
  have h2 := sum_range_mul_two (K := K) N
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ (((N : K) - 1) / 2 - i) ^ 2)]
  have h_term (i : ℕ) : (((N : K) - 1) / 2 - i) ^ 2 =
      (i : K) ^ 2 - (N - 1) * i + ((N - 1) / 2) ^ 2 := by ring
  simp only [h_term, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range,
    nsmul_eq_mul]
  linear_combination (1 / 6 : K) * h6 - ((N : K) - 1) / 2 * h2

/-- **The `gl N` Casimir eigenvalue as `|λ|² - |ρ|²`.** On a highest weight vector of weight `μ`
the trace-form Casimir acts by `∑ μ i (μ i + N - 1 - 2 i)`
(`TauCeti.glCasimir_smul_of_isGlHighestWeightVector`); this is `|μ + ρ|² - |ρ|²` for
`ρ = ((N - 1) / 2, …, -(N - 1) / 2)`. -/
theorem glCasimir_eigenvalue_eq_sum_sq_sub (N : ℕ) (μ : Fin N → K) :
    ∑ i : Fin N, μ i * (μ i + N - 1 - 2 * i) =
      ∑ i : Fin N, (μ i + (((N : K) - 1) / 2 - i)) ^ 2 - (N : K) * (N ^ 2 - 1) / 12 := by
  rw [← sum_rho_sq, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  ring

omit [DecidableEq I] [DecidableEq I'] in
/-- **Inserting the string `ρ_t` into a parameter.** If `λ'` is `λ` with the string
`σ_t = ((t - 1) / 2, …, -(t - 1) / 2)` inserted, as described by an equivalence
`e : I ⊕ Fin t ≃ I'`, then `|λ'|² - |ρ_{n'}|² = |λ|² - |ρ_n|² - n n' (n' - n) / 4`, where `n` and
`n'` are the numbers of entries. -/
theorem sum_sq_sub_eq_of_equiv_sum {t : ℕ} (e : I ⊕ Fin t ≃ I') (lam : I → K) (lam' : I' → K)
    (h_left : ∀ a, lam' (e (.inl a)) = lam a)
    (h_right : ∀ k : Fin t, lam' (e (.inr k)) = ((t : K) - 1) / 2 - k) :
    ∑ c, lam' c ^ 2 - card I' * (card I' ^ 2 - 1) / 12 =
      ∑ a, lam a ^ 2 - card I * (card I ^ 2 - 1) / 12 -
        card I * card I' * (card I' - card I) / 4 := by
  have h_card : (card I' : K) = card I + t := by
    rw [← Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin]
    push_cast
    rfl
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [h_left, h_right, sum_rho_sq, h_card]
  ring

end Parameters

end TauCeti
