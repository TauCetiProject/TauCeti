/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.PeriodPolynomial.Finrank
import TauCeti.LinearAlgebra.Trace.Submodule
import TauCeti.LinearAlgebra.Trace.Exchange
import TauCeti.LinearAlgebra.Trace.Idempotent
import Mathlib.LinearAlgebra.PID

/-!
# Dimensions of the even and odd period-polynomial spaces

Over a characteristic-zero field, for positive even degree `w`, parity has trace `1` on the
period-polynomial space. Consequently its even part has one more dimension than its odd part.
Combining this with the algebraic
calculation of the total dimension identifies, over `ℂ` and for every degree `w`, the dimensions
of the even and odd parts with those of level-one modular and cusp forms, respectively.
These are the dimension comparisons needed to turn injective even and odd period maps into
isomorphisms.

The reflection `J : P(X,Y) ↦ P(Y,X)` preserves both kernels defining the period-polynomial
space. It has trace zero on each kernel and trace one on all binary forms of even degree.
Inclusion–exclusion therefore gives trace minus one on their intersection. On the intersection,
parity is minus `J`.

## References

* W. Kohnen and D. Zagier, *Modular forms with rational periods*, §1.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §2.
-/

public noncomputable section

open Matrix MulOpposite MvPolynomial ModularGroup Module Polynomial
open scoped MatrixGroups

namespace TauCeti

variable {K : Type*} [Field K] {w : ℕ}

local notation "V" => homogeneousSubmodule (Fin 2) K w
local notation "σ" => binaryFormRep K w (op !![0, -1; 1, 0])
local notation "υ" => binaryFormRep K w (op !![1, -1; 1, 0])
local notation "δ" => binaryFormRep K w (op !![0, 1; 1, 0])
local notation "ε" => binaryFormRep K w (op !![-1, 0; 0, 1])

private lemma U_matrix :
    ((T * S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma S_sq (hw : Even w) : σ ^ 2 = 1 := by
  simpa only [coe_S] using binaryFormRep_S_sq_of_even (R := K) hw

private lemma U_cube (hw : Even w) : υ ^ 3 = 1 := by
  simpa only [U_matrix] using binaryFormRep_U_pow_three_of_even (R := K) hw

private lemma swap_commute_S (hw : Even w) : Commute σ δ := by
  have h : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * !![0, -1; 1, 0] =
      -(!![0, -1; 1, 0] * !![0, 1; 1, 0]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Commute, SemiconjBy, ← map_mul, ← map_mul, ← op_mul, ← op_mul, h,
    binaryFormRep_op_neg_of_even hw]

private lemma swap_mul_U (hw : Even w) : δ * υ = υ ^ 2 * δ := by
  have h : (!![1, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * !![0, 1; 1, 0] =
      -(!![0, 1; 1, 0] * (!![1, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [← map_pow, ← op_pow, ← map_mul, ← map_mul, ← op_mul, ← op_mul, h,
    binaryFormRep_op_neg_of_even hw]

private lemma swap_commute_U_sum (hw : Even w) : Commute (1 + υ + υ ^ 2) δ := by
  have h₁ := swap_mul_U (K := K) hw
  have h₃ := U_cube (K := K) hw
  have h₂ : δ * υ ^ 2 = υ * δ := by
    calc
      δ * υ ^ 2 = (δ * υ) * υ := by rw [sq, mul_assoc]
      _ = υ ^ 2 * (δ * υ) := by rw [h₁, mul_assoc, h₁]
      _ = υ * δ := by rw [h₁, ← mul_assoc, ← pow_add, pow_succ, h₃, one_mul]
  rw [Commute, SemiconjBy]
  rw [add_mul, add_mul, mul_add, mul_add, one_mul, mul_one, h₁, h₂]
  abel

private lemma swap_mem_ker {c : End K V} (hc : Commute c δ) :
    ∀ x ∈ LinearMap.ker c, δ x ∈ LinearMap.ker c := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hx, map_zero]

private lemma swap_mem_periodPolynomials (hw : Even w) :
    ∀ x ∈ periodPolynomials K w, δ x ∈ periodPolynomials K w := by
  rw [periodPolynomials_def, coe_S, U_matrix]
  exact fun x hx ↦ ⟨swap_mem_ker ((Commute.one_left δ).add_left (swap_commute_S hw)) x hx.1,
    swap_mem_ker (swap_commute_U_sum hw) x hx.2⟩

private lemma trace_swap (hw : Even w) : LinearMap.trace K V δ = 1 :=
  trace_binaryFormRep_eq_one_of_trace_eq_zero_det_eq_neg_one
    (by simp [Matrix.trace_fin_two]) (by norm_num [Matrix.det_fin_two]) hw

private lemma trace_S_swap (hw : Even w) : LinearMap.trace K V (σ * δ) = 1 := by
  rw [← map_mul, ← op_mul]
  exact trace_binaryFormRep_eq_one_of_trace_eq_zero_det_eq_neg_one
    (by norm_num [Matrix.trace_fin_two])
    (by norm_num [Matrix.det_fin_two]) hw

private lemma trace_U_swap (hw : Even w) : LinearMap.trace K V (υ * δ) = 1 := by
  rw [← map_mul, ← op_mul]
  exact trace_binaryFormRep_eq_one_of_trace_eq_zero_det_eq_neg_one
    (by norm_num [Matrix.trace_fin_two]) (by norm_num [Matrix.det_fin_two]) hw

private lemma trace_U_sq_swap (hw : Even w) : LinearMap.trace K V (υ ^ 2 * δ) = 1 := by
  rw [← swap_mul_U hw, LinearMap.trace_mul_comm]
  exact trace_U_swap hw

variable [CharZero K]

private lemma trace_swap_ker_S (hw : Even w) :
    LinearMap.trace K (LinearMap.ker (1 + σ))
      ((δ).restrict (swap_mem_ker ((Commute.one_left δ).add_left (swap_commute_S hw)))) = 0 := by
  have h := LinearMap.two_mul_trace_restrict_ker_one_add (S_sq (K := K) hw)
    (swap_commute_S hw)
  rw [trace_swap hw, trace_S_swap hw] at h
  linear_combination h / 2

private lemma trace_swap_ker_U (hw : Even w) :
    LinearMap.trace K (LinearMap.ker (1 + υ + υ ^ 2))
      ((δ).restrict (swap_mem_ker (swap_commute_U_sum hw))) = 0 := by
  have h := LinearMap.three_mul_trace_restrict_ker_one_add_add_sq (U_cube (K := K) hw)
    (swap_commute_U_sum hw)
  rw [trace_swap hw, trace_U_swap hw, trace_U_sq_swap hw] at h
  linear_combination h / 3

private lemma trace_swap_periodPolynomials (hw : Even w) (hw₀ : w ≠ 0) :
    LinearMap.trace K (periodPolynomials K w)
      ((δ).restrict (swap_mem_periodPolynomials hw)) = -1 := by
  have h := trace_restrict_inf_add_trace_restrict_sup δ
    (swap_mem_ker ((Commute.one_left δ).add_left (swap_commute_S hw)))
    (swap_mem_ker (swap_commute_U_sum hw))
  rw [trace_swap_ker_S hw, trace_swap_ker_U hw] at h
  rw [LinearMap.trace_restrict_congr
    (by simpa only [coe_S, U_matrix] using
      codisjoint_iff.mp (codisjoint_ker_one_add_S_ker_one_add_U_add_U_sq (K := K) hw hw₀)) _ _
      (fun x _ ↦ Submodule.mem_top)] at h
  rw [LinearMap.trace_restrict_eq_of_forall_mem _ δ (fun x ↦ Submodule.mem_top),
    trace_swap hw] at h
  have hW : (LinearMap.ker (1 + σ) ⊓ LinearMap.ker (1 + υ + υ ^ 2) : Submodule K V) =
      periodPolynomials K w := by
    rw [periodPolynomials_def, coe_S, U_matrix]
  have htr := LinearMap.trace_restrict_congr hW (δ)
    (fun x hx ↦ ⟨swap_mem_ker ((Commute.one_left δ).add_left (swap_commute_S hw)) x
      (Submodule.mem_inf.mp hx).1,
      swap_mem_ker (swap_commute_U_sum hw) x (Submodule.mem_inf.mp hx).2⟩)
    (swap_mem_periodPolynomials hw)
  linear_combination h - htr

/-- For positive even degree, parity `P(X,Y) ↦ P(-X,Y)` has trace `1` on period polynomials. -/
theorem trace_parity_periodPolynomials (hw : Even w) (hw₀ : w ≠ 0) :
    LinearMap.trace K (periodPolynomials K w)
      ((ε).restrict fun _ hx ↦ mem_periodPolynomials_binaryFormRep_parity hw hx) = 1 := by
  have hmat : (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ) * !![-1, 0; 0, 1] = -!![0, 1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hε : ε * σ = δ := by
    rw [← map_mul, ← op_mul, hmat, binaryFormRep_op_neg_of_even hw]
  let e : End K (periodPolynomials K w) :=
    (ε).restrict fun _ hx ↦ mem_periodPolynomials_binaryFormRep_parity hw hx
  let d : End K (periodPolynomials K w) := (δ).restrict (swap_mem_periodPolynomials hw)
  have heq : e + d = 0 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have hS : σ x = -x := by
      simpa only [coe_S] using
        eq_neg_of_add_eq_zero_right (mem_periodPolynomials_iff.mp x.2).1
    have h := LinearMap.congr_fun hε x
    have h' : ε x + δ x = 0 := by
      rw [Module.End.mul_apply, hS, map_neg] at h
      rw [← h]
      exact add_neg_cancel _
    simpa [e, d, LinearMap.restrict_apply] using h'
  have h := congrArg (LinearMap.trace K (periodPolynomials K w)) heq
  rw [map_add, map_zero, trace_swap_periodPolynomials hw hw₀] at h
  linear_combination h

private lemma finrank_even_add_finrank_odd :
    finrank K (evenPeriodPolynomials K w) + finrank K (oddPeriodPolynomials K w) =
      finrank K (periodPolynomials K w) := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (evenPeriodPolynomials K w) (oddPeriodPolynomials K w)
  let _ : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [evenPeriodPolynomials_sup_oddPeriodPolynomials,
    (disjoint_evenPeriodPolynomials_oddPeriodPolynomials
      (mul_right_injective₀ (two_ne_zero : (2 : K) ≠ 0))).eq_bot, finrank_bot, add_zero] at hsum
  exact hsum.symm

/-- In positive even degree, the even period-polynomial space has one more dimension than
its odd part. This statement is independent of modular forms. -/
theorem finrank_evenPeriodPolynomials_eq_finrank_odd_add_one (hw : Even w) (hw₀ : w ≠ 0) :
    finrank K (evenPeriodPolynomials K w) = finrank K (oddPeriodPolynomials K w) + 1 := by
  let τ : End K (periodPolynomials K w) :=
    (ε).restrict fun _ hx ↦ mem_periodPolynomials_binaryFormRep_parity hw hx
  have hε : ε ^ 2 = 1 := by
    apply LinearMap.ext
    intro x
    simpa only [sq, Module.End.mul_apply, Module.End.one_apply] using
      binaryFormRep_parity_involutive (R := K) (w := w) x
  have hτ : τ ^ 2 = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hε x
  have hker : LinearMap.ker (1 + τ) =
      (oddPeriodPolynomials K w).comap (periodPolynomials K w).subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.subtype_apply, mem_oddPeriodPolynomials_iff,
      x.2, true_and, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      have hv' : (x : V) + ε x = 0 := by
        simpa only [τ, Submodule.coe_add, LinearMap.coe_restrict_apply,
          ZeroMemClass.coe_zero] using hv
      exact eq_neg_of_add_eq_zero_right hv'
    · intro h
      apply Subtype.ext
      simp [τ, LinearMap.restrict_apply, h]
  have hdim := LinearMap.two_mul_finrank_ker_one_add_of_sq_eq_one
    (K := K) (M := periodPolynomials K w) («σ» := τ) hτ
  rw [hker, (Submodule.comapSubtypeEquivOfLe
    (by rw [oddPeriodPolynomials_def]; exact inf_le_left)).finrank_eq,
    trace_parity_periodPolynomials hw hw₀] at hdim
  have hsum := finrank_even_add_finrank_odd (K := K) (w := w)
  have heq : finrank K (periodPolynomials K w) =
      2 * finrank K (oddPeriodPolynomials K w) + 1 := by
    apply Nat.cast_injective (R := K)
    push_cast
    linear_combination -hdim
  omega

/-- The dimension of the odd period-polynomial space, computed algebraically, in a form
without truncated subtraction: `dim W_w⁻ + w/2 + 1 = ⌈w/4⌉ + ⌈w/3⌉`. -/
theorem finrank_oddPeriodPolynomials_add_eq (hw : Even w) (hw₀ : w ≠ 0) :
    finrank K (oddPeriodPolynomials K w) + w / 2 + 1 = (w + 3) / 4 + (w + 2) / 3 := by
  have hdiff := finrank_evenPeriodPolynomials_eq_finrank_odd_add_one (K := K) hw hw₀
  have hsum := finrank_even_add_finrank_odd (K := K) (w := w)
  have htotal := finrank_periodPolynomials_add_eq (K := K) hw hw₀
  obtain ⟨m, rfl⟩ := hw
  omega

/-- The dimension of the even period-polynomial space, computed algebraically, in a form
without truncated subtraction: `dim W_w⁺ + w/2 = ⌈w/4⌉ + ⌈w/3⌉`. -/
theorem finrank_evenPeriodPolynomials_add_eq (hw : Even w) (hw₀ : w ≠ 0) :
    finrank K (evenPeriodPolynomials K w) + w / 2 = (w + 3) / 4 + (w + 2) / 3 := by
  have hdiff := finrank_evenPeriodPolynomials_eq_finrank_odd_add_one (K := K) hw hw₀
  have hodd := finrank_oddPeriodPolynomials_add_eq (K := K) hw hw₀
  omega

/-- For every degree, the even period-polynomial space has the dimension of the
level-one modular-form space of weight `w + 2`. -/
theorem finrank_evenPeriodPolynomials_eq_finrank_modularForm (w : ℕ) :
    finrank ℂ (evenPeriodPolynomials ℂ w) = finrank ℂ (ModularForm 𝒮ℒ (w + 2 : ℕ)) := by
  have htotal := finrank_periodPolynomials_eq_finrank_modularForm_add_finrank_cuspForm w
  have hsum := finrank_even_add_finrank_odd (K := ℂ) (w := w)
  by_cases hw₀ : w = 0
  · subst w
    rw [periodPolynomials_zero, finrank_bot] at htotal hsum
    omega
  by_cases hw : Even w
  · have hdiff := finrank_evenPeriodPolynomials_eq_finrank_odd_add_one (K := ℂ) hw hw₀
    have : FiniteDimensional ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) :=
      .of_injective _ CuspForm.toModularFormₗ_injective
    have hMS := ModularForm.rank_eq_one_add_rank_cuspForm (k := w + 2) (by omega)
      (hw.add even_two)
    rw [← finrank_eq_rank, ← finrank_eq_rank] at hMS
    norm_cast at hMS
    omega
  · rw [periodPolynomials_eq_bot_of_odd (mul_right_injective₀ two_ne_zero)
      (Nat.not_even_iff_odd.mp hw), finrank_bot] at htotal hsum
    omega

/-- For every degree, the odd period-polynomial space has the dimension of the
level-one cusp-form space of weight `w + 2`. -/
theorem finrank_oddPeriodPolynomials_eq_finrank_cuspForm (w : ℕ) :
    finrank ℂ (oddPeriodPolynomials ℂ w) = finrank ℂ (CuspForm 𝒮ℒ (w + 2 : ℕ)) := by
  have hM := finrank_evenPeriodPolynomials_eq_finrank_modularForm w
  have hsum := finrank_even_add_finrank_odd (K := ℂ) (w := w)
  have htotal := finrank_periodPolynomials_eq_finrank_modularForm_add_finrank_cuspForm w
  omega

end TauCeti
