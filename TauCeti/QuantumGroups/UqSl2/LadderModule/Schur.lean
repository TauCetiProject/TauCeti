/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.LadderModule.Basic
public import TauCeti.RingTheory.Semisimple.Schur

import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Schur scalars for signed ladder modules

At a generic parameter `q`, the signed ladder modules `L_m^ε` of `U_q(sl₂)` are simple, pairwise
non-isomorphic for distinct `(m, ε)`, and have one-dimensional endomorphism algebras over `ℂ`.
This file packages Schur's lemma into a uniform scalar extraction `LadderModule.schurScalar` on
arbitrary `UqSl2 q`-linear maps `L_m^ε →ₗ[UqSl2 q] L_n^δ` as the `v₀`-coordinate of `f v₀`.

Every intertwiner `f : L_m^ε →ₗ[UqSl2 q] L_n^δ` satisfies
`f (vec q m ε j) = schurScalar f • vec q n δ j` for every `j : ℤ` (`apply_vec_eq_schurScalar_smul`),
so `schurScalar` is multiplicative under composition (`schurScalar_comp`) and agrees on
endomorphisms with `TauCeti.endAlgEquivSelfOfIsSimpleModule`
(`endAlgEquivSelfOfIsSimpleModule_eq_schurScalar`).

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Section VI.3.
-/

public noncomputable section

namespace TauCeti.UqSl2.LadderModule

variable {q : ℂ} [Fact (q ≠ 0)] {m n : ℕ} {ε δ : ℤˣ}

/-- At a generic parameter, any `UqSl2 q`-linear map between signed ladder modules with different
highest weights or signs vanishes. -/
theorem hom_eq_zero_of_ne (hq : IsGenericQuantumParameter q) (h : m ≠ n ∨ ε ≠ δ)
    (f : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) : f = 0 := by
  have := isSimpleModule (m := m) (ε := ε) hq
  have := isSimpleModule (m := n) (ε := δ) hq
  exact hom_eq_zero_of_isEmpty_linearEquiv (isEmpty_linearEquiv_of_ne hq h) f

/-- The scalar attached to a `UqSl2 q`-linear map `L_m^ε → L_n^δ`, extracted as the `v₀`
coordinate of the image of `v₀`. -/
def schurScalar (f : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) : ℂ :=
  (basis q n δ).repr (f (vec q m ε 0)) 0

/-- The zero intertwiner has Schur scalar zero. -/
@[simp] theorem schurScalar_zero :
    schurScalar (0 : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) = 0 := by
  simp [schurScalar]

/-- `schurScalar` is additive. -/
@[simp] theorem schurScalar_add (f g : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    schurScalar (f + g) = schurScalar f + schurScalar g := by simp [schurScalar]

/-- `schurScalar` commutes with negation. -/
@[simp] theorem schurScalar_neg (f : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    schurScalar (-f) = -schurScalar f := by simp [schurScalar]

/-- `schurScalar` commutes with subtraction. -/
@[simp] theorem schurScalar_sub (f g : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    schurScalar (f - g) = schurScalar f - schurScalar g := by simp [schurScalar]

/-- `schurScalar` is `ℂ`-linear. -/
@[simp] theorem schurScalar_smul (c : ℂ) (f : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    schurScalar (c • f) = c * schurScalar f := by simp [schurScalar]

/-- `schurScalar` commutes with finite sums. -/
theorem schurScalar_sum {ι : Type*} (s : Finset ι)
    (f : ι → LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    schurScalar (∑ i ∈ s, f i) = ∑ i ∈ s, schurScalar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ ha ih => simp [Finset.sum_insert ha, ih]

/-- If `f` sends `v₀` to `c • v₀`, then `schurScalar f = c`. -/
theorem schurScalar_eq_of_apply_vec_zero
    {f : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ} {c : ℂ}
    (hf : f (vec q m ε 0) = c • vec q n δ 0) : schurScalar f = c := by
  simp [schurScalar, hf]

/-- The identity endomorphism has Schur scalar `1`. -/
@[simp] theorem schurScalar_id :
    schurScalar (LinearMap.id : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q m ε) = 1 :=
  schurScalar_eq_of_apply_vec_zero (by simp)

/-- On a simple signed ladder module, `TauCeti.endAlgEquivSelfOfIsSimpleModule` evaluates to
`schurScalar`. -/
@[simp] theorem endAlgEquivSelfOfIsSimpleModule_eq_schurScalar
    [IsSimpleModule (UqSl2 q) (LadderModule q m ε)]
    (f : Module.End (UqSl2 q) (LadderModule q m ε)) :
    endAlgEquivSelfOfIsSimpleModule (k := ℂ) f = schurScalar f :=
  (schurScalar_eq_of_apply_vec_zero
    ((endAlgEquivSelfOfIsSimpleModule_smul f (vec q m ε 0)).symm)).symm

/-- At a generic parameter, every `UqSl2 q`-endomorphism of `L_m^ε` acts as scalar multiplication
by its `schurScalar`. -/
theorem apply_eq_schurScalar_smul (hq : IsGenericQuantumParameter q)
    (f : Module.End (UqSl2 q) (LadderModule q m ε)) (x : LadderModule q m ε) :
    f x = schurScalar f • x := by
  have := isSimpleModule (m := m) (ε := ε) hq
  rw [← endAlgEquivSelfOfIsSimpleModule_eq_schurScalar, endAlgEquivSelfOfIsSimpleModule_smul]

/-- At a generic parameter, `schurScalar` vanishes between inequivalent signed ladder modules. -/
theorem schurScalar_eq_zero_of_ne (hq : IsGenericQuantumParameter q) (h : m ≠ n ∨ ε ≠ δ)
    (f : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) : schurScalar f = 0 := by
  rw [hom_eq_zero_of_ne hq h f, schurScalar_zero]

/-- At a generic parameter, any `UqSl2 q`-linear map `L_m^ε → L_n^δ` sends every ladder vector
`v_j` to `schurScalar f • v_j`. -/
theorem apply_vec_eq_schurScalar_smul (hq : IsGenericQuantumParameter q)
    (f : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) (j : ℤ) :
    f (vec q m ε j) = schurScalar f • vec q n δ j := by
  by_cases hmn : m = n ∧ ε = δ
  · rcases hmn with ⟨rfl, rfl⟩; exact apply_eq_schurScalar_smul hq f (vec q m ε j)
  · rw [hom_eq_zero_of_ne hq (by tauto) f, schurScalar_zero, LinearMap.zero_apply, zero_smul]

/-- `schurScalar` is multiplicative under composition of `UqSl2 q`-linear maps between arbitrary
signed ladder modules. -/
@[simp] theorem schurScalar_comp (hq : IsGenericQuantumParameter q) {p : ℕ} {ζ : ℤˣ}
    (g : LadderModule q n δ →ₗ[UqSl2 q] LadderModule q p ζ)
    (f : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q n δ) :
    schurScalar (g.comp f) = schurScalar g * schurScalar f := by
  refine schurScalar_eq_of_apply_vec_zero ?_
  rw [LinearMap.comp_apply, apply_vec_eq_schurScalar_smul hq f 0, LinearMap.map_smul_of_tower,
    apply_vec_eq_schurScalar_smul hq g 0, smul_smul, mul_comm]

end TauCeti.UqSl2.LadderModule
