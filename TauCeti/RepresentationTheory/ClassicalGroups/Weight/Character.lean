/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Weight.Decomposition
public import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.DirectSum.LinearMap

/-!
# Weight multiplicities from torus characters

For a finite-dimensional representation whose integer weight spaces span the carrier, its
character on the diagonal torus is the sum of the weight characters with their multiplicities.
Consequently, if that character is the evaluation of a polynomial, its coefficients are the
dimensions of the corresponding weight spaces. This identifies combinatorial character
coefficients with representation-theoretic multiplicities.

The trace calculation uses Mathlib's `LinearMap.trace_eq_sum_trace_restrict'`.
Coefficient recovery uses Artin's independence of torus characters, through
`TauCeti.linearIndependent_weightCharHom`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 15.
-/

public section

open TauCeti

namespace Representation

universe u v

variable {K : Type u} [Field K] [Infinite K] {n : ℕ}
  {W : Type v} [AddCommGroup W] [Module K W] [Module.Finite K W]

/-- The torus character is the sum of the weight characters with their multiplicities,
provided the integer weight spaces span the representation. -/
theorem character_diagGL_eq_sum_finrank_weightSpace
    (ρ : Representation K (Matrix.GeneralLinearGroup (Fin n) K) W)
    (hρ : ⨆ l : Fin n → ℤ, weightSpace ρ l = ⊤) (t : Fin n → Kˣ) :
    ρ.character (diagGL t) =
      ∑ l ∈ (finite_setOf_weightSpace_ne_bot weightChar_injective ρ).toFinset,
        (Module.finrank K (weightSpace ρ l) : K) * weightCharHom K l t := by
  classical
  have hmaps (l : Fin n → ℤ) :
      Set.MapsTo (ρ (diagGL t)) (weightSpace ρ l) (weightSpace ρ l) := by
    intro w hw
    rw [apply_of_mem_weightSpace hw]
    exact Submodule.smul_mem _ _ hw
  have hrestrict (l : Fin n → ℤ) :
      (ρ (diagGL t)).restrict (fun w hw => hmaps l hw) =
        weightCharHom K l t • LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    rw [LinearMap.coe_restrict_apply]
    simpa only [LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.coe_smul, weightCharHom_apply] using apply_of_mem_weightSpace w.property t
  rw [Representation.character, LinearMap.trace_eq_sum_trace_restrict'
    (isInternal_weightSpace_of_iSup_eq_top weightChar_injective hρ)
      (finite_setOf_weightSpace_ne_bot weightChar_injective ρ) hmaps]
  simp only [hrestrict, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

/-- If a torus character is represented by a polynomial, the coefficient of each monomial
is the dimension of its integer weight space, cast into the coefficient field.
In characteristic zero this recovers the dimension as a natural number. -/
theorem coeff_eq_finrank_weightSpace_of_character_diagGL
    (ρ : Representation K (Matrix.GeneralLinearGroup (Fin n) K) W)
    (hρ : ⨆ l : Fin n → ℤ, weightSpace ρ l = ⊤) (P : MvPolynomial (Fin n) K)
    (hP : ∀ t : Fin n → Kˣ, ρ.character (diagGL t) =
      MvPolynomial.eval (fun i => (t i : K)) P) (d : Fin n →₀ ℕ) :
    P.coeff d = (Module.finrank K (weightSpace ρ (fun i => (d i : ℤ))) : K) := by
  classical
  let e : (Fin n →₀ ℕ) → (Fin n → ℤ) := fun d i => (d i : ℤ)
  have he : Function.Injective e := by
    intro d d' h
    ext i
    exact Nat.cast_injective (congrFun h i)
  have hs : Function.support (fun l => (Module.finrank K (weightSpace ρ l) : K)) ⊆
      {l | weightSpace ρ l ≠ ⊥} := by
    intro l hl hbot
    exact hl (by dsimp only; rw [hbot]; simp)
  let a : (Fin n → ℤ) →₀ K := Finsupp.ofSupportFinite
    (fun l => (Module.finrank K (weightSpace ρ l) : K))
    ((finite_setOf_weightSpace_ne_bot weightChar_injective ρ).subset hs)
  have hcomb : Finsupp.linearCombination K (fun l => ⇑(weightCharHom K l)) a =
      Finsupp.linearCombination K (fun l => ⇑(weightCharHom K l))
        (Finsupp.mapDomain e P.coeff) := by
    rw [Finsupp.linearCombination_apply_of_mem_supported K
      (s := (finite_setOf_weightSpace_ne_bot weightChar_injective ρ).toFinset) (by
        simpa only [Finsupp.mem_supported, a, Finsupp.ofSupportFinite_support,
          Set.Finite.coe_toFinset] using hs), Finsupp.linearCombination_mapDomain]
    ext t
    rw [Finset.sum_apply]
    simp only [a, Finsupp.ofSupportFinite_coe, Pi.smul_apply, smul_eq_mul]
    rw [← ρ.character_diagGL_eq_sum_finrank_weightSpace hρ, hP t,
      Finsupp.linearCombination_apply, Finsupp.sum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
    rw [MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    simp [e, weightCharHom_apply, weightChar_apply, torusCharacter_def]
  have ha := LinearIndependent.finsuppLinearCombination_injective
    (linearIndependent_weightCharHom (K := K) (κ := Fin n)) hcomb
  have h := congrArg (fun b : (Fin n → ℤ) →₀ K => b (e d)) ha
  simpa only [a, Finsupp.ofSupportFinite_coe, Finsupp.mapDomain_apply_of_injective he] using h.symm

end Representation
