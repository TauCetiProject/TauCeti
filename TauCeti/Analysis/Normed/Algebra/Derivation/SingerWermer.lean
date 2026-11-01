/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Character
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Normed.Algebra.Derivation.Exponential
import TauCeti.Analysis.Normed.Algebra.SeparatingIdeal.Derivation

/-!
# The Singer–Wermer theorem for bounded derivations

A bounded derivation of a commutative complex Banach algebra maps it into its Jacobson radical.
In particular a commutative semisimple complex Banach algebra has no nonzero bounded derivation,
and, by the Johnson–Sinclair automatic continuity theorem, no nonzero derivation at all.

The proof is the character and Liouville argument. Let `D` be a bounded derivation of a complex
Banach algebra `A`, which need not be commutative or unital, and let `φ` be a character of `A`.
For every `z : ℂ` the operator `exp (z • D)` is an algebra endomorphism of `A`, so
`φ ∘ exp (z • D)` is again a character, and characters are contractive. Thus the entire function
`z ↦ φ (exp (z • D) x)` is bounded by `‖x‖`, hence constant by Liouville's theorem, and its
derivative `φ (D x)` at `0` vanishes. When `A` is commutative, an element killed by every
character lies in the Jacobson radical.

## Main results

* `ContinuousLinearMap.map_apply_eq_zero_of_derivation`: every character of a complex Banach
  algebra kills the range of a bounded derivation.
* `ContinuousLinearMap.apply_mem_nonUnitalJacobson_of_derivation`: the Singer–Wermer theorem
  for bounded derivations of a commutative complex Banach algebra, possibly without unit.
* `ContinuousLinearMap.apply_mem_jacobson_of_derivation`: the Singer–Wermer theorem for bounded
  derivations of a commutative unital complex Banach algebra.
* `LinearMap.eq_zero_of_derivation_of_jacobson_eq_bot`: a commutative semisimple unital complex
  Banach algebra has no nonzero derivation, bounded or not.

## References

* I. M. Singer and J. Wermer, *Derivations on commutative normed algebras*, Math. Ann. 129
  (1955), 260–264.
* B. E. Johnson and A. M. Sinclair, *Continuity of derivations and a problem of Kaplansky*,
  Amer. J. Math. 90 (1968), 1067–1073, for the automatic continuity used in the last result.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.7, for the Singer–Wermer theorem
  and the automorphisms `exp (z • D)`.
-/

public section

open NormedSpace

namespace ContinuousLinearMap

section Character

variable {A F : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [CompleteSpace A] [FunLike F A ℂ] [NonUnitalAlgHomClass F ℂ A ℂ]

/-- **Characters kill the range of a bounded derivation.** If `D` is a bounded linear map on a
complex Banach algebra satisfying the Leibniz rule `D (x * y) = x * D y + D x * y`, then
`φ (D x) = 0` for every character `φ`, unital or not. The algebra need not be commutative. -/
theorem map_apply_eq_zero_of_derivation (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (φ : F) (x : A) : φ (D x) = 0 := by
  -- For each `z`, `φ ∘ exp (z • D)` is a character, because `z • D` is again a derivation.
  have hzD (z : ℂ) (x y : A) : (z • D) (x * y) = x * (z • D) y + (z • D) x * y := by
    simp [hD, smul_add, mul_smul_comm, smul_mul_assoc]
  let ψ (z : ℂ) : A →ₙₐ[ℂ] ℂ :=
    { toFun y := φ (exp (z • D) y)
      map_smul' := by simp
      map_zero' := by simp
      map_add' := by simp
      map_mul' := by simp [exp_apply_mul_of_derivation _ (hzD z)] }
  -- The entire function `f z = φ (exp (z • D) x)` has derivative `φ (exp (z • D) (D x))`.
  let φL : A →L[ℂ] ℂ :=
    { toFun := φ, map_add' := map_add φ, map_smul' := map_smul φ, cont := map_continuous φ }
  let f (z : ℂ) : ℂ := φL (exp (z • D) x)
  have hf (z : ℂ) : HasDerivAt f (φL (exp (z • D) (D x))) z := by
    simpa [f, Function.comp_def, mul_apply_eq_comp] using φL.hasFDerivAt.comp_hasDerivAt z
      ((hasDerivAt_exp_smul_const D z).clm_apply (hasDerivAt_const z x))
  -- Characters are contractive, so `f` is bounded by `‖x‖`; by Liouville it is constant.
  have hb : Bornology.IsBounded (Set.range f) := by
    refine isBounded_iff_forall_norm_le.2 ⟨‖x‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    simpa [ψ, φL, f] using NonUnitalAlgHom.norm_apply_le_self (ψ z) x
  have hconst : f = fun _ ↦ f 0 :=
    funext fun z ↦ Differentiable.apply_eq_apply_of_bounded (fun w ↦ (hf w).differentiableAt) hb z 0
  -- Hence its derivative `φ (D x)` at `0` vanishes.
  have h0 := (hf 0).deriv
  rw [hconst, deriv_const] at h0
  simpa [φL] using h0.symm

end Character

/-- **Singer–Wermer theorem for bounded derivations.** A bounded derivation of a commutative
complex Banach algebra, possibly without unit, takes values in its Jacobson radical. -/
theorem apply_mem_nonUnitalJacobson_of_derivation {A : Type*} [NonUnitalNormedCommRing A]
    [NormedSpace ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [CompleteSpace A]
    (D : A →L[ℂ] A) (hD : ∀ x y, D (x * y) = x * D y + D x * y) (x : A) :
    D x ∈ TauCeti.nonUnitalJacobson ℂ A :=
  TauCeti.mem_nonUnitalJacobson_iff_forall_nonUnitalAlgHom_apply_eq_zero.2 fun φ ↦
    D.map_apply_eq_zero_of_derivation hD φ x

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Singer–Wermer theorem for bounded derivations, unital form.** A bounded derivation of a
commutative unital complex Banach algebra takes values in its Jacobson radical. -/
theorem apply_mem_jacobson_of_derivation (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (x : A) : D x ∈ Ring.jacobson A :=
  TauCeti.Ring.mem_jacobson_iff_forall_algHom_apply_eq_zero.2 fun φ ↦
    D.map_apply_eq_zero_of_derivation hD φ x

end ContinuousLinearMap

namespace LinearMap

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **A commutative semisimple Banach algebra has no nonzero derivation.** Every linear map
`D : A → A` satisfying the Leibniz rule on a commutative unital complex Banach algebra with zero
Jacobson radical vanishes. No continuity is assumed: `D` is continuous by the Johnson–Sinclair
theorem, and its values lie in the radical by the Singer–Wermer theorem. -/
theorem eq_zero_of_derivation_of_jacobson_eq_bot (D : A →ₗ[ℂ] A)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (hA : Ring.jacobson A = ⊥) : D = 0 := by
  ext x
  have hx := ContinuousLinearMap.apply_mem_jacobson_of_derivation
    ⟨D, D.continuous_of_derivation_of_jacobson_eq_bot hD hA⟩ hD x
  rwa [hA, Ideal.mem_bot] at hx

end LinearMap
