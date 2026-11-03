/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.Character
public import TauCeti.Analysis.Normed.Algebra.Derivation.Exponential
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Normed.Algebra.SeparatingIdeal.Derivation

/-!
# The Singer–Wermer theorem for bounded derivations

**The Singer–Wermer theorem**: a bounded derivation `D` of a commutative complex Banach algebra
`B` maps `B` into its Jacobson radical. The algebra need not be unital. In particular a
commutative semisimple complex Banach algebra has no nonzero bounded derivations.

## Main results

* `ContinuousLinearMap.map_apply_eq_zero_of_derivation`: every character of a complex Banach
  algebra, not necessarily commutative or unital, kills the range of a bounded derivation.
* `ContinuousLinearMap.apply_mem_nonUnitalJacobson_of_derivation`: the Singer–Wermer theorem for
  a commutative complex Banach algebra, possibly without unit.
* `ContinuousLinearMap.apply_mem_jacobson_of_derivation`: the unital form.
* `ContinuousLinearMap.eq_zero_of_derivation_of_nonUnitalJacobson_eq_bot`: a bounded derivation
  of a commutative semisimple complex Banach algebra, possibly without unit, is zero.
* `LinearMap.eq_zero_of_derivation_of_jacobson_eq_bot`: combined with the Johnson–Sinclair
  automatic continuity theorem, every derivation of a commutative semisimple unital complex
  Banach algebra is zero, with no continuity assumption.

## References

* I. M. Singer and J. Wermer, *Derivations on commutative normed algebras*, Math. Ann. 129
  (1955), 260–264.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.7, the Singer–Wermer theorem.
-/

public section

open NormedSpace

namespace ContinuousLinearMap

section Character

variable {A F : Type*} [NonUnitalNormedRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [CompleteSpace A] [FunLike F A ℂ] [NonUnitalAlgHomClass F ℂ A ℂ]

/-- **Characters kill the range of a bounded derivation.** If `D` is a bounded linear map on a
complex Banach algebra satisfying the Leibniz rule `D (x * y) = x * D y + D x * y`, then
`φ (D a) = 0` for every character `φ`, unital or not. The algebra need not be commutative. -/
theorem map_apply_eq_zero_of_derivation (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (φ : F) (a : A) : φ (D a) = 0 := by
  -- For each `z`, `φ ∘ exp (z • D)` is again a character, hence contractive, so
  -- `z ↦ φ (exp (z • D) a)` is a bounded entire function. By Liouville's theorem it is constant,
  -- and its derivative `φ (D a)` at `z = 0` vanishes.
  suffices ∀ φ : A →ₙₐ[ℂ] ℂ, φ (D a) = 0 from this φ
  intro φ
  -- Each `exp (z • D)` is an algebra endomorphism, because `z • D` is again a derivation.
  let Θ (z : ℂ) : A →ₙₐ[ℂ] A :=
    { ((exp (z • D) : A →L[ℂ] A) : A →ₗ[ℂ] A) with
      map_zero' := (exp (z • D)).map_zero
      map_mul' := (z • D).exp_apply_mul_of_derivation fun x y ↦ by
        simp [hD, smul_add, mul_smul_comm, smul_mul_assoc] }
  have hΘ (z : ℂ) (x : A) : Θ z x = exp (z • D) x := (rfl)
  -- The entire function `f z = φ (exp (z • D) a)` is bounded by `‖a‖`, hence constant.
  let f : ℂ → ℂ := fun z ↦ φ (exp (z • D) a)
  have hf (z : ℂ) : HasDerivAt f (φ (exp (z • D) (D a))) z := by
    have h : HasDerivAt (fun s : ℂ ↦ exp (s • D) a) (exp (z • D) (D a)) z := by
      simpa [mul_apply_eq_comp] using
        (hasDerivAt_exp_smul_const D z).clm_apply (hasDerivAt_const z a)
    exact (⟨(φ : A →ₗ[ℂ] ℂ), map_continuous φ⟩ : A →L[ℂ] ℂ).hasFDerivAt.comp_hasDerivAt z h
  have hbdd : Bornology.IsBounded (Set.range f) := by
    refine (Metric.isBounded_closedBall (x := 0) (r := ‖a‖)).subset ?_
    rintro _ ⟨z, rfl⟩
    rw [mem_closedBall_zero_iff]
    simpa [f, hΘ] using NonUnitalAlgHom.norm_apply_le_self (φ.comp (Θ z)) a
  have hconst : f = fun _ ↦ f 0 := funext fun z ↦
    Differentiable.apply_eq_apply_of_bounded (fun z ↦ (hf z).differentiableAt) hbdd z 0
  have h0 := (hf 0).deriv
  rw [hconst, deriv_const] at h0
  simpa using h0.symm

end Character

variable {B : Type*} [NonUnitalNormedCommRing B] [NormedSpace ℂ B] [IsScalarTower ℂ B B]
  [SMulCommClass ℂ B B] [CompleteSpace B]

/-- **The Singer–Wermer theorem.** A bounded derivation `D` of a commutative complex Banach
algebra, possibly without unit, takes values in the Jacobson radical. -/
theorem apply_mem_nonUnitalJacobson_of_derivation (D : B →L[ℂ] B)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (a : B) :
    D a ∈ TauCeti.nonUnitalJacobson ℂ B :=
  -- In a commutative complex Banach algebra the elements killed by every character, possibly
  -- zero, form the radical.
  TauCeti.mem_nonUnitalJacobson_iff_forall_nonUnitalAlgHom_apply_eq_zero.2 fun φ ↦
    D.map_apply_eq_zero_of_derivation hD φ a

/-- **Commutative semisimple Banach algebras have no nonzero bounded derivations.** A bounded
derivation of a commutative complex Banach algebra, possibly without unit, with zero Jacobson
radical is zero. -/
theorem eq_zero_of_derivation_of_nonUnitalJacobson_eq_bot (D : B →L[ℂ] B)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (hB : TauCeti.nonUnitalJacobson ℂ B = ⊥) :
    D = 0 := by
  ext a
  simpa [hB] using D.apply_mem_nonUnitalJacobson_of_derivation hD a

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **The Singer–Wermer theorem**, unital form: a bounded derivation of a commutative unital
complex Banach algebra takes values in the Jacobson radical. -/
theorem apply_mem_jacobson_of_derivation (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (a : A) : D a ∈ Ring.jacobson A := by
  simpa using D.apply_mem_nonUnitalJacobson_of_derivation hD a

end ContinuousLinearMap

namespace LinearMap

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- **Commutative semisimple Banach algebras have no nonzero derivations.** A linear map
`D : A → A` on a commutative unital complex Banach algebra with zero Jacobson radical that
satisfies the Leibniz rule is zero. No continuity is assumed. -/
theorem eq_zero_of_derivation_of_jacobson_eq_bot (D : A →ₗ[ℂ] A)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (hA : Ring.jacobson A = ⊥) : D = 0 := by
  -- `D` is continuous by the Johnson–Sinclair theorem, and then zero by Singer–Wermer.
  ext a
  simpa [hA] using (ContinuousLinearMap.mk D (D.continuous_of_derivation_of_jacobson_eq_bot hD hA)
    |>.apply_mem_jacobson_of_derivation hD a)

end LinearMap
