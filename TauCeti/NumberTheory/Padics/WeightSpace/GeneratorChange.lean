/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.WeightSpace.Basic

/-!
# Changing the principal generator of weight coordinates

For a unit `u : ℤ_pˣ`, the generator `γ ^ u = exp(q u)` is the image of `u` under
`unitsPrincipalLogEquiv.symm`. Evaluating a weight at this generator changes its coordinate by
`T ↦ (1 + T) ^ u - 1`. Here the power is Mathlib's actual continuous binomial character
`PadicInt.addChar_of_value_at_one`, whose Mahler series has coefficients `T ^ n`.

`weightCoordChangeEquiv` packages this change on topologically nilpotent elements of an arbitrary
complete ultrametric normed `ℤ_p`-algebra with contractive scalar action. Its inverse uses `u⁻¹`;
commutativity and a multiplicative norm are not required. `WeightSpace.coordAt` is the coordinate
of an actual weight at the new generator.
`WeightSpace.coordAt_eq_weightCoordChangeEquiv` identifies the two.

The construction transports precomposition of additive characters through Mathlib's
`PadicInt.continuousAddCharEquiv`, rather than defining another binomial power operation.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §§3–4.
-/

public section

open Filter Topology

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]
variable (R : Type*) [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R] [CompleteSpace R]

/-- Changing the principal generator by `γ ↦ γ ^ u` changes a topologically nilpotent
coordinate by `T ↦ (1 + T) ^ u - 1`. The inverse changes the generator by `u⁻¹`. -/
noncomputable def weightCoordChangeEquiv (u : ℤ_[p]ˣ) :
    {t : R // Tendsto (t ^ ·) atTop (𝓝 0)} ≃ {t : R // Tendsto (t ^ ·) atTop (𝓝 0)} :=
  let e : {κ : AddChar ℤ_[p] R // Continuous κ} ≃
      {κ : AddChar ℤ_[p] R // Continuous κ} :=
    { toFun κ := ⟨κ.1.compAddMonoidHom (AddMonoidHom.mulLeft (u : ℤ_[p])),
        κ.2.comp (continuous_const.mul continuous_id)⟩
      invFun κ := ⟨κ.1.compAddMonoidHom (AddMonoidHom.mulLeft (↑u⁻¹ : ℤ_[p])),
        κ.2.comp (continuous_const.mul continuous_id)⟩
      left_inv κ := by ext s; simp
      right_inv κ := by ext s; simp }
  (PadicInt.continuousAddCharEquiv p R).symm.trans
    (e.trans (PadicInt.continuousAddCharEquiv p R))

variable {p R}

/-- The generator change is evaluation of the native binomial character at `u`, minus one. -/
theorem coe_weightCoordChangeEquiv_apply (u : ℤ_[p]ˣ)
    (t : {t : R // Tendsto (t ^ ·) atTop (𝓝 0)}) :
    (weightCoordChangeEquiv p R u t : R) =
      PadicInt.addChar_of_value_at_one t.1 t.2 (u : ℤ_[p]) - 1 := by
  rcases t with ⟨t, ht⟩
  simp [weightCoordChangeEquiv, PadicInt.continuousAddCharEquiv_apply]

/-- The binomial character in the new coordinate is the original one evaluated at `u * s`. -/
theorem addChar_of_value_at_one_weightCoordChangeEquiv (u : ℤ_[p]ˣ)
    (t : {t : R // Tendsto (t ^ ·) atTop (𝓝 0)}) (s : ℤ_[p]) :
    PadicInt.addChar_of_value_at_one (weightCoordChangeEquiv p R u t).1
      (weightCoordChangeEquiv p R u t).2 s =
        PadicInt.addChar_of_value_at_one t.1 t.2 ((u : ℤ_[p]) * s) := by
  have h := PadicInt.eq_addChar_of_value_at_one (weightCoordChangeEquiv p R u t).2
    ((PadicInt.continuous_addChar_of_value_at_one t.2).comp
      (continuous_const.mul continuous_id))
    (κ := (PadicInt.addChar_of_value_at_one t.1 t.2).compAddMonoidHom
      (AddMonoidHom.mulLeft (u : ℤ_[p]))) (by
        simp [coe_weightCoordChangeEquiv_apply])
  exact congrArg (fun κ : AddChar ℤ_[p] R ↦ κ s) h.symm

/-- The coordinate substitution is the convergent binomial (Mahler) series, minus one. -/
theorem weightCoordChangeEquiv_eq_tsum (u : ℤ_[p]ˣ)
    (t : {t : R // Tendsto (t ^ ·) atTop (𝓝 0)}) :
    (weightCoordChangeEquiv p R u t : R) =
      (∑' n : ℕ, mahler n (u : ℤ_[p]) • (t : R) ^ n) - 1 := by
  rw [coe_weightCoordChangeEquiv_apply, PadicInt.coe_addChar_of_value_at_one,
    PadicInt.mahlerSeries_apply t.2]

@[simp]
theorem weightCoordChangeEquiv_one : weightCoordChangeEquiv p R 1 = Equiv.refl _ := by
  ext t
  simp [coe_weightCoordChangeEquiv_apply]

/-- Successive changes of generator multiply their `p`-adic exponents. -/
theorem weightCoordChangeEquiv_mul_apply (u v : ℤ_[p]ˣ)
    (t : {t : R // Tendsto (t ^ ·) atTop (𝓝 0)}) :
    weightCoordChangeEquiv p R (u * v) t =
      weightCoordChangeEquiv p R v (weightCoordChangeEquiv p R u t) := by
  apply Subtype.ext
  rw [coe_weightCoordChangeEquiv_apply, coe_weightCoordChangeEquiv_apply,
    addChar_of_value_at_one_weightCoordChangeEquiv]
  rw [Units.val_mul]

/-- The inverse coordinate change uses the reciprocal exponent. -/
theorem weightCoordChangeEquiv_symm (u : ℤ_[p]ˣ) :
    (weightCoordChangeEquiv p R u).symm = weightCoordChangeEquiv p R u⁻¹ := by
  ext t
  rfl

@[simp]
theorem weightCoordChangeEquiv_apply_zero (u : ℤ_[p]ˣ)
    (h0 : Tendsto ((0 : R) ^ ·) atTop (𝓝 0)) :
    weightCoordChangeEquiv p R u ⟨0, h0⟩ = ⟨0, h0⟩ := by
  have h := PadicInt.eq_addChar_of_value_at_one (p := p) h0 (κ := 0) continuous_const (by simp)
  apply Subtype.ext
  simp [coe_weightCoordChangeEquiv_apply, ← h]

namespace WeightSpace

section Ring

variable {S : Type*} [Ring S] [TopologicalSpace S]

/-- The coordinate `κ(γ ^ u) - 1` obtained from the principal generator `γ ^ u = exp(q u)`. -/
noncomputable def coordAt (κ : WeightSpace p S) (u : ℤ_[p]ˣ) : S :=
  κ ((unitsPrincipalLogEquiv p).symm (.ofAdd (u : ℤ_[p]))) - 1

/-- Evaluation at the changed generator agrees with the principal character. -/
theorem coordAt_eq_principalChar_sub_one (κ : WeightSpace p S) (u : ℤ_[p]ˣ) :
    κ.coordAt u = κ.principalChar (u : ℤ_[p]) - 1 :=
  by rw [principalChar_apply]; rfl

@[simp]
theorem coordAt_one (κ : WeightSpace p S) : κ.coordAt 1 = κ.coord := by
  rw [coordAt_eq_principalChar_sub_one, Units.val_one, principalChar_one, coord_def]

end Ring

omit [CompleteSpace R] in
/-- The coordinate at any principal generator is topologically nilpotent. -/
theorem tendsto_coordAt_pow (κ : WeightSpace p R) (u : ℤ_[p]ˣ) :
    Tendsto (κ.coordAt u ^ ·) atTop (𝓝 0) := by
  let χ := κ.principalChar.compAddMonoidHom (AddMonoidHom.mulLeft (u : ℤ_[p]))
  simpa [χ, coordAt_eq_principalChar_sub_one] using χ.tendsto_eval_one_sub_pow
    (κ.continuous_principalChar.comp (continuous_const.mul continuous_id))

/-- **Change of principal generator for a weight.** Its new coordinate is
`(1 + T_κ) ^ u - 1`, using the continuous binomial character. -/
theorem coordAt_eq_weightCoordChangeEquiv (κ : WeightSpace p R) (u : ℤ_[p]ˣ) :
    κ.coordAt u = (weightCoordChangeEquiv p R u ⟨κ.coord, κ.tendsto_coord_pow⟩ : R) := by
  rw [coordAt_eq_principalChar_sub_one, coe_weightCoordChangeEquiv_apply,
    κ.principalChar_eq_addChar_of_value_at_one]

/-- The original coordinate is recovered from the new one by the inverse binomial exponent. -/
theorem coord_eq_addChar_of_value_at_one_coordAt_inv (κ : WeightSpace p R) (u : ℤ_[p]ˣ) :
    κ.coord = PadicInt.addChar_of_value_at_one (κ.coordAt u) (κ.tendsto_coordAt_pow u)
      (↑u⁻¹ : ℤ_[p]) - 1 := by
  have h := addChar_of_value_at_one_weightCoordChangeEquiv u ⟨κ.coord, κ.tendsto_coord_pow⟩
    (↑u⁻¹ : ℤ_[p])
  simp only [Units.mul_inv, PadicInt.addChar_of_value_at_one_def] at h
  simpa only [← coordAt_eq_weightCoordChangeEquiv, add_sub_cancel_left] using
    congrArg (fun x : R ↦ x - 1) h.symm

end WeightSpace

end TauCeti
