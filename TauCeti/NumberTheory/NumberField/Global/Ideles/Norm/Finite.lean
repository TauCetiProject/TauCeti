/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Transport
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# The idele norm on finite ideles

The norm of a finite adele that is a unit agrees with the global idele norm when its
infinite components are filled with ones. This allows use of the multiplicative idele
norm and its invariance under field isomorphisms with Mathlib's finite-adele norm.
-/

public section

open NumberField IsDedekindDomain

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]

/-- The idele norm of a finite idele with trivial infinite components agrees with
`NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit`. -/
@[simp]
theorem coe_ideleNorm_ofFiniteIdele (a : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((ideleNorm (IdeleGroup.ofFiniteIdele (𝓞 K) K a) : NNReal) : ℝ) =
      ‖(a : FiniteAdeleRing (𝓞 K) K)‖ := by
  rw [NumberField.FiniteAdeleRing.norm_eq_finprod_of_unit, coe_ideleNorm]
  simp only [InfinitePlace.ideleInfiniteCoord_ofFiniteIdele, Units.val_one, map_one,
    Finset.prod_const_one, one_mul]
  exact finprod_congr fun v ↦ by rw [v.ideleFiniteCoord_ofFiniteIdele]; rfl

/-- The norm of a finite idele is unchanged by transport along a number field isomorphism. -/
@[simp]
theorem norm_finiteAdeleEquiv (e : K ≃+* L) (a : FiniteAdeleRing (𝓞 K) K) :
    ‖finiteAdeleEquiv K L e a‖ = ‖a‖ := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    let b := Units.map (finiteAdeleEquiv K L e).toMonoidHom u
    have h : IdeleGroup.ofFiniteIdele (𝓞 L) L b =
        Units.map (adeleEquiv K L e).toMonoidHom (IdeleGroup.ofFiniteIdele (𝓞 K) K u) := by
      apply Units.ext
      rw [Units.coe_map, IdeleGroup.coe_ofFiniteIdele, IdeleGroup.coe_ofFiniteIdele]
      apply Prod.ext <;> simp [b, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    have hb : (b : FiniteAdeleRing (𝓞 L) L) = finiteAdeleEquiv K L e u := rfl
    rw [← hb, ← coe_ideleNorm_ofFiniteIdele, h]
    simp
  · have hb : ¬IsUnit (finiteAdeleEquiv K L e a) := fun h ↦ ha <| by
      simpa using h.map (finiteAdeleEquiv K L e).symm
    rw [NumberField.FiniteAdeleRing.norm_eq_zero_of_not_isUnit ha,
      NumberField.FiniteAdeleRing.norm_eq_zero_of_not_isUnit hb]

end TauCeti.GlobalNumberFields

namespace NumberField.FiniteAdeleRing

section

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The finite-adele norm multiplies. Both sides vanish if either factor is a nonunit. -/
@[simp]
theorem norm_mul (a b : IsDedekindDomain.FiniteAdeleRing R K) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  by_cases h : IsUnit (a * b)
  · obtain ⟨u, rfl⟩ := isUnit_of_mul_isUnit_left h
    obtain ⟨v, rfl⟩ := isUnit_of_mul_isUnit_right h
    rw [← Units.val_mul, norm_eq_finprod_of_unit, norm_eq_finprod_of_unit u,
      norm_eq_finprod_of_unit v, ← finprod_mul_distrib (hasFiniteMulSupport_norm u)
        (hasFiniteMulSupport_norm v)]
    exact finprod_congr fun _ ↦ _root_.norm_mul _ _
  · rw [norm_eq_zero_of_not_isUnit h]
    rcases not_and_or.mp (fun hu : IsUnit a ∧ IsUnit b ↦ h (hu.1.mul hu.2)) with ha | hb
    · rw [norm_eq_zero_of_not_isUnit ha, zero_mul]
    · rw [norm_eq_zero_of_not_isUnit hb, mul_zero]

/-- An everywhere-integral finite idele unit has norm one. -/
theorem norm_eq_one_of_mem_integralUnits {a : (IsDedekindDomain.FiniteAdeleRing R K)ˣ}
    (ha : a ∈ IsDedekindDomain.FiniteAdeleRing.integralUnits R K) :
    ‖(a : IsDedekindDomain.FiniteAdeleRing R K)‖ = 1 := by
  rw [norm_eq_finprod_of_unit]
  exact finprod_eq_one_of_forall_eq_one fun w ↦ by
    rw [FinitePlace.norm_def, IsDedekindDomain.FiniteAdeleRing.mem_integralUnits_iff.mp ha w,
      map_one, NNReal.coe_one]

end

open TauCeti.GlobalNumberFields IsDedekindDomain.FiniteAdeleRing

variable {K : Type*} [Field K] [NumberField K]

/-- If the product of `a`, a conjugate of `a`, and the diagonal finite idele of `x` is
an integral unit, the square of the modulus of `a` is the absolute field norm of `x`.
The transport may be along any field automorphism, not only complex conjugation. -/
theorem norm_sq_eq_abs_norm_of_mul_map_mem_integralUnits (σ : K ≃+* K)
    (a : (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)ˣ) (x : Kˣ)
    (h : a * Units.map (finiteAdeleEquiv K K σ).toMonoidHom a * unitEmbedding (𝓞 K) K x ∈
      integralUnits (𝓞 K) K) :
    ‖(a : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)‖ ^ 2 = |(Algebra.norm ℚ (x : K) : ℝ)| := by
  have hn := norm_eq_one_of_mem_integralUnits h
  have hσ : (↑(Units.map (finiteAdeleEquiv K K σ).toMonoidHom a) :
      IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) = finiteAdeleEquiv K K σ a := rfl
  simp only [Units.val_mul, hσ, norm_mul, norm_finiteAdeleEquiv,
    unitEmbedding_norm_eq_inv_abs_norm, Rat.cast_inv, Rat.cast_abs, ← sq, ← div_eq_mul_inv] at hn
  have hnorm : (Algebra.norm ℚ (x : K) : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_eq_zero_iff (R := ℚ)).not.mpr x.ne_zero
  simpa only [one_mul] using (div_eq_iff (abs_ne_zero.mpr hnorm)).mp hn

end NumberField.FiniteAdeleRing
