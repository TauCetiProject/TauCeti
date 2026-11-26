/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.HermitianLine

/-!
# Isometric hermitian lines of Arakelov divisors

The hermitian lines `O(D)` and `O(D')` of two Arakelov divisors are isometric exactly when `D` and
`D'` have the same class in the compactified Picard group
(`TauCeti.ArakelovPicardGroup.mk_eq_mk_iff_nonempty_isometryEquiv`). So `D ↦ O(D)` induces an
injection of `Div^(𝓞 K) / {principal}` into the isometry classes of hermitian lines, compatible
with the degree (`TauCeti.ArakelovDivisor.sectionDegree_hermitianMetric`).

One direction is the isometry `O(D + (f)) ≃ O(D)` of
`TauCeti.ArakelovDivisor.isometryEquivAddPrincipal`. For the other, an `𝓞 K`-linear map between
two submodules of `K` is multiplication by an element of `K`
(`LinearMap.exists_coe_apply_eq_mul`). An isometry `O(D) ≃ O(D')` is thus `x ↦ f x` for
some `f ∈ Kˣ`; comparing the modules gives the finite parts and comparing the norms gives the
archimedean coefficients of `D = D' + (f)`
(`TauCeti.ArakelovDivisor.exists_coe_apply_eq_mul_and_add_principal_eq_of_isometryEquiv`).

## Main results

* `TauCeti.ArakelovDivisor.exists_coe_apply_eq_mul_and_add_principal_eq_of_isometryEquiv`: an
  isometry `O(D) ≃ O(D')` is multiplication by some `f`, and then `D' + (f) = D`.
* `TauCeti.ArakelovPicardGroup.mk_eq_mk_iff_nonempty_isometryEquiv`: `O(D)` and `O(D')` are
  isometric iff `D` and `D'` have the same class.

## References

* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127 (1985), §1.1–1.2,
  Proposition 1.1 and Corollaire.
-/

public section

open NumberField NumberField.InfinitePlace FractionalIdeal
open scoped nonZeroDivisors

namespace TauCeti

namespace ArakelovDivisor

variable {K : Type*} [Field K] [NumberField K]

/-- **An isometry of hermitian lines of Arakelov divisors is a multiplication.** If
`O(D) ≃ O(D')` is an isometry, there is `f ∈ Kˣ` such that the isometry is `x ↦ f x` and
`D' + (f) = D`. -/
theorem exists_coe_apply_eq_mul_and_add_principal_eq_of_isometryEquiv
    {D D' : ArakelovDivisor K}
    (e : HermitianMetric.IsometryEquiv D.hermitianMetric D'.hermitianMetric) :
    ∃ f : Kˣ, (∀ x, (e x : K) = f * x) ∧ D' + principal K (Additive.ofMul f) = D := by
  set I : FractionalIdeal (𝓞 K)⁰ K := ((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal (𝓞 K)⁰ K)
  set J : FractionalIdeal (𝓞 K)⁰ K := ((D'.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal (𝓞 K)⁰ K) with hJdef
  obtain ⟨f, hf⟩ := e.toLinearEquiv.toLinearMap.exists_coe_apply_eq_mul
  -- The modules: `J = f I`.
  have hJ : J = spanSingleton _ f * I :=
    e.toLinearEquiv.toLinearMap.eq_spanSingleton_mul_of_surjective e.toLinearEquiv.surjective hf
  simp only [LinearEquiv.coe_coe, HermitianMetric.IsometryEquiv.coe_toLinearEquiv] at hf
  obtain ⟨x₀, hx₀I, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((FractionalIdeal.coeToSubmodule_ne_bot).mpr (Units.ne_zero (D.finitePart⁻¹)))
  set x₀' : I := ⟨x₀, hx₀I⟩
  have hex₀ : (e x₀' : K) ≠ 0 := fun h ↦
    hx₀ (congrArg Subtype.val ((map_eq_zero_iff e (EquivLike.injective e)).mp (Subtype.ext h)))
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hex₀ (by simpa using hf x₀')
  refine ⟨Units.mk0 f hf0, hf, ?_⟩
  ext1
  · rw [← inv_inj]
    apply Units.ext
    simp [← hJdef, hJ, hf0, I]
  · ext v
    have hm : (0 : ℝ) < v.mult := Nat.cast_pos.mpr mult_pos
    have hv₀ : 0 < v (x₀' : K) := pos_iff.mpr hx₀
    have hvf : 0 < v f := pos_iff.mpr hf0
    have hnorm := e.placeNorm_map v x₀'
    rw [placeNorm_hermitianMetric, placeNorm_hermitianMetric, hf, map_mul] at hnorm
    have hlog := congrArg Real.log hnorm
    simp only [Real.log_mul, Real.log_exp, Real.exp_ne_zero, hvf.ne', hv₀.ne', mul_ne_zero_iff,
      ne_eq, not_false_eq_true, and_self] at hlog
    rw [infinitePart_add, Pi.add_apply, infinitePart_principal, toMul_ofMul, Units.val_mk0]
    field_simp at hlog
    linear_combination (-1 : ℝ) * hlog

end ArakelovDivisor

namespace ArakelovPicardGroup

variable {K : Type*} [Field K] [NumberField K]

open ArakelovDivisor

/-- **Arakelov divisors with the same class have isometric hermitian lines, and conversely.**
The hermitian lines `O(D)` and `O(D')` are isometric exactly when `D - D'` is principal, so
`D ↦ O(D)` is injective on the compactified Picard group. -/
theorem mk_eq_mk_iff_nonempty_isometryEquiv {D D' : ArakelovDivisor K} :
    mk K D = mk K D' ↔
      Nonempty (HermitianMetric.IsometryEquiv D.hermitianMetric D'.hermitianMetric) := by
  constructor
  · intro h
    obtain ⟨f, rfl⟩ := mk_eq_mk_iff.mp h
    exact ⟨(isometryEquivAddPrincipal D f.toMul).symm⟩
  · rintro ⟨e⟩
    obtain ⟨f, -, hf⟩ := exists_coe_apply_eq_mul_and_add_principal_eq_of_isometryEquiv e
    exact (mk_eq_mk_iff.mpr ⟨_, hf⟩).symm

end ArakelovPicardGroup

end TauCeti
