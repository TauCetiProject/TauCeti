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
(`TauCeti.exists_coe_linearMap_apply_eq_mul`). An isometry `O(D) ≃ O(D')` is thus `x ↦ f x` for
some `f ∈ Kˣ`; comparing the modules gives the finite parts and comparing the norms gives the
archimedean coefficients of `D = D' + (f)`
(`TauCeti.ArakelovDivisor.add_principal_eq_of_isometryEquiv`).

## Main results

* `TauCeti.exists_coe_linearMap_apply_eq_mul`: a linear map between submodules of the fraction
  field of a domain is multiplication by an element of the field.
* `TauCeti.ArakelovDivisor.add_principal_eq_of_isometryEquiv`: an isometry `O(D) ≃ O(D')` is
  multiplication by some `f`, and then `D' + (f) = D`.
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

/-- **A linear map between submodules of a fraction field is a multiplication.** If `K` is the
fraction field of a domain `R` and `I, J` are `R`-submodules of `K`, every `R`-linear map
`I → J` is `x ↦ f x` for some `f ∈ K`. -/
theorem exists_coe_linearMap_apply_eq_mul {R K : Type*} [CommRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] {I J : Submodule R K} (φ : I →ₗ[R] J) :
    ∃ f : K, ∀ x : I, (φ x : K) = f * x := by
  have : IsDomain R := (IsFractionRing.injective R K).isDomain (algebraMap R K)
  by_cases hI : ∀ x : I, (x : K) = 0
  · refine ⟨0, fun x ↦ ?_⟩
    rw [show x = 0 from Subtype.ext (hI x), map_zero, Submodule.coe_zero, zero_mul]
  push Not at hI
  obtain ⟨x₀, hx₀⟩ := hI
  refine ⟨φ x₀ / x₀, fun x ↦ ?_⟩
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj R⁰ ((x : K) / x₀)
  have hs : algebraMap R K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property
  have hrs' : (x : K) * algebraMap R K s = algebraMap R K r * x₀ := by
    rw [← hrs]
    field_simp
  have key : (s : R) • x = r • x₀ :=
    Subtype.ext (by simpa [Algebra.smul_def, mul_comm] using hrs')
  have hφ := congrArg (fun y : J ↦ (y : K)) (congrArg φ key)
  simp only [map_smul, Submodule.coe_smul, Algebra.smul_def] at hφ
  field_simp
  apply mul_left_cancel₀ hs
  linear_combination (x₀ : K) * hφ - (φ x₀ : K) * hrs'

namespace ArakelovDivisor

variable {K : Type*} [Field K] [NumberField K]

/-- **An isometry of hermitian lines of Arakelov divisors is a multiplication.** If
`O(D) ≃ O(D')` is an isometry, there is `f ∈ Kˣ` such that the isometry is `x ↦ f x` and
`D' + (f) = D`. -/
theorem add_principal_eq_of_isometryEquiv {D D' : ArakelovDivisor K}
    (e : HermitianMetric.IsometryEquiv D.hermitianMetric D'.hermitianMetric) :
    ∃ f : Kˣ, (∀ x, (e x : K) = f * x) ∧ D' + principal K (Additive.ofMul f) = D := by
  set I : FractionalIdeal (𝓞 K)⁰ K := ((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal (𝓞 K)⁰ K)
  set J : FractionalIdeal (𝓞 K)⁰ K := ((D'.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal (𝓞 K)⁰ K) with hJdef
  obtain ⟨f, hf⟩ := exists_coe_linearMap_apply_eq_mul (e.toLinearEquiv.toLinearMap)
  replace hf : ∀ x, (e x : K) = f * x := hf
  obtain ⟨x₀, hx₀I, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((FractionalIdeal.coeToSubmodule_ne_bot).mpr (Units.ne_zero (D.finitePart⁻¹)))
  set x₀' : I := ⟨x₀, hx₀I⟩
  have hex₀ : (e x₀' : K) ≠ 0 := fun h ↦
    hx₀ (congrArg Subtype.val (e.toLinearEquiv.map_eq_zero_iff.mp (Subtype.ext h)))
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hex₀ (by simpa using hf x₀')
  refine ⟨Units.mk0 f hf0, hf, ?_⟩
  -- The modules: `J = f I`.
  have hJ : J = spanSingleton _ f * I := by
    ext y
    rw [mem_singleton_mul]
    constructor
    · intro hy
      refine ⟨_, (e.symm ⟨y, hy⟩).property, ?_⟩
      rw [← hf]
      exact (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)).symm
    · rintro ⟨x, hx, rfl⟩
      rw [← hf ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
  ext1
  · rw [← inv_inj]
    apply Units.ext
    rw [coe_finitePart_add_principal_inv, ← hJdef, hJ, ← mul_assoc, ← map_mul, Units.val_mk0,
      inv_mul_cancel₀ hf0, map_one, one_mul]
  · ext v
    have hm : (0 : ℝ) < v.mult := Nat.cast_pos.mpr mult_pos
    have hv₀ : 0 < v x₀ := pos_iff.mpr hx₀
    have hvf : 0 < v f := pos_iff.mpr hf0
    have hnorm := e.placeNorm_map v x₀'
    rw [placeNorm_hermitianMetric, placeNorm_hermitianMetric, hf, map_mul] at hnorm
    have hlog := congrArg Real.log hnorm
    rw [Real.log_mul (Real.exp_pos _).ne' (mul_pos hvf hv₀).ne', Real.log_mul hvf.ne' hv₀.ne',
      Real.log_mul (Real.exp_pos _).ne' hv₀.ne', Real.log_exp, Real.log_exp] at hlog
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
    obtain ⟨f, -, hf⟩ := add_principal_eq_of_isometryEquiv e
    exact (mk_eq_mk_iff.mpr ⟨_, hf⟩).symm

end ArakelovPicardGroup

end TauCeti
