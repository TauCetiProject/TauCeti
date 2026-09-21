/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Uniformizer coordinates on maximal-ideal graded pieces

Let `R` be a discrete valuation ring with maximal ideal `𝔪` and residue field `k`.  Fixing a
uniformizer `π` identifies `k` with the graded piece `𝔪^m / 𝔪^(m+1)` by sending the residue
of `x` to the class of `x * π ^ m`.  This file constructs that identification explicitly and
computes how it changes when the uniformizer is replaced.

If `π' = π * a` for a unit `a` of `R`, then the identification for `π'` is the identification
for `π` precomposed with multiplication by the residue of `a ^ m`.  Thus it is independent of
the uniformizer up to the additive automorphism of the residue field induced by that residue.

The explicit principal-power equivalence below follows the construction of Mathlib's
`Ideal.quotEquivPowQuotPowSucc`, retaining a specified generator in order to expose the
change-of-uniformizer formula.

## Main results

* `TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer`: the identification of the residue
  field with a maximal-ideal graded piece determined by a uniformizer.
* `TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer_change`: changing the uniformizer
  scales the residue coordinate by the corresponding residue-field unit.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The unique unit `a` such that `π * a = π'`, for two uniformizers `π` and `π'` of a discrete
valuation ring. -/
noncomputable def uniformizerChangeUnit (π π' : R) (hπ : Irreducible π)
    (hπ' : Irreducible π') : Rˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible R hπ hπ').choose

/-- The unit `uniformizerChangeUnit π π'` carries `π` to `π'`. -/
@[simp]
theorem mul_uniformizerChangeUnit (π π' : R) (hπ : Irreducible π)
    (hπ' : Irreducible π') :
    π * (uniformizerChangeUnit π π' hπ hπ' : R) = π' :=
  (IsDiscreteValuationRing.associated_of_irreducible R hπ hπ').choose_spec

/-- The change unit from a uniformizer to itself is one. -/
@[simp]
theorem uniformizerChangeUnit_self (π : R) (hπ : Irreducible π) :
    uniformizerChangeUnit π π hπ hπ = 1 := by
  apply Units.ext
  exact mul_left_cancel₀ hπ.ne_zero (by simp)

/-- Change units compose when passing through a third uniformizer. -/
theorem uniformizerChangeUnit_mul (π₁ π₂ π₃ : R) (h₁ : Irreducible π₁)
    (h₂ : Irreducible π₂) (h₃ : Irreducible π₃) :
    uniformizerChangeUnit π₁ π₂ h₁ h₂ * uniformizerChangeUnit π₂ π₃ h₂ h₃ =
      uniformizerChangeUnit π₁ π₃ h₁ h₃ := by
  apply Units.ext
  apply mul_left_cancel₀ h₁.ne_zero
  rw [Units.val_mul, ← mul_assoc, mul_uniformizerChangeUnit, mul_uniformizerChangeUnit,
    mul_uniformizerChangeUnit]

/-- Multiplication by the `m`th power of the change unit, acting on the residue field.  This is
the additive coordinate change between the degree-`m` coordinates associated to two
uniformizers. -/
noncomputable def uniformizerChangeResidueAddEquiv (π π' : R) (hπ : Irreducible π)
    (hπ' : Irreducible π') (m : ℕ) : ResidueField R ≃+ ResidueField R :=
  DistribMulAction.toAddEquiv (ResidueField R)
    (Units.map (residue R).toMonoidHom (uniformizerChangeUnit π π' hπ hπ') ^ m)

/-- The coordinate-change automorphism acts by multiplication by the residue of the change
unit to the indicated power. -/
@[simp]
theorem uniformizerChangeResidueAddEquiv_apply (π π' : R) (hπ : Irreducible π)
    (hπ' : Irreducible π') (m : ℕ) (x : ResidueField R) :
    uniformizerChangeResidueAddEquiv π π' hπ hπ' m x =
      (residue R (uniformizerChangeUnit π π' hπ hπ' : R)) ^ m * x := by
  simp [uniformizerChangeResidueAddEquiv, Units.smul_def]

private noncomputable def uniformizerPowToMaximalIdealGraded (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    R →ₗ[R] (maximalIdeal R ^ m : Ideal R) ⧸
      (maximalIdeal R • ⊤ : Submodule R (maximalIdeal R ^ m : Ideal R)) :=
  (Submodule.mkQ _).comp <|
    (LinearMap.mulRight R π ^ m).codRestrict _ fun x ↦ by
      simpa only [LinearMap.pow_mulRight, LinearMap.mulRight_apply] using
        (maximalIdeal R ^ m).mul_mem_left x (by
          rw [hπ.maximalIdeal_eq]
          exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m)

@[simp]
private theorem uniformizerPowToMaximalIdealGraded_apply (π : R)
    (hπ : Irreducible π) (m : ℕ) (x : R) :
    uniformizerPowToMaximalIdealGraded π hπ m x =
      Submodule.Quotient.mk
        (⟨x * π ^ m, by
          apply (maximalIdeal R ^ m).mul_mem_left x
          rw [hπ.maximalIdeal_eq]
          exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m⟩ :
          (maximalIdeal R ^ m : Ideal R)) := by
  simp [uniformizerPowToMaximalIdealGraded, LinearMap.pow_mulRight]
  congr 1

private theorem ker_uniformizerPowToMaximalIdealGraded (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    LinearMap.ker (uniformizerPowToMaximalIdealGraded π hπ m) = maximalIdeal R := by
  ext x
  rw [LinearMap.mem_ker, uniformizerPowToMaximalIdealGraded_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, smul_eq_mul]
  -- Strip the ideal-subtype coercion introduced by the displayed representative.
  change x * π ^ m ∈ maximalIdeal R * maximalIdeal R ^ m ↔ x ∈ maximalIdeal R
  constructor
  · intro hx
    rw [← pow_succ', hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hx
    obtain ⟨y, hy⟩ := hx
    rw [mul_comm, pow_succ, mul_assoc, mul_right_inj' (pow_ne_zero m hπ.ne_zero)] at hy
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact ⟨y, hy⟩
  · intro hx
    have hπm : π ^ m ∈ maximalIdeal R ^ m := by
      rw [hπ.maximalIdeal_eq]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m
    exact Submodule.mul_mem_mul hx hπm

private theorem uniformizerPowToMaximalIdealGraded_surjective (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    Function.Surjective (uniformizerPowToMaximalIdealGraded π hπ m) := by
  intro z
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨x, hx⟩ := x
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y, ?_⟩
  rw [uniformizerPowToMaximalIdealGraded_apply]
  congr 2
  simp only [mul_comm]

private noncomputable def residueToMaximalIdealGradedOfUniformizer (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    ResidueField R →ₗ[R] (maximalIdeal R ^ m : Ideal R) ⧸
      (maximalIdeal R • ⊤ : Submodule R (maximalIdeal R ^ m : Ideal R)) :=
  (maximalIdeal R).liftQ (uniformizerPowToMaximalIdealGraded π hπ m) <| by
    rw [ker_uniformizerPowToMaximalIdealGraded]

@[simp]
private theorem residueToMaximalIdealGradedOfUniformizer_mk (π : R)
    (hπ : Irreducible π) (m : ℕ) (x : R) :
    residueToMaximalIdealGradedOfUniformizer π hπ m (residue R x) =
      uniformizerPowToMaximalIdealGraded π hπ m x := by
  rw [residueToMaximalIdealGradedOfUniformizer]
  -- The ideal-quotient constructor is the module-quotient constructor used by `liftQ`.
  change (maximalIdeal R).liftQ (uniformizerPowToMaximalIdealGraded π hπ m) _
      (Submodule.Quotient.mk x) = _
  rw [Submodule.liftQ_apply]

private theorem residueToMaximalIdealGradedOfUniformizer_bijective (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    Function.Bijective (residueToMaximalIdealGradedOfUniformizer π hπ m) := by
  constructor
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _
      (ker_uniformizerPowToMaximalIdealGraded π hπ m).symm
  · intro z
    obtain ⟨x, rfl⟩ := uniformizerPowToMaximalIdealGraded_surjective π hπ m z
    exact ⟨Submodule.Quotient.mk x, residueToMaximalIdealGradedOfUniformizer_mk π hπ m x⟩

/-- Multiplication by a chosen uniformizer to the `m`th power identifies the residue field with
the `m`th graded piece `𝔪^m / 𝔪^(m+1)` of the maximal-ideal filtration. -/
noncomputable def residueFieldEquivMaximalIdealGradedOfUniformizer (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    ResidueField R ≃ₗ[R] (maximalIdeal R ^ m : Ideal R) ⧸
      (maximalIdeal R • ⊤ : Submodule R (maximalIdeal R ^ m : Ideal R)) :=
  LinearEquiv.ofBijective (residueToMaximalIdealGradedOfUniformizer π hπ m)
    (residueToMaximalIdealGradedOfUniformizer_bijective π hπ m)

/-- The explicit principal-power equivalence sends the residue of `x` to the class of
`x * π ^ m`. -/
@[simp]
theorem residueFieldEquivMaximalIdealGradedOfUniformizer_mk (π : R)
    (hπ : Irreducible π) (m : ℕ) (x : R) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m (residue R x) =
      Submodule.Quotient.mk
        (⟨x * π ^ m, by
          exact (maximalIdeal R ^ m).mul_mem_left x (by
            rw [hπ.maximalIdeal_eq]
            exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m)⟩ :
          (maximalIdeal R ^ m : Ideal R)) := by
  rw [residueFieldEquivMaximalIdealGradedOfUniformizer, LinearEquiv.ofBijective_apply,
    residueToMaximalIdealGradedOfUniformizer_mk,
    uniformizerPowToMaximalIdealGraded_apply]

/-- Replacing `π` by `π' = π * a` in the principal-power equivalence is the same as first
multiplying the residue coordinate by `a ^ m`. -/
theorem residueFieldEquivMaximalIdealGradedOfUniformizer_change (π π' : R)
    (hπ : Irreducible π) (hπ' : Irreducible π') (m : ℕ)
    (x : ResidueField R) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π' hπ' m x =
      residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m
        (uniformizerChangeResidueAddEquiv π π' hπ hπ' m x) := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [uniformizerChangeResidueAddEquiv_apply, ← map_pow, ← map_mul,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk]
  have heq : x * π' ^ m =
      (uniformizerChangeUnit π π' hπ hπ' : R) ^ m * x * π ^ m := by
    calc
      x * π' ^ m = x *
          (π * (uniformizerChangeUnit π π' hπ hπ' : R)) ^ m :=
        congrArg (fun z : R ↦ x * z ^ m)
          (mul_uniformizerChangeUnit π π' hπ hπ').symm
      _ = (uniformizerChangeUnit π π' hπ hπ' : R) ^ m * x * π ^ m := by
        ring
  exact congrArg Submodule.Quotient.mk (Subtype.ext heq)

/-- In inverse coordinates, when `π' = π * a`, the coordinate relative to `π` equals the
residue of `a ^ m` times the coordinate relative to `π'`. -/
theorem residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change (π π' : R)
    (hπ : Irreducible π) (hπ' : Irreducible π') (m : ℕ)
    (z : (maximalIdeal R ^ m : Ideal R) ⧸
      (maximalIdeal R • ⊤ : Submodule R (maximalIdeal R ^ m : Ideal R))) :
    (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m).symm z =
      uniformizerChangeResidueAddEquiv π π' hπ hπ' m
        ((residueFieldEquivMaximalIdealGradedOfUniformizer π' hπ' m).symm z) := by
  apply (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m).injective
  rw [← residueFieldEquivMaximalIdealGradedOfUniformizer_change]
  simp

end TauCeti
