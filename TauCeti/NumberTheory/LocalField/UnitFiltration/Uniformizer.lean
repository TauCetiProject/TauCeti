/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded

/-!
# Uniformizer coordinates on unit-filtration graded pieces

Fixing a uniformizer `π` identifies the `m`th positive graded piece of the unit filtration
with the additive residue field: the class of `u` has coordinate `(u - 1) / π ^ m` modulo the
maximal ideal.  This file constructs that coordinate explicitly and computes how it changes when
the uniformizer is replaced.

If `π' = π * a` for a unit `a` of the integer ring, then the coordinate relative to `π` is
`a ^ m` times the coordinate relative to `π'`.  Thus the identification is independent of the
uniformizer up to the additive automorphism of the residue field induced by multiplication by
the residue of `a ^ m`.

The explicit principal-power equivalence below follows the construction of Mathlib's
`Ideal.quotEquivPowQuotPowSucc`, retaining a specified generator in order to expose the
change-of-uniformizer formula.

## Main results

* `TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer`: the residue coordinate
  determined by a uniformizer.
* `TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change`: changing the
  uniformizer scales the coordinate by the corresponding residue-field unit.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The unique unit `a` such that `π * a = π'`, for two uniformizers `π` and `π'` of the
integer ring of a local field. -/
noncomputable def uniformizerChangeUnit (π π' : 𝒪[K]) (hπ : Irreducible π)
    (hπ' : Irreducible π') : 𝒪[K]ˣ :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[K] hπ hπ').choose

/-- The unit `uniformizerChangeUnit π π'` carries `π` to `π'`. -/
@[simp]
theorem mul_uniformizerChangeUnit (π π' : 𝒪[K]) (hπ : Irreducible π)
    (hπ' : Irreducible π') :
    π * (uniformizerChangeUnit π π' hπ hπ' : 𝒪[K]) = π' :=
  (IsDiscreteValuationRing.associated_of_irreducible 𝒪[K] hπ hπ').choose_spec

/-- The change unit from a uniformizer to itself is one. -/
@[simp]
theorem uniformizerChangeUnit_self (π : 𝒪[K]) (hπ : Irreducible π) :
    uniformizerChangeUnit π π hπ hπ = 1 := by
  apply Units.ext
  exact mul_left_cancel₀ hπ.ne_zero (by simp)

/-- Change units compose when passing through a third uniformizer. -/
theorem uniformizerChangeUnit_mul (π₁ π₂ π₃ : 𝒪[K]) (h₁ : Irreducible π₁)
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
noncomputable def uniformizerChangeResidueAddEquiv (π π' : 𝒪[K]) (hπ : Irreducible π)
    (hπ' : Irreducible π') (m : ℕ) : 𝓀[K] ≃+ 𝓀[K] :=
  DistribMulAction.toAddEquiv 𝓀[K]
    (Units.map (IsLocalRing.residue 𝒪[K]).toMonoidHom
      (uniformizerChangeUnit π π' hπ hπ') ^ m)

/-- The coordinate-change automorphism acts by multiplication by the residue of the change
unit to the indicated power. -/
@[simp]
theorem uniformizerChangeResidueAddEquiv_apply (π π' : 𝒪[K]) (hπ : Irreducible π)
    (hπ' : Irreducible π') (m : ℕ) (x : 𝓀[K]) :
    uniformizerChangeResidueAddEquiv π π' hπ hπ' m x =
      (IsLocalRing.residue 𝒪[K]
        (uniformizerChangeUnit π π' hπ hπ' : 𝒪[K])) ^ m * x := by
  simp [uniformizerChangeResidueAddEquiv, Units.smul_def]

private noncomputable def uniformizerPowToMaximalIdealGraded (π : 𝒪[K])
    (hπ : Irreducible π) (m : ℕ) : 𝒪[K] →ₗ[𝒪[K]] MaximalIdealGraded K m :=
  (Submodule.mkQ _).comp <|
    (LinearMap.mulRight 𝒪[K] π ^ m).codRestrict _ fun x ↦ by
      simpa only [LinearMap.pow_mulRight, LinearMap.mulRight_apply] using
        (𝓂[K] ^ m).mul_mem_left x (by
          rw [hπ.maximalIdeal_eq]
          exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m)

@[simp]
private theorem uniformizerPowToMaximalIdealGraded_apply (π : 𝒪[K])
    (hπ : Irreducible π) (m : ℕ) (x : 𝒪[K]) :
    uniformizerPowToMaximalIdealGraded π hπ m x =
      Submodule.Quotient.mk
        (⟨x * π ^ m, by
          apply (𝓂[K] ^ m).mul_mem_left x
          rw [hπ.maximalIdeal_eq]
          exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m⟩ :
          (𝓂[K] ^ m : Ideal 𝒪[K])) := by
  simp [uniformizerPowToMaximalIdealGraded, LinearMap.pow_mulRight]
  congr 1

private theorem ker_uniformizerPowToMaximalIdealGraded (π : 𝒪[K])
    (hπ : Irreducible π) (m : ℕ) :
    LinearMap.ker (uniformizerPowToMaximalIdealGraded π hπ m) = 𝓂[K] := by
  ext x
  rw [LinearMap.mem_ker, uniformizerPowToMaximalIdealGraded_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, smul_eq_mul]
  -- Strip the ideal-subtype coercion introduced by the displayed representative.
  change x * π ^ m ∈ 𝓂[K] * 𝓂[K] ^ m ↔ x ∈ 𝓂[K]
  constructor
  · intro hx
    rw [← pow_succ', hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hx
    obtain ⟨y, hy⟩ := hx
    rw [mul_comm, pow_succ, mul_assoc, mul_right_inj' (pow_ne_zero m hπ.ne_zero)] at hy
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton]
    exact ⟨y, hy⟩
  · intro hx
    have hπm : π ^ m ∈ 𝓂[K] ^ m := by
      rw [hπ.maximalIdeal_eq]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m
    exact Submodule.mul_mem_mul hx hπm

private theorem uniformizerPowToMaximalIdealGraded_surjective (π : 𝒪[K])
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

private noncomputable def residueToMaximalIdealGradedOfUniformizer (π : 𝒪[K])
    (hπ : Irreducible π) (m : ℕ) :
    𝓀[K] →ₗ[𝒪[K]] MaximalIdealGraded K m :=
  𝓂[K].liftQ (uniformizerPowToMaximalIdealGraded π hπ m) <| by
    rw [ker_uniformizerPowToMaximalIdealGraded]

@[simp]
private theorem residueToMaximalIdealGradedOfUniformizer_mk (π : 𝒪[K])
    (hπ : Irreducible π) (m : ℕ) (x : 𝒪[K]) :
    residueToMaximalIdealGradedOfUniformizer π hπ m (IsLocalRing.residue 𝒪[K] x) =
      uniformizerPowToMaximalIdealGraded π hπ m x := by
  rw [residueToMaximalIdealGradedOfUniformizer]
  -- The ideal-quotient constructor is the module-quotient constructor used by `liftQ`.
  change 𝓂[K].liftQ (uniformizerPowToMaximalIdealGraded π hπ m) _
      (Submodule.Quotient.mk x) = _
  rw [Submodule.liftQ_apply]

private theorem residueToMaximalIdealGradedOfUniformizer_bijective (π : 𝒪[K])
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
the `m`th maximal-ideal graded piece. -/
noncomputable def residueFieldEquivMaximalIdealGradedOfUniformizer (π : 𝒪[K])
    (hπ : Irreducible π) (m : ℕ) :
    𝓀[K] ≃ₗ[𝒪[K]] MaximalIdealGraded K m :=
  LinearEquiv.ofBijective (residueToMaximalIdealGradedOfUniformizer π hπ m)
    (residueToMaximalIdealGradedOfUniformizer_bijective π hπ m)

/-- The explicit principal-power equivalence sends the residue of `x` to the class of
`x * π ^ m`. -/
@[simp]
theorem residueFieldEquivMaximalIdealGradedOfUniformizer_mk (π : 𝒪[K])
    (hπ : Irreducible π) (m : ℕ) (x : 𝒪[K]) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m (IsLocalRing.residue 𝒪[K] x) =
      Submodule.Quotient.mk
        (⟨x * π ^ m, by
          exact (𝓂[K] ^ m).mul_mem_left x (by
            rw [hπ.maximalIdeal_eq]
            exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m)⟩ :
          (𝓂[K] ^ m : Ideal 𝒪[K])) := by
  rw [residueFieldEquivMaximalIdealGradedOfUniformizer, LinearEquiv.ofBijective_apply,
    residueToMaximalIdealGradedOfUniformizer_mk,
    uniformizerPowToMaximalIdealGraded_apply]

/-- Replacing `π` by `π' = π * a` in the principal-power equivalence is the same as first
multiplying the residue coordinate by `a ^ m`. -/
theorem residueFieldEquivMaximalIdealGradedOfUniformizer_change (π π' : 𝒪[K])
    (hπ : Irreducible π) (hπ' : Irreducible π') (m : ℕ)
    (x : 𝓀[K]) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π' hπ' m x =
      residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m
        (uniformizerChangeResidueAddEquiv π π' hπ hπ' m x) := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  rw [uniformizerChangeResidueAddEquiv_apply, ← map_pow, ← map_mul,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk]
  rw [Submodule.Quotient.eq]
  have hπm : π ^ m ∈ 𝓂[K] ^ m := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) m
  have heq : x * π' ^ m =
      (uniformizerChangeUnit π π' hπ hπ' : 𝒪[K]) ^ m * x * π ^ m := by
    calc
      x * π' ^ m = x *
          (π * (uniformizerChangeUnit π π' hπ hπ' : 𝒪[K])) ^ m :=
        congrArg (fun z : 𝒪[K] ↦ x * z ^ m)
          (mul_uniformizerChangeUnit π π' hπ hπ').symm
      _ = (uniformizerChangeUnit π π' hπ hπ' : 𝒪[K]) ^ m * x * π ^ m := by
        ring
  have hright :
      (uniformizerChangeUnit π π' hπ hπ' : 𝒪[K]) ^ m * x * π ^ m ∈ 𝓂[K] ^ m :=
    (𝓂[K] ^ m).mul_mem_left _ hπm
  have hleft : x * π' ^ m ∈ 𝓂[K] ^ m := heq ▸ hright
  let a : (𝓂[K] ^ m : Ideal 𝒪[K]) := ⟨x * π' ^ m, hleft⟩
  let b : (𝓂[K] ^ m : Ideal 𝒪[K]) :=
    ⟨(uniformizerChangeUnit π π' hπ hπ' : 𝒪[K]) ^ m * x * π ^ m, hright⟩
  change a - b ∈ 𝓂[K] • ⊤
  rw [show a = b from Subtype.ext heq, sub_self]
  exact Submodule.zero_mem _

/-- In inverse coordinates, replacing `π` by `π' = π * a` multiplies the residue
coordinate by `a ^ m`. -/
theorem residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change (π π' : 𝒪[K])
    (hπ : Irreducible π) (hπ' : Irreducible π') (m : ℕ)
    (z : MaximalIdealGraded K m) :
    (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m).symm z =
      uniformizerChangeResidueAddEquiv π π' hπ hπ' m
        ((residueFieldEquivMaximalIdealGradedOfUniformizer π' hπ' m).symm z) := by
  apply (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m).injective
  rw [← residueFieldEquivMaximalIdealGradedOfUniformizer_change]
  simp

/-- The positive-depth unit-filtration coordinate associated to a uniformizer.  The class of
`u ∈ U(K,n+1)` is sent to the residue of `(u - 1) / π^(n+1)`. -/
noncomputable def unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (n : ℕ)
    (π : 𝒪[K]) (hπ : Irreducible π) : Additive (UnitFiltrationGraded K (n + 1)) ≃+ 𝓀[K] :=
  (unitFiltrationGradedSuccEquivMaximalIdealGraded (K := K) n).toAdditive.trans <|
    (AddEquiv.additiveMultiplicative (MaximalIdealGraded K (n + 1))).trans <|
      (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).symm.toAddEquiv

/-- The uniformizer coordinate of the class of `u` is characterized by multiplying it by
`π^(n+1)`: the result is the class of `u - 1` in the maximal-ideal graded piece. -/
@[simp]
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk (n : ℕ)
    (π : 𝒪[K]) (hπ : Irreducible π) (x : unitFiltration K (n + 1)) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)
        (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ
          (Additive.ofMul (QuotientGroup.mk x))) =
      Submodule.Quotient.mk (unitFiltrationDifference n x) := by
  rw [unitFiltrationGradedSuccEquivResidueFieldOfUniformizer]
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply,
    MonoidHom.toAdditive_apply_apply, MulEquiv.coe_toMonoidHom, toMul_ofMul,
    unitFiltrationGradedSuccEquivMaximalIdealGraded_mk]
  exact LinearEquiv.apply_symm_apply _ _

/-- Coordinates attached to `π` and `π'` differ by multiplication by the residue of the
`(n+1)`st power of the unit carrying `π` to `π'`. -/
theorem unitFiltrationGradedSuccEquivResidueFieldOfUniformizer_change (n : ℕ)
    (π π' : 𝒪[K]) (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : Additive (UnitFiltrationGraded K (n + 1))) :
    unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π hπ x =
      uniformizerChangeResidueAddEquiv π π' hπ hπ' (n + 1)
        (unitFiltrationGradedSuccEquivResidueFieldOfUniformizer (K := K) n π' hπ' x) := by
  exact residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change π π' hπ hπ'
    (n + 1) _

end TauCeti
