/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.DiscreteValuationRing.Basic
public import TauCeti.RingTheory.Ideal.Operations
public import TauCeti.RingTheory.LocalRing.PrincipalUnitGroup

/-!
# Uniformizer coordinates on maximal-ideal and principal-unit graded pieces

Let `R` be a discrete valuation ring with maximal ideal `𝔪` and residue field `k`.  Fixing a
uniformizer `π` identifies `k` with the graded piece `𝔪^m / 𝔪^(m+1)` by sending the residue
of `x` to the class of `x * π ^ m`, and hence identifies the positive-depth principal-unit graded
piece `(1 + 𝔪^(n+1)) / (1 + 𝔪^(n+2))` with the additive residue field by sending the class of `u`
to the residue of `(u - 1) / π ^ (n + 1)`.  This file constructs these identifications explicitly
and computes how they change when the uniformizer is replaced.

If `π' = π * a` for a unit `a` of `R`, then the identification `k ≃ 𝔪^m / 𝔪^(m+1)` for `π'` is the
identification for `π` precomposed with multiplication by `residue R a ^ m`, while in the opposite
direction the `(n + 1)`-st principal-unit residue coordinate `(1 + 𝔪^(n+1)) / (1 + 𝔪^(n+2)) ≃+ k`
for `π` equals `residue R a ^ (n + 1)` times that for `π'`.  Thus both identifications are
independent of the uniformizer up to multiplication by a unit of the residue field.

The explicit principal-power equivalence below follows the construction of Mathlib's
`Ideal.quotEquivPowQuotPowSucc`, retaining a specified generator in order to expose the
change-of-uniformizer formula; the principal-unit coordinate adapts
`TauCeti.unitFiltrationGradedSuccEquivResidueFieldOfUniformizer` from
`TauCeti/NumberTheory/LocalField/UnitFiltration/Uniformizer.lean` to an arbitrary discrete
valuation ring.

## Main results

* `TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer`: the identification of the residue
  field with a maximal-ideal graded piece determined by a uniformizer.
* `TauCeti.residueFieldEquivMaximalIdealGradedOfUniformizer_change`: changing the uniformizer
  scales the residue coordinate by the residue of the `m`th power of the change unit.
* `TauCeti.principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer`: the identification of the
  `(n + 1)`-st principal-unit graded piece with the additive residue field determined by `π`, and
  `TauCeti.principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_change` for its scaling under
  a change of uniformizer.

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

private noncomputable def uniformizerPowToMaximalIdealGraded (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    R →ₗ[R] (maximalIdeal R ^ m : Ideal R) ⧸
      (maximalIdeal R • ⊤ : Submodule R (maximalIdeal R ^ m : Ideal R)) :=
  (Submodule.mkQ _).comp <|
    (LinearMap.mulRight R (π ^ m)).codRestrict _
      (Ideal.mul_pow_mem_pow
        ((mem_maximalIdeal π).2 hπ.not_isUnit) m)

private theorem uniformizerPowToMaximalIdealGraded_apply (π : R)
    (hπ : Irreducible π) (m : ℕ) (x : R) :
    uniformizerPowToMaximalIdealGraded π hπ m x =
      Submodule.Quotient.mk
        ⟨x * π ^ m, Ideal.mul_pow_mem_pow
        ((mem_maximalIdeal π).2 hπ.not_isUnit) m x⟩ :=
  rfl

private theorem ker_uniformizerPowToMaximalIdealGraded (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    LinearMap.ker (uniformizerPowToMaximalIdealGraded π hπ m) = maximalIdeal R := by
  ext x
  -- The class of `x * π ^ m` vanishes iff `x * π ^ m ∈ 𝔪 * 𝔪 ^ m`.
  simp only [LinearMap.mem_ker, uniformizerPowToMaximalIdealGraded_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, smul_eq_mul]
  -- Cancel the uniformizer power `π ^ m`.
  refine ⟨fun h ↦ ?_, fun hx ↦ Ideal.mul_mem_mul hx <|
    Ideal.pow_mem_pow ((mem_maximalIdeal π).2 hπ.not_isUnit) m⟩
  rw [← pow_succ'] at h
  exact IsDiscreteValuationRing.mem_maximalIdeal_of_mul_pow_mem_maximalIdeal_pow_succ hπ h

private theorem uniformizerPowToMaximalIdealGraded_surjective (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    Function.Surjective (uniformizerPowToMaximalIdealGraded π hπ m) := by
  rintro ⟨x, hx⟩
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, congrArg Submodule.Quotient.mk (Subtype.ext (mul_comm y _))⟩

/-- Multiplication by a chosen uniformizer to the `m`th power identifies the residue field with
the `m`th graded piece `𝔪^m / 𝔪^(m+1)` of the maximal-ideal filtration. -/
noncomputable def residueFieldEquivMaximalIdealGradedOfUniformizer (π : R)
    (hπ : Irreducible π) (m : ℕ) :
    ResidueField R ≃ₗ[R] (maximalIdeal R ^ m : Ideal R) ⧸
      (maximalIdeal R • ⊤ : Submodule R (maximalIdeal R ^ m : Ideal R)) :=
  (Submodule.quotEquivOfEq _ _ (ker_uniformizerPowToMaximalIdealGraded π hπ m).symm).trans <|
    (uniformizerPowToMaximalIdealGraded π hπ m).quotKerEquivOfSurjective
      (uniformizerPowToMaximalIdealGraded_surjective π hπ m)

/-- The explicit principal-power equivalence sends the residue of `x` to the class of
`x * π ^ m`. -/
@[simp]
theorem residueFieldEquivMaximalIdealGradedOfUniformizer_mk (π : R)
    (hπ : Irreducible π) (m : ℕ) (x : R) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m (residue R x) =
      Submodule.Quotient.mk
        ⟨x * π ^ m, Ideal.mul_pow_mem_pow
        ((mem_maximalIdeal π).2 hπ.not_isUnit) m x⟩ := by
  -- `residue R x` is the class of `x` in `R ⧸ 𝔪`.
  rw [residue_def, ← Ideal.Quotient.mk_eq_mk]
  -- The equivalence is a composite out of `R ⧸ 𝔪`, while its stated domain is the definition
  -- `ResidueField R`; `rw [LinearEquiv.trans_apply]` cannot see through that definition, so the
  -- composite is split by unification and each factor is computed by its `_mk` lemma.
  exact (LinearEquiv.trans_apply ..).trans <| (congrArg _ (Submodule.quotEquivOfEq_mk ..)).trans <|
    (LinearMap.quotKerEquivOfSurjective_apply_mk ..).trans
      (uniformizerPowToMaximalIdealGraded_apply π hπ m x)

/-- Replacing `π` by `π' = π * a` in the principal-power equivalence is the same as first
multiplying the residue coordinate by `a ^ m`. -/
theorem residueFieldEquivMaximalIdealGradedOfUniformizer_change (π π' : R)
    (hπ : Irreducible π) (hπ' : Irreducible π') (m : ℕ)
    (x : ResidueField R) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π' hπ' m x =
      residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m
        (residue R (uniformizerChangeUnit π π' hπ hπ' : R) ^ m * x) := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [← map_pow, ← map_mul, residueFieldEquivMaximalIdealGradedOfUniformizer_mk,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  dsimp only
  conv_lhs => rw [← mul_uniformizerChangeUnit π π' hπ hπ']
  ring

/-- In inverse coordinates, when `π' = π * a`, the coordinate relative to `π` equals the
residue of `a ^ m` times the coordinate relative to `π'`. -/
theorem residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change (π π' : R)
    (hπ : Irreducible π) (hπ' : Irreducible π') (m : ℕ)
    (z : (maximalIdeal R ^ m : Ideal R) ⧸
      (maximalIdeal R • ⊤ : Submodule R (maximalIdeal R ^ m : Ideal R))) :
    (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m).symm z =
      residue R (uniformizerChangeUnit π π' hπ hπ' : R) ^ m *
        (residueFieldEquivMaximalIdealGradedOfUniformizer π' hπ' m).symm z := by
  apply (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ m).injective
  rw [← residueFieldEquivMaximalIdealGradedOfUniformizer_change]
  simp

/-- The positive-depth principal-unit coordinate determined by a uniformizer `π`: the class of
`u ∈ 1 + 𝔪 ^ (n + 1)` is sent to the residue of `(u - 1) / π ^ (n + 1)`. -/
def principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer (n : ℕ) (π : R)
    (hπ : Irreducible π) :
    Additive (IsLocalRing.PrincipalUnitGroupGraded R (n + 1)) ≃+ ResidueField R :=
  (IsLocalRing.principalUnitGroupGradedSuccEquivMaximalIdealGraded R n).toAdditive.trans <|
    (AddEquiv.additiveMultiplicative _).trans <|
      (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).symm.toAddEquiv

/-- Multiplying the uniformizer coordinate of the class of `u` by `π ^ (n + 1)` recovers the class
of `u - 1` in `𝔪 ^ (n + 1) ⧸ 𝔪 • ⊤`. -/
@[simp]
theorem principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk (n : ℕ) (π : R)
    (hπ : Irreducible π) (u : (maximalIdeal R ^ (n + 1)).principalUnitGroup) :
    residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)
        (principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n π hπ
          (Additive.ofMul (QuotientGroup.mk u))) =
      Submodule.Quotient.mk ⟨((u : Rˣ) : R) - 1, Ideal.mem_principalUnitGroup.mp u.property⟩ := by
  rw [principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer]
  simp only [AddEquiv.trans_apply, MulEquiv.toAdditive_apply_apply, toMul_ofMul,
    IsLocalRing.principalUnitGroupGradedSuccEquivMaximalIdealGraded_mk]
  exact LinearEquiv.apply_symm_apply _ _

/-- If `u - 1 = y * π ^ (n + 1)`, then the uniformizer coordinate of the class of `u` is the
residue of `y`. -/
theorem principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk_eq_residue (n : ℕ)
    (π : R) (hπ : Irreducible π) (u : (maximalIdeal R ^ (n + 1)).principalUnitGroup) (y : R)
    (huy : ((u : Rˣ) : R) - 1 = y * π ^ (n + 1)) :
    principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n π hπ
        (Additive.ofMul (QuotientGroup.mk u)) = residue R y := by
  apply (residueFieldEquivMaximalIdealGradedOfUniformizer π hπ (n + 1)).injective
  rw [principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_ofMul_mk,
    residueFieldEquivMaximalIdealGradedOfUniformizer_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext huy)

/-- Replacing `π` by `π' = π * a` scales the `(n + 1)`-st principal-unit residue coordinate: the
coordinate relative to `π` equals the residue of `a ^ (n + 1)` times the coordinate relative to
`π'`. -/
theorem principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer_change (n : ℕ) (π π' : R)
    (hπ : Irreducible π) (hπ' : Irreducible π')
    (x : Additive (IsLocalRing.PrincipalUnitGroupGraded R (n + 1))) :
    principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n π hπ x =
      residue R (uniformizerChangeUnit π π' hπ hπ' : R) ^ (n + 1) *
        principalUnitGroupGradedSuccEquivResidueFieldOfUniformizer n π' hπ' x :=
  residueFieldEquivMaximalIdealGradedOfUniformizer_symm_change π π' hπ hπ' (n + 1) _

end TauCeti
