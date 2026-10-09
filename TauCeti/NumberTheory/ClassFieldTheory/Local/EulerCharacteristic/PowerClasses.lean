/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.EquivariantKummer
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.LatticeDefect
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.ZMod
public import TauCeti.RepresentationTheory.QuotSMulTop
public import TauCeti.RepresentationTheory.RestrictScalars

/-!
# Power classes as reductions of the multiplicative group

The unit calculation used in the local Euler characteristic is phrased in terms of the additive
reduction `Lˣ / nLˣ`, while Kummer theory is phrased in terms of the multiplicative quotient
`Lˣ / (Lˣ)ⁿ`. This file identifies the two quotients and checks that the identification respects
the natural Galois actions. It is the bridge through which the power-class Grothendieck-group
calculation enters equivariant Kummer theory.

## Main results

* `TauCeti.quotSMulTopPowerClassEquiv`: the additive equivalence between reduction modulo `n` and
  the group of `n`th power classes.
* `TauCeti.quotSMulTopUnitsPowerClassRepresentationEquiv`: the equivalence respects the action of
  `Gal(L/K)`.
* `TauCeti.exactK0_powerClassRepresentation_of_isUnit` and
  `TauCeti.exactK0_powerClassRepresentation_eq_add_finrank_smul`: the class of the power-class
  representation of a finite extension of local fields in `G₀(𝔽_ℓ[Gal(L/K)])` is
  `1 + [μ_ℓ(L)]`, plus `[K : ℚ_p] [𝔽_p[Gal(L/K)]]` when `ℓ = p`.
-/

public noncomputable section

open ValuativeRel
open scoped Pointwise MonoidAlgebra

namespace TauCeti

/-- In the additive group of a commutative group, the subgroup of integer multiples by `n` is the
additive form of the subgroup of `n`th powers. -/
theorem zsmulTop_toAddSubgroup_eq_powerSubgroup {G : Type*} [CommGroup G] (n : ℕ) :
    ((n : ℤ) • (⊤ : Submodule ℤ (Additive G))).toAddSubgroup =
      (powerSubgroup G n).toAddSubgroup := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.mem_top, true_and, Additive.mem_toAddSubgroup, mem_powerSubgroup_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.toMul, by simp [natCast_zsmul]⟩
  · rintro ⟨y, hy⟩
    exact ⟨Additive.ofMul y, by simpa [natCast_zsmul] using congrArg Additive.ofMul hy⟩

/-- Reduction modulo `n` of a commutative group, written additively, is its group of `n`th power
classes. -/
def quotSMulTopPowerClassEquiv {G : Type*} [CommGroup G] (n : ℕ) :
    QuotSMulTop (n : ℤ) (Additive G) ≃+ Additive (powerClassQuotient G n) := by
  let f : Additive G →+ Additive (powerClassQuotient G n) :=
    MonoidHom.toAdditive (powerClassHom G n)
  have hker : ((n : ℤ) • (⊤ : Submodule ℤ (Additive G))).toAddSubgroup = f.ker := by
    rw [zsmulTop_toAddSubgroup_eq_powerSubgroup]
    ext x
    -- Membership in `Additive.toAddSubgroup` and in the kernel of `toAdditive` unfold to these.
    change x.toMul ∈ powerSubgroup G n ↔ powerClassHom G n x.toMul = 1
    rw [← MonoidHom.mem_ker, ker_powerClassHom]
  exact (QuotientAddGroup.quotientAddEquivOfEq hker).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective f (powerClassHom_surjective G n))

/-- The reduction/power-class equivalence sends the class of `x` to its power class. -/
@[simp]
theorem quotSMulTopPowerClassEquiv_mk {G : Type*} [CommGroup G] (n : ℕ) (x : Additive G) :
    quotSMulTopPowerClassEquiv n (Submodule.Quotient.mk x) =
      Additive.ofMul (powerClassHom G n x.toMul) := by
  -- Both quotient equivalences are `lift`s, which compute on classes by definition.
  rfl

/-- The natural identification of additive reduction with power classes is equivariant for the
action of `Gal(L/K)`. -/
def quotSMulTopUnitsPowerClassRepresentationEquiv
    {K L : Type*} [Field K] [Field L] [Algebra K L] (n : ℕ) :
    ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)).quotSMulTop
      (n : ℤ)).Equiv
        (powerClassRepresentation (K := K) (L := L) n).restrictScalarsInt where
  toLinearEquiv := (quotSMulTopPowerClassEquiv n).toIntLinearEquiv
  isIntertwining' tau := by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Representation.quotSMulTop_apply_mk, Representation.restrictScalarsInt_apply,
      powerClassRepresentation_apply]
    -- Compare in the multiplicative quotient, where the actions are given by `Units.map`.
    change Additive.toMul (quotSMulTopPowerClassEquiv n
        (Submodule.Quotient.mk
          ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)) tau x))) =
      Additive.toMul (MonoidHom.toAdditive (powerClassMap n (Units.map (tau : L →* L)))
        (quotSMulTopPowerClassEquiv n (Submodule.Quotient.mk x)))
    rw [quotSMulTopPowerClassEquiv_mk, quotSMulTopPowerClassEquiv_mk]
    simp

/-! ### The class of the power-class representation -/

section LocalField

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  (ℓ : ℕ) [Fact ℓ.Prime]

/-- When `ℓ` is nonzero in a local field `L`, the `ℓ`th power classes of `L` form a
finite-dimensional `ZMod ℓ`-vector space. -/
instance [NeZero (ℓ : L)] : Module.Finite (ZMod ℓ) (Additive (powerClassQuotient Lˣ ℓ)) :=
  have : Finite (Additive (powerClassQuotient Lˣ ℓ)) :=
    Finite.of_equiv _ (quotSMulTopPowerClassEquiv (G := Lˣ) ℓ).toEquiv
  Module.Finite.of_finite

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension K L] [Module.Finite K L] in
/-- The class of the power-class representation is the reduction class of `Lˣ ⧸ ℓLˣ`. -/
private theorem exactK0_powerClassRepresentation_eq_reductionK0 [NeZero (ℓ : L)] :
    haveI : Module.Finite (ZMod ℓ)[Gal(L/K)]
        (powerClassRepresentation (K := K) (L := L) ℓ).asModule :=
      Module.Finite.of_restrictScalars_finite (ZMod ℓ) (ZMod ℓ)[Gal(L/K)] _
    ExactK0.of (FGModuleCat.of (ZMod ℓ)[Gal(L/K)]
        (powerClassRepresentation (K := K) (L := L) ℓ).asModule) =
      reductionK0 (ZMod ℓ)
        ((Representation.ofDistribMulAction ℤ (L ≃ₐ[K] L) (Additive Lˣ)).quotSMulTop ℓ) := by
  have : Module.Finite (ZMod ℓ)[Gal(L/K)]
      (powerClassRepresentation (K := K) (L := L) ℓ).asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod ℓ) (ZMod ℓ)[Gal(L/K)] _
  have : Module.Finite (ZMod ℓ) (TensorProduct ℤ (ZMod ℓ) (Additive (powerClassQuotient Lˣ ℓ))) :=
    Module.Finite.equiv
      ((powerClassRepresentation (K := K) (L := L) ℓ).baseChangeRestrictScalarsIntEquiv
        ).toLinearEquiv.symm
  rw [← reductionK0_restrictScalarsInt]
  exact (reductionK0_congr (ZMod ℓ) (quotSMulTopUnitsPowerClassRepresentationEquiv ℓ)).symm

/-- **The class of `Lˣ ⧸ (Lˣ)^ℓ` away from the residue characteristic**: if `ℓ` is a unit of
`𝒪[L]`, the power-class representation of `Gal(L/K)` has class `1 + [μ_ℓ(L)]` in
`G₀(𝔽_ℓ[Gal(L/K)])`, where `μ_ℓ(L)` is the `ℓ`-torsion of `Lˣ`. -/
theorem exactK0_powerClassRepresentation_of_isUnit (hℓ : IsUnit (ℓ : 𝒪[L])) :
    haveI : NeZero (ℓ : L) := ⟨natCast_ne_zero_of_isUnit hℓ⟩
    haveI : Module.Finite (ZMod ℓ)[Gal(L/K)]
        (powerClassRepresentation (K := K) (L := L) ℓ).asModule :=
      Module.Finite.of_restrictScalars_finite (ZMod ℓ) (ZMod ℓ)[Gal(L/K)] _
    ExactK0.of (FGModuleCat.of (ZMod ℓ)[Gal(L/K)]
        (powerClassRepresentation (K := K) (L := L) ℓ).asModule) =
      1 + reductionK0 (ZMod ℓ)
        ((Representation.ofDistribMulAction ℤ (L ≃ₐ[K] L) (Additive Lˣ)).torsionBy ℓ) := by
  have : NeZero (ℓ : L) := ⟨natCast_ne_zero_of_isUnit hℓ⟩
  rw [exactK0_powerClassRepresentation_eq_reductionK0,
    reductionK0_quotSMulTop_units_of_isUnit K L (ZMod ℓ) ℓ hℓ]

/-- **The class of `Lˣ ⧸ (Lˣ)^p` at the residue characteristic**: for `L/K` a finite Galois
extension of finite extensions of `ℚ_p`, the power-class representation of `Gal(L/K)` has class
`1 + [μ_p(L)] + [K : ℚ_p] [𝔽_p[Gal(L/K)]]` in `G₀(𝔽_p[Gal(L/K)])`. -/
theorem exactK0_powerClassRepresentation_eq_add_finrank_smul [FinitePadicExtension L ℓ]
    [FinitePadicExtension K ℓ] [IsGalois K L] :
    haveI : CharZero L := FinitePadicExtension.charZero L ℓ
    haveI : NeZero (ℓ : L) := ⟨Nat.cast_ne_zero.2 (NeZero.ne ℓ)⟩
    haveI : Module.Finite (ZMod ℓ)[Gal(L/K)]
        (powerClassRepresentation (K := K) (L := L) ℓ).asModule :=
      Module.Finite.of_restrictScalars_finite (ZMod ℓ) (ZMod ℓ)[Gal(L/K)] _
    ExactK0.of (FGModuleCat.of (ZMod ℓ)[Gal(L/K)]
        (powerClassRepresentation (K := K) (L := L) ℓ).asModule) =
      1 + reductionK0 (ZMod ℓ)
          ((Representation.ofDistribMulAction ℤ (L ≃ₐ[K] L) (Additive Lˣ)).torsionBy ℓ) +
        Module.finrank ℚ_[ℓ] K • permK0 (ZMod ℓ) (L ≃ₐ[K] L) (L ≃ₐ[K] L) := by
  have : CharZero L := FinitePadicExtension.charZero L ℓ
  have : NeZero (ℓ : L) := ⟨Nat.cast_ne_zero.2 (NeZero.ne ℓ)⟩
  rw [exactK0_powerClassRepresentation_eq_reductionK0,
    reductionK0_quotSMulTop_units_eq_add_finrank_smul K L (ZMod ℓ) ℓ]

end LocalField

end TauCeti
