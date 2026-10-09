/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.EquivariantKummer
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.LatticeDefect
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.ZMod

/-!
# Power classes as reductions of the multiplicative group

The unit calculation used in the local Euler characteristic is phrased in terms of the additive
reduction `Lˣ / nLˣ`, while Kummer theory is phrased in terms of the multiplicative quotient
`Lˣ / (Lˣ)ⁿ`. Through the equivariant identification of the two quotients,
`TauCeti.quotSMulTopUnitsPowerClassRepresentationEquiv`, this file transports the power-class
Grothendieck-group calculation to the representation of equivariant Kummer theory.

## Main results

* `TauCeti.exactK0_powerClassRepresentation_of_isUnit` and
  `TauCeti.exactK0_powerClassRepresentation_eq_add_finrank_smul`: the class of the power-class
  representation of a finite extension of local fields in `G₀(𝔽_ℓ[Gal(L/K)])` is
  `1 + [μ_ℓ(L)]`, plus `[K : ℚ_p] [𝔽_p[Gal(L/K)]]` when `ℓ = p`.
-/

public noncomputable section

open ValuativeRel
open scoped MonoidAlgebra

namespace TauCeti

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
        ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)).quotSMulTop ℓ) := by
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
        ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)).torsionBy ℓ) := by
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
          ((Representation.ofDistribMulAction ℤ Gal(L/K) (Additive Lˣ)).torsionBy ℓ) +
        Module.finrank ℚ_[ℓ] K • permK0 (ZMod ℓ) Gal(L/K) Gal(L/K) := by
  have : CharZero L := FinitePadicExtension.charZero L ℓ
  have : NeZero (ℓ : L) := ⟨Nat.cast_ne_zero.2 (NeZero.ne ℓ)⟩
  rw [exactK0_powerClassRepresentation_eq_reductionK0,
    reductionK0_quotSMulTop_units_eq_add_finrank_smul K L (ZMod ℓ) ℓ]

end LocalField

end TauCeti
