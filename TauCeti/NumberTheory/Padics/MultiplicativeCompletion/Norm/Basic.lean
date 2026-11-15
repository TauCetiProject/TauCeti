/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.PowerClassGroup.Basic
public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Basic
public import TauCeti.RingTheory.Norm.Units
public import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RingTheory.Norm.Basic

/-!
# Norms on completed multiplicative modules

For a finite extension `L/K`, the field norm induces a `ℤ_p`-linear map `A(L) → A(K)` on
the inverse limits of the `p`-power class groups. Its value on the canonical class of a unit
is the canonical class of its norm.

The completed norm is invariant under every `K`-automorphism of `L`, including on elements
of `A(L)` that do not come from individual units. It therefore factors through Mathlib's
coinvariants of the representation `padicCompletionUnitsRepresentation p L K`. This is the
norm map whose cokernel enters the reciprocity description of a finite Galois layer.

The construction uses the algebraic inverse-limit carrier; it requires neither a topology
on the fields nor a Galois hypothesis.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., VII §4,
  especially (7.4.4).
-/

public section

noncomputable section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L]

-- `powerSubgroup` has an unexposed body in the imported module, so its equality with the
-- raw power-hom range cannot be used definitionally here. Transport `powerClassMap` along
-- the public subgroup equality to obtain the completion's coordinate types.
/-- The field norm on `p^m`-power classes for a finite extension `L/K`.
Finiteness excludes the constant-one norm on infinite extensions. -/
def padicCompletionPowerClassNorm [_hfin : FiniteDimensional K L] (m : ℕ) :
    (Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) →*
      (Kˣ ⧸ (powMonoidHom (p ^ m) : Kˣ →* Kˣ).range) :=
  ((QuotientGroup.quotientMulEquivOfEq
    (powerSubgroup_eq_range_powMonoidHom Kˣ (p ^ m))).toMonoidHom).comp
    ((powerClassMap (p ^ m) (Algebra.normUnits K : Lˣ →* Kˣ)).comp
      (QuotientGroup.quotientMulEquivOfEq
        (powerSubgroup_eq_range_powMonoidHom Lˣ (p ^ m)).symm).toMonoidHom)

variable [FiniteDimensional K L]

omit [Fact p.Prime] in
/-- The norm on power classes sends the class of a unit to the class of its norm. -/
@[simp]
theorem padicCompletionPowerClassNorm_mk (m : ℕ) (x : Lˣ) :
    padicCompletionPowerClassNorm p K L m
        (x : Lˣ ⧸ (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range) =
      (Algebra.normUnits K x : Kˣ ⧸ (powMonoidHom (p ^ m) : Kˣ →* Kˣ).range) := by
  simp [padicCompletionPowerClassNorm]

omit [Fact p.Prime] in
/-- The norm on power classes commutes with the completion's transition maps. -/
theorem padicCompletionPowerClassNorm_transition (m : ℕ)
    (x : Lˣ ⧸ (powMonoidHom (p ^ (m + 1)) : Lˣ →* Lˣ).range) :
    padicCompletionTransition p K m (padicCompletionPowerClassNorm p K L (m + 1) x) =
      padicCompletionPowerClassNorm p K L m (padicCompletionTransition p L m x) := by
  induction x using QuotientGroup.induction_on with
  | H x => simp

private def padicCompletionUnitsNormHom :
    ↑(padicCompletionUnits p L) →* ↑(padicCompletionUnits p K) :=
  padicCompletionUnitsLift p L K (padicCompletionPowerClassNorm p K L)
    (padicCompletionPowerClassNorm_transition p K L)

omit [Fact p.Prime] in
@[simp]
private theorem padicCompletionUnitsNormHom_apply (x : ↑(padicCompletionUnits p L))
    (m : ℕ) :
    (padicCompletionUnitsNormHom p K L x).1 m =
      padicCompletionPowerClassNorm p K L m (x.1 m) := by
  simp only [padicCompletionUnitsNormHom, padicCompletionUnitsLift_apply]

/-- The `ℤ_p`-linear norm `A(L) → A(K)` induced by the field norm at every finite level.
Finiteness excludes the constant-one value of Mathlib's total norm on infinite extensions. -/
def padicCompletionUnitsNorm :
    Additive ↑(padicCompletionUnits p L) →ₗ[ℤ_[p]]
      Additive ↑(padicCompletionUnits p K) where
  toFun x := Additive.ofMul (padicCompletionUnitsNormHom p K L x.toMul)
  map_add' x y := by
    apply Additive.toMul.injective
    exact map_mul (padicCompletionUnitsNormHom p K L) x.toMul y.toMul
  map_smul' a x := by
    apply Additive.toMul.injective
    ext m
    simp only [toMul_ofMul, RingHom.id_apply, padicCompletionUnitsNormHom_apply,
      padicCompletionUnits_smul_apply]
    simp only [map_pow]

/-- The completed norm is computed by the norm on each power-class coordinate. -/
@[simp]
theorem padicCompletionUnitsNorm_apply (x : Additive ↑(padicCompletionUnits p L)) (m : ℕ) :
    (padicCompletionUnitsNorm p K L x).toMul.1 m =
      padicCompletionPowerClassNorm p K L m (x.toMul.1 m) := by
  simpa only [padicCompletionUnitsNorm, LinearMap.coe_mk, AddHom.coe_mk, toMul_ofMul] using
    padicCompletionUnitsNormHom_apply p K L x.toMul m

/-- The norm of the canonical class of a unit is the canonical class of its norm. -/
@[simp]
theorem padicCompletionUnitsNorm_of (x : Lˣ) :
    padicCompletionUnitsNorm p K L (Additive.ofMul (padicCompletionUnitsOf p L x)) =
      Additive.ofMul (padicCompletionUnitsOf p K (Algebra.normUnits K x)) := by
  apply Additive.toMul.injective
  ext m
  simp

omit [Fact p.Prime] [FiniteDimensional K L] in
/-- The canonical class of a norm is unchanged on replacing a unit by a Galois conjugate. -/
@[simp]
theorem padicCompletionUnitsOf_norm_algEquiv (σ : L ≃ₐ[K] L) (x : Lˣ) :
    padicCompletionUnitsOf p K (Algebra.normUnits K (Units.map ((σ : L →+* L) : L →* L) x)) =
      padicCompletionUnitsOf p K (Algebra.normUnits K x) := by
  congr 1
  exact Units.ext (by simp [Algebra.norm_eq_of_algEquiv σ])

/-- The completed norm is invariant under the full `K`-automorphism action on `A(L)`. -/
@[simp]
theorem padicCompletionUnitsNorm_aut (σ : L ≃ₐ[K] L)
    (x : ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsNorm p K L (Additive.ofMul (padicCompletionUnitsAut p L K σ x)) =
      padicCompletionUnitsNorm p K L (Additive.ofMul x) := by
  apply Additive.toMul.injective
  ext m
  simp only [padicCompletionUnitsNorm_apply, toMul_ofMul, padicCompletionUnitsAut_apply]
  induction x.1 m using QuotientGroup.induction_on with
  | H y =>
    simp only [padicCompletionPowerClassMap_mk, padicCompletionPowerClassNorm_mk]
    simpa only [padicCompletionUnitsOf_apply, QuotientGroup.mk'_apply,
      RingHom.toMonoidHom_eq_coe,
      RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom] using
      congrArg (fun z : ↑(padicCompletionUnits p K) ↦ z.1 m)
      (padicCompletionUnitsOf_norm_algEquiv p K L σ y)

/-- The group algebra acts through its augmentation after applying the completed norm.
In particular the augmentation ideal annihilates the norm. -/
@[simp]
theorem padicCompletionUnitsNorm_smul
    (r : MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (x : Additive ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsNorm p K L (r • x) =
      MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L) r • padicCompletionUnitsNorm p K L x := by
  induction r using _root_.MonoidAlgebra.induction_linear with
  | zero => simp
  | add r s hr hs => simp [add_smul, hr, hs]
  | single σ a =>
    conv_lhs => rw [← ofMul_toMul x, padicCompletionUnits_single_smul]
    simp

/-- The completed norm descends to the coinvariants of the Galois representation on `A(L)`. -/
def padicCompletionUnitsCoinvariantsNorm :
    (padicCompletionUnitsRepresentation p L K).Coinvariants →ₗ[ℤ_[p]]
      Additive ↑(padicCompletionUnits p K) :=
  Representation.Coinvariants.lift _ (padicCompletionUnitsNorm p K L) fun σ ↦ by
    ext x
    simp

/-- The norm on coinvariants recovers the completed norm on a representative. -/
@[simp]
theorem padicCompletionUnitsCoinvariantsNorm_mk (x : Additive ↑(padicCompletionUnits p L)) :
    padicCompletionUnitsCoinvariantsNorm p K L
        (Representation.Coinvariants.mk (padicCompletionUnitsRepresentation p L K) x) =
      padicCompletionUnitsNorm p K L x :=
  Representation.Coinvariants.lift_mk _ _ _ x

end TauCeti
