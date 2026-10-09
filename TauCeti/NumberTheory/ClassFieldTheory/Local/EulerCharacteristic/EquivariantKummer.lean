/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.Algebra.Module.ZMod.SMulCommClass
public import TauCeti.Data.ZMod.TrivialAction
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import TauCeti.FieldTheory.GaloisCohomology.EquivariantKummer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H1.ZMod
public import TauCeti.RingTheory.RootsOfUnity.ZMod

/-!
# Finite-layer representations for equivariant Kummer theory

Let `L/K` be a normal extension embedded in a separable closure. This file packages the three
actions used in equivariant Kummer theory at finite Galois layers: the natural action of
`Gal(L/K)` on power classes, the quotient action on roots of unity, and the conjugation action on
first cohomology. The constructions themselves do not require finite dimensionality. The file also
records how the latter two actions evaluate on restrictions of absolute Galois elements.

## Main definitions

* `TauCeti.kummerCoeffFiniteRepresentation`: the roots-of-unity representation of `Gal(L/K)`.
* `TauCeti.powerClassFiniteRep`: the natural representation on `Lˣ/(Lˣ)^ell`.
* `TauCeti.kummerH1FiniteRep`: the conjugation representation on first cohomology.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

universe u v

-- Adapted from the Tau Ceti lookahead branch
-- `lookahead/ClassFieldTheory/kummer-equiv-mixed-equivariant` (split 2).

/-! ### Power classes as a `ZMod`-module -/

/-- The `n`th power classes, written additively, form a `ZMod n`-module. -/
instance instModuleZModPowerClassQuotient {L : Type*} [Field L] (n : ℕ) :
    Module (ZMod n) (Additive (powerClassQuotient Lˣ n)) :=
  AddCommGroup.zmodModule fun x ↦ by
    induction x using Additive.rec with | ofMul x => ?_
    induction x using QuotientGroup.induction_on with | H a => ?_
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero, toMul_ofMul, ← QuotientGroup.mk_pow,
      QuotientGroup.eq_one_iff]
    exact (mem_powerSubgroup_iff n).2 ⟨a, rfl⟩

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

/-- The action of `Gal(L/K)` on `n`th power classes, induced functorially by its action on
`Lˣ`. -/
@[expose] def powerClassRepresentation (n : ℕ) :
    Representation (ZMod n) Gal(L/K) (Additive (powerClassQuotient Lˣ n)) where
  toFun tau := AddMonoidHom.toZModLinearMap n
    (MonoidHom.toAdditive (powerClassMap n (Units.map (tau : L →* L))))
  map_one' := by
    have hmap : Units.map ((1 : Gal(L/K)) : L →* L) = MonoidHom.id Lˣ := by
      ext a
      simp
    ext x
    -- Expose the additive map hidden by the representation and `ZMod`-linear-map wrappers.
    change MonoidHom.toAdditive (powerClassMap n (Units.map ((1 : Gal(L/K)) : L →* L))) x = x
    rw [hmap, powerClassMap_id]
    rfl
  map_mul' tau upsilon := by
    have hmap : Units.map ((tau * upsilon : Gal(L/K)) : L →* L) =
        (Units.map (tau : L →* L)).comp (Units.map (upsilon : L →* L)) := by
      ext a
      rfl
    ext x
    -- Expose the additive map hidden by the representation and `ZMod`-linear-map wrappers.
    change MonoidHom.toAdditive
      (powerClassMap n (Units.map ((tau * upsilon : Gal(L/K)) : L →* L))) x = _
    rw [hmap, powerClassMap_comp]
    rfl

/-- The `ZMod n[Gal(L/K)]`-representation on the `n`th power classes of `L`. -/
@[expose] def powerClassFiniteRep (n : ℕ) : Rep (ZMod n) Gal(L/K) :=
  Rep.of (powerClassRepresentation (K := K) (L := L) n)

/-- The action of a `K`-automorphism on the power-class representation is the map induced on
units. -/
@[simp]
theorem powerClassRepresentation_apply (n : ℕ) (tau : Gal(L/K))
    (x : Additive (powerClassQuotient Lˣ n)) :
    powerClassRepresentation (K := K) (L := L) n tau x =
      MonoidHom.toAdditive (powerClassMap n (Units.map (tau : L →* L))) x :=
  rfl

/-! ### Quotients of the absolute Galois action -/

section FiniteGalois

variable [Normal K L]
  (sigma : L →ₐ[K] SeparableClosure K) (n : ℕ)

/-- The roots-of-unity representation of `Gal(L/K)`, obtained by factoring the absolute Galois
action through the subgroup fixing `sigma(L)`. -/
@[expose] def kummerCoeffFiniteRepresentation
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    Representation (ZMod n) Gal(L/K) (KummerCoeff K n) := by
  let rho : Representation (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
    Representation.ofDistribMulAction (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n)
  let _ : Representation.IsTrivial
      (rho.comp sigma.fieldRange.fixingSubgroup.subtype) :=
    ⟨fun g ↦ by
      apply LinearMap.ext
      intro xi
      exact hN g g.2 xi⟩
  exact (rho.ofQuotient sigma.fieldRange.fixingSubgroup).comp
    (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm.toMonoidHom

/-- The roots-of-unity representation as an object of `Rep`. -/
def kummerCoeffFiniteRep
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    Rep (ZMod n) Gal(L/K) :=
  Rep.of (kummerCoeffFiniteRepresentation sigma n hN)

/-- The quotient roots-of-unity action, evaluated at the restriction of an absolute Galois
element, is its original action. -/
@[simp]
theorem kummerCoeffFiniteRepresentation_restrictNormalHom
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi)
    (g : AbsoluteGaloisGroup K) (xi : KummerCoeff K n) :
    kummerCoeffFiniteRepresentation sigma n hN (sigma.restrictNormalHom g) xi = g • xi := by
  let rho : Representation (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
    Representation.ofDistribMulAction (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n)
  let _ : Representation.IsTrivial
      (rho.comp sigma.fieldRange.fixingSubgroup.subtype) :=
    ⟨fun h ↦ by
      apply LinearMap.ext
      intro zeta
      exact hN h h.2 zeta⟩
  unfold kummerCoeffFiniteRepresentation
  rw [← quotientFixingSubgroupFieldRangeEquiv_mk K L sigma g]
  rw [MonoidHom.comp_apply]
  have hq : (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm.toMonoidHom
      ((quotientFixingSubgroupFieldRangeEquiv K L sigma)
        (g : AbsoluteGaloisGroup K ⧸ sigma.fieldRange.fixingSubgroup)) = g :=
    (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm_apply_apply _
  rw [hq, Representation.ofQuotient_coe_apply]
  rfl

/-- The absolute Galois group acts trivially on the constant coefficient module. -/
local instance : DistribMulAction (AbsoluteGaloisGroup K) (ZMod n) :=
  trivialZModAction n (AbsoluteGaloisGroup K)

local instance : ContinuousSMul (AbsoluteGaloisGroup K) (ZMod n) :=
  ⟨continuous_snd⟩

/-- The conjugation action of the absolute Galois group on first cohomology, as a linear
representation over `ZMod n`. -/
def kummerH1AbsoluteRepresentation :
    Representation (ZMod n) (AbsoluteGaloisGroup K)
      (H1 sigma.fieldRange.fixingSubgroup (ZMod n)) where
  toFun g := AddMonoidHom.toZModLinearMap n
    (ContCohomology.explicitConj1 sigma.fieldRange.fixingSubgroup g)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

/-- The conjugation representation on `H¹` is trivial on the subgroup acting by inner
automorphisms. -/
instance instIsTrivialKummerH1AbsoluteRepresentation : Representation.IsTrivial
    ((kummerH1AbsoluteRepresentation sigma n).comp
      sigma.fieldRange.fixingSubgroup.subtype) where
  out g := by
    ext x
    exact ContCohomology.smul_eq_self_of_mem sigma.fieldRange.fixingSubgroup g x

/-- The `Gal(L/K)`-representation on `H¹(Gal(Kˢ/sigma(L)), ZMod n)` induced by conjugation. -/
@[expose] def kummerH1FiniteRepresentation :
    Representation (ZMod n) Gal(L/K)
      (H1 sigma.fieldRange.fixingSubgroup (ZMod n)) :=
  ((kummerH1AbsoluteRepresentation sigma n).ofQuotient
      sigma.fieldRange.fixingSubgroup).comp
    (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm.toMonoidHom

/-- The finite-layer first-cohomology representation as an object of `Rep`. -/
def kummerH1FiniteRep : Rep (ZMod n) Gal(L/K) :=
  Rep.of (kummerH1FiniteRepresentation sigma n)

/-- The finite-layer cohomology action, evaluated at the restriction of an absolute Galois
element, is conjugation by that element. -/
@[simp]
theorem kummerH1FiniteRepresentation_restrictNormalHom (g : AbsoluteGaloisGroup K)
    (x : H1 sigma.fieldRange.fixingSubgroup (ZMod n)) :
    kummerH1FiniteRepresentation sigma n (sigma.restrictNormalHom g) x = g • x := by
  unfold kummerH1FiniteRepresentation
  rw [← quotientFixingSubgroupFieldRangeEquiv_mk K L sigma g]
  rw [MonoidHom.comp_apply]
  have hq : (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm.toMonoidHom
      ((quotientFixingSubgroupFieldRangeEquiv K L sigma)
        (g : AbsoluteGaloisGroup K ⧸ sigma.fieldRange.fixingSubgroup)) = g :=
    (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm_apply_apply _
  rw [hq, Representation.ofQuotient_coe_apply]
  rfl

end FiniteGalois

end TauCeti
