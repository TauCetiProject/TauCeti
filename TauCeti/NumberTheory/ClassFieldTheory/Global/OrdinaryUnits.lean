/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SIdeles
import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

/-!
# Ordinary units as S-units with no allowed finite denominators

For an extension of number fields `L/K`, the S-units with `S = ∅` are the units of `𝓞 L`.
The identification respects the action of `Aut(L/K)`, so it is an isomorphism of integral
representations, rather than just an isomorphism of the underlying groups. In particular, their
Herbrand quotients agree. This identifies the ordinary-unit term in the valuation sequence used
to calculate the Herbrand quotient of S-units.

The underlying group identification is `Set.unitEmptyEquivUnits`; the action on integer units
is Mathlib's `Units.mulDistribMulActionRight` applied to the action on the ring of integers.

## Reference

* J. S. Milne, *Class Field Theory*, Chapter VII, §3 (the S-unit valuation sequence).
-/

public noncomputable section

open CategoryTheory IsDedekindDomain NumberField
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Pointwise

namespace TauCeti.ClassFieldTheory

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- The S-units with no allowed finite denominators and the units of the ring of integers are
canonically isomorphic as integral representations of `Aut(L/K)`. -/
def sUnitsEmptyIsoUnits :
    sUnitsRep L (∅ : Set (HeightOneSpectrum (𝓞 K))) ≅
      Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ := by
  let e := (MulEquiv.subgroupCongr (congrArg (fun S : Set (HeightOneSpectrum (𝓞 L)) =>
    S.unit L) (primesAbove_empty (𝓞 K) (𝓞 L)))).trans (Set.unitEmptyEquivUnits L)
  have he (u : (primesAbove (𝓞 K) (𝓞 L) ∅).unit L) :
      algebraMap (𝓞 L) L (e u : 𝓞 L) = (u : Lˣ) := by
    simp [e]
  refine Rep.mkIso (Representation.Equiv.mk e.toAdditive.toIntLinearEquiv ?_)
  intro σ
  apply LinearMap.ext
  intro u
  apply Additive.toMul.injective
  apply Units.ext
  apply IsFractionRing.injective (𝓞 L) L
  simp only [LinearMap.comp_apply, Representation.ofMulDistribMulAction_apply_apply]
  -- Read the additive adapters on their underlying multiplicative groups.
  change algebraMap (𝓞 L) L (e (σ • u.toMul) : 𝓞 L) =
    algebraMap (𝓞 L) L (σ • e u.toMul : 𝓞 L)
  simp [he]

/-- The forward identification preserves the underlying element of the number field. -/
@[simp]
theorem algebraMap_sUnitsEmptyIsoUnits_hom_apply
    (u : sUnitsRep L (∅ : Set (HeightOneSpectrum (𝓞 K)))) :
    algebraMap (𝓞 L) L
        (Additive.toMul (α := (𝓞 L)ˣ)
          ((sUnitsEmptyIsoUnits (K := K) (L := L)).hom.hom u) : 𝓞 L) =
      (Additive.toMul (α := (primesAbove (𝓞 K) (𝓞 L) ∅).unit L) u : Lˣ) := by
  -- The representation and additive adapters are identities on elements; only the underlying
  -- group equivalence needs its characteristic formula.
  change algebraMap (𝓞 L) L
    (Set.unitEmptyEquivUnits L
      ((MulEquiv.subgroupCongr (congrArg (fun S : Set (HeightOneSpectrum (𝓞 L)) =>
        S.unit L) (primesAbove_empty (𝓞 K) (𝓞 L))))
          (Additive.toMul (α := (primesAbove (𝓞 K) (𝓞 L) ∅).unit L) u)) : 𝓞 L) = _
  simp

/-- The inverse identification preserves the underlying element of the number field. -/
@[simp]
theorem coe_sUnitsEmptyIsoUnits_inv_apply
    (u : Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ) :
    (Additive.toMul (α := (primesAbove (𝓞 K) (𝓞 L) ∅).unit L)
        ((sUnitsEmptyIsoUnits (K := K) (L := L)).inv.hom u) : Lˣ) =
      Units.map (algebraMap (𝓞 L) L).toMonoidHom (Additive.toMul (α := (𝓞 L)ˣ) u) := by
  apply Units.ext
  have h := algebraMap_sUnitsEmptyIsoUnits_hom_apply
    ((sUnitsEmptyIsoUnits (K := K) (L := L)).inv.hom u)
  rw [Rep.hom_inv_apply] at h
  -- `Units.map` applies the algebra map to the value of the unit.
  change _ = algebraMap (𝓞 L) L (Additive.toMul (α := (𝓞 L)ˣ) u : 𝓞 L)
  exact h.symm

/-- The empty-set S-unit term in a Herbrand-quotient computation can be replaced by the ordinary
units with their Galois action. -/
theorem herbrandQuotient_sUnitsRep_empty :
    TateCohomology.herbrandQuotient (sUnitsRep L (∅ : Set (HeightOneSpectrum (𝓞 K)))) =
      TateCohomology.herbrandQuotient (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (𝓞 L)ˣ) :=
  TateCohomology.herbrandQuotient_eq_of_iso sUnitsEmptyIsoUnits

end TauCeti.ClassFieldTheory
