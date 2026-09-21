/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Finite.RootsOfUnity
public import TauCeti.RingTheory.RootsOfUnity.Henselian
public import TauCeti.RingTheory.RootsOfUnity.IntegrallyClosed

/-!
# The Teichmüller lift of a Henselian local ring with finite residue field

Let `R` be a Henselian local ring whose residue field `k` is finite, of cardinality `q`. Reduction
`Rˣ → kˣ` identifies the `(q - 1)`-st roots of unity on both sides, because `q - 1` is a
unit in `R`. Since every unit of `k` is a `(q - 1)`-st root of unity, the inverse equivalence gives
the *Teichmüller lift* `teichmuller R : kˣ →* Rˣ`.

Thus this construction reuses the general Henselian roots-of-unity equivalence. Its public
characterization says that the lift of `x` is the unique `(q - 1)`-st root of unity reducing to
`x`; in particular its image is exactly `μ_{q-1}(R)`.

A ring `R` that is moreover integrally closed in an `R`-algebra `A` has the same `(q - 1)`-st
roots of unity as `A`, since roots of unity are integral. This gives the corresponding
identification `μ_{q-1}(A) ≃* kˣ`; the case of a fraction ring of `R` is the one used for local
fields.

## Main results

* `TauCeti.IsLocalRing.teichmuller`: the Teichmüller lift `kˣ →* Rˣ`.
* `TauCeti.IsLocalRing.teichmuller_eq_iff`: the characterization of its values.
* `TauCeti.IsLocalRing.eq_teichmuller`: it is the only multiplicative section of reduction whose
  values are `(q - 1)`-st roots of unity.
* `TauCeti.IsLocalRing.range_teichmuller`: its image is exactly `μ_{q-1}(R)`.
* `TauCeti.IsLocalRing.rootsOfUnityMulEquivUnitsResidueField`: reduction is an isomorphism
  `μ_{q-1}(R) ≃* kˣ`.
* `TauCeti.IsLocalRing.rootsOfUnityAlgebraMulEquivUnitsResidueField`: if `R` is integrally
  closed in an `R`-algebra `A`, then `μ_{q-1}(A) ≃* kˣ`.

## References

* J.-P. Serre, *Corps Locaux*, II §4.
* J. Neukirch, *Algebraic Number Theory*, II §5.
-/

public section

noncomputable section

namespace TauCeti.IsLocalRing

open _root_.IsLocalRing

variable (R : Type*) [CommRing R] [HenselianLocalRing R] [Finite (ResidueField R)]

/-- A finite field has at least two elements, so the exponent `q - 1` is nonzero. -/
theorem card_residueField_sub_one_ne_zero : Nat.card (ResidueField R) - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt Finite.one_lt_card

private theorem isUnit_card_residueField_sub_one :
    IsUnit ((Nat.card (ResidueField R) - 1 : ℕ) : R) := by
  rw [← residue_ne_zero_iff_isUnit, map_natCast,
    TauCeti.natCast_natCard_sub_one_eq_neg_one, neg_ne_zero]
  exact one_ne_zero

/-- Reduction identifies the `(q - 1)`-st roots of unity of `R` with the units of its residue
field. -/
noncomputable def rootsOfUnityMulEquivUnitsResidueField :
    rootsOfUnity (Nat.card (ResidueField R) - 1) R ≃* (ResidueField R)ˣ :=
  (TauCeti.rootsOfUnityEquivResidueField (isUnit_card_residueField_sub_one R)).trans
    (TauCeti.rootsOfUnityEquivUnits (ResidueField R))

@[simp] theorem coe_rootsOfUnityMulEquivUnitsResidueField
    (u : rootsOfUnity (Nat.card (ResidueField R) - 1) R) :
    (rootsOfUnityMulEquivUnitsResidueField R u : ResidueField R) = residue R (u : Rˣ) := by
  rw [rootsOfUnityMulEquivUnitsResidueField, MulEquiv.trans_apply,
    TauCeti.rootsOfUnityEquivUnits_apply]
  exact TauCeti.coe_rootsOfUnityEquivResidueField _ u

/-- The **Teichmüller lift** of a Henselian local ring `R` with finite residue field `k` of
cardinality `q`: the multiplicative section of reduction that sends `x` to the unique
`(q - 1)`-st root of unity above `x`. -/
noncomputable def teichmuller : (ResidueField R)ˣ →* Rˣ :=
  (rootsOfUnity (Nat.card (ResidueField R) - 1) R).subtype.comp
    (rootsOfUnityMulEquivUnitsResidueField R).symm.toMonoidHom

/-- The Teichmüller lift is the inverse of the roots-of-unity equivalence, read in `Rˣ`. This
unfolds the definition of `teichmuller`; stating it once lets the proofs below work with the
equivalence. -/
@[simp] theorem rootsOfUnityMulEquivUnitsResidueField_symm_apply (x : (ResidueField R)ˣ) :
    ((rootsOfUnityMulEquivUnitsResidueField R).symm x : Rˣ) = teichmuller R x := by
  rw [teichmuller, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply]

/-- The Teichmüller lift takes its values in the `(q - 1)`-st roots of unity. -/
theorem teichmuller_pow_card_sub_one (x : (ResidueField R)ˣ) :
    teichmuller R x ^ (Nat.card (ResidueField R) - 1) = 1 := by
  rw [← rootsOfUnityMulEquivUnitsResidueField_symm_apply]
  exact (mem_rootsOfUnity _ _).1 ((rootsOfUnityMulEquivUnitsResidueField R).symm x).2

/-- The simplifier-normalized form of the torsion property of the Teichmüller lift, stated with
`Fintype.card` rather than `Nat.card`. -/
@[simp] theorem teichmuller_pow_fintype_card_sub_one (x : (ResidueField R)ˣ) :
    teichmuller R x ^ (@Fintype.card (ResidueField R) (Fintype.ofFinite _) - 1) = 1 := by
  rw [← @Nat.card_eq_fintype_card (ResidueField R) (Fintype.ofFinite _)]
  exact teichmuller_pow_card_sub_one R x

/-- The Teichmüller lift is a section of reduction. -/
@[simp] theorem residue_teichmuller (x : (ResidueField R)ˣ) :
    residue R (teichmuller R x : R) = x := by
  rw [← rootsOfUnityMulEquivUnitsResidueField_symm_apply,
    ← coe_rootsOfUnityMulEquivUnitsResidueField, MulEquiv.apply_symm_apply]

/-- The Teichmüller lift is a section of reduction, read in the unit group of the residue field. -/
@[simp] theorem unitsMap_residue_teichmuller (x : (ResidueField R)ˣ) :
    Units.map (residue R : R →* ResidueField R) (teichmuller R x) = x :=
  Units.ext (residue_teichmuller R x)

/-- The Teichmüller lift of `x` is the unique root of unity of order dividing `q - 1` above
`x`. -/
theorem teichmuller_eq_iff {x : (ResidueField R)ˣ} {u : Rˣ} :
    teichmuller R x = u ↔
      u ^ (Nat.card (ResidueField R) - 1) = 1 ∧ residue R (u : R) = x := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact ⟨teichmuller_pow_card_sub_one R x, residue_teichmuller R x⟩
  · rintro ⟨hpow, hres⟩
    let v : rootsOfUnity (Nat.card (ResidueField R) - 1) R := ⟨u, hpow⟩
    have hv : rootsOfUnityMulEquivUnitsResidueField R v = x := by
      apply Units.ext
      simpa only [coe_rootsOfUnityMulEquivUnitsResidueField] using hres
    have hv' := congrArg (rootsOfUnityMulEquivUnitsResidueField R).symm hv
    rw [MulEquiv.symm_apply_apply] at hv'
    rw [← rootsOfUnityMulEquivUnitsResidueField_symm_apply, ← hv']

/-- The Teichmüller lift is injective, being a section of reduction. -/
theorem teichmuller_injective : Function.Injective (teichmuller R) := fun x y h ↦ by
  simpa using congrArg (Units.map (residue R : R →* ResidueField R)) h

/-- The Teichmüller lift is the only multiplicative section of reduction all of whose values are
`q - 1`-st roots of unity. -/
theorem eq_teichmuller (s : (ResidueField R)ˣ →* Rˣ) (hsec : ∀ x, residue R (s x : R) = x)
    (htor : ∀ x, s x ^ (Nat.card (ResidueField R) - 1) = 1) : s = teichmuller R :=
  MonoidHom.ext fun x ↦ ((teichmuller_eq_iff R).2 ⟨htor x, hsec x⟩).symm

/-- The image of the Teichmüller lift is `μ_{q-1}(R)`. -/
theorem range_teichmuller :
    (teichmuller R).range = rootsOfUnity (Nat.card (ResidueField R) - 1) R := by
  ext u
  simp only [MonoidHom.mem_range, mem_rootsOfUnity]
  refine ⟨?_, fun h ↦ ⟨rootsOfUnityMulEquivUnitsResidueField R ⟨u, h⟩, ?_⟩⟩
  · rintro ⟨x, rfl⟩
    exact teichmuller_pow_card_sub_one R x
  · rw [← rootsOfUnityMulEquivUnitsResidueField_symm_apply, MulEquiv.symm_apply_apply]

/-- A Henselian local ring with residue field of cardinality `q` has exactly `q - 1` roots of
unity of order dividing `q - 1`. -/
theorem card_rootsOfUnity :
    Nat.card (rootsOfUnity (Nat.card (ResidueField R) - 1) R) =
      Nat.card (ResidueField R) - 1 := by
  rw [Nat.card_congr (rootsOfUnityMulEquivUnitsResidueField R).toEquiv, Nat.card_units]

section IsIntegrallyClosedIn

variable (A : Type*) [CommRing A] [Algebra R A] [IsIntegrallyClosedIn R A]

/-- If `R` is integrally closed in an `R`-algebra `A`, reduction identifies `μ_{q-1}(A)` with
the unit group of the residue field: the roots of unity of `A` are integral over `R`, hence
already lie in `R`. -/
noncomputable def rootsOfUnityAlgebraMulEquivUnitsResidueField :
    rootsOfUnity (Nat.card (ResidueField R) - 1) A ≃* (ResidueField R)ˣ :=
  haveI : NeZero (Nat.card (ResidueField R) - 1) := ⟨card_residueField_sub_one_ne_zero R⟩
  (IsIntegrallyClosedIn.rootsOfUnityMulEquiv R A _).symm.trans
    (rootsOfUnityMulEquivUnitsResidueField R)

@[simp] theorem rootsOfUnityAlgebraMulEquivUnitsResidueField_symm_apply
    (x : (ResidueField R)ˣ) :
    (((rootsOfUnityAlgebraMulEquivUnitsResidueField R A).symm x : Aˣ) : A) =
      algebraMap R A (teichmuller R x : R) := by
  have : NeZero (Nat.card (ResidueField R) - 1) := ⟨card_residueField_sub_one_ne_zero R⟩
  simp [rootsOfUnityAlgebraMulEquivUnitsResidueField]

end IsIntegrallyClosedIn

end TauCeti.IsLocalRing
