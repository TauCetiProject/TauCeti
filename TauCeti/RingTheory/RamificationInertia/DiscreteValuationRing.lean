/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Ramification and inertia over local rings and discrete valuation rings

Let `S → T` be a local homomorphism from a local ring to a discrete valuation ring such that the
maximal ideal `𝔪_S` of `S` does not map to zero. Then `𝔪_S T` is a nonzero ideal of `T`, hence a
power `𝔪_T ^ e` of the maximal ideal of `T`, and `e` is Mathlib's ramification index
`(maximalIdeal T).ramificationIdx S`, the length of `T ⧸ 𝔪_S T`. For an extension of discrete
valuation rings this is the ramification index of Stacks, Definition 15.113.1 (09E4): the
exponent `e` with `π_S = u π_T ^ e` for uniformizers `π_S`, `π_T` and a unit `u`.

This file also records the companion local-ring inertia-degree identity
`(maximalIdeal B).inertiaDeg A = Module.finrank (ResidueField A) (ResidueField B)` and the
height-one maximal-ideal bridge for discrete valuation rings.

## Main results

* `TauCeti.IsLocalRing.quotientMaximalIdealEquivResidueField` and
  `TauCeti.IsLocalRing.inertiaDeg_maximalIdeal`: the canonical ring equivalence
  `R ⧸ maximalIdeal R ≃+* ResidueField R`, and the resulting identity
  `(maximalIdeal B).inertiaDeg A = Module.finrank (ResidueField A) (ResidueField B)` for a local
  homomorphism `A → B` of local rings.
* `TauCeti.IsDiscreteValuationRing.asIdeal_maximalIdeal` and
  `TauCeti.IsDiscreteValuationRing.maximalIdeal_liesOver`: the underlying ideal of
  `IsDiscreteValuationRing.maximalIdeal A` is `IsLocalRing.maximalIdeal A`, and for a local
  homomorphism of DVRs `A → B` it lies over that of `A`.
* `TauCeti.IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx`: `𝔪_S T = 𝔪_T ^ e` with
  `e` the ramification index of `𝔪_T` over `S`.
* `TauCeti.IsDiscreteValuationRing.ramificationIdx_eq_of_map_maximalIdeal_eq_pow`: the index equals
  any exponent satisfying this maximal-ideal identity.

## References

* [Stacks Project, Definition 15.113.1](https://stacks.math.columbia.edu/tag/09E4).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Bounding/Divisors.lean`:
  `map_maximalIdeal_eq_pow_ramificationIdx` is the local form of its
  `Pcf.heightOneRamificationIdx_eq_dvrExponent` with `Pcf.heightOneDvrExponent_spec`, stated
  there at a height-one prime of a finite extension of normal Noetherian domains.
-/

public section

open IsLocalRing IsDiscreteValuationRing

namespace TauCeti.IsLocalRing

/-- The canonical ring equivalence `R ⧸ maximalIdeal R ≃+* ResidueField R` induced by
`IsLocalRing.residue`. -/
noncomputable def quotientMaximalIdealEquivResidueField (R : Type*) [CommRing R]
    [IsLocalRing R] : R ⧸ IsLocalRing.maximalIdeal R ≃+* ResidueField R :=
  (Ideal.quotEquivOfEq (IsLocalRing.ker_residue (R := R)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (IsLocalRing.residue_surjective (R := R)))

/-- `quotientMaximalIdealEquivResidueField` maps a quotient class to `IsLocalRing.residue`. -/
@[simp]
theorem quotientMaximalIdealEquivResidueField_mk {R : Type*} [CommRing R] [IsLocalRing R]
    (a : R) :
    quotientMaximalIdealEquivResidueField R (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) a) =
      IsLocalRing.residue R a := by
  simp [quotientMaximalIdealEquivResidueField]

/-- For a local homomorphism `A → B` between local rings, the inertia degree of the maximal ideal of
`B` over `A` equals the degree of the residue-field extension. -/
theorem inertiaDeg_maximalIdeal {A B : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] :
    (IsLocalRing.maximalIdeal B).inertiaDeg A =
      Module.finrank (ResidueField A) (ResidueField B) := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)]
  refine Algebra.finrank_eq_of_equiv_equiv
    (quotientMaximalIdealEquivResidueField A) (quotientMaximalIdealEquivResidueField B)
    (RingHom.ext fun x ↦ ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    Ideal.Quotient.algebraMap_mk_of_liesOver, quotientMaximalIdealEquivResidueField_mk,
    IsLocalRing.ResidueField.algebraMap_residue]

end TauCeti.IsLocalRing

namespace TauCeti.IsDiscreteValuationRing

/-- The underlying ideal of `IsDiscreteValuationRing.maximalIdeal A` is the maximal ideal of the
local ring `A`. -/
theorem asIdeal_maximalIdeal (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    (_root_.IsDiscreteValuationRing.maximalIdeal A).asIdeal = IsLocalRing.maximalIdeal A :=
  rfl

/-- For a local homomorphism `A → B` between discrete valuation rings, the height-one maximal ideal
of `B` lies over that of `A`. -/
instance maximalIdeal_liesOver {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] :
    (_root_.IsDiscreteValuationRing.maximalIdeal B).asIdeal.LiesOver
      (_root_.IsDiscreteValuationRing.maximalIdeal A).asIdeal := by
  rw [asIdeal_maximalIdeal, asIdeal_maximalIdeal]
  infer_instance

variable {S T : Type*} [CommRing S] [CommRing T] [IsLocalRing S] [IsDomain T]
  [IsDiscreteValuationRing T] [Algebra S T] [IsLocalHom (algebraMap S T)]

/-- For a local homomorphism from a local ring `S` to a discrete valuation ring `T` under which
the maximal ideal of `S` does not vanish, `𝔪_S T = 𝔪_T ^ e` with `e` the ramification index of the
maximal ideal of `T` over `S`. -/
theorem map_maximalIdeal_eq_pow_ramificationIdx
    (h : (IsLocalRing.maximalIdeal S).map (algebraMap S T) ≠ ⊥) :
    (IsLocalRing.maximalIdeal S).map (algebraMap S T) =
      IsLocalRing.maximalIdeal T ^ (IsLocalRing.maximalIdeal T).ramificationIdx S := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible T
  obtain ⟨n, hn⟩ := ideal_eq_span_pow_irreducible h hϖ
  have hpow :
      (IsLocalRing.maximalIdeal S).map (algebraMap S T) = IsLocalRing.maximalIdeal T ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  -- The length-based ramification index agrees with the exponent-based one over the Dedekind
  -- domain `T` (`Ideal.ramificationIdx'_eq_ramificationIdx'`), and the latter is `n`.
  have hidx : (IsLocalRing.maximalIdeal T).ramificationIdx S = n := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx' (IsLocalRing.maximalIdeal S)
      (IsLocalRing.maximalIdeal T) h]
    refine Ideal.ramificationIdx'_spec hpow.le ?_
    rw [hpow]
    exact (Ideal.pow_succ_lt_pow (not_a_field T) n).not_ge
  rw [hidx, hpow]

/-- For a local homomorphism to a DVR, the exponent in a maximal-ideal power identity is the
ramification index. This is the exponent characterization of Stacks, Definition 15.113.1 (09E4),
with no DVR assumption on the base ring. -/
@[stacks 09E4 "exponent characterization with arbitrary local base ring"]
theorem ramificationIdx_eq_of_map_maximalIdeal_eq_pow {exponent : ℕ}
    (hexponent :
      (IsLocalRing.maximalIdeal S).map (algebraMap S T) =
        IsLocalRing.maximalIdeal T ^ exponent) :
    (IsLocalRing.maximalIdeal T).ramificationIdx S = exponent := by
  have hpowers : StrictAnti (fun power : ℕ ↦ IsLocalRing.maximalIdeal T ^ power) :=
    Ideal.pow_right_strictAnti (IsLocalRing.maximalIdeal T) (not_a_field T)
      (IsLocalRing.maximalIdeal.isMaximal T).ne_top
  have hmap : (IsLocalRing.maximalIdeal S).map (algebraMap S T) ≠ ⊥ := by
    rw [hexponent]
    exact ne_of_gt (lt_of_le_of_lt bot_le (hpowers (Nat.lt_succ_self exponent)))
  exact hpowers.injective ((map_maximalIdeal_eq_pow_ramificationIdx hmap).symm.trans hexponent)

end TauCeti.IsDiscreteValuationRing
