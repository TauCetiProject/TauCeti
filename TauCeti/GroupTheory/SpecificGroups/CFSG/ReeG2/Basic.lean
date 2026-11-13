/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.SpecialIsogeny
public import TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Carrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.HalfFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.OddPowerSteinberg
public import TauCeti.GroupTheory.FixedPointCandidate

/-!
# The Ree G2 Steinberg map and candidate group

The signed-minor construction gives the exceptional endomorphism of the characteristic-three
short-root carrier. Its odd power is the Steinberg map for a validated Ree G2 index. The candidate
is the derived subgroup of its fixed points modulo the centre of that derived subgroup.

The ambient group consists of algebraic-closure points of the explicit prime-field short-root
carrier. A comparison with the pinned simply connected G2 group scheme requires an isomorphism
preserving the root subgroups and exceptional endomorphism. No finiteness or simplicity is assumed
or proved here. The conventions follow Carter, *Simple Groups of Lie Type*, §12.4.

The root equations cover both positive and negative simple roots. They specialize
`G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints` and use
`SuzukiReeIndex.pow_fieldExponent_apply_lengthPerm` for the odd iterate, following A.-C. Radu,
*On the cohomology of the Ree groups and kernels of exceptional isogenies*,
arXiv:2108.06291v2, §2.2.
-/

/- Adapted from the family interface in
`TauCeti/GroupTheory/SpecificGroups/CFSG/Suzuki/Basic.lean`. -/

public section

namespace TauCeti.ReeG2LieIndex

noncomputable section

variable (d : ReeG2LieIndex)

/-- The exceptional endomorphism of the Ree G2 ambient carrier. -/
def halfFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.specialIsogeny d.1.Closure

/-- The half-Frobenius is the characteristic-three carrier's special isogeny. -/
theorem halfFrobenius_def :
    d.halfFrobenius = G2ShortRoot.PrimeField.specialIsogeny d.1.Closure := by rfl

/-- The half-Frobenius squares to the prime-field Frobenius. -/
@[simp] theorem halfFrobenius_halfFrobenius (g : d.AmbientGroup) :
    d.halfFrobenius (d.halfFrobenius g) = d.primeFrobenius g := by
  rw [halfFrobenius_def, primeFrobenius_def,
    G2ShortRoot.PrimeField.specialIsogeny_specialIsogeny]

/-- The carrier's positive-root exponent agrees with the indexed source-root exponent. -/
theorem specialIsogenyExponent_inl_finCongr (i : Fin d.1.rank) :
    G2ShortRoot.PrimeField.specialIsogenyExponent (.inl (finCongr d.rank_eq_two i)) =
      d.toSuzukiReeIndex.exponent i := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  fin_cases i
  · have h := SuzukiReeIndex.exponent_of_not_isLongSimpleRoot
      (of m hvalid).toSuzukiReeIndex
      ⟨0, by simp [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType]⟩ (by
        rw [DynkinType.isLongSimpleRoot_congr (LieTypeIndex.dynkinType_reeG2 m),
          DynkinType.isLongSimpleRoot_G2]
        exact Nat.zero_ne_one)
    rw [(of m hvalid).characteristic_eq_three] at h
    simpa using h.symm
  · have h := SuzukiReeIndex.exponent_of_isLongSimpleRoot
      (of m hvalid).toSuzukiReeIndex
      ⟨1, by simp [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType]⟩ (by
        rw [DynkinType.isLongSimpleRoot_congr (LieTypeIndex.dynkinType_reeG2 m),
          DynkinType.isLongSimpleRoot_G2]
        exact finCongr_apply_coe _ _)
    simpa [Fin.ext_iff] using h.symm

/-- The half-Frobenius has the index's own root permutation and long/short exponents. -/
@[simp] theorem halfFrobenius_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  obtain ⟨t, rfl⟩ := Multiplicative.ofAdd.surjective u
  rw [halfFrobenius_def, simpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, simpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogenyRootIndex_inl,
    finCongr_lengthPerm, ← specialIsogenyExponent_inl_finCongr]
  simp only [toAdd_ofAdd]

/-- The exceptional endomorphism exchanges negative simple roots with the indexed source-root
exponent: three on the short root and one on the long root. -/
@[simp]
theorem halfFrobenius_negativeSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.negativeSimpleRootSubgroup i u) =
      d.negativeSimpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  obtain ⟨t, rfl⟩ := Multiplicative.ofAdd.surjective u
  rw [halfFrobenius_def, negativeSimpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, negativeSimpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogenyRootIndex_inr, finCongr_lengthPerm,
    ← specialIsogenyExponent_inl_finCongr]
  simp only [G2ShortRoot.PrimeField.specialIsogenyExponent_inr,
    G2ShortRoot.PrimeField.specialIsogenyExponent_inl, toAdd_ofAdd]

/-- The Steinberg endomorphism is the recorded odd power of the exceptional endomorphism. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  HPow.hPow (α := Monoid.End d.AmbientGroup) d.halfFrobenius d.1.fieldExponent

/-- The Steinberg map is the recorded power in the monoid of endomorphisms. -/
theorem steinberg_def :
    d.steinberg = HPow.hPow (α := Monoid.End d.AmbientGroup)
      d.halfFrobenius d.1.fieldExponent := by rfl

/-- The square of the Steinberg endomorphism is the field-order Frobenius. -/
@[simp] theorem steinberg_steinberg (g : d.AmbientGroup) :
    d.steinberg (d.steinberg g) = d.frobenius g := by
  rw [d.frobenius_eq_primeFrobenius_pow]
  exact d.toSuzukiReeIndex.pow_fieldExponent_pow_fieldExponent d.halfFrobenius_halfFrobenius g

/-- The odd iterate exchanges the numbered roots with the prescribed parameter power. -/
@[simp] theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^
          (d.1.characteristic ^ d.toSuzukiReeIndex.halfExponent *
            d.toSuzukiReeIndex.exponent i))) :=
  d.toSuzukiReeIndex.pow_fieldExponent_apply_lengthPerm
    (x := fun j t => d.simpleRootSubgroup j t)
    (fun j t => d.halfFrobenius_simpleRootSubgroup j t) i u

/-- The Ree Steinberg map has parameter exponent `p^m * aᵢ` on each negative simple root,
where `aᵢ` is the exceptional exponent at the source node. -/
@[simp]
theorem steinberg_negativeSimpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.negativeSimpleRootSubgroup i u) =
      d.negativeSimpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^
          (d.1.characteristic ^ d.toSuzukiReeIndex.halfExponent *
            d.toSuzukiReeIndex.exponent i))) := by
  rw [steinberg_def]
  exact d.toSuzukiReeIndex.pow_fieldExponent_apply_lengthPerm
    (x := fun j t => d.negativeSimpleRootSubgroup j t)
    (fun j t => d.halfFrobenius_negativeSimpleRootSubgroup j t) i u

/-- The fixed subgroup of the Ree G2 Steinberg endomorphism. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- The Ree G2 candidate: the derived subgroup of the Steinberg fixed points modulo its own
centre. This definition carries no assertion of finiteness, perfectness, or simplicity. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

example : _root_.Group d.Group := inferInstance

end

end TauCeti.ReeG2LieIndex
