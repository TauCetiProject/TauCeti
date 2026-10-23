/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.QuotientSpecialIsogeny
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Tits.Carrier
public import TauCeti.GroupTheory.FixedPointCandidate

/-!
# The Tits Steinberg map and candidate group

The Tits index uses the exceptional endomorphism itself, the first odd iterate of the
characteristic-two F4 special isogeny. Its candidate is the derived subgroup of the fixed points
modulo the centre of that derived subgroup.

The ambient group consists of algebraic-closure points of the explicit prime-field short-root
carrier. A comparison with the pinned simply connected F4 group scheme requires an isomorphism
preserving the root subgroups and exceptional endomorphism.
No finiteness, perfectness, or simplicity
is assumed or proved here.
See Carter, *Simple Groups of Lie Type*, §14.
-/

public section

namespace TauCeti.TitsLieIndex

noncomputable section

variable (d : TitsLieIndex)

/-- The Tits Steinberg endomorphism is the exceptional endomorphism itself. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.specialIsogeny d.1.Closure

/-- The Tits Steinberg map is the characteristic-two carrier's special isogeny. -/
theorem steinberg_def :
    d.steinberg = F4ShortRoot.PrimeField.specialIsogeny d.1.Closure := by rfl

/-- The Tits map is the index's recorded odd iterate, whose exponent is one. -/
theorem steinberg_eq_specialIsogeny_pow :
    d.steinberg =
      -- Keep the carrier's endomorphism monoid so powers mean composition.
      (show Monoid.End _ from F4ShortRoot.PrimeField.specialIsogeny d.1.Closure) ^
        d.1.fieldExponent := by
  rw [fieldExponent_eq_one, pow_one, steinberg_def]

/-- Squaring the Tits Steinberg map gives the prime-field Frobenius. -/
@[simp] theorem steinberg_steinberg (g : d.AmbientGroup) :
    d.steinberg (d.steinberg g) = d.frobenius g := by
  rw [steinberg_def, frobenius_def, F4ShortRoot.PrimeField.specialIsogeny_specialIsogeny]

private theorem carrierNode_lengthPerm (i : Fin d.1.rank) :
    finCongr d.rank_eq_four (d.toSuzukiReeIndex.lengthPerm i) =
      Fin.revPerm (finCongr d.rank_eq_four i) := by
  obtain rfl := d.eq_of
  simp [toSuzukiReeIndex, SuzukiReeIndex.lengthPerm_tits, Equiv.permCongr_def,
    lengthPermF4_apply]

private theorem carrierExponent (i : Fin d.1.rank) :
    F4ShortRoot.isogenyExponent (.inl (finCongr d.rank_eq_four i)) =
      d.toSuzukiReeIndex.exponent i := by
  rw [exponent_eq]
  have h : ∀ j : Fin 4, F4ShortRoot.isogenyExponent (.inl j) =
      if (j : ℕ) < 2 then 1 else 2 := by decide
  exact h (finCongr d.rank_eq_four i)

/-- The Tits map exchanges the numbered simple roots, with exponent one on long roots and
two on short roots, matching the validated index. -/
@[simp] theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  rw [steinberg_def, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, simpleRootSubgroup_def,
    carrierNode_lengthPerm, ← carrierExponent]
  simp only [F4ShortRoot.isogenyReverse, Sum.map_inl]

/-- The fixed subgroup of the exceptional F4 endomorphism at the Tits index. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- The Tits candidate is the derived subgroup of the fixed points modulo its own centre.
No finiteness or simplicity assertion is part of this definition. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

example : _root_.Group d.Group := inferInstance

end

end TauCeti.TitsLieIndex
