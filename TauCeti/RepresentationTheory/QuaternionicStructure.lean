/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic

/-!
# Quaternionic structures on a representation

Classically, a **quaternionic structure** on a representation `ρ` of `G` on a complex vector
space `V` is a conjugate-linear map `J : V →ₗ⋆[ℂ] V` with `J (J v) = -v` that commutes with the
action.  It is the `-1` case of the Frobenius-Schur reality trichotomy; the `1` case is a real
structure, a conjugate-linear *involution* commuting with the action,
`Representation.IsRealStructure` in `TauCeti/RepresentationTheory/RealForm.lean`.  The predicate
is stated over any commutative star ring `k`, semilinear for `starRingEnd k`; the classical notion
is the case `k = ℂ`.

Up to the sign of the square the two predicates are alike, and the constructions in
`TauCeti/RepresentationTheory/InvariantForm/StructureMap.lean` treat them together.  What separates
them over `ℂ` is that a quaternionic structure has no nonzero fixed vector, so, unlike a real
structure, it cuts out no real form; that is why the real-form theory lives beside
`Representation.IsRealStructure` while this predicate stands on its own.  Over a general `k` this
separation needs `2` to act injectively on `V`: it holds when `2 ≠ 0` in a cancellative `k` and
`V` is torsion-free (`Representation.IsQuaternionicStructure.apply_eq_self_iff`), and it fails in
characteristic `2`, where `-v = v` and `J (J v) = -v` just says that `J` is an involution.

Only the predicate and the two elementary facts about it are here, so that stating a quaternionic
structure costs no invariant-form or finite-dimensional machinery.  Its equivalence with a
nondegenerate invariant alternating form, and the reading of the Frobenius-Schur value `-1` off it,
are in
`TauCeti/RepresentationTheory/InvariantForm/StructureMap.lean` and
`TauCeti/RepresentationTheory/Compact/FrobeniusSchur/StructureMap.lean`.

## Main definitions

* `Representation.IsQuaternionicStructure`: a `starRingEnd k`-semilinear `J` with `J (J v) = -v`
  commuting with the action.

## Main results

* `Representation.IsQuaternionicStructure.bijective`: a quaternionic structure is bijective.
* `Representation.IsQuaternionicStructure.apply_eq_self_iff`: when `2 ≠ 0` in a cancellative `k`
  and `V` is torsion-free (for instance over `ℂ`), a quaternionic structure fixes only `0`.

## References

* T. Bröcker, T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter II, §6.
-/

public section

namespace Representation

variable {k G V : Type*} [CommSemiring k] [StarRing k] [Monoid G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

variable (ρ) in
/-- A **quaternionic structure** on a representation over a commutative star ring `k`: a map `J` of
the underlying space, semilinear for `starRingEnd k`, that squares to `-1` and commutes with the
action.  For `k = ℂ` it is a conjugate-linear map, and the predicate is the `-1` case of the
Frobenius-Schur reality trichotomy, `Representation.IsRealStructure` being the `1` case.

When `2` acts injectively on `V` (for instance over `ℂ`), a quaternionic structure has no nonzero
fixed vector (`Representation.IsQuaternionicStructure.apply_eq_self_iff`), so no real form attaches
to it; in characteristic `2` the condition `J (J v) = -v` just says that `J` is an involution.
The map is carried unbundled, matching `Representation.IsRealStructure` and
`TauCeti.Representation.IsInvariantForm`. -/
structure IsQuaternionicStructure (J : V →ₛₗ[starRingEnd k] V) : Prop where
  /-- The map squares to `-1`. -/
  sq_eq_neg (v : V) : J (J v) = -v
  /-- The map intertwines the action with itself. -/
  isIntertwining (g : G) (v : V) : J (ρ g v) = ρ g (J v)

-- `grind` splits a witness in the context into its two fields, so both defining equations are
-- available to it without the projections being invoked by hand.  `sq_eq_neg` cannot be registered
-- as a rewrite rule on its own: neither `G` nor `ρ` occurs in it, so `grind =` rejects it.
attribute [grind cases] IsQuaternionicStructure

-- The intertwining equation moves `J` past the action, which is the normal form the constructions
-- downstream use; `ρ` occurs in its left-hand side, so `simp` can instantiate it.  `sq_eq_neg`
-- cannot be tagged for the reason `grind =` rejects it: its left-hand side `J (J v)` mentions
-- neither `G` nor `ρ`, so `simpNF` reports that the lemma "will never apply".  It is passed
-- explicitly, `simp [h.sq_eq_neg]`, as `Representation.IsRealStructure.involutive` is.
attribute [simp] IsQuaternionicStructure.isIntertwining

namespace IsQuaternionicStructure

variable {J : V →ₛₗ[starRingEnd k] V} (h : IsQuaternionicStructure ρ J)

include h

/-- **A quaternionic structure is bijective**, with `-J` as its two-sided inverse -- the analogue
of the bijectivity a real structure has as an involution. -/
theorem bijective : Function.Bijective ⇑J :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun v => -J v, fun v => by simp [h.sq_eq_neg], fun v => by simp [h.sq_eq_neg]⟩

/-- **A quaternionic structure fixes only `0`**: a fixed vector satisfies `v = -v`, so
`(2 : k) • v = 0`, which forces `v = 0` once `2` is nonzero in a cancellative `k` acting on a
torsion-free `V`, as over `ℂ`.  So, unlike a real structure, a quaternionic structure cuts out no
real form. -/
theorem apply_eq_self_iff [IsCancelMulZero k] [NeZero (2 : k)] [Module.IsTorsionFree k V]
    {v : V} : J v = v ↔ v = 0 := by
  refine ⟨fun hv => (smul_eq_zero_iff_right (two_ne_zero' k)).mp ?_, fun hv => by simp [hv]⟩
  have hneg : v = -v := by simpa [hv] using h.sq_eq_neg v
  rw [two_smul]
  nth_rw 2 [hneg]
  exact add_neg_cancel v

end IsQuaternionicStructure

end Representation
