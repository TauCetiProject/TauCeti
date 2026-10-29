/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.InvariantDerivation
public import Mathlib.RingTheory.Coalgebra.GroupLike

/-!
# Invariant vector fields on group-like elements

A group-like element `g` of a commutative bialgebra `H` is a character `G → 𝔾ₘ` of the
corresponding affine monoid, and the left-invariant derivation `D` attached to a tangent vector
`d` at the identity differentiates it into a multiple of itself:

```text
D g = d(g) • g,     Dⁿ g = d(g)ⁿ • g.
```

The scalar `d(g)` is the differential of the character at the identity. Consequently `D` is
nilpotent on `g` exactly up to nilpotence of this scalar: if `d(g)` is nilpotent then some
iterate of `D` kills `g`. For the determinant of `GLₙ`, `d(det)` is the trace of the tangent
matrix.

## Main results

* `TauCeti.Bialgebra.leftInvariantDerivation_apply_of_isGroupLikeElem`: `D g = d(g) • g`.
* `TauCeti.Bialgebra.iterate_leftInvariantDerivation_apply_of_isGroupLikeElem`:
  `Dⁿ g = d(g)ⁿ • g`.
* `TauCeti.Bialgebra.exists_iterate_leftInvariantDerivation_eq_zero_of_isGroupLikeElem`: if
  `d(g)` is nilpotent then an iterate of `D` kills `g`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 10.
-/

public section

open TensorProduct LinearMap

namespace TauCeti.Bialgebra

variable {R H : Type*} [CommRing R] [CommRing H] [_root_.Bialgebra R H]

/-- **An invariant vector field multiplies a group-like element by its differential at the
identity**: `D g = d(g) • g`. -/
theorem leftInvariantDerivation_apply_of_isGroupLikeElem
    (d : Derivation R H (CounitAlgebra R H R)) {g : H} (hg : IsGroupLikeElem R g) :
    leftInvariantDerivation d g = CounitAlgebra.algEquivSelf R H R (d g) • g := by
  rw [leftInvariantDerivation_apply, hg.comul_eq_tmul_self, tensorComponent_tmul,
    LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, Derivation.coeFn_coe]

/-- Iterating an invariant vector field on a group-like element multiplies it by the
corresponding power of its differential at the identity: `Dⁿ g = d(g)ⁿ • g`. -/
theorem iterate_leftInvariantDerivation_apply_of_isGroupLikeElem
    (d : Derivation R H (CounitAlgebra R H R)) {g : H} (hg : IsGroupLikeElem R g) (n : ℕ) :
    (leftInvariantDerivation d)^[n] g = CounitAlgebra.algEquivSelf R H R (d g) ^ n • g := by
  induction n with
  | zero => rw [Function.iterate_zero_apply, pow_zero, one_smul]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.map_smul,
      leftInvariantDerivation_apply_of_isGroupLikeElem d hg, smul_smul, pow_succ]

/-- If the differential of a group-like element at the identity is nilpotent, then some iterate of
the invariant vector field kills that element. -/
theorem exists_iterate_leftInvariantDerivation_eq_zero_of_isGroupLikeElem
    (d : Derivation R H (CounitAlgebra R H R)) {g : H} (hg : IsGroupLikeElem R g)
    (hd : IsNilpotent (CounitAlgebra.algEquivSelf R H R (d g))) :
    ∃ n, (leftInvariantDerivation d)^[n] g = 0 := by
  obtain ⟨n, hn⟩ := hd
  exact ⟨n, by rw [iterate_leftInvariantDerivation_apply_of_isGroupLikeElem d hg, hn, zero_smul]⟩

end TauCeti.Bialgebra
