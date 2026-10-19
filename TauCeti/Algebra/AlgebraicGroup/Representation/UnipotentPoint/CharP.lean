/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.UnipotentPoint.Basic
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Lemmas
import TauCeti.Algebra.AlgebraicGroup.Representation.Embedding
import TauCeti.Algebra.AlgebraicGroup.Representation.Faithful.Basic

/-!
# Unipotent points in positive characteristic

Over a value ring of characteristic `p > 0`, a unipotent point of an affine group of finite type
has order a power of `p`. In a faithful finite-dimensional representation the point acts as
`1 + N` with `N` nilpotent, and `(1 + N) ^ p ^ n = 1 + N ^ p ^ n = 1` once `N ^ n = 0`; a
faithful representation separates points.

Over a value field of characteristic zero the opposite happens: a nonidentity unipotent point has
infinite order, see `TauCeti.HopfAlgebra.IsUnipotentPoint.eq_one_of_isOfFinOrder`.

## Main declaration

* `TauCeti.HopfAlgebra.IsUnipotentPoint.exists_pow_char_pow_eq_one`: a unipotent point in
  characteristic `p` is killed by a power of `p`.

## References

* T. A. Springer, *Linear Algebraic Groups*, §2.4.
* J. S. Milne, *Algebraic Groups* (2017), §9.d.
-/

public section

open WithConv
open scoped TensorProduct

namespace TauCeti.HopfAlgebra.IsUnipotentPoint

universe u v

variable {k H : Type u} {K : Type v} [Field k] [CommRing H] [_root_.HopfAlgebra k H]
  [Algebra.FiniteType k H] [CommRing K] [Algebra k K]

/-- **A unipotent point in characteristic `p` has `p`-power order.** Over a commutative value
ring of characteristic `p`, some power `p ^ n` kills a unipotent point of an affine group of finite
type. -/
theorem exists_pow_char_pow_eq_one (p : ℕ) [Fact p.Prime] [CharP K p]
    {g : WithConv (H →ₐ[k] K)} (hg : IsUnipotentPoint g) :
    ∃ n : ℕ, g ^ p ^ n = 1 := by
  have hprime : p.Prime := Fact.out
  obtain ⟨M, d, b, hb⟩ := Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom (k := k)
    (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Finite k M := Module.Finite.of_basis b
  have hfaithful : Comodule.IsFaithful (k := k) (H := H) (V := M) :=
    (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).mpr hb
  obtain ⟨n, hn⟩ := (isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp hg
    (FGComoduleCat.of (R := k) (C := H) M)
  refine ⟨n, Comodule.pointsAction_injective_of_isFaithful hfaithful ?_⟩
  apply LinearEquiv.toLinearMap_injective
  rw [map_pow, map_one, ← LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply, map_pow,
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply, Comodule.pointsAction_toLinearMap]
  -- Write the action as `1 + N` with `N` nilpotent and expand by the Frobenius binomial formula.
  set N := Comodule.endOfPoint M g.ofConv - 1
  obtain ⟨r, hr⟩ := (Commute.one_left N).exists_add_pow_prime_pow_eq hprime n
  have hp : (p : Module.End K (K ⊗[k] M)) = 0 := by
    rw [← map_natCast (algebraMap K (Module.End K (K ⊗[k] M))), CharP.cast_eq_zero, map_zero]
  have hN : N ^ p ^ n = 0 :=
    pow_eq_zero_of_le (Nat.lt_pow_self hprime.one_lt).le hn
  rw [show Comodule.endOfPoint M g.ofConv = 1 + N from
    (add_sub_cancel (1 : Module.End K (K ⊗[k] M)) _).symm, hr, hp, hN]
  simp [Module.End.one_eq_id]

end TauCeti.HopfAlgebra.IsUnipotentPoint
