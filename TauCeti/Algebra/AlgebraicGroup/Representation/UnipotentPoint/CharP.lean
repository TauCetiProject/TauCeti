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
import TauCeti.Algebra.Ring.SubOnePow

/-!
# Unipotent points in positive characteristic

Over a value ring of characteristic `p > 0`, a unipotent point of an affine group of finite type
has order a power of `p`. In a faithful finite-dimensional representation the point acts as
`1 + N` with `N` nilpotent, and `(1 + N) ^ p ^ n = 1 + N ^ p ^ n = 1` once `N ^ n = 0`; a
faithful representation separates points.

Conversely, a point killed by a power `p ^ n` is unipotent, without any finiteness hypothesis:
in every representation it acts by some `1 + N` with `(1 + N) ^ p ^ n = 1`, and the same binomial
expansion gives `N ^ p ^ n = 0`.

Over a value field of characteristic zero the opposite happens: a nonidentity unipotent point has
infinite order, see `TauCeti.HopfAlgebra.IsUnipotentPoint.eq_one_of_isOfFinOrder`.

## Main declaration

* `TauCeti.HopfAlgebra.IsUnipotentPoint.exists_pow_char_pow_eq_one`: a unipotent point in
  characteristic `p` is killed by a power of `p`.
* `TauCeti.HopfAlgebra.isUnipotentPoint_of_pow_char_pow_eq_one`: conversely, a point killed by a
  power of `p` is unipotent.
* `TauCeti.HopfAlgebra.isUnipotentPoint_iff_exists_pow_char_pow_eq_one`: for affine groups of
  finite type, the unipotent points in characteristic `p` are those of `p`-power order.

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
theorem exists_pow_char_pow_eq_one (p : ℕ) [CharP K p]
    {g : WithConv (H →ₐ[k] K)} (hg : IsUnipotentPoint g) :
    ∃ n : ℕ, g ^ p ^ n = 1 := by
  rcases eq_or_ne p 0 with rfl | hp0
  · exact ⟨1, by simp⟩
  obtain ⟨M, d, b, hb⟩ := Comodule.exists_isClosedImmersion_coordinateGroupSchemeHom (k := k)
    (H := H)
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Finite k M := Module.Finite.of_basis b
  have hfaithful : Comodule.IsFaithful (k := k) (H := H) (V := M) :=
    (Comodule.isFaithful_iff_isClosedImmersion_coordinateGroupSchemeHom b).mpr hb
  obtain ⟨n, hn⟩ := (isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one g).mp hg
    (FGComoduleCat.of (R := k) (C := H) M)
  -- Write the action as `1 + N` with `N` nilpotent; this has `p`-power order since `p = 0`.
  set N := Comodule.endOfPoint M g.ofConv - 1
  have hp : (p : Module.End K (K ⊗[k] M)) = 0 := by
    rw [← map_natCast (algebraMap K (Module.End K (K ⊗[k] M))), CharP.cast_eq_zero, map_zero]
  obtain ⟨n', hn'⟩ := exists_one_add_pow_eq_one_of_natCast_eq_zero hp0 hp ⟨n, hn⟩
  refine ⟨n', Comodule.pointsAction_injective_of_isFaithful hfaithful ?_⟩
  apply LinearEquiv.toLinearMap_injective
  rw [map_pow, map_one, ← LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply, map_pow,
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply, Comodule.pointsAction_toLinearMap,
    show Comodule.endOfPoint M g.ofConv = 1 + N from
      (add_sub_cancel (1 : Module.End K (K ⊗[k] M)) _).symm, hn']
  simp [Module.End.one_eq_id]

end TauCeti.HopfAlgebra.IsUnipotentPoint

namespace TauCeti.HopfAlgebra

universe u v w

section General

variable {k : Type u} {H : Type v} {K : Type w} [CommSemiring k] [Semiring H]
  [_root_.HopfAlgebra k H] [CommRing K] [Algebra k K]

/-- **A point of `p`-power order in characteristic `p` is unipotent.** Over a commutative value
ring of characteristic `p`, a point killed by some power `p ^ n` acts on every finitely generated
comodule by `1 + N` with `N ^ p ^ n = 0`. -/
theorem isUnipotentPoint_of_pow_char_pow_eq_one (p : ℕ) [Fact p.Prime] [CharP K p]
    {g : WithConv (H →ₐ[k] K)} {n : ℕ} (hg : g ^ p ^ n = 1) : IsUnipotentPoint g := by
  have hprime : p.Prime := Fact.out
  rw [isUnipotentPoint_iff_forall_isNilpotent_endOfPoint_sub_one]
  intro M
  set E := Comodule.endOfPoint M g.ofConv
  have hE : E ^ p ^ n = 1 := by
    have h := congrArg (fun g ↦ (Comodule.pointsAction M g).toLinearMap) hg
    simp only [map_pow, map_one] at h
    rwa [← LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply, map_pow,
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply,
      Comodule.pointsAction_toLinearMap] at h
  -- `p` divides `(E - 1) ^ p ^ n` by the binomial theorem, and `p = 0` in characteristic `p`.
  have hp : (p : Module.End K (K ⊗[k] M)) = 0 := by
    rw [← map_natCast (algebraMap K (Module.End K (K ⊗[k] M))), CharP.cast_eq_zero, map_zero]
  exact ⟨p ^ n, by simpa only [hp, zero_dvd_iff] using
    hprime.dvd_sub_one_pow_of_pow_eq_one (A := Module.End K (K ⊗[k] M)) hE⟩

end General

/-- **In characteristic `p`, the unipotent points of an affine group of finite type are those of
`p`-power order.** -/
theorem isUnipotentPoint_iff_exists_pow_char_pow_eq_one {k H : Type u} {K : Type v} [Field k]
    [CommRing H] [_root_.HopfAlgebra k H] [Algebra.FiniteType k H] [CommRing K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP K p] {g : WithConv (H →ₐ[k] K)} :
    IsUnipotentPoint g ↔ ∃ n : ℕ, g ^ p ^ n = 1 :=
  ⟨IsUnipotentPoint.exists_pow_char_pow_eq_one p, fun ⟨_, hn⟩ ↦
    isUnipotentPoint_of_pow_char_pow_eq_one p hn⟩

end TauCeti.HopfAlgebra
