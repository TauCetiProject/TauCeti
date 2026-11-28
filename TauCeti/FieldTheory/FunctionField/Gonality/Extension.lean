/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Gonality.Basic
public import TauCeti.FieldTheory.FunctionField.Divisor.Charpoly
import TauCeti.FieldTheory.IntermediateField.Map
import TauCeti.RingTheory.Algebraic.Basic

/-!
# Gonality along finite extensions

Let `F ⊆ F'` be a finite extension of algebraic function fields over the same field `k`, that is,
a finite map of curves `X' → X`. This file proves

`gonality k F ≤ gonality k F' ≤ [F' : F] · gonality k F`.

The upper bound composes a pencil: if `[F : k(x)]` is the gonality of `F`, then
`[F' : k(x)] = [F' : F] · [F : k(x)]`.

The lower bound is Poonen's Proposition A.1(vii): a curve dominating another has at least its
gonality. If `z ∈ F'` attains the gonality of `F'`, some coefficient `s` of the characteristic
polynomial of `z` over `F` is transcendental over `k`, since otherwise `z` would be algebraic over
`k`. The poles of `s` are bounded by the norm `N((z)_∞)` of the pole divisor of `z`
(`TauCeti.Divisor.coeff_charpoly_mem_riemannRochSpace_norm`), so
`[F : k(s)] ≤ deg N((z)_∞) = deg (z)_∞ = [F' : k(z)]`.

Neither bound needs separability of `F' / F` or exactness of the constant fields.

## Main results

* `TauCeti.gonality_le_gonality_of_finiteDimensional`: `gonality k F ≤ gonality k F'`.
* `TauCeti.gonality_le_finrank_mul_gonality`: `gonality k F' ≤ [F' : F] · gonality k F`.

## References

* B. Poonen, *Gonality of modular curves in characteristic `p`*, Math. Res. Lett. 14 (2007),
  Appendix A, Proposition A.1(vii).
-/

public section

open scoped IntermediateField

namespace TauCeti

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra F F'] [IsScalarTower k F F']

/-- **An extension multiplies the gonality by at most its degree**: if `F / k` is an
algebraic function field and `F' / F` is an extension, then
`gonality k F' ≤ [F' : F] · gonality k F`. A rational subfield `k(x) ⊆ F` attaining the gonality
of `F` has index `[F' : F] · [F : k(x)]` in `F'`. For an infinite extension both sides are the
junk value zero. -/
theorem gonality_le_finrank_mul_gonality (hF : IsFunctionField k F) :
    gonality k F' ≤ Module.finrank F F' * gonality k F := by
  obtain ⟨x, hx, hrank⟩ := exists_finrank_adjoin_eq_gonality hF
  have hx' : Transcendental k (algebraMap F F' x) :=
    (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx
  calc gonality k F' ≤ Module.finrank k⟮algebraMap F F' x⟯ F' := gonality_le_finrank_adjoin hx'
    _ = Module.finrank F F' * gonality k F := by
      rw [IntermediateField.finrank_adjoin_simple_algebraMap, hrank, mul_comm]

variable [FiniteDimensional F F']

/-- **Gonality does not drop along a finite extension** (Poonen, Proposition A.1(vii)): if `F' / F`
is a finite extension, then `gonality k F ≤ gonality k F'`. No separability of `F' / F` or
exactness of the constants is needed, and when `F / k` is not an algebraic function field its
gonality is the junk value zero. -/
theorem gonality_le_gonality_of_finiteDimensional : gonality k F ≤ gonality k F' := by
  rcases Nat.eq_zero_or_pos (gonality k F) with h | h
  · exact h ▸ Nat.zero_le _
  have hF := gonality_pos_iff.mp h
  have hF' : IsFunctionField k F' := hF.finite_extension
  obtain ⟨z, hz, hrank⟩ := exists_finrank_adjoin_eq_gonality hF'
  let D := Divisor.poles hF' (Units.mk0 z hz.ne_zero)
  have hD : 0 ≤ D := Divisor.poles_nonneg hF' _
  -- A coefficient `s` of the characteristic polynomial of `z` is transcendental, with
  -- `s ∈ L(N((z)_∞))`.
  obtain ⟨i, hi⟩ := hz.exists_transcendental_coeff_charpoly_lmul (F := F)
  have hmem := Divisor.coeff_charpoly_mem_riemannRochSpace_norm (k' := k) hF hD
    (mem_riemannRochSpace_poles hF' (Units.mk0 z hz.ne_zero)) i
  have hle := Divisor.finrank_adjoin_le_degree_of_mem_riemannRochSpace hF
    (Divisor.norm_nonneg k F hD) hmem
  -- `deg N((z)_∞) = [k : k] · deg (z)_∞ = [F' : k(z)]`.
  have hdeg : (Divisor.norm k F D).degree = gonality k F' := by
    rw [Divisor.degree_norm, Divisor.degree_poles hF' (Units.mk0 z hz.ne_zero) hz,
      Units.val_mk0, hrank]
    simp
  exact (gonality_le_finrank_adjoin hi).trans (by exact_mod_cast hle.trans_eq hdeg)

end TauCeti
