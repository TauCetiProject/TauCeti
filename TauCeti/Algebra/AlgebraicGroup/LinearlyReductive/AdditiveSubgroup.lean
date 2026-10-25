/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive.FiniteSubgroup

/-!
# Additive subgroups obstruct linear reductivity in positive characteristic

If the additive group of the ground field embeds in the rational points of a linearly
reductive affine group of finite type, the field has characteristic zero. In characteristic
`p`, the image of `1` would have order `p`, contradicting the invertibility of orders of finite
subgroups. No closedness or algebraicity assumption on the embedding is needed.

This criterion applies to the elementary transvection subgroups of classical groups.
It uses `HopfAlgebra.natCast_orderOf_ne_zero_of_isLinearlyReductive`.

## References

* M. Nagata, *Complete reducibility of rational representations of a matric group*,
  J. Math. Kyoto Univ. **1** (1961), 87–99.
* J. S. Milne, *Algebraic Groups* (2017), §12.g.
-/

public section

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [_root_.HopfAlgebra k H]
  [Algebra.FiniteType k H]

/-- If the additive group of the ground field embeds in the rational points of a linearly
reductive affine group of finite type, the field has characteristic zero. -/
theorem charZero_of_isLinearlyReductive_of_injective_additiveHom
    (hH : Coalgebra.IsLinearlyReductive.{u, v, u} k H)
    (f : Multiplicative k →* WithConv (H →ₐ[k] k)) (hf : Function.Injective f) :
    CharZero k := by
  rcases CharP.exists' k with h | ⟨p, hp, hchar⟩
  · exact h
  · let _ := hp
    let _ := hchar
    have hord : orderOf (f (Multiplicative.ofAdd (1 : k))) = p := by
      rw [orderOf_injective f hf, orderOf_ofAdd_eq_addOrderOf]
      exact CharP.eq k (CharP.addOrderOf_one k) hchar
    have hfin : IsOfFinOrder (f (Multiplicative.ofAdd (1 : k))) :=
      orderOf_pos_iff.mp (hord ▸ hp.out.pos)
    have hne := natCast_orderOf_ne_zero_of_isLinearlyReductive hH hfin
    rw [hord, CharP.cast_eq_zero] at hne
    exact (hne rfl).elim

end TauCeti.HopfAlgebra
