/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Cartan subalgebras of linear Killing Lie algebras are toral

Let `L ⊆ 𝔤𝔩(V)` be a Lie algebra of endomorphisms of a finite-dimensional vector space over a
perfect field, with nondegenerate Killing form, which contains the nilpotent part of the
Jordan–Chevalley decomposition of each of its elements. This file shows that every element of a
Cartan subalgebra `H` of `L` is a semisimple endomorphism of `V`
(`LieSubalgebra.isSemisimple_of_mem_isCartanSubalgebra`).

Write `x = n + s` for the Jordan–Chevalley decomposition of `x ∈ H`. The Cartan subalgebra `H` is
abelian (`LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra`), so every element of `H`
commutes with `x`, hence with the polynomial `n` in `x`. So `n`, which lies in `L` by hypothesis,
normalizes `H` and therefore lies in `H`. Its adjoint action on `L` is nilpotent, and the only such
element of a Cartan subalgebra of a Killing Lie algebra is zero
(`LieAlgebra.IsKilling.eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra`). Hence `x = s`.

No splitting of `H` is assumed, unlike Mathlib's
`LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`, which needs the action of `H`
to be triangularizable. The closure hypothesis replaces it, and holds for the Lie algebras of
skew-adjoint endomorphisms of nondegenerate forms (`LinearMap.IsSkewAdjoint.of_isNilpotent_of_add`)
over any perfect field, such as the real symplectic Lie algebras, whose Cartan subalgebras are in
general not split over `ℝ`. Over an algebraically closed field of characteristic zero every Killing
Lie subalgebra of `𝔤𝔩(V)` satisfies it (`LieSubalgebra.mem_of_isNilpotent_of_add_mem`).

## Main results

* `LieSubalgebra.isSemisimple_of_mem_isCartanSubalgebra`: the elements of a Cartan subalgebra are
  semisimple endomorphisms.
* `LieSubalgebra.commute_of_mem_isCartanSubalgebra`: they commute with each other.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §8.1 and §15.3
  (Cartan subalgebras of semisimple Lie algebras are toral).
-/

public section

open LieAlgebra Module Module.End

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieSubalgebra

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {L : LieSubalgebra K (Module.End K V)} [IsKilling K L] (H : LieSubalgebra K L)
  [H.IsCartanSubalgebra]

/-- **Elements of a Cartan subalgebra commute** as endomorphisms, for a Lie algebra `L ⊆ 𝔤𝔩(V)`
with nondegenerate Killing form: the Cartan subalgebra is abelian. -/
theorem commute_of_mem_isCartanSubalgebra {x y : L} (hx : x ∈ H) (hy : y ∈ H) :
    Commute (x : Module.End K V) y := by
  have h : ⁅x, y⁆ = 0 := congrArg Subtype.val (trivial_lie_zero H H (⟨x, hx⟩ : H) ⟨y, hy⟩)
  rw [commute_iff_lie_eq, ← coe_bracket, h, ZeroMemClass.coe_zero]

/-- **Cartan subalgebras of linear Killing Lie algebras are toral.** Let `L ⊆ 𝔤𝔩(V)` be a Lie
algebra over a perfect field with nondegenerate Killing form that contains the nilpotent part of
the Jordan–Chevalley decomposition of each of its elements. Then every element of a Cartan
subalgebra of `L` is a semisimple endomorphism of `V`. -/
theorem isSemisimple_of_mem_isCartanSubalgebra [PerfectField K]
    (hL : ∀ ⦃n s : Module.End K V⦄, Commute n s → IsNilpotent n → s.IsSemisimple → n + s ∈ L →
      n ∈ L)
    {x : L} (hx : x ∈ H) : (x : Module.End K V).IsSemisimple := by
  obtain ⟨n, hn, s, hs, hnil, hss, hxns⟩ := (x : Module.End K V).exists_isNilpotent_isSemisimple
  have hc : Commute n s := Algebra.commute_of_mem_adjoin_singleton_of_commute hs
    (Algebra.commute_of_mem_adjoin_self hn).symm
  let n' : L := ⟨n, hL hc hnil hss (hxns ▸ x.2)⟩
  -- `n` is a polynomial in `x`, so it commutes with every element of the abelian algebra `H`;
  -- hence it normalizes `H`, and lies in `H` because `H` is self-normalizing.
  have hn'H : n' ∈ H := by
    rw [← IsCartanSubalgebra.self_normalizing (H := H), mem_normalizer_iff]
    intro y hy
    have hcomm : Commute n (y : Module.End K V) :=
      (Algebra.commute_of_mem_adjoin_singleton_of_commute hn
        (commute_of_mem_isCartanSubalgebra H hy hx)).symm
    have : ⁅n', y⁆ = 0 := Subtype.ext <| by
      rw [coe_bracket, ZeroMemClass.coe_zero]
      exact hcomm.lie_eq
    rw [this]
    exact H.zero_mem
  have hn'0 : n' = 0 := IsKilling.eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra K L H
    hn'H (isNilpotent_ad_of_isNilpotent (x := n') hnil)
  have hn0 : n = 0 := congrArg Subtype.val hn'0
  rw [hxns, hn0, zero_add]
  exact hss

end LieSubalgebra
