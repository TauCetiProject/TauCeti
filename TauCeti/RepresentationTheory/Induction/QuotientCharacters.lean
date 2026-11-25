/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.ClassFunction
public import TauCeti.RepresentationTheory.CharacterTable.Gallagher

/-!
# Inducing restrictions across a normal subgroup

Inducing the restriction of a class function multiplies it by the inflated regular character of
the quotient. Expanding that regular character gives a sum of inflated irreducible characters
with their degrees as weights. In particular, for an abelian quotient, the induction of an
irreducible character that extends is the sum of the irreducible characters lying over it,
each with multiplicity one.

The decomposition uses Gallagher's correspondence (Isaacs, *Character Theory of Finite Groups*,
Corollary 6.17) in the form `TauCeti.gallagher_bijOn`.
-/

public section

open TauCeti

namespace Subgroup

/-- The induction of a restricted class function is the sum of its products with the inflated
irreducible characters of the quotient, each weighted by its degree. -/
theorem indClassFun_comp_subtype_eq_sum_quotient_characters {G k : Type*} [Group G] [Field k]
    [IsAlgClosed k] (N : Subgroup G) [N.Normal] [N.FiniteIndex] [Invertible (Nat.card (G ⧸ N) : k)]
    {f : G → k} (hf : f ∈ ClassFunction k G) (g : G) :
    N.indClassFun (fun n : N => f n) g =
      ∑ i : Fin (Nat.card (ConjClasses (G ⧸ N))),
        (characterDegree k i : k) * (f g * irreducibleCharacter k i (g : G ⧸ N)) := by
  classical
  have hregular := sum_finrank_mul_character (irreducibleRepresentation k (G := G ⧸ N))
    (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) (g : G ⧸ N)
  simp only [Module.finrank_fin_fun, character_irreducibleRepresentation,
    QuotientGroup.eq_one_iff] at hregular
  rw [N.indClassFun_comp_subtype_apply_of_normal (ClassFunction.mem_iff.mp hf)]
  calc
    (if g ∈ N then N.index • f g else 0) =
        f g * (if g ∈ N then (N.index : k) else 0) := by split_ifs <;> simp [nsmul_eq_mul, mul_comm]
    _ = _ := by
      rw [N.index_eq_card, ← hregular, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- If an irreducible character of a normal subgroup extends to the whole group and the quotient
is abelian, its induction is the sum of the irreducible characters lying over it. In particular,
each constituent occurs once. This applies to normal subgroups of prime index, since a group of
prime order is cyclic. -/
theorem indClassFun_eq_finsum_irreducibleCharactersOver {G k : Type*} [Group G] [Finite G]
    [Field k] [IsAlgClosed k] [CharZero k] (N : Subgroup G) [N.Normal]
    [IsMulCommutative (G ⧸ N)] {χ : G → k} {θ : N → k}
    (hχ : χ ∈ irreducibleCharacters k G) (hθ : θ ∈ irreducibleCharacters k N)
    (hres : ∀ n : N, χ n = θ n) (g : G) :
    N.indClassFun θ g = ∑ᶠ ψ : irreducibleCharactersOver k N θ, ψ.val g := by
  classical
  let : Invertible (Nat.card (G ⧸ N) : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let e := (finEquivIrreducibleCharacters k (G ⧸ N)).trans (gallagher_bijOn hχ hθ hres).equiv
  have : Finite (irreducibleCharactersOver k N θ) := Finite.of_equiv _ e
  let := Fintype.ofFinite (irreducibleCharactersOver k N θ)
  have hf : χ ∈ ClassFunction k G := by
    obtain ⟨V, rfl⟩ := irreducibleCharacters_subset_range hχ
    simpa only [funext (ClassFunction.ofFDRep_apply V)] using (ClassFunction.ofFDRep V).property
  conv_lhs => rw [← funext hres, N.indClassFun_comp_subtype_eq_sum_quotient_characters hf]
  rw [finsum_eq_sum_of_fintype]
  refine Fintype.sum_equiv e _ _ fun i => ?_
  have hdeg : characterDegree k i = 1 := by
    simpa using Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      (ρ := irreducibleRepresentation k (G := G ⧸ N) i)
  simp [hdeg, e, Set.BijOn.equiv]

end Subgroup
