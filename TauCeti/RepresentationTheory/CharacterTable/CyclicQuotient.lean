/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Gallagher
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Character twists across a cyclic quotient

Once an irreducible character of a normal subgroup has an irreducible extension, Gallagher's
correspondence describes the characters over it. For an abelian quotient, these are exactly the
extensions (`TauCeti.irreducibleCharactersOver_eq_setOf_restrict_eq_of_isMulCommutative`). For a
cyclic quotient, powers of a single linear character enumerate them without repetition. Choosing
its value at a generator makes the enumeration explicit on each coset, as needed when collecting
terms of a virtual character by their common restriction.

This uses Gallagher's correspondence in the form of Isaacs, *Character Theory of Finite Groups*,
Corollary 6.17.
-/

public section

namespace TauCeti

variable {k G : Type*} [Field k] [IsAlgClosed k] [Group G] [Finite G]

/-- If a linear character takes a primitive root of order `|G|` at some element, its powers
enumerate the irreducible characters of `G`. -/
theorem _root_.MonoidHom.bijOn_pow_irreducibleCharacters (ε : G →* kˣ) {x : G}
    (hε : IsPrimitiveRoot (ε x : k) (Nat.card G)) :
    Set.BijOn (fun (i : Fin (Nat.card G)) (g : G) => (ε g : k) ^ (i : ℕ))
      Set.univ (irreducibleCharacters k G) := by
  let f (i : Fin (Nat.card G)) : irreducibleCharacters k G :=
    ⟨_, by simpa using (ε ^ (i : ℕ)).coe_mem_irreducibleCharacters⟩
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card G : k) := hε.neZero'
  let : Invertible (Nat.card G : k) := invertibleOfNonzero (NeZero.ne _)
  have hf : Function.Bijective f := by
    refine (Nat.bijective_iff_injective_and_card f).mpr ⟨fun i j hij => ?_, ?_⟩
    · exact Fin.ext (hε.pow_inj i.isLt j.isLt (congrFun (congrArg Subtype.val hij) x))
    · have horder : Nat.card G ∣ orderOf x := by
        rw [hε.eq_orderOf, orderOf_units]
        exact orderOf_map_dvd ε x
      have : IsCyclic G := isCyclic_of_card_le_orderOf x
        (Nat.le_of_dvd (orderOf_pos x) horder)
      let : CommGroup G := IsCyclic.commGroup
      rw [Nat.card_fin, card_irreducibleCharacters, ← Nat.card_congr ConjClasses.mkEquiv]
  refine ⟨fun i _ => (f i).property, fun i _ j _ h => hf.injective (Subtype.ext h), ?_⟩
  intro ψ hψ
  obtain ⟨i, hi⟩ := hf.surjective ⟨ψ, hψ⟩
  exact ⟨i, Set.mem_univ _, congrArg Subtype.val hi⟩

variable [CharZero k] {N : Subgroup G} [N.Normal] {θ : N → k} {χ : G → k}

/-- The twists of an extension by the successive powers of a primitive linear character of the
cyclic quotient enumerate the irreducible characters over the original character. -/
theorem gallagher_bijOn_pow
    (hχ : χ ∈ irreducibleCharacters k G) (hθ : θ ∈ irreducibleCharacters k N)
    (hres : ∀ n : N, χ n = θ n) (ε : G ⧸ N →* kˣ) {x : G ⧸ N}
    (hε : IsPrimitiveRoot (ε x : k) N.index) :
    Set.BijOn (fun (i : Fin N.index) (g : G) => χ g * (ε g : k) ^ (i : ℕ))
      Set.univ (irreducibleCharactersOver k N θ) := by
  rw [N.index_eq_card] at hε ⊢
  exact (gallagher_bijOn hχ hθ hres).comp (ε.bijOn_pow_irreducibleCharacters hε)

/-- A choice of primitive root `ζ` and generator `x` of the quotient gives a quotient character
sending `x` to `ζ` whose powers, multiplied by `χ`, enumerate all the characters over `θ`.
On the coset of `x` the `i`th twist therefore multiplies `χ` by `ζ ^ i`. -/
theorem exists_gallagher_bijOn_pow
    (hχ : χ ∈ irreducibleCharacters k G) (hθ : θ ∈ irreducibleCharacters k N)
    (hres : ∀ n : N, χ n = θ n) {x : G ⧸ N} (hx : Subgroup.zpowers x = ⊤)
    {ζ : k} (hζ : IsPrimitiveRoot ζ N.index) :
    ∃ ε : G ⧸ N →* kˣ, (ε x : k) = ζ ∧
      Set.BijOn (fun (i : Fin N.index) (g : G) => χ g * (ε g : k) ^ (i : ℕ))
        Set.univ (irreducibleCharactersOver k N θ) := by
  have hgen (q : G ⧸ N) : q ∈ Subgroup.zpowers x := hx.ge (Subgroup.mem_top q)
  have hn : N.index ≠ 0 := N.index_ne_zero_of_finite
  have hu := hζ.isUnit hn
  have hord : orderOf hu.unit ∣ orderOf x := by
    rw [← (hζ.isUnit_unit hn).eq_orderOf, orderOf_eq_card_of_forall_mem_zpowers hgen,
      ← N.index_eq_card]
  refine ⟨monoidHomOfForallMemZpowers hgen hord, ?_, ?_⟩
  · rw [monoidHomOfForallMemZpowers_apply_gen, hu.unit_spec]
  · refine gallagher_bijOn_pow hχ hθ hres _ (x := x) ?_
    rwa [monoidHomOfForallMemZpowers_apply_gen, hu.unit_spec]

end TauCeti
