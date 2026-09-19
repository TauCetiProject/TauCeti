/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Eigenrow

/-!
# The Frobenius formula for product-one triples

Fix a finite group `G` and three conjugacy classes `C₀`, `C₁`, `C∞` of it. The **product-one
triples** of that data are the triples `(x, y, z)` with `x ∈ C₀`, `y ∈ C₁`, `z ∈ C∞` and
`z * y * x = 1`. They are the finite shadow of a covering of the sphere branched over three points
with prescribed local monodromy, and counting them is the first step in counting such coverings.

Two counts are proved here.

* Splitting a triple into its last entry and a factorization `y * x = z⁻¹` counts the triples as
  `|C∞|` times a structure constant of the class algebra (`TauCeti.card_productOneTriples`).
* Feeding that structure constant through the central characters turns the count into a sum over
  the irreducible characters, the **Frobenius formula**
  (`TauCeti.card_productOneTriples_eq_sum_characterTable`)

  `#{(x, y, z) | …} = (|C₀| · |C₁| · |C∞| / |G|) · ∑_χ χ(C₀) χ(C₁) χ(C∞) / χ(1)`.

The route is the class algebra rather than a direct manipulation of characters: the values of a
central character on the class sums are a common left eigenrow of the class-multiplication matrices
(`TauCeti.isClassEigenrow_centralCharacterTable`), which is exactly the structure-constant identity
`∑_C aᵢⱼC ω(K_C) = ω(K_Cᵢ) ω(K_Cⱼ)`; the second orthogonality relation inverts it, and
`TauCeti.centralCharacterTable_eq_div` converts between `ω` and the character table. Characteristic
zero enters only through that conversion, which divides by the degrees `χ(1)`.

What the count is not: it counts triples, not isomorphism classes; it puts no generation condition
on the three entries; and its data are three conjugacy classes of `G`, not three cycle types. For a
permutation group `G` the two differ: a single cycle type of the ambient symmetric group can split
into several `G`-conjugacy classes, and then a count of triples of prescribed cycle types is a sum
of several of these counts.

## Main definitions

* `TauCeti.productOneTriples`: the triples with entries in three prescribed conjugacy classes whose
  product, in the order `z * y * x`, is `1`.

## Main statements

* `TauCeti.card_productOneTriples`: the count as `|C∞|` times a structure constant.
* `TauCeti.structureConstant_eq_sum_characterTable`: the structure constants of the class algebra,
  read off the character table.
* `TauCeti.card_productOneTriples_eq_sum_characterTable`: the Frobenius formula.

## References

* I. M. Isaacs, *Character Theory of Finite Groups* (1976), Problem 3.9.
* J.-P. Serre, *Topics in Galois Theory*, 2nd ed. (2008), §7.2.
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications* (2004), §5.3, for the
  use of the formula in counting coverings.
-/

public section

namespace TauCeti

universe u v

section Count

variable {G : Type v} [Group G] [Fintype G] [DecidableEq G]

/-- The **product-one triples** with entries in the conjugacy classes `C₀`, `C₁`, `C∞`: the triples
`(x, y, z)` with `x ∈ C₀`, `y ∈ C₁`, `z ∈ C∞` and `z * y * x = 1`.

The order of the product is the one in which a triple of loops around three branch points
concatenates to a nullhomotopic loop. -/
def productOneTriples (C0 C1 Cinf : ConjClasses G) : Finset (G × G × G) :=
  {p ∈ Finset.univ | ConjClasses.mk p.1 = C0 ∧ ConjClasses.mk p.2.1 = C1 ∧
    ConjClasses.mk p.2.2 = Cinf ∧ p.2.2 * p.2.1 * p.1 = 1}

@[simp]
theorem mem_productOneTriples {C0 C1 Cinf : ConjClasses G} {p : G × G × G} :
    p ∈ productOneTriples C0 C1 Cinf ↔
      ConjClasses.mk p.1 = C0 ∧ ConjClasses.mk p.2.1 = C1 ∧ ConjClasses.mk p.2.2 = Cinf ∧
        p.2.2 * p.2.1 * p.1 = 1 := by
  simp [productOneTriples]

/-- **The product-one triples fibre over their last entry.** Over `z ∈ C∞` the fibre consists of the
factorizations `y * x = z⁻¹` with `y ∈ C₁` and `x ∈ C₀`, so a structure constant of the class
algebra counts it, independently of `z`. -/
theorem card_productOneTriples (C0 C1 Cinf : ConjClasses G) :
    (productOneTriples C0 C1 Cinf).card =
      Nat.card Cinf.carrier * structureConstant C1 C0 Cinf⁻¹ := by
  classical
  have hmem : ∀ p ∈ productOneTriples C0 C1 Cinf, p.2.2 ∈ Cinf.carrier.toFinset := by
    intro p hp
    rw [mem_productOneTriples] at hp
    simpa [ConjClasses.mem_carrier_iff_mk_eq] using hp.2.2.1
  have hfibre : ∀ z ∈ Cinf.carrier.toFinset,
      {p ∈ productOneTriples C0 C1 Cinf | p.2.2 = z}.card = structureConstant C1 C0 Cinf⁻¹ := by
    intro z hz
    rw [Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq] at hz
    -- Rewriting `C∞` back to the class of `z` puts both sides in terms of the representative `z`.
    rw [← hz, ConjClasses.inv_mk, structureConstant_mk_eq_card_filter]
    refine Finset.card_bij (fun p _ => (p.2.1, p.1)) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter, mem_productOneTriples] at hp
      obtain ⟨⟨hx, hy, -, hprod⟩, hlast⟩ := hp
      rw [hlast, mul_assoc] at hprod
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hy, hx, eq_inv_of_mul_eq_one_right hprod⟩
    · intro p hp q hq hpq
      rw [Finset.mem_filter] at hp hq
      rw [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.2 (Prod.ext hpq.1 (hp.2.trans hq.2.symm))
    · intro q hq
      rw [Finset.mem_filter] at hq
      obtain ⟨-, hy, hx, hprod⟩ := hq
      refine ⟨(q.2, q.1, z), Finset.mem_filter.2
        ⟨mem_productOneTriples.2 ⟨hx, hy, rfl, ?_⟩, rfl⟩, rfl⟩
      rw [mul_assoc, hprod, mul_inv_cancel]
  rw [Finset.card_eq_sum_card_fiberwise hmem, Finset.sum_congr rfl hfibre, Finset.sum_const,
    smul_eq_mul, Set.toFinset_card, Nat.card_eq_fintype_card]

end Count

section Frobenius

variable {k : Type u} {G : Type v} [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Fintype G]
  [DecidableEq G] [Invertible (Nat.card G : k)]

/-- **The structure constants of the class algebra, read off the character table.** The number of
factorizations `x * y = g` with `x ∈ Cᵢ`, `y ∈ Cⱼ` and `g` a representative of `Cₖ` is

`(|Cᵢ| · |Cⱼ| / |G|) · ∑_χ χ(Cᵢ) χ(Cⱼ) χ(Cₖ⁻¹) / χ(1)`,

the sum running over the irreducible characters of `G`. -/
theorem structureConstant_eq_sum_characterTable (Ci Cj Ck : ConjClasses G) :
    (structureConstant Ci Cj Ck : k) =
      (Nat.card Ci.carrier : k) * Nat.card Cj.carrier / Nat.card G *
        ∑ l, characterTable k G l Ci * characterTable k G l Cj * characterTable k G l Ck⁻¹ /
          (characterDegree k l : k) := by
  have hdeg : ∀ l : Fin (Nat.card (ConjClasses G)), (characterDegree k l : k) ≠ 0 := fun l =>
    Nat.cast_ne_zero.2 (characterDegree_pos k l).ne'
  have hG : (Nat.card G : k) ≠ 0 := Invertible.ne_zero _
  -- The column at `Cₖ⁻¹`, weighted by the degrees, against the products of central characters.
  set S : k := ∑ l : Fin (Nat.card (ConjClasses G)), (characterDegree k l : k) *
    characterTable k G l Ck⁻¹ *
      (centralCharacterTable k G l Ci * centralCharacterTable k G l Cj) with hS
  -- Evaluating each central character by `ω(K_C) = |C| χ(C) / χ(1)` gives the character side.
  have hS₁ : S = (Nat.card Ci.carrier : k) * Nat.card Cj.carrier *
      ∑ l, characterTable k G l Ci * characterTable k G l Cj * characterTable k G l Ck⁻¹ /
        (characterDegree k l : k) := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hd := hdeg l
    rw [centralCharacterTable_eq_div l hd Ci, centralCharacterTable_eq_div l hd Cj]
    field_simp
  -- Expanding the product of central characters by the structure constants, and then applying
  -- column orthogonality, leaves a single structure constant.
  have hS₂ : S = (Nat.card G : k) * structureConstant Ci Cj Ck := by
    have hrow : ∀ l : Fin (Nat.card (ConjClasses G)),
        ∑ C : ConjClasses G, (structureConstant Ci Cj C : k) * centralCharacterTable k G l C =
          centralCharacterTable k G l Ci * centralCharacterTable k G l Cj := fun l =>
      (isClassEigenrow_iff _).1 (isClassEigenrow_centralCharacterTable l) Ci Cj
    have hterm : ∀ l : Fin (Nat.card (ConjClasses G)),
        (characterDegree k l : k) * characterTable k G l Ck⁻¹ *
            (centralCharacterTable k G l Ci * centralCharacterTable k G l Cj) =
          ∑ C : ConjClasses G, (structureConstant Ci Cj C : k) * (Nat.card C.carrier : k) *
            (characterTable k G l C * characterTable k G l Ck⁻¹) := by
      intro l
      rw [← hrow l, Finset.mul_sum]
      refine Finset.sum_congr rfl fun C _ => ?_
      have hd := hdeg l
      rw [centralCharacterTable_eq_div l hd C]
      field_simp
    have hswap : S = ∑ C : ConjClasses G, (structureConstant Ci Cj C : k) *
        ((Nat.card C.carrier : k) *
          ∑ l, characterTable k G l C * characterTable k G l Ck⁻¹) := by
      rw [hS, Finset.sum_congr rfl fun l _ => hterm l, Finset.sum_comm]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => mul_assoc _ _ _
    rw [hswap, Finset.sum_eq_single_of_mem Ck (Finset.mem_univ _)
      (fun C _ hC => by rw [sum_characterTable_mul_characterTable_inv_of_ne hC, mul_zero,
        mul_zero]),
      card_carrier_mul_sum_characterTable_mul_characterTable_inv, mul_comm]
  rw [div_mul_eq_mul_div, eq_div_iff hG, ← hS₁, hS₂, mul_comm]

/-- **The Frobenius formula.** The number of triples `(x, y, z)` with `x ∈ C₀`, `y ∈ C₁`,
`z ∈ C∞` and `z * y * x = 1` is

`(|C₀| · |C₁| · |C∞| / |G|) · ∑_χ χ(C₀) χ(C₁) χ(C∞) / χ(1)`,

the sum running over the irreducible characters of `G`. -/
theorem card_productOneTriples_eq_sum_characterTable (C0 C1 Cinf : ConjClasses G) :
    ((productOneTriples C0 C1 Cinf).card : k) =
      (Nat.card C0.carrier : k) * Nat.card C1.carrier * Nat.card Cinf.carrier / Nat.card G *
        ∑ l, characterTable k G l C0 * characterTable k G l C1 * characterTable k G l Cinf /
          (characterDegree k l : k) := by
  rw [card_productOneTriples, Nat.cast_mul, structureConstant_eq_sum_characterTable (k := k),
    inv_inv]
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← mul_div_assoc]
  refine congrArg₂ (· / ·) ?_ rfl
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  field_simp

end Frobenius

end TauCeti
