/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Table
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
import TauCeti.RepresentationTheory.Invariants

/-!
# Character constituents of class functions with constant complement sum

Suppose that a class function on a finite group satisfies `f(g) + f(cg) = d`.
If the group order is invertible in the coefficient field, twice the trivial coefficient equals
`d`. On every nontrivial irreducible with nonzero coefficient, `c` acts as minus the identity.
When the order is invertible and the coefficient field is algebraically closed, these two
conditions also recover the complement identity.

For a finite Galois quotient carrying a CM class function, take `c` to be complex conjugation.
This separates the trivial character from the totally odd characters in the analytic height.
The result applies to every finite quotient through which the function factors.

## References

* F. Andreatta, E. Z. Goren, B. Howard, K. Madapusi Pera, *Faltings heights of abelian
  varieties with complex multiplication*, Ann. of Math. 187 (2018), §9.1.
-/

public section

namespace TauCeti.ClassFunction

open _root_.Representation
open scoped MonoidAlgebra

variable {k G : Type*} [Field k] [Group G] [Fintype G]

/-- If the sum of a class function and its left translate is constant, that constant is twice
the coefficient of the trivial character. The division-free identity also applies in
characteristic two. -/
theorem two_mul_characterPairing_trivial_of_add_mul_eq_const (f : ClassFunction k G)
    {c : G} {d : k} (hf : ∀ g, f.val g + f.val (c * g) = d)
    (hG : (Nat.card G : k) ≠ 0) :
    2 * characterPairing (ofCharacter (trivial k G k)) f = d := by
  have hsum := congrArg (fun u : G → k ↦ ∑ g, u g) (funext hf)
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_eq_nat_card, nsmul_eq_mul] at hsum
  have hreindex : ∑ g, f.val (c * g) = ∑ g, f.val g := Equiv.sum_comp (Equiv.mulLeft c) f.val
  rw [hreindex] at hsum
  rw [characterPairing_symm, characterPairing_apply]
  simp only [ofCharacter_apply, char_trivial, Module.finrank_self, Nat.cast_one, mul_one]
  field_simp
  linear_combination hsum

/-- On a nontrivial irreducible constituent of a class function with constant complement sum,
the translating element acts by minus the identity. In particular all its conjugates act by
the same sign. -/
theorem apply_eq_neg_one_of_characterPairing_ne_zero (f : ClassFunction k G)
    {c : G} {d : k} (hf : ∀ g, f.val g + f.val (c * g) = d)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsIrreducible]
    (hρ : ρ ≠ trivial k G V) (hp : characterPairing (ofCharacter ρ) f ≠ 0) :
    ρ c = -1 := by
  classical
  -- The central element with coefficients f(g⁻¹) acts with nonzero trace on this constituent.
  let z := ofConjClassesCenter (toConjClasses (invMap f))
  have hz (g : G) : (z : k[G]).coeff g = f.val g⁻¹ := by simp [z]
  have htrace : characterPairing (ofCharacter ρ) f =
      (Nat.card G : k)⁻¹ * LinearMap.trace k V (ρ.asAlgebraHom (z : k[G])) := by
    simp [characterPairing_apply, asAlgebraHom_eq_sum, hz, character, mul_comm]
  have hnorm : ρ.norm = 0 := by
    ext v
    have hv : ρ.norm v ∈ ρ.invariants := fun g ↦ ρ.self_norm_apply g v
    rwa [IsIrreducible.invariants_eq_bot inferInstance hρ, Submodule.mem_bot] at hv
  -- The complement identity multiplies z by 1 + c to give a multiple of the norm.
  have hcomp : (z : k[G]) + (z : k[G]) * MonoidAlgebra.of k G c =
      d • ∑ g : G, MonoidAlgebra.single g (1 : k) := by
    ext g
    simpa [MonoidAlgebra.of_apply, hz, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      Finsupp.single_apply] using hf g⁻¹
  have hzero := congrArg ρ.asAlgebraHom hcomp
  rw [map_add, map_mul, asAlgebraHom_of, map_smul, asAlgebraHom_sum_single_one, hnorm,
    smul_zero] at hzero
  -- Schur's lemma lets us cancel the action of z, over any coefficient field.
  let T : IntertwiningMap ρ ρ := (ρ.asAlgebraHom (z : k[G])).intertwiningMap_of_isIntertwiningMap
    ρ ρ fun g v ↦ by
      have h := congrArg ρ.asAlgebraHom (Subalgebra.mem_center_iff.mp z.property
        (MonoidAlgebra.of k G g))
      rw [map_mul, map_mul, asAlgebraHom_of] at h
      exact LinearMap.congr_fun h.symm v
  have hinj := (IsIrreducible.injective_or_eq_zero T).resolve_right (fun h ↦ hp (by
    have ht : ρ.asAlgebraHom (z : k[G]) = 0 := congrArg IntertwiningMap.toLinearMap h
    rw [htrace, ht, map_zero, mul_zero]))
  ext v
  apply hinj
  simpa [T] using eq_neg_of_add_eq_zero_right (LinearMap.congr_fun hzero v)

/-- The complement sum of a class function is the prescribed scalar precisely when twice the
trivial coefficient has that value and every nontrivial row occurring in the character
expansion sends the translating element to minus the identity. -/
theorem add_mul_eq_const_iff_characterPairing [IsAlgClosed k] [Invertible (Nat.card G : k)]
    (f : ClassFunction k G) (c : G) (d : k) :
    (∀ g, f.val g + f.val (c * g) = d) ↔
      2 * characterPairing (ofCharacter (trivial k G k)) f = d ∧
      ∀ i : Fin (Nat.card (ConjClasses G)),
        irreducibleRepresentation k i ≠ trivial k G _ →
        characterPairing (ofCharacter (irreducibleRepresentation k i)) f ≠ 0 →
          irreducibleRepresentation k i c = -1 := by
  constructor
  · intro hf
    exact ⟨two_mul_characterPairing_trivial_of_add_mul_eq_const f hf (Invertible.ne_zero _),
      fun i ↦ apply_eq_neg_one_of_characterPairing_ne_zero f hf _⟩
  rintro ⟨hd, hodd⟩
  let ρ := fun i : Fin (Nat.card (ConjClasses G)) ↦ irreducibleRepresentation k i
  let a := fun i ↦ characterPairing (ofCharacter (ρ i)) f
  have hexp (g : G) : f.val g = ∑ i, a i * (ρ i).character g :=
    apply_eq_sum_characterPairing_mul_character ρ
      (pairwise_isEmpty_equiv_irreducibleRepresentation k) (by simp) f g
  -- The trivial rows are constant, and the two translates cancel on each supported odd row.
  have hconst (g : G) : f.val g + f.val (c * g) = f.val 1 + f.val c := by
    simp only [hexp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hzero : a i = 0
    · simp [hzero]
    by_cases htriv : ρ i = trivial k G _
    · simp [htriv, char_trivial]
    have hc : ρ i c = -1 := hodd i htriv hzero
    have hcg : ρ i (c * g) = -(ρ i g) := by
      rw [map_mul, hc]
      exact neg_one_mul (ρ i g)
    simp [character, hcg, hc]
  have hmean := two_mul_characterPairing_trivial_of_add_mul_eq_const f hconst (Invertible.ne_zero _)
  exact fun g ↦ (hconst g).trans (hmean.symm.trans hd)

end TauCeti.ClassFunction
