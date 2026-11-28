/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Pairing
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.NormInvariants

/-!
# Character constituents of class functions with constant complement sum

Suppose that a class function on a finite group satisfies `f(g) + f(cg) = d`.
If the group order is invertible in the coefficient field, twice the pairing of `f` with the
trivial character equals `d`. On every nontrivial irreducible whose character pairs nontrivially
with `f`, `c` acts as minus the identity.
When the order is invertible and the class function has an expansion in irreducible characters
with coefficients given by the character pairing, these two conditions also recover the
complement identity.

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

/-- If a class function has constant complement sum, the translating element acts by minus the
identity on every nontrivial irreducible representation whose character pairs nontrivially with
that class function. Its conjugates act by the same sign. -/
theorem apply_eq_neg_one_of_add_apply_mul_left_eq_const_of_characterPairing_ne_zero
    (f : ClassFunction k G)
    {c : G} {d : k} (hf : ∀ g, f.val g + f.val (c * g) = d)
    {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsIrreducible]
    (hρ : ρ ≠ trivial k G V) (hp : characterPairing (ofCharacter ρ) f ≠ 0) :
    ρ c = -1 := by
  classical
  -- As in TauCeti.Representation.characterSumCenter, use the central element with coefficients
  -- f(g⁻¹). The nonzero character pairing ensures its action has nonzero trace.
  let z := ofConjClassesCenter (toConjClasses (invMap f))
  have hz (g : G) : (z : k[G]).coeff g = f.val g⁻¹ := by simp [z]
  have hnorm : ρ.norm = 0 := by
    ext v
    have hv := (ρ.normInvariants v).property
    rwa [coe_normInvariants_apply, IsIrreducible.invariants_eq_bot inferInstance hρ,
      Submodule.mem_bot] at hv
  -- The complement identity multiplies z by 1 + c to give a multiple of the norm.
  have hcomp : (z : k[G]) + (z : k[G]) * MonoidAlgebra.of k G c =
      d • ∑ g : G, MonoidAlgebra.single g (1 : k) := by
    ext g
    have hcoeff : (∑ h : G, MonoidAlgebra.single h (1 : k)).coeff g = 1 := by
      simp
    simpa [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply, hz, hcoeff] using hf g⁻¹
  have hzero := congrArg ρ.asAlgebraHom hcomp
  rw [map_add, map_mul, asAlgebraHom_of, map_smul, asAlgebraHom_sum_single_one, hnorm,
    smul_zero] at hzero
  -- Schur's lemma lets us cancel the action of z, over any coefficient field.
  let T := IntertwiningMap.centralAlgebraMul ρ z.property
  have hinj := (IsIrreducible.injective_or_eq_zero T).resolve_right fun hT ↦ hp (by
    have hz0 : ρ.asAlgebraHom (z : k[G]) = 0 := by
      ext v
      rw [← IntertwiningMap.centralAlgebraMul_apply ρ z.property]
      exact DFunLike.congr_fun hT v
    rw [characterPairing_ofCharacter_eq_inv_card_mul_trace, hz0, map_zero, mul_zero])
  ext v
  apply hinj
  simpa only [T, IntertwiningMap.centralAlgebraMul_apply ρ z.property, LinearMap.add_apply,
    mul_apply_eq_comp, LinearMap.neg_apply, one_apply_eq_self, map_neg] using
    eq_neg_of_add_eq_zero_right (LinearMap.congr_fun hzero v)

/-- Suppose the group order is invertible in the coefficient field and a class function has an
irreducible character expansion with coefficients given by the character pairing. The sum of the
class function and its left translate equals `d` precisely when twice the trivial coefficient
equals `d` and `c` acts by minus the identity on every nontrivial representation with nonzero
coefficient in the expansion. -/
theorem add_apply_mul_left_eq_const_iff_characterPairing_trivial_and_apply_eq_neg_one_of_expansion
    (f : ClassFunction k G) {ι : Type*} [Fintype ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k G (V i)) [∀ i, (ρ i).IsIrreducible]
    (hexp : ∀ g, f.val g = ∑ i, characterPairing (ofCharacter (ρ i)) f * (ρ i).character g)
    (hG : (Nat.card G : k) ≠ 0) (c : G) (d : k) :
    (∀ g, f.val g + f.val (c * g) = d) ↔
      2 * characterPairing (ofCharacter (trivial k G k)) f = d ∧
      ∀ i, ρ i ≠ trivial k G (V i) → characterPairing (ofCharacter (ρ i)) f ≠ 0 →
        ρ i c = -1 := by
  constructor
  · intro hf
    refine ⟨two_mul_characterPairing_trivial_of_add_apply_mul_left_eq_const f hf hG, ?_⟩
    intro i
    exact apply_eq_neg_one_of_add_apply_mul_left_eq_const_of_characterPairing_ne_zero f hf (ρ i)
  rintro ⟨hd, hodd⟩
  -- The trivial rows are constant, and the two translates cancel on each supported odd row.
  have hconst (g : G) : f.val g + f.val (c * g) = f.val 1 + f.val c := by
    simp only [hexp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hzero : characterPairing (ofCharacter (ρ i)) f = 0
    · simp [hzero]
    by_cases htriv : ρ i = trivial k G (V i)
    · let := (ρ i).asModuleEquiv.finiteDimensional
      simp only [htriv, char_trivial]
    have hc : ρ i c = -1 := hodd i htriv hzero
    have hcg : ρ i (c * g) = -(ρ i g) := by
      rw [map_mul, hc]
      exact neg_one_mul (ρ i g)
    simp [character, hcg, hc]
  have hmean := two_mul_characterPairing_trivial_of_add_apply_mul_left_eq_const f hconst hG
  exact fun g ↦ (hconst g).trans (hmean.symm.trans hd)

end TauCeti.ClassFunction
