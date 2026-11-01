/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Torsion classes modulo signs and deck monomials

A homomorphism `m : G →* Aˣ` specifies the deck monomials in a commutative ring `A`.
`TorsionClass m` is the orbit quotient of **all** of `A` by multiplication by
`±m g`, not a quotient of its units. In particular, it accommodates torsions
with some zero field components. Multiplication descends, but addition generally does not.

The representative criterion `TorsionClass.mk_eq_mk_iff` makes the ambiguity explicit.
`TorsionClass.map` transports classes along ring homomorphisms respecting monomials;
an injective ring homomorphism induces an injective map when the deck group is unchanged.
The zero pattern in every ring image is invariant under the ambiguity.

## References

* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  Section 2.
-/

public section

namespace TauCeti

variable {G A : Type*} [Group G] [CommRing A]

/-- The subgroup of units consisting of signed deck monomials. -/
def signedMonomialSubgroup (m : G →* Aˣ) : Subgroup Aˣ where
  carrier := {u | ∃ g, u = m g ∨ u = -m g}
  one_mem' := ⟨1, Or.inl (map_one m).symm⟩
  mul_mem' := by
    rintro u v ⟨g, rfl | rfl⟩ ⟨h, rfl | rfl⟩ <;>
      refine ⟨g * h, ?_⟩ <;> simp [map_mul]
  inv_mem' := by
    rintro u ⟨g, rfl | rfl⟩ <;> refine ⟨g⁻¹, ?_⟩ <;> simp

/-- Membership in the ambiguity subgroup means equality to a monomial or its negative. -/
@[simp]
theorem mem_signedMonomialSubgroup (m : G →* Aˣ) (u : Aˣ) :
    u ∈ signedMonomialSubgroup m ↔ ∃ g, u = m g ∨ u = -m g := Iff.rfl

/-- The signed-monomial orbit relation is a multiplicative congruence. -/
def torsionCon (m : G →* Aˣ) : Con A where
  toSetoid := MulAction.orbitRel (signedMonomialSubgroup m) A
  mul' := by
    rintro a b c d ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u * v, by simp [MulAction.subgroup_smul_def, Units.smul_def,
      mul_mul_mul_comm]⟩

/-- Scalars modulo the sign and deck-monomial ambiguity of based torsion.
The underlying equivalence relation is the orbit relation on the whole ring. -/
abbrev TorsionClass (m : G →* Aˣ) := (torsionCon m).Quotient

namespace TorsionClass

variable (m : G →* Aˣ)

/-- The class of a scalar, as a multiplicative map. -/
def mk : A →* TorsionClass m := (torsionCon m).mk'

/-- Every torsion class has a scalar representative. -/
theorem mk_surjective : Function.Surjective (mk m) := Con.mk'_surjective

/-- Two scalars represent the same torsion class exactly when they differ by a signed
monomial. This includes zero and zero divisors. -/
theorem mk_eq_mk_iff {a b : A} : mk m a = mk m b ↔
    ∃ g, a = (m g : A) * b ∨ a = -(m g : A) * b := by
  rw [mk, Con.coe_mk', (torsionCon m).eq]
  constructor
  · rintro ⟨⟨u, g, hu | hu⟩, h⟩
    · exact ⟨g, Or.inl (by simpa [MulAction.subgroup_smul_def, Units.smul_def, hu]
        using h.symm)⟩
    · exact ⟨g, Or.inr (by simpa [MulAction.subgroup_smul_def, Units.smul_def, hu]
        using h.symm)⟩
  · rintro ⟨g, h | h⟩
    · exact ⟨⟨m g, g, Or.inl rfl⟩,
        by simpa [MulAction.subgroup_smul_def, Units.smul_def] using h.symm⟩
    · exact ⟨⟨-m g, g, Or.inr rfl⟩,
        by simpa [MulAction.subgroup_smul_def, Units.smul_def] using h.symm⟩

instance : Zero (TorsionClass m) := ⟨mk m 0⟩

@[simp]
theorem mk_zero : mk m 0 = 0 := (rfl)

instance : CommMonoidWithZero (TorsionClass m) where
  toCommMonoid := inferInstance
  zero_mul a := Quotient.inductionOn a fun a => by
    exact (map_mul (mk m) 0 a).symm.trans (by simp)
  mul_zero a := Quotient.inductionOn a fun a => by
    exact (map_mul (mk m) a 0).symm.trans (by simp)

/-- The zero class has only the zero representative. -/
@[simp]
theorem mk_eq_zero_iff {a : A} : mk m a = 0 ↔ a = 0 := by
  rw [← mk_zero m, mk_eq_mk_iff]
  simp

instance [Nontrivial A] : Nontrivial (TorsionClass m) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro h
  exact one_ne_zero ((mk_eq_zero_iff m).1 ((map_one (mk m)).trans h))

/-- Changing the sign does not change the torsion class. -/
@[simp]
theorem mk_neg (a : A) : mk m (-a) = mk m a :=
  (mk_eq_mk_iff m).2 ⟨1, Or.inr (by simp)⟩

/-- Multiplying by a deck monomial does not change the torsion class. -/
@[simp]
theorem mk_monomial_mul (g : G) (a : A) : mk m ((m g : A) * a) = mk m a :=
  (mk_eq_mk_iff m).2 ⟨g, Or.inl rfl⟩

/-- In particular every deck monomial has class one. -/
@[simp]
theorem mk_monomial (g : G) : mk m (m g) = 1 := by
  simpa using mk_monomial_mul m g 1

/-- The sign/monomial ambiguity preserves the zero pattern in every ring image, in particular
in each field component of a total quotient ring. -/
theorem map_eq_zero_iff_of_mk_eq_mk {B : Type*} [Ring B] (f : A →+* B) {a b : A}
    (h : mk m a = mk m b) : f a = 0 ↔ f b = 0 := by
  obtain ⟨g, h | h⟩ := (mk_eq_mk_iff m).1 h
  · rw [h, map_mul]
    exact (Units.map f.toMonoidHom (m g)).mul_right_eq_zero
  · rw [h, map_mul, map_neg, neg_mul, neg_eq_zero]
    exact (Units.map f.toMonoidHom (m g)).mul_right_eq_zero

variable {B : Type*} [CommRing B] {m} {n : G →* Bˣ} (f : A →+* B)
  (hf : ∀ g, Units.map f (m g) = n g)

/-- A coefficient map respecting the specified deck monomials descends to torsion classes. -/
def map : TorsionClass m →*₀ TorsionClass n where
  __ := (torsionCon m).lift ((mk n).comp f.toMonoidHom) <| by
    intro a b hab
    obtain ⟨g, h | h⟩ := (mk_eq_mk_iff m).1 ((torsionCon m).eq.2 hab)
    · apply (mk_eq_mk_iff n).2
      exact ⟨g, Or.inl (by simpa [← hf g] using congrArg f h)⟩
    · apply (mk_eq_mk_iff n).2
      exact ⟨g, Or.inr (by simpa [← hf g] using congrArg f h)⟩
  map_zero' := congrArg (mk n) f.map_zero

@[simp]
theorem map_mk (a : A) : map f hf (mk m a) = mk n (f a) := (rfl)

/-- No new ambiguity is introduced by an injective coefficient map with the same deck group. -/
theorem map_injective (hinj : Function.Injective f) : Function.Injective (map f hf) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun a b h => ?_
  obtain ⟨g, h | h⟩ := (mk_eq_mk_iff n).1 h
  · apply (mk_eq_mk_iff m).2
    exact ⟨g, Or.inl (hinj (by simpa [← hf g] using h))⟩
  · apply (mk_eq_mk_iff m).2
    exact ⟨g, Or.inr (hinj (by simpa [← hf g] using h))⟩

/-- The identity coefficient map induces the identity on torsion classes. -/
@[simp]
theorem map_id : map (RingHom.id A) (fun _ => rfl : ∀ g, Units.map (RingHom.id A) (m g) = m g) =
    MonoidWithZeroHom.id (TorsionClass m) := by
  ext a
  exact Quotient.inductionOn a fun _ => rfl

/-- Transporting torsion classes commutes with composition of coefficient maps. -/
theorem map_comp {C : Type*} [CommRing C] {p : G →* Cˣ} (g : B →+* C)
    (hg : ∀ h, Units.map g (n h) = p h) :
    (map g hg).comp (map f hf) =
      map (g.comp f) (fun h => by
        apply Units.ext
        simp [← hf h, ← hg h]) := by
  ext a
  exact Quotient.inductionOn a fun _ => rfl

end TorsionClass

end TauCeti
