/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
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

/-- A coefficient map respecting deck monomials maps the ambiguity subgroup onto the
corresponding ambiguity subgroup. -/
theorem map_signedMonomialSubgroup {B : Type*} [CommRing B] {m : G →* Aˣ}
    {n : G →* Bˣ} (f : A →+* B) (hf : ∀ g, Units.map f (m g) = n g) :
    (signedMonomialSubgroup m).map (Units.map f.toMonoidHom) = signedMonomialSubgroup n := by
  ext u
  constructor
  · rintro ⟨v, ⟨g, rfl | rfl⟩, rfl⟩
    · exact ⟨g, Or.inl (hf g)⟩
    · exact ⟨g, Or.inr (by simp [hf])⟩
  · rintro ⟨g, rfl | rfl⟩
    · exact ⟨m g, ⟨g, Or.inl rfl⟩, hf g⟩
    · exact ⟨-m g, ⟨g, Or.inr rfl⟩, by simp [hf]⟩

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

/-- Two representatives agree exactly when a unit in the ambiguity subgroup relates them. -/
theorem mk_eq_mk_iff_exists_unit {a b : A} : mk m a = mk m b ↔
    ∃ u ∈ signedMonomialSubgroup m, a = (u : A) * b := by
  rw [mk, Con.coe_mk', (torsionCon m).eq]
  constructor
  · rintro ⟨⟨u, hu⟩, h⟩
    exact ⟨u, hu, by simpa [MulAction.subgroup_smul_def, Units.smul_def] using h.symm⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨⟨u, hu⟩, by simpa [MulAction.subgroup_smul_def, Units.smul_def] using h.symm⟩

/-- Two scalars represent the same torsion class exactly when they differ by a signed
monomial. This includes zero and zero divisors. -/
theorem mk_eq_mk_iff {a b : A} : mk m a = mk m b ↔
    ∃ g, a = (m g : A) * b ∨ a = -(m g : A) * b := by
  rw [mk_eq_mk_iff_exists_unit]
  constructor
  · rintro ⟨u, ⟨g, rfl | rfl⟩, h⟩
    · exact ⟨g, Or.inl h⟩
    · exact ⟨g, Or.inr (by simpa using h)⟩
  · rintro ⟨g, h | h⟩
    · exact ⟨m g, ⟨g, Or.inl rfl⟩, h⟩
    · exact ⟨-m g, ⟨g, Or.inr rfl⟩, by simpa using h⟩

/-- An invariant multiplicative map factors through torsion classes. The two hypotheses express
invariance under signs and multiplication by deck monomials, respectively. -/
def lift {M : Type*} [Monoid M] (f : A →* M) (hneg : ∀ a, f (-a) = f a)
    (hmon : ∀ g a, f ((m g : A) * a) = f a) : TorsionClass m →* M :=
  (torsionCon m).lift f <| by
    intro a b hab
    obtain ⟨g, rfl | rfl⟩ := (mk_eq_mk_iff m).1 ((torsionCon m).eq.2 hab)
    · exact hmon g b
    · rw [Con.ker_rel, neg_mul, hneg, hmon]

@[simp]
theorem lift_mk {M : Type*} [Monoid M] (f : A →* M) (hneg : ∀ a, f (-a) = f a)
    (hmon : ∀ g a, f ((m g : A) * a) = f a) (a : A) :
    lift m f hneg hmon (mk m a) = f a := (rfl)

instance : Zero (TorsionClass m) := ⟨mk m 0⟩

@[simp]
theorem mk_zero : mk m 0 = 0 := (rfl)

instance : CommMonoidWithZero (TorsionClass m) where
  toCommMonoid := inferInstance
  zero_mul a := by
    obtain ⟨a, rfl⟩ := mk_surjective m a
    rw [← mk_zero, ← map_mul]
    simp
  mul_zero a := by
    obtain ⟨a, rfl⟩ := mk_surjective m a
    rw [← mk_zero, ← map_mul]
    simp

/-- Zero-preserving multiplicative maps are determined on scalar representatives. -/
@[ext]
theorem hom_ext₀ {M : Type*} [MulZeroOneClass M] {f g : TorsionClass m →*₀ M}
    (h : ∀ a, f (mk m a) = g (mk m a)) : f = g :=
  MonoidWithZeroHom.ext ((mk_surjective m).forall.2 h)

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

/-- Right multiplication by a deck monomial does not change the torsion class. -/
@[simp]
theorem mk_mul_monomial (g : G) (a : A) : mk m (a * (m g : A)) = mk m a := by
  rw [mul_comm, mk_monomial_mul]

/-- In particular every deck monomial has class one. -/
@[simp]
theorem mk_monomial (g : G) : mk m (m g) = 1 := by
  simpa using mk_monomial_mul m g 1

/-- The sign/monomial ambiguity preserves the zero pattern in every ring image, in particular
in each field component of a total quotient ring. -/
theorem map_eq_zero_iff_of_mk_eq_mk {B : Type*} [Ring B] (f : A →+* B) {a b : A}
    (h : mk m a = mk m b) : f a = 0 ↔ f b = 0 := by
  obtain ⟨u, _, rfl⟩ := (mk_eq_mk_iff_exists_unit m).1 h
  rw [map_mul]
  exact (Units.map f.toMonoidHom u).mul_right_eq_zero

variable {B : Type*} [CommRing B] {m} {n : G →* Bˣ} (f : A →+* B)
  (hf : ∀ g, Units.map f (m g) = n g)

/-- A coefficient map respecting the specified deck monomials descends to torsion classes. -/
def map : TorsionClass m →*₀ TorsionClass n where
  __ := lift m ((mk n).comp f.toMonoidHom) (by simp) (by
    intro g a
    have hg : f (m g : A) = (n g : B) := congrArg Units.val (hf g)
    simp [hg])
  map_zero' := congrArg (mk n) f.map_zero

@[simp]
theorem map_mk (a : A) : map f hf (mk m a) = mk n (f a) := (rfl)

/-- No new ambiguity is introduced by an injective coefficient map with the same deck group. -/
theorem map_injective (hinj : Function.Injective f) : Function.Injective (map f hf) := by
  intro a b h
  obtain ⟨a, rfl⟩ := mk_surjective m a
  obtain ⟨b, rfl⟩ := mk_surjective m b
  rw [map_mk, map_mk, mk_eq_mk_iff_exists_unit] at h
  obtain ⟨u, hu, h⟩ := h
  rw [← map_signedMonomialSubgroup f hf] at hu
  obtain ⟨v, hv, rfl⟩ := hu
  exact (mk_eq_mk_iff_exists_unit m).2 ⟨v, hv, hinj (by simpa using h)⟩

/-- The identity coefficient map induces the identity on torsion classes. -/
@[simp]
theorem map_id : map (m := m) (n := m) (RingHom.id A) (fun g => by ext; simp) =
    MonoidWithZeroHom.id (TorsionClass m) := by
  apply hom_ext₀
  intro a
  rw [map_mk]
  simp

/-- Transporting torsion classes commutes with composition of coefficient maps. -/
theorem map_comp {C : Type*} [CommRing C] {p : G →* Cˣ} (g : B →+* C)
    (hg : ∀ h, Units.map g (n h) = p h) :
    (map g hg).comp (map f hf) =
      map (g.comp f) (fun h => by
        apply Units.ext
        simp [← hf h, ← hg h]) := by
  apply hom_ext₀
  intro a
  simp

end TorsionClass

end TauCeti
