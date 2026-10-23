/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Nielsen
public import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.Divisibility.Units

/-!
# Primitive elements of free groups

An element of a free group is primitive if it occurs in some free basis. The basis
formulation works for any group equipped with a free-group structure and makes
primitivity invariant under group isomorphisms. A primitive element has a map to
the infinite cyclic group taking it to a generator; this detects several basic
nonexamples.

For a free group, primitivity is equivalent to an automorphism sending the element
to a canonical generator. The Nielsen automorphism `FreeGroup.mulGeneratorEquiv`
sends `of a` to `of a * of b` when `a ≠ b`; its generator formulas are simp
lemmas, and it gives `isPrimitive_of_mul`.
-/

public section

namespace TauCeti.FreeGroup

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- An element is primitive if it occurs in a free basis of its group. -/
def IsPrimitive (x : G) : Prop :=
  ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x

/-- An element is primitive exactly when it belongs to some free basis. -/
theorem isPrimitive_def {x : G} : IsPrimitive x ↔
    ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x := Iff.rfl

end TauCeti.FreeGroup

namespace FreeGroupBasis

variable {G : Type u} [Group G]

/-- Every element of a free basis is primitive. -/
theorem isPrimitive {ι : Type*} (b : FreeGroupBasis ι G) (i : ι) :
    TauCeti.FreeGroup.IsPrimitive (b i) := by
  let e : ι ≃ Set.range b := Equiv.ofInjective b b.injective
  refine ⟨Set.range b, b.reindex e, e i, ?_⟩
  simp [e]

end FreeGroupBasis

namespace TauCeti.FreeGroup

open scoped commutatorElement

variable {G : Type u} [Group G]

namespace IsPrimitive

variable {x : G}

/-- A group isomorphism carries primitive elements to primitive elements. -/
theorem map_mulEquiv {H : Type*} [Group H] (e : G ≃* H) (hx : IsPrimitive x) :
    IsPrimitive (e x) := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  simpa using (b.map e).isPrimitive i

/-- A primitive element maps to a generator of an infinite cyclic group. -/
theorem exists_hom_int (hx : IsPrimitive x) :
    ∃ f : G →* Multiplicative ℤ, f x = Multiplicative.ofAdd 1 := by
  classical
  obtain ⟨ι, b, i, rfl⟩ := hx
  let f : G →* Multiplicative ℤ :=
    b.lift fun j : ι => Multiplicative.ofAdd (if j = i then 1 else 0)
  refine ⟨f, ?_⟩
  simp [f]

/-- Some map to the infinite cyclic group detects a primitive element. -/
theorem not_forall_hom_int_eq_one (hx : IsPrimitive x) :
    ¬ ∀ f : G →* Multiplicative ℤ, f x = 1 := by
  rintro h
  obtain ⟨f, hf⟩ := hx.exists_hom_int
  have hn : (1 : Multiplicative ℤ) ≠ Multiplicative.ofAdd 1 := by decide
  exact hn ((h f).symm.trans hf)

/-- A primitive element is nontrivial. -/
theorem ne_one (hx : IsPrimitive x) : x ≠ 1 := by
  intro h
  apply hx.not_forall_hom_int_eq_one
  intro f
  simp [h]

/-- A primitive element is not a positive power with exponent at least two. -/
theorem ne_pow_of_two_le (hx : IsPrimitive x) {y : G} {n : ℕ} (hn : 2 ≤ n) :
    x ≠ y ^ n := by
  obtain ⟨f, hf⟩ := hx.exists_hom_int
  intro h
  rw [h, map_pow] at hf
  have hi : (n : ℤ) * Multiplicative.toAdd (f y) = 1 := by
    have hh := congrArg Multiplicative.toAdd hf
    simpa using hh
  have hu : IsUnit (n : ℤ) := isUnit_iff_dvd_one.mpr ⟨_, hi.symm⟩
  have hn1 : n = 1 := Nat.isUnit_iff.mp (Int.ofNat_isUnit.mp hu)
  omega

end IsPrimitive

/-- Primitivity is invariant under a group isomorphism. -/
@[simp]
theorem isPrimitive_map_iff {H : Type*} [Group H] {x : G} (e : G ≃* H) :
    IsPrimitive (e x) ↔ IsPrimitive x := by
  constructor
  · intro h
    simpa using h.map_mulEquiv e.symm
  · exact IsPrimitive.map_mulEquiv e

/-- The identity element of a group is not primitive. -/
@[simp]
theorem not_isPrimitive_one : ¬ IsPrimitive (1 : G) := by
  intro h
  exact h.ne_one rfl

/-- A power with exponent at least two is not primitive. -/
theorem not_isPrimitive_pow {y : G} {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsPrimitive (y ^ n) := by
  intro h
  exact h.ne_pow_of_two_le hn rfl

/-- An element of the commutator subgroup is not primitive. -/
theorem not_isPrimitive_of_mem_commutator {x : G} (hx : x ∈ commutator G) :
    ¬ IsPrimitive x := by
  intro h
  apply h.not_forall_hom_int_eq_one
  intro f
  exact MonoidHom.mem_ker.mp ((Abelianization.commutator_le_ker f) hx)

/-- A commutator is not primitive, since every map to an abelian group kills it. -/
@[simp]
theorem not_isPrimitive_commutatorElement (x y : G) :
    ¬ IsPrimitive (⁅x, y⁆) := by
  apply not_isPrimitive_of_mem_commutator
  rw [commutator_def]
  exact Subgroup.commutator_mem_commutator (by simp) (by simp)

end TauCeti.FreeGroup

namespace TauCeti.FreeGroup.IsPrimitive

/-- Every canonical generator of a free group is primitive. -/
@[simp]
theorem of {α : Type u} (a : α) :
    IsPrimitive (_root_.FreeGroup.of a) :=
  ⟨α, FreeGroupBasis.ofFreeGroup α, a, FreeGroupBasis.ofFreeGroup_apply a⟩

end TauCeti.FreeGroup.IsPrimitive

namespace FreeGroup

/-- A free-group element is primitive exactly when some automorphism sends it to a
canonical generator. -/
theorem isPrimitive_iff_exists_mulEquiv {α : Type u} (x : FreeGroup α) :
    TauCeti.FreeGroup.IsPrimitive x ↔
      ∃ (e : FreeGroup α ≃* FreeGroup α) (a : α), e x = of a := by
  constructor
  · rintro ⟨ι, b, i, rfl⟩
    let r : α ≃ ι := Equiv.ofFreeGroupEquiv b.repr
    let b' : FreeGroupBasis α (FreeGroup α) := b.reindex r.symm
    refine ⟨b'.repr, r.symm i, ?_⟩
    have hb : b' (r.symm i) = b i := by simp [b']
    rw [← hb]
    exact b'.repr_apply_coe _
  · rintro ⟨e, a, h⟩
    refine ⟨α, FreeGroupBasis.ofRepr e, a, ?_⟩
    apply e.injective
    exact (FreeGroupBasis.repr_apply_coe (FreeGroupBasis.ofRepr e) a).trans h.symm

end FreeGroup


namespace TauCeti.FreeGroup

open _root_.FreeGroup

/-- The product of two distinct canonical generators is primitive. -/
theorem isPrimitive_of_mul {α : Type u} {a b : α} (hab : a ≠ b) :
    TauCeti.FreeGroup.IsPrimitive (of a * of b) := by
  classical
  have h := (TauCeti.FreeGroup.IsPrimitive.of a).map_mulEquiv
    (FreeGroup.mulGeneratorEquiv a b hab)
  simpa only [FreeGroup.mulGeneratorEquiv_apply_of] using h

end TauCeti.FreeGroup
