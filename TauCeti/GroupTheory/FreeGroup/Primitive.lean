/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.GroupTheory.FreeGroup.Nielsen
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
public import TauCeti.GroupTheory.FreeGroup.ProperPower.Basic

/-!
# Primitive elements of free groups

An element is primitive if it occurs in a free basis. The definition applies to any group,
and the basis witness ensures that the group is free. Primitive elements cannot be proper
powers or lie in the commutator subgroup: a basis coordinate maps them to the generator
of the infinite cyclic group. Primitivity is preserved by group isomorphisms.

The Nielsen move replacing one free generator `a` by `a b ^ n` for a distinct generator
`b` and any `n : ℤ` shows that `a b ^ n`, in particular `a b`, is primitive.
-/

public section

namespace Group

universe u v
open scoped commutatorElement

/-- An element of a group is primitive when it belongs to some free basis of the group. -/
def IsPrimitive {G : Type u} [Group G] (x : G) : Prop :=
  ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x

theorem isPrimitive_iff {G : Type u} [Group G] {x : G} :
    IsPrimitive x ↔ ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x := Iff.rfl

end Group

namespace FreeGroupBasis

/-- Every element of a free basis is primitive. -/
@[simp]
theorem isPrimitive {G : Type u} [Group G] {ι : Type v}
    (b : FreeGroupBasis ι G) (i : ι) : Group.IsPrimitive (b i) :=
  ⟨Set.range b, b.reindex (Equiv.ofInjective _ b.injective),
    ⟨b i, ⟨i, rfl⟩⟩, by simp⟩

/-- The inverse basis representation sends a free generator to its basis element. -/
@[simp] theorem repr_symm_apply_of {G : Type u} [Group G] {ι : Type v}
    (b : FreeGroupBasis ι G) (i : ι) : b.repr.symm (FreeGroup.of i) = b i := by
  apply b.repr.injective
  simp

end FreeGroupBasis

namespace Group

open scoped commutatorElement

namespace IsPrimitive

/-- A primitive element is preserved by a group isomorphism. -/
theorem map_mulEquiv {G : Type u} {H : Type v} [Group G] [Group H] {x : G}
    (hx : IsPrimitive x) (e : G ≃* H) : IsPrimitive (e x) := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  simpa using (b.map e).isPrimitive i

/-- The inverse of a primitive element is primitive. -/
theorem inv {G : Type u} [Group G] {x : G} (hx : IsPrimitive x) : IsPrimitive x⁻¹ := by
  have inv_of {α : Type u} (a : α) : IsPrimitive (FreeGroup.of a)⁻¹ := by
    simpa using ((FreeGroupBasis.ofFreeGroup α).isPrimitive a).map_mulEquiv
      (TauCeti.FreeGroup.generatorInversion)
  obtain ⟨ι, b, i, rfl⟩ := hx
  simpa only [map_inv, FreeGroupBasis.repr_symm_apply_of] using
    (inv_of i).map_mulEquiv b.repr.symm

/-- A primitive element is not a proper power. -/
theorem not_isProperPower {G : Type u} [Group G] {x : G} (hx : IsPrimitive x) :
    ¬ Group.IsProperPower x := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  intro hp
  exact FreeGroup.not_isProperPower_of i (by
    simpa using Group.IsProperPower.map b.repr hp)

/-- A primitive element is nontrivial. -/
theorem ne_one {G : Type u} [Group G] {x : G} (hx : IsPrimitive x) : x ≠ 1 :=
  Group.ne_one_of_not_isProperPower hx.not_isProperPower

/-- Some homomorphism sends a primitive element to the generator
`Multiplicative.ofAdd 1` of the infinite cyclic group. -/
theorem exists_monoidHom_apply_eq_ofAdd_one {G : Type u} [Group G] {x : G}
    (hx : IsPrimitive x) :
    ∃ f : G →* Multiplicative ℤ, f x = Multiplicative.ofAdd 1 := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  obtain ⟨f, hf⟩ := FreeGroup.exists_monoidHom_apply_eq_ofAdd_one i
  refine ⟨f.comp b.repr.toMonoidHom, ?_⟩
  simpa using hf

end IsPrimitive

/-- An element is primitive exactly when its inverse is primitive. -/
@[simp] theorem isPrimitive_inv {G : Type u} [Group G] {x : G} :
    IsPrimitive x⁻¹ ↔ IsPrimitive x :=
  ⟨fun h => by simpa using h.inv, IsPrimitive.inv⟩

end Group

namespace MulEquiv

/-- Primitivity is preserved and reflected by a group isomorphism. -/
@[simp] theorem isPrimitive_map_iff {G : Type u} {H : Type v} [Group G] [Group H]
    (e : G ≃* H) {x : G} : Group.IsPrimitive (e x) ↔ Group.IsPrimitive x := by
  constructor
  · intro h
    simpa using h.map_mulEquiv e.symm
  · exact fun h => h.map_mulEquiv e

end MulEquiv

namespace Group

open scoped commutatorElement

/-- Conjugation preserves and reflects primitivity. -/
@[simp] theorem isPrimitive_conj_iff {G : Type u} [Group G] (g x : G) :
    IsPrimitive (g * x * g⁻¹) ↔ IsPrimitive x :=
  MulEquiv.isPrimitive_map_iff (MulAut.conj g)

/-- The identity is not a primitive element. -/
@[simp] theorem not_isPrimitive_one {G : Type u} [Group G] : ¬ IsPrimitive (1 : G) := by
  intro h
  exact h.ne_one rfl

/-- A proper natural power cannot be a primitive element. -/
theorem not_isPrimitive_pow {G : Type u} [Group G] (x : G) {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsPrimitive (x ^ n) := by
  intro h
  exact h.not_isProperPower (Group.isProperPower_pow x hn)

/-- A proper integer power cannot be a primitive element. -/
theorem not_isPrimitive_zpow {G : Type u} [Group G] (x : G) {n : ℤ}
    (hn : 2 ≤ n.natAbs) : ¬ IsPrimitive (x ^ n) := by
  intro h
  exact h.not_isProperPower (Group.isProperPower_zpow x hn)

/-- A square cannot be a primitive element. -/
@[simp] theorem not_isPrimitive_sq {G : Type u} [Group G] (x : G) :
    ¬ IsPrimitive (x ^ 2) :=
  not_isPrimitive_pow x (by omega)

/-- An element of the commutator subgroup cannot belong to a free basis. -/
theorem not_isPrimitive_of_mem_commutator {G : Type u} [Group G] {x : G}
    (hx : x ∈ commutator G) : ¬ IsPrimitive x := by
  intro h
  obtain ⟨f, hf⟩ := h.exists_monoidHom_apply_eq_ofAdd_one
  have hcomm : f x = 1 := (Abelianization.commutator_le_ker f hx)
  have hone : (Multiplicative.ofAdd (1 : ℤ)) ≠ 1 := by decide
  exact hone (hf ▸ hcomm)

/-- A commutator cannot belong to a free basis. -/
@[simp] theorem not_isPrimitive_commutator {G : Type u} [Group G] (x y : G) :
    ¬ IsPrimitive ⁅x, y⁆ :=
  not_isPrimitive_of_mem_commutator
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

end Group

namespace FreeGroup

/-- Every free generator is primitive. -/
@[simp]
theorem isPrimitive_of {α : Type u} (a : α) : Group.IsPrimitive (of a) :=
  (FreeGroupBasis.ofFreeGroup α).isPrimitive a

end FreeGroup

namespace FreeGroupBasis

/-- Multiplying a basis element by an integral power of another gives a primitive element. -/
theorem isPrimitive_mul_zpow {G : Type u} [Group G] {ι : Type v}
    (b : FreeGroupBasis ι G) {i j : ι} (hij : i ≠ j) (n : ℤ) :
    Group.IsPrimitive (b i * b j ^ n) := by
  classical
  simpa only [TauCeti.FreeGroup.nielsenMul_of_left, map_mul, map_zpow,
    FreeGroupBasis.repr_symm_apply_of] using
    (((FreeGroup.isPrimitive_of i).map_mulEquiv
      (TauCeti.FreeGroup.nielsenMul i j hij n)).map_mulEquiv b.repr.symm)

/-- The product of two distinct basis elements is primitive. -/
theorem isPrimitive_mul {G : Type u} [Group G] {ι : Type v}
    (b : FreeGroupBasis ι G) {i j : ι} (hij : i ≠ j) :
    Group.IsPrimitive (b i * b j) := by
  simpa using b.isPrimitive_mul_zpow hij 1

end FreeGroupBasis

namespace FreeGroup

/-- Multiplying a free generator by an integral power of another gives a primitive element. -/
theorem isPrimitive_of_mul_of_zpow {α : Type u} (a b : α) (hab : a ≠ b) (n : ℤ) :
    Group.IsPrimitive (of a * of b ^ n) := by
  simpa using (FreeGroupBasis.ofFreeGroup α).isPrimitive_mul_zpow hab n

/-- The product of two distinct free generators is primitive. -/
theorem isPrimitive_of_mul_of {α : Type u} (a b : α) (hab : a ≠ b) :
    Group.IsPrimitive (of a * of b) := by
  simpa using isPrimitive_of_mul_of_zpow a b hab 1

end FreeGroup

namespace FreeGroup

/-- An element of a free group is primitive exactly when it is the image of a canonical
generator under an automorphism. -/
theorem isPrimitive_iff_exists_mulEquiv_of {α : Type u} {x : FreeGroup α} :
    Group.IsPrimitive x ↔
      ∃ (e : FreeGroup α ≃* FreeGroup α) (a : α), e (FreeGroup.of a) = x := by
  constructor
  · rintro ⟨ι, b, i, rfl⟩
    let c : α ≃ ι := Equiv.ofFreeGroupEquiv b.repr
    let e : FreeGroup α ≃* FreeGroup α := (FreeGroup.freeGroupCongr c).trans b.repr.symm
    refine ⟨e, c.symm i, ?_⟩
    simp [e]
  · rintro ⟨e, a, rfl⟩
    exact (FreeGroup.isPrimitive_of a).map_mulEquiv e

end FreeGroup
