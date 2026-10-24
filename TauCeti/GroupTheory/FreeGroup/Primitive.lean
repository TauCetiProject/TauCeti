/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Nielsen
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NormNum
public import TauCeti.GroupTheory.FreeGroup.ProperPower

/-!
# Primitive elements of free groups

An element is primitive if it occurs in a free basis. A primitive element admits an integer
character taking value one, which separates it from proper powers, the identity, and
commutators. The definition uses Mathlib's `FreeGroupBasis`, so it applies to any free group.
-/

public section

open scoped commutatorElement

namespace TauCeti.FreeGroup

universe u

variable {G : Type u} [Group G]

/-- An element of a free group is primitive if it belongs to some free basis. -/
def IsPrimitive (x : G) : Prop :=
  ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x

/-- A primitive element is exactly an element of some free basis. -/
theorem isPrimitive_def (x : G) :
    IsPrimitive x ↔ ∃ (ι : Type u) (b : FreeGroupBasis ι G) (i : ι), b i = x :=
  Iff.rfl

end TauCeti.FreeGroup

namespace FreeGroupBasis

variable {G : Type u} [Group G]

/-- Every element of a free basis is primitive. -/
@[simp] theorem isPrimitive {ι : Type u} (b : FreeGroupBasis ι G) (i : ι) :
    TauCeti.FreeGroup.IsPrimitive (b i) :=
  ⟨ι, b, i, rfl⟩

/-- Applying a free basis to an index is the inverse of its representation map applied to
the corresponding canonical generator. -/
@[simp] theorem repr_symm_apply_of {ι : Type u} (b : FreeGroupBasis ι G) (i : ι) :
    b.repr.symm (FreeGroup.of i) = b i :=
  rfl

end FreeGroupBasis

namespace TauCeti.FreeGroup

variable {G : Type u} [Group G]

/-- The canonical generators of a free group are primitive. -/
@[simp] theorem IsPrimitive.of {α : Type u} (a : α) :
    IsPrimitive (FreeGroup.of a) := by
  simpa only [FreeGroupBasis.ofFreeGroup_apply] using
    (FreeGroupBasis.ofFreeGroup α).isPrimitive a

/-- A group isomorphism carries primitive elements to primitive elements. -/
theorem IsPrimitive.map_mulEquiv {H : Type u} [Group H]
    (e : G ≃* H) {x : G} (hx : IsPrimitive x) : IsPrimitive (e x) := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  exact ⟨ι, b.map e, i, FreeGroupBasis.map_apply b e i⟩

/-- Primitivity is invariant under group isomorphisms. -/
@[simp] theorem isPrimitive_map_mulEquiv_iff {H : Type u} [Group H]
    (e : G ≃* H) {x : G} : IsPrimitive (e x) ↔ IsPrimitive x := by
  constructor
  · intro hx
    simpa using hx.map_mulEquiv e.symm
  · exact IsPrimitive.map_mulEquiv e

/-- Conjugation preserves and reflects primitivity. -/
@[simp] theorem isPrimitive_conj_iff (g x : G) :
    IsPrimitive (g * x * g⁻¹) ↔ IsPrimitive x :=
  isPrimitive_map_mulEquiv_iff (MulAut.conj g)

/-- The inverse of a primitive element is primitive. -/
theorem IsPrimitive.inv {x : G} (hx : IsPrimitive x) : IsPrimitive x⁻¹ := by
  have inv_of {α : Type u} (a : α) : IsPrimitive (FreeGroup.of a)⁻¹ := by
    simpa using (IsPrimitive.of a).map_mulEquiv generatorInversion
  obtain ⟨ι, b, i, rfl⟩ := hx
  simpa only [FreeGroupBasis.repr_symm_apply_of, map_inv] using
    (inv_of i).map_mulEquiv b.repr.symm

/-- An element is primitive exactly when its inverse is primitive. -/
@[simp] theorem isPrimitive_inv {x : G} : IsPrimitive x⁻¹ ↔ IsPrimitive x :=
  ⟨fun h => by simpa using h.inv, IsPrimitive.inv⟩

end TauCeti.FreeGroup

namespace FreeGroupBasis

variable {G : Type u} [Group G]

/-- The product of two distinct elements of a free basis is primitive. -/
theorem isPrimitive_mul {ι : Type u} (b : FreeGroupBasis ι G) {i j : ι} (hij : i ≠ j) :
    TauCeti.FreeGroup.IsPrimitive (b i * b j) := by
  classical
  have h := (TauCeti.FreeGroup.IsPrimitive.of i).map_mulEquiv
    (TauCeti.FreeGroup.nielsenMul i j hij)
  have h' := h.map_mulEquiv b.repr.symm
  simpa only [TauCeti.FreeGroup.nielsenMul_of_left, map_mul, repr_symm_apply_of] using h'

end FreeGroupBasis

namespace TauCeti.FreeGroup

variable {G : Type u} [Group G]

/-- The product of two distinct canonical generators is primitive. -/
theorem isPrimitive_of_mul_of {α : Type u} (a b : α) (hab : a ≠ b) :
    IsPrimitive (FreeGroup.of a * FreeGroup.of b) := by
  simpa only [FreeGroupBasis.ofFreeGroup_apply] using
    (FreeGroupBasis.ofFreeGroup α).isPrimitive_mul hab

/-- A primitive element has an integer character that takes value one on it. -/
theorem IsPrimitive.exists_monoidHom_apply_eq_ofAdd_one {x : G} (hx : IsPrimitive x) :
    ∃ f : G →* Multiplicative ℤ, f x = Multiplicative.ofAdd 1 := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  classical
  let f : G →* Multiplicative ℤ :=
    b.lift (fun j : ι => if j = i then Multiplicative.ofAdd 1 else 1)
  refine ⟨f, ?_⟩
  simp [f]

/-- Primitive elements cannot be proper powers. -/
theorem IsPrimitive.not_isProperPower {x : G} (hx : IsPrimitive x) :
    ¬ Group.IsProperPower x := by
  obtain ⟨ι, b, i, rfl⟩ := hx
  simpa only [FreeGroupBasis.repr_symm_apply_of] using
    (MulEquiv.isProperPower_map_iff b.repr.symm (x := FreeGroup.of i)).not.mpr
      (FreeGroup.not_isProperPower_of i)

/-- The identity is not primitive in a free group. -/
@[simp] theorem not_isPrimitive_one : ¬ IsPrimitive (1 : G) := by
  intro h
  exact h.not_isProperPower Group.IsProperPower.one

/-- A primitive element does not lie in the commutator subgroup. -/
theorem IsPrimitive.notMem_commutator {x : G} (hx : IsPrimitive x) :
    x ∉ commutator G := by
  obtain ⟨f, hf⟩ := hx.exists_monoidHom_apply_eq_ofAdd_one
  intro h
  have : (Multiplicative.ofAdd (1 : ℤ)) = 1 := by
    rw [← hf]
    exact (Abelianization.commutator_le_ker f) h
  norm_num at this

/-- A commutator is never primitive in a free group. -/
@[simp] theorem not_isPrimitive_commutator (x y : G) : ¬ IsPrimitive ⁅x, y⁆ := by
  intro h
  exact h.notMem_commutator
    (Subgroup.commutator_mem_commutator (show x ∈ (⊤ : Subgroup G) from trivial)
      (show y ∈ (⊤ : Subgroup G) from trivial))

/-- A power with exponent at least two is not primitive. -/
theorem not_isPrimitive_pow (x : G) {n : ℕ} (hn : 2 ≤ n) : ¬ IsPrimitive (x ^ n) :=
  fun h => h.not_isProperPower (Group.isProperPower_pow x hn)

/-- The square of any group element is not primitive. -/
@[simp] theorem not_isPrimitive_sq (x : G) : ¬ IsPrimitive (x ^ 2) :=
  not_isPrimitive_pow x (by decide)

end TauCeti.FreeGroup
