/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Semiprimary

/-!
# Primitive ideals and the Jacobson radical

A primitive ideal is the annihilator of a nonzero simple left module. We define this
using the quotients by maximal left ideals, so the predicate does not depend on a
choice of universe for the simple module. The characterization by arbitrary simple
modules follows from Mathlib's `isSimpleModule_iff_quot_maximal`.

The Jacobson radical is the intersection of the primitive ideals. Thus a ring has
zero Jacobson radical exactly when its simple left modules separate its elements.
No commutativity, norm or finiteness hypothesis is needed. In the commutative case,
primitive ideals are exactly maximal ideals.

## References

* Dales, *Banach Algebras and Automatic Continuity*, §§1.3–1.5.
* The simple-module realization uses `isSimpleModule_iff_quot_maximal`, and the
  radical inclusion uses `IsSemisimpleModule.jacobson_le_annihilator`.
-/

public section

universe u v

namespace Ideal

variable {R : Type u} [Ring R]

/-- A primitive ideal is the annihilator of the simple left module associated to
a maximal left ideal. Equivalently, it is the annihilator of a simple left module in any universe;
see `isPrimitive_annihilator` and `IsPrimitive.exists_annihilator`. -/
def IsPrimitive (I : Ideal R) : Prop :=
  ∃ J : Ideal R, J.IsMaximal ∧ Module.annihilator R (R ⧸ J) = I

/-- Primitive ideals are exactly annihilators of quotients by maximal left ideals. -/
theorem isPrimitive_iff_exists_isMaximal (I : Ideal R) :
    I.IsPrimitive ↔ ∃ J : Ideal R, J.IsMaximal ∧ Module.annihilator R (R ⧸ J) = I :=
  Iff.rfl

/-- The annihilator of a simple left module is primitive. The module may live in
any universe. -/
theorem isPrimitive_annihilator (M : Type v) [AddCommGroup M] [Module R M]
    [hM : IsSimpleModule R M] : (Module.annihilator R M).IsPrimitive := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hM
  exact ⟨J, hJ, e.annihilator_eq.symm⟩

/-- A primitive ideal has a simple-module realization in the universe of the ring. -/
theorem IsPrimitive.exists_annihilator {I : Ideal R} (hI : I.IsPrimitive) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M),
      IsSimpleModule R M ∧ Module.annihilator R M = I := by
  obtain ⟨J, hJ, hJI⟩ := hI
  exact ⟨R ⧸ J, inferInstance, inferInstance,
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp hJ), hJI⟩

/-- Primitive ideals are two-sided even when the ring is noncommutative. -/
theorem IsPrimitive.isTwoSided {I : Ideal R} (hI : I.IsPrimitive) : I.IsTwoSided := by
  obtain ⟨J, _, rfl⟩ := hI
  infer_instance

/-- A primitive ideal is proper, because its realizing simple module is nonzero. -/
theorem IsPrimitive.ne_top {I : Ideal R} (hI : I.IsPrimitive) : I ≠ ⊤ := by
  obtain ⟨M, _, _, hM, rfl⟩ := hI.exists_annihilator
  have := hM.nontrivial
  simpa [Module.annihilator_eq_top_iff] using (not_subsingleton M)

/-- The whole ring is never a primitive ideal. -/
@[simp]
theorem not_isPrimitive_top : ¬ (⊤ : Ideal R).IsPrimitive :=
  fun h ↦ h.ne_top rfl

/-- Every primitive ideal contains the Jacobson radical. -/
theorem IsPrimitive.jacobson_le {I : Ideal R} (hI : I.IsPrimitive) :
    Ring.jacobson R ≤ I := by
  obtain ⟨M, _, _, hM, rfl⟩ := hI.exists_annihilator
  exact IsSemisimpleModule.jacobson_le_annihilator R M

/-- In a commutative ring, primitive ideals are exactly maximal ideals. -/
@[simp]
theorem isPrimitive_iff_isMaximal {S : Type*} [CommRing S] (I : Ideal S) :
    I.IsPrimitive ↔ I.IsMaximal := by
  constructor
  · intro hI
    obtain ⟨M, _, _, hM, rfl⟩ := hI.exists_annihilator
    exact IsSimpleModule.annihilator_isMaximal
  · intro hI
    exact ⟨I, hI, Ideal.annihilator_quotient⟩

end Ideal

namespace TauCeti.Ring

variable (R : Type u) [Ring R]

/-- The Jacobson radical of a ring is the intersection of its primitive ideals. -/
theorem jacobson_eq_sInf_isPrimitive :
    Ring.jacobson R = sInf {I : Ideal R | I.IsPrimitive} := by
  refine le_antisymm (le_sInf fun I hI ↦ hI.jacobson_le) ?_
  rw [Ring.jacobson_eq_sInf_isMaximal]
  refine le_sInf fun J hJ ↦ ?_
  have : J.IsMaximal := hJ
  have hprim : (Module.annihilator R (R ⧸ J)).IsPrimitive := ⟨J, hJ, rfl⟩
  refine (sInf_le hprim).trans ?_
  intro a ha
  rw [Submodule.annihilator_quotient] at ha
  simpa using (Submodule.mem_colon.mp ha) 1 (Set.mem_univ 1)

/-- An element is in the radical exactly when it belongs to every primitive ideal. -/
theorem mem_jacobson_iff_forall_mem_isPrimitive {a : R} :
    a ∈ Ring.jacobson R ↔ ∀ I : Ideal R, I.IsPrimitive → a ∈ I := by
  rw [jacobson_eq_sInf_isPrimitive, Submodule.mem_sInf]
  rfl

/-- Zero Jacobson radical means that primitive ideals separate nonzero elements. -/
theorem jacobson_eq_bot_iff_exists_isPrimitive :
    Ring.jacobson R = ⊥ ↔
      ∀ a : R, a ≠ 0 → ∃ I : Ideal R, I.IsPrimitive ∧ a ∉ I := by
  simp only [Submodule.eq_bot_iff, mem_jacobson_iff_forall_mem_isPrimitive]
  constructor
  · intro h a ha
    by_contra! h'
    exact ha (h a h')
  · intro h a ha
    by_contra ha0
    obtain ⟨I, hI, haI⟩ := h a ha0
    exact haI (ha I hI)

end TauCeti.Ring
