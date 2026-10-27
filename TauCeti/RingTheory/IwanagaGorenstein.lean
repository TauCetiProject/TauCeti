/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Algebra.Module.Injective
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Iwanaga–Gorenstein rings

A ring `A` is **Iwanaga–Gorenstein** when it is left and right noetherian and the regular module
has finite injective dimension on both sides. Right modules are left `Aᵐᵒᵖ`-modules, so the
right-hand conditions are stated for `Aᵐᵒᵖ`. These are the rings of Buchweitz's comparison between
Gorenstein-projective modules and the singularity category.

A left and right noetherian ring that is self-injective on both sides, a quasi-Frobenius ring, is
Iwanaga–Gorenstein with both injective dimensions zero
(`TauCeti.IsIwanagaGorenstein.of_injective`). In particular division rings are
Iwanaga–Gorenstein.

## Main definitions

* `TauCeti.IsIwanagaGorenstein`: left and right noetherian with both self-injective dimensions
  finite.

## References

* Yasuo Iwanaga, *On rings with finite self-injective dimension*, Comm. Algebra **7** (1979).
* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Section 4.
* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, Section 9.1.
-/

@[expose] public section

namespace TauCeti

open CategoryTheory

universe u

/-- A ring is **Iwanaga–Gorenstein** if it is left and right noetherian and the regular module has
finite injective dimension both as a left and as a right module. -/
class IsIwanagaGorenstein (A : Type u) [Ring A] : Prop where
  isNoetherianRing : IsNoetherianRing A
  isNoetherianRing_op : IsNoetherianRing Aᵐᵒᵖ
  exists_hasInjectiveDimensionLE : ∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of A A) n
  exists_hasInjectiveDimensionLE_op : ∃ n : ℕ, HasInjectiveDimensionLE (ModuleCat.of Aᵐᵒᵖ A) n

namespace IsIwanagaGorenstein

/-- **Quasi-Frobenius rings are Iwanaga–Gorenstein**: a left and right noetherian ring that is
self-injective on both sides has both self-injective dimensions zero. -/
theorem of_injective (A : Type u) [Ring A] [IsNoetherianRing A] [IsNoetherianRing Aᵐᵒᵖ]
    [Module.Injective A A] [Module.Injective Aᵐᵒᵖ A] : IsIwanagaGorenstein A where
  isNoetherianRing := inferInstance
  isNoetherianRing_op := inferInstance
  exists_hasInjectiveDimensionLE := by
    have := Module.injective_object_of_injective_module A A
    exact ⟨0, inferInstance⟩
  exists_hasInjectiveDimensionLE_op := by
    have := Module.injective_object_of_injective_module Aᵐᵒᵖ A
    exact ⟨0, inferInstance⟩

/-- A division ring is injective over itself: a left ideal is zero or everything. -/
private theorem injective_self (D : Type u) [DivisionRing D] : Module.Injective D D :=
  Module.Baer.injective fun I g ↦ by
    rcases Ideal.eq_bot_or_top I with rfl | rfl
    · refine ⟨0, fun x hx ↦ ?_⟩
      obtain rfl := (Submodule.mem_bot D).1 hx
      rw [show (⟨0, hx⟩ : (⊥ : Ideal D)) = 0 from rfl, map_zero, map_zero]
    · exact ⟨g ∘ₗ (LinearEquiv.ofTop (⊤ : Ideal D) rfl).symm.toLinearMap, fun x hx ↦ rfl⟩

/-- Division rings are Iwanaga–Gorenstein. -/
instance (D : Type u) [DivisionRing D] : IsIwanagaGorenstein D :=
  have := injective_self D
  have := injective_self Dᵐᵒᵖ
  have : Module.Injective Dᵐᵒᵖ D :=
    Module.Injective.of_ringEquiv (RingEquiv.refl Dᵐᵒᵖ) (MulOpposite.opLinearEquiv Dᵐᵒᵖ).symm
  of_injective D

end IsIwanagaGorenstein

end TauCeti
