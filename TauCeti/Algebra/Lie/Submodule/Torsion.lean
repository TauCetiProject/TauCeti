/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# The torsion Lie submodule

The torsion submodule `Submodule.torsion R M` of a Lie module `M` over a commutative ring `R`, the
elements killed by a non-zero-divisor of `R`, is stable under the Lie action because
`a • ⁅x, m⁆ = ⁅x, a • m⁆`. This file packages it as a Lie submodule and records the facts that
cannot be read off from `Submodule.torsion` downstream: the Lie submodule and the quotient by it
are indexed by `LieSubmodule`, not by its carrier.

## Main definitions

* `LieSubmodule.torsion`: the torsion submodule of a Lie module, as a Lie submodule.

## Main results

* `LieSubmodule.torsion_eq_bot_iff` and `LieSubmodule.torsion_eq_top_iff`: the torsion Lie
  submodule is trivial exactly when the module is torsion-free, and everything exactly when the
  module is torsion. Neither needs `R` to be a domain.
* `LieSubmodule.torsion_isTorsion` and `LieSubmodule.torsion_quotient`: the torsion Lie submodule is
  a torsion module, and the quotient by it is torsion-free, so
  `Module.IsTorsionFree R (M ⧸ LieSubmodule.torsion R L M)` is an instance.
* `TauCeti.isTorsion_or_isTorsionFree_of_isIrreducible`: an irreducible Lie module is either
  torsion or torsion-free.
-/

public section

namespace LieSubmodule

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (R L M) in
/-- The **torsion Lie submodule** of a Lie module: the torsion submodule `Submodule.torsion R M`
of the elements killed by a non-zero-divisor of `R`, which is stable under the Lie action because
`a • ⁅x, m⁆ = ⁅x, a • m⁆`. -/
def torsion : LieSubmodule R L M :=
  { Submodule.torsion R M with
    lie_mem := fun {x m} hm ↦ by
      obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hm
      refine (Submodule.mem_torsion_iff _).2 ⟨a, ?_⟩
      rw [Submonoid.smul_def, ← lie_smul, ← Submonoid.smul_def, ha, lie_zero] }

@[simp]
theorem toSubmodule_torsion : (torsion R L M).toSubmodule = Submodule.torsion R M :=
  (rfl)

@[simp]
theorem mem_torsion_iff (m : M) : m ∈ torsion R L M ↔ ∃ a : nonZeroDivisors R, a • m = 0 :=
  Submodule.mem_torsion_iff m

/-- The torsion Lie submodule is trivial exactly when the module is torsion-free. This holds over
any commutative ring: the non-zero-divisors defining the torsion are exactly the regular elements
defining torsion-freeness, so unlike `Submodule.isTorsionFree_iff_torsion_eq_bot` no domain
hypothesis is needed. -/
theorem torsion_eq_bot_iff : torsion R L M = ⊥ ↔ Module.IsTorsionFree R M := by
  rw [eq_bot_iff]
  refine ⟨fun h ↦ ⟨fun r hr ↦ ?_⟩, fun h m hm ↦ ?_⟩
  · refine (isSMulRegular_iff_torsionBy_eq_bot M r).2 <| (Submodule.eq_bot_iff _).2 fun m hm ↦ ?_
    exact (mem_bot (R := R) (L := L) m).1 <| h m <| (mem_torsion_iff m).2
      ⟨⟨r, isRegular_iff_mem_nonZeroDivisors.1 hr⟩, (Submodule.mem_torsionBy_iff r m).1 hm⟩
  · obtain ⟨a, ha⟩ := (mem_torsion_iff (L := L) m).1 hm
    exact (mem_bot (R := R) (L := L) m).2 <|
      ((isRegular_iff_mem_nonZeroDivisors.2 a.2).smul_eq_zero_iff_right).1 ha

/-- The torsion Lie submodule is everything exactly when the module is torsion. -/
theorem torsion_eq_top_iff :
    torsion R L M = ⊤ ↔ Module.IsTorsion R M := by
  rw [← LieSubmodule.toSubmodule_eq_top, toSubmodule_torsion,
    ← Submodule.isTorsion'_iff_torsion'_eq_top (R := R) (nonZeroDivisors R)]

/-- The torsion Lie submodule is a torsion module. -/
theorem torsion_isTorsion : Module.IsTorsion R (torsion R L M) := fun x ↦ by
  obtain ⟨a, ha⟩ := (mem_torsion_iff _).1 x.2
  exact ⟨a, Subtype.ext ha⟩

/-- The torsion Lie submodule of the torsion Lie submodule is everything. -/
@[simp]
theorem torsion_torsion_eq_top : torsion R L (torsion R L M) = ⊤ :=
  torsion_eq_top_iff.2 torsion_isTorsion

/-- Quotienting by the torsion Lie submodule kills all torsion. -/
@[simp]
theorem torsion_quotient : torsion R L (M ⧸ torsion R L M) = ⊥ := by
  rw [← toSubmodule_eq_bot, toSubmodule_torsion]
  exact Submodule.QuotientTorsion.torsion_eq_bot

/-- The quotient of a Lie module by its torsion Lie submodule is torsion-free. -/
instance instIsTorsionFreeQuotientTorsion : Module.IsTorsionFree R (M ⧸ torsion R L M) :=
  (torsion_eq_bot_iff (L := L)).1 torsion_quotient

end LieSubmodule

namespace TauCeti

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- **An irreducible Lie module is torsion or torsion-free.** -/
theorem isTorsion_or_isTorsionFree_of_isIrreducible [LieModule.IsIrreducible R L M] :
    Module.IsTorsion R M ∨ Module.IsTorsionFree R M := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (LieSubmodule.torsion R L M) with hbot | htop
  · exact Or.inr (LieSubmodule.torsion_eq_bot_iff.1 hbot)
  · exact Or.inl (LieSubmodule.torsion_eq_top_iff.1 htop)

end TauCeti
