/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.IsSimple

/-!
# Faithfulness is detected on a Cartan subalgebra

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over a field of
characteristic zero and let `H` be a splitting Cartan subalgebra. This file proves that an
`L`-module is faithful as soon as `H` acts faithfully on it.

The kernel of the action is a Lie ideal, and a Lie ideal of `L` is its intersection with `H` plus
the root spaces it contains (`LieAlgebra.IsKilling.lieIdeal_eq_inf_cartan_sup_biSup_rootSpace`).
A root space inside an ideal drags its coroot into the ideal (`LieIdeal.corootSubmodule_le`), and
coroots of roots are nonzero, so an ideal meeting `H` trivially is zero.

This is how faithfulness of a module is checked in highest-weight theory: if the weights of a
module span the dual of `H`, no nonzero element of `H` acts by zero, and the module is faithful.

## Main results

* `TauCeti.isFaithful_of_isFaithful_cartanSubalgebra`: an `L`-module on which `H` acts faithfully
  is faithful.
-/

public section

namespace TauCeti

open LieAlgebra LieModule LieAlgebra.IsKilling

variable {K L M : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- **Faithfulness is detected on a Cartan subalgebra.** Over a Killing Lie algebra, a module on
which a splitting Cartan subalgebra `H` acts faithfully is faithful. -/
theorem isFaithful_of_isFaithful_cartanSubalgebra [IsFaithful K H M] : IsFaithful K L M := by
  rw [isFaithful_iff_ker_eq_bot]
  set I := LieModule.ker K L M
  -- The kernel meets the Cartan subalgebra trivially, since `H` acts faithfully.
  have hH : ∀ x ∈ I.restr H, x ∈ H → x = 0 := fun x hxI hxH ↦ by
    have hx : (⟨x, hxH⟩ : H) ∈ LieModule.ker K H M :=
      (LieModule.mem_ker K H M _).mpr fun m ↦ (LieModule.mem_ker K L M x).mp hxI m
    rw [ker_eq_bot, LieSubmodule.mem_bot] at hx
    exact congrArg Subtype.val hx
  -- Hence it contains no root space: it would contain the nonzero coroot.
  have hroot (α : H.root) : ¬ rootSpace H α.1 ≤ I.restr H := fun hα ↦ by
    have hc := hH _ (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule α.1))
      (coroot α.1).2
    exact H.isNonZero_coe_root α
      (coroot_eq_zero_iff.mp (Subtype.ext hc))
  have hrestr : I.restr H = ⊥ := by
    rw [lieIdeal_eq_inf_cartan_sup_biSup_rootSpace I, eq_bot_iff]
    refine sup_le (fun x hx ↦ (LieSubmodule.mem_bot x).mpr (hH x hx.1 hx.2)) ?_
    exact iSup₂_le fun α hα ↦ (hroot α hα).elim
  ext x
  simpa using congrArg (x ∈ ·) hrestr

end TauCeti
