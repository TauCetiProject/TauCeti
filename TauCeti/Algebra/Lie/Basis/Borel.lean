/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basis.Root
public import TauCeti.Algebra.Lie.Weights.Borel

/-!
# Borels from a Lie algebra basis

This file connects a `LieAlgebra.Basis` to the positive nilradical and Borel subalgebra determined
by its root-system base. The positive nilradical is generated as a Lie algebra by the raising
operators `eᵢ`, so the corresponding Borel is the Cartan subalgebra together with their Lie span.

The construction follows the simple-root presentation in Meinolf Geck, *On the construction of
semisimple Lie algebras and Chevalley groups*, and the positive-root generation argument of
Humphreys, *Introduction to Lie Algebras and Representation Theory*, §10.

## Main results

* `LieAlgebra.Basis.positiveNilradical_eq_lieSpan_e` identifies the positive nilradical with the
  Lie span of the raising operators.
* `LieAlgebra.Basis.borelSubalgebra_eq_sup_lieSpan_e` gives the corresponding Borel.
-/

public section

open LieAlgebra LieModule Module

namespace LieAlgebra.Basis

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L}

section

variable {ι : Type*} [Fintype ι]

/-- A positive root for the base associated to a Lie algebra basis is a nonzero natural-number
combination of the basis's simple roots. -/
theorem exists_ne_zero_and_eq_sum_nat_baseSupp_of_mem_posRoots
    (b : LieAlgebra.Basis ι H) :
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    ∀ {α : H.root}, α ∈ TauCeti.posRoots (IsKilling.rootSystem H) b.base →
      ∃ n : ι → ℕ, n ≠ 0 ∧
        (α : H → K) = ∑ i, n i • (b.baseSupp i : H → K) := by
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  intro α hα
  let _ : Fintype b.base.support := Fintype.ofEquiv ι b.baseSupportEquiv
  obtain ⟨f, _, hroot⟩ :=
    TauCeti.exists_root_eq_sum_nat_of_mem_posRoots (IsKilling.rootSystem H) b.base hα
  let n : ι → ℕ := fun i => f (b.baseSupportEquiv i)
  have hsum : (α : H → K) = ∑ i, n i • (b.baseSupp i : H → K) := by
    funext z
    have hz := DFunLike.congr_fun hroot z
    simp only [LinearMap.coe_sum, Finset.sum_apply] at hz ⊢
    calc
      _ = ∑ j ∈ b.base.support,
          (f j • (IsKilling.rootSystem H).root j) z := hz
      _ = ∑ j : b.base.support,
          (f (j : H.root) • (IsKilling.rootSystem H).root (j : H.root)) z := by
        simpa using Finset.sum_subtype
          (p := fun j : H.root => j ∈ b.base.support) b.base.support
          (fun _ => Iff.rfl)
          (fun j => (f j • (IsKilling.rootSystem H).root j) z)
      _ = ∑ i : ι, (f (b.baseSupportEquiv i : H.root) •
          (IsKilling.rootSystem H).root (b.baseSupportEquiv i : H.root)) z := by
        exact (b.baseSupportEquiv.sum_comp fun j =>
          (f (j : H.root) • (IsKilling.rootSystem H).root (j : H.root)) z).symm
      _ = _ := by
        simp [n, coe_baseSupportEquiv_apply, IsKilling.rootSystem_root_apply,
          Pi.smul_apply]
  refine ⟨n, ?_, hsum⟩
  intro hn
  have hzero : (α : H → K) = 0 := by simp [hsum, hn]
  exact H.isNonZero_coe_root α hzero

/-- The positive nilradical associated to a Lie algebra basis is the Lie span of its raising
operators. -/
theorem positiveNilradical_eq_lieSpan_e (b : LieAlgebra.Basis ι H) :
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.positiveNilradical H b.base = LieSubalgebra.lieSpan K L (Set.range b.e) := by
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  apply le_antisymm
  · rw [TauCeti.positiveNilradical_le_iff]
    intro α hα x hx
    obtain ⟨n, hn, hsum⟩ := b.exists_ne_zero_and_eq_sum_nat_baseSupp_of_mem_posRoots hα
    have hle : rootSpace H (∑ i, n i • (b.baseSupp i : H → K)) ≤
        ⨆ (m : ι → ℕ) (_ : m ≠ 0),
          rootSpace H (∑ i, m i • (b.baseSupp i : H → K)) :=
      (le_iSup (fun m : ι → ℕ => ⨆ _ : m ≠ 0,
        rootSpace H (∑ i, m i • (b.baseSupp i : H → K))) n).trans'
        (le_iSup (fun _ : n ≠ 0 =>
          rootSpace H (∑ i, n i • (b.baseSupp i : H → K))) hn)
    rw [hsum] at hx
    have hx' : x ∈ b.borelUpper := by
      rw [b.borelUpper_eq]
      exact hle hx
    have h_borelUpper :
        (b.borelUpper : Submodule K L) =
          (LieSubalgebra.lieSpan K L (Set.range b.e) : Submodule K L) := by
      -- Mathlib's `borelUpper` definition inherits the `LieSubmodule.lieSpan`
      -- carrier, whose coercion here is definitionally the carrier of the
      -- corresponding `LieSubalgebra.lieSpan`; name that transport explicitly
      -- instead of hiding it in the membership proof below.
      rfl
    rw [← LieSubalgebra.mem_toSubmodule]
    rw [← h_borelUpper]
    exact (LieSubmodule.mem_toSubmodule b.borelUpper).mpr hx'
  · rw [LieSubalgebra.lieSpan_le, Set.range_subset_iff]
    intro i
    exact TauCeti.mem_positiveNilradical_of_mem_rootSpace H b.base
      (TauCeti.support_subset_posRoots (IsKilling.rootSystem H) b.base
        (b.baseSupportEquiv i).property)
      (TauCeti.lieBasis_e_mem_rootSpace b i)

/-- The Borel associated to a Lie algebra basis is its Cartan subalgebra together with the Lie
span of its raising operators. -/
theorem borelSubalgebra_eq_sup_lieSpan_e (b : LieAlgebra.Basis ι H) :
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.borelSubalgebra H b.base = H ⊔ LieSubalgebra.lieSpan K L (Set.range b.e) := by
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  rw [TauCeti.borelSubalgebra_eq_sup, b.positiveNilradical_eq_lieSpan_e]

end

end LieAlgebra.Basis
