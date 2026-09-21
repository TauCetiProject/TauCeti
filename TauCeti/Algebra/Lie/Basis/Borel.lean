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
* `LieAlgebra.Basis.mem_borelUpper_iff_mem_lieSpan` characterizes membership in the upper Borel as
  membership in that Lie span.
* `LieAlgebra.Basis.borelSubalgebra_eq_sup_lieSpan_e` gives the corresponding Borel.
-/

public section

open LieAlgebra LieModule Module

namespace LieAlgebra.Basis

universe u v

section Carrier

variable {K : Type u} {L : Type v} [CommRing K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L} {ι : Type*} [Finite ι]

/-- Membership in the upper Borel's nilpotent part is equivalent to membership in the Lie span of
the raising operators. -/
@[simp] theorem mem_borelUpper_iff_mem_lieSpan (b : LieAlgebra.Basis ι H) {x : L} :
    x ∈ b.borelUpper ↔ x ∈ LieSubalgebra.lieSpan K L (Set.range b.e) := by
  simp only [borelUpper, LieSubmodule.mem_mk_iff', LieSubalgebra.mem_toSubmodule]

end Carrier

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L}

section

variable {ι : Type*} [Finite ι]

/-- The positive nilradical associated to a Lie algebra basis is the Lie span of its raising
operators. -/
theorem positiveNilradical_eq_lieSpan_e (b : LieAlgebra.Basis ι H) :
    letI : Fintype ι := Fintype.ofFinite ι
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.positiveNilradical H b.base = LieSubalgebra.lieSpan K L (Set.range b.e) := by
  let _ : Fintype ι := Fintype.ofFinite ι
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
    rw [← LieSubalgebra.mem_toSubmodule]
    exact b.mem_borelUpper_iff_mem_lieSpan.mp hx'
  · rw [LieSubalgebra.lieSpan_le, Set.range_subset_iff]
    intro i
    exact TauCeti.mem_positiveNilradical_of_mem_rootSpace H b.base
      (TauCeti.support_subset_posRoots (IsKilling.rootSystem H) b.base
        (b.baseSupportEquiv i).property)
      (TauCeti.lieBasis_e_mem_rootSpace b i)

/-- The Borel associated to a Lie algebra basis is its Cartan subalgebra together with the Lie
span of its raising operators. -/
theorem borelSubalgebra_eq_sup_lieSpan_e (b : LieAlgebra.Basis ι H) :
    letI : Fintype ι := Fintype.ofFinite ι
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.borelSubalgebra H b.base = H ⊔ LieSubalgebra.lieSpan K L (Set.range b.e) := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  rw [TauCeti.borelSubalgebra_eq_sup, b.positiveNilradical_eq_lieSpan_e]

end

end LieAlgebra.Basis
