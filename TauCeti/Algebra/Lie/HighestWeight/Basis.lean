/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Basis.Root
public import TauCeti.Algebra.Lie.HighestWeight.Basic

/-!
# Highest-weight vectors from a Lie algebra basis

This file connects a `LieAlgebra.Basis` to the positive-system definitions used in
highest-weight theory.  The positive nilradical is generated as a Lie algebra by the raising
operators `eᵢ`, so the corresponding Borel and highest-weight-vector conditions can be read
directly from the basis.

The construction follows the simple-root presentation in Meinolf Geck, *On the construction of
semisimple Lie algebras and Chevalley groups*, and the positive-root generation argument of
Humphreys, *Introduction to Lie Algebras and Representation Theory*, §10.

## Main results

* `LieAlgebra.Basis.positiveNilradical_eq_lieSpan_e` identifies the positive nilradical with the
  Lie span of the raising operators.
* `LieAlgebra.Basis.borelSubalgebra_eq_sup_lieSpan_e` gives the corresponding Borel.
* `LieAlgebra.Basis.isHighestWeightVector_iff_forall_e` reduces the highest-weight condition to
  annihilation by the raising operators.
-/

public section

open LieAlgebra LieModule Module

namespace LieAlgebra.Basis

universe u v w

variable {ι : Type*} [Finite ι]
  {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L}

/-- The positive nilradical associated to a Lie algebra basis is the Lie span of its raising
operators. -/
theorem positiveNilradical_eq_lieSpan_e (b : LieAlgebra.Basis ι H) :
    letI : Fintype ι := Fintype.ofFinite ι
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.positiveNilradical H b.base = LieSubalgebra.lieSpan K L (Set.range b.e) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  let _ : Fintype b.base.support := Fintype.ofEquiv ι b.baseSupportEquiv
  apply le_antisymm
  · rw [TauCeti.positiveNilradical_le_iff]
    intro α hα x hx
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
    have hn : n ≠ 0 := by
      intro hn
      have hzero : (α : H → K) = 0 := by simp [hsum, hn]
      exact H.isNonZero_coe_root α hzero
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
    rw [← LieSubmodule.mem_toSubmodule] at hx'
    simpa only [LieAlgebra.Basis.borelUpper] using hx'
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

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]
  [LieModule K L M]

/-- A vector is highest weight for the base of a Lie algebra basis exactly when it is a nonzero
weight vector annihilated by every raising operator. -/
theorem isHighestWeightVector_iff_forall_e (b : LieAlgebra.Basis ι H)
    {lam : Module.Dual K H} {v : M} :
    letI : Fintype ι := Fintype.ofFinite ι
    letI := b.isCartanSubalgebra
    letI := b.isTriangularizable
    TauCeti.IsHighestWeightVector b.base lam v ↔
      v ≠ 0 ∧ (∀ x : H, ⁅(x : L), v⁆ = lam x • v) ∧ ∀ i, ⁅b.e i, v⁆ = 0 := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ := b.isCartanSubalgebra
  let _ := b.isTriangularizable
  rw [TauCeti.isHighestWeightVector_iff, b.positiveNilradical_eq_lieSpan_e]
  refine and_congr_right' (and_congr_right' ?_)
  constructor
  · intro h i
    exact h (b.e i) (LieSubalgebra.subset_lieSpan (Set.mem_range_self i))
  · intro h x hx
    have hle : LieSubalgebra.lieSpan K L (Set.range b.e) ≤ TauCeti.lieAnnihilator K L v :=
      LieSubalgebra.lieSpan_le.mpr fun _ hy => by
        obtain ⟨i, rfl⟩ := hy
        exact (TauCeti.mem_lieAnnihilator K L).mpr (h i)
    exact (TauCeti.mem_lieAnnihilator K L).mp (hle hx)

end LieAlgebra.Basis
