/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Valuation.Integral

/-!
# The residue field of an algebraically closed valued field

Let `K` be a valued field with valuation ring `𝒪[K]` and residue field `𝓀[K]`. If `K` is
algebraically closed then so is `𝓀[K]`: a monic polynomial over `𝓀[K]` lifts to a monic
polynomial over `𝒪[K]`, whose roots in `K` are integral over `𝒪[K]` and so lie in `𝒪[K]`; their
residues are roots of the given polynomial.

## Main results

* `Valued.instIsAlgClosedResidueField`: the residue field of an algebraically closed valued field
  is algebraically closed.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §6.
-/

public section

open Polynomial IsLocalRing
open scoped Valued

namespace Valued

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/-- **The residue field of an algebraically closed valued field is algebraically closed.** -/
instance instIsAlgClosedResidueField [IsAlgClosed K] : IsAlgClosed 𝓀[K] := by
  refine IsAlgClosed.of_exists_root _ fun g hg hirr ↦ ?_
  have hinj : Function.Injective (algebraMap 𝒪[K] K) := FaithfulSMul.algebraMap_injective _ _
  have hlifts : g ∈ lifts (residue 𝒪[K]) :=
    lifts_iff_coeff_lifts _ |>.2 fun n ↦ residue_surjective _
  obtain ⟨f, hf, hfdeg, hfm⟩ := lifts_and_natDegree_eq_and_monic hlifts hg
  have hdeg : (f.map (algebraMap 𝒪[K] K)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective hinj, degree_eq_natDegree hfm.ne_zero, hfdeg]
    exact_mod_cast (natDegree_pos_iff_degree_pos.2 (degree_pos_of_irreducible hirr)).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  rw [IsRoot.def, eval_map] at hα
  set a : 𝒪[K] := ⟨α, (Valuation.integer.integers _).mem_of_integral ⟨f, hfm, hα⟩⟩
  have haα : algebraMap 𝒪[K] K a = α := Algebra.algebraMap_ofSubsemiring_apply _ a
  have ha : f.eval a = 0 :=
    hinj (by rw [map_zero, ← eval₂_at_apply, haα, hα])
  exact ⟨residue _ a, by rw [← hf, eval_map, eval₂_hom, ha, map_zero]⟩

end Valued
