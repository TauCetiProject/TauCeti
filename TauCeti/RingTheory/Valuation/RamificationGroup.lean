/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# The action of a decomposition group on its valuation subring

For a valuation subring `A` of a field `L` and a subfield `K`, Mathlib's
`ValuationSubring.decompositionSubgroup K A` acts on `A` by restricting its action on `L`.
This file records that the restricted action is computed in `L`, that it is faithful
because `L` is the field of fractions of `A`, that an element of the decomposition group maps
an element of `L` into `A` exactly when that element already lies in `A`, and that Mathlib's
`ValuationSubring.inertiaSubgroup` consists of the elements acting trivially on residues.

## Main results

* `ValuationSubring.coe_decompositionSubgroup_smul`: the action on `A` is the restriction of the
  action on `L`.
* `ValuationSubring.decompositionSubgroup_apply_mem_iff`: the decomposition group preserves `A`
  and its complement in `L`.
* `ValuationSubring.decompositionSubgroup.ext`: two elements of the decomposition group that agree
  on `A` are equal.
* `ValuationSubring.instFaithfulSMulDecompositionSubgroup`: the decomposition group acts
  faithfully on `A`.
* `ValuationSubring.mem_inertiaSubgroup_iff`: an element of the decomposition group lies in the
  inertia group exactly when it fixes the residue of every element of `A`.
-/

public section

open scoped Pointwise

namespace ValuationSubring

universe w w'

variable {K : Type w} {L : Type w'} [Field K] [Field L] [Algebra K L]

/-- The action of a decomposition group on its valuation subring is the restriction of its
action on the fraction field. -/
@[simp]
theorem coe_decompositionSubgroup_smul (A : ValuationSubring L)
    (g : A.decompositionSubgroup K) (x : A) :
    ((g • x : A) : L) = (g : L ≃ₐ[K] L) (x : L) := by
  rw [← AlgEquiv.smul_def, ← Submonoid.smul_def]
  rfl

/-- An element of the decomposition group of a valuation subring `A` maps an element of the
ambient field into `A` exactly when that element lies in `A`. -/
@[simp]
theorem decompositionSubgroup_apply_mem_iff (A : ValuationSubring L)
    (g : A.decompositionSubgroup K) {x : L} : (g : L ≃ₐ[K] L) x ∈ A ↔ x ∈ A := by
  obtain ⟨σ, hσ⟩ := g
  have h : σ • A = A := hσ
  rw [Subgroup.coe_mk, ← AlgEquiv.smul_def]
  calc σ • x ∈ A ↔ σ • x ∈ σ • A := by rw [h]
    _ ↔ x ∈ A := smul_mem_pointwise_smul_iff

/-- Two automorphisms in the decomposition group of a valuation subring that agree on the
valuation subring are equal, because its ambient field is its field of fractions. -/
@[ext]
theorem decompositionSubgroup.ext (A : ValuationSubring L)
    {g h : A.decompositionSubgroup K}
    (hgh : ∀ x : A, (g : L ≃ₐ[K] L) x = (h : L ≃ₐ[K] L) x) : g = h :=
  Subtype.ext <| AlgEquiv.ext fun y ↦ DFunLike.congr_fun
    (IsFractionRing.ringHom_ext (A := A) (f1 := ((g : L ≃ₐ[K] L) : L →+* L))
      (f2 := ((h : L ≃ₐ[K] L) : L →+* L)) hgh) y

/-- The decomposition group of a valuation subring acts faithfully on that subring. -/
instance instFaithfulSMulDecompositionSubgroup (A : ValuationSubring L) :
    FaithfulSMul (A.decompositionSubgroup K) A where
  eq_of_smul_eq_smul {g h} heq := decompositionSubgroup.ext A fun x ↦ by
    simpa only [coe_decompositionSubgroup_smul] using congrArg Subtype.val (heq x)

/-- **The inertia group, elementwise**: an element of the decomposition group of `A` lies in the
inertia group exactly when it acts trivially on the residue field of `A`, that is, when it fixes
the residue of every element of `A`. -/
@[simp]
theorem mem_inertiaSubgroup_iff (A : ValuationSubring L) (g : A.decompositionSubgroup K) :
    g ∈ A.inertiaSubgroup K ↔
      ∀ x : A, IsLocalRing.residue A (g • x) = IsLocalRing.residue A x := by
  rw [inertiaSubgroup, MonoidHom.mem_ker, RingEquiv.ext_iff]
  refine ⟨fun h x ↦ by simpa using h (IsLocalRing.residue A x), fun h z ↦ ?_⟩
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := A) z
  simpa using h x

end ValuationSubring
