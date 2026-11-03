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
an element of `L` into `A` exactly when that element already lies in `A`, which characterizes the
decomposition group, and that Mathlib's `ValuationSubring.inertiaSubgroup` consists of the
elements acting trivially on residues, that is, moving every element of `A` by an element of the
maximal ideal.

## Main results

* `ValuationSubring.coe_decompositionSubgroup_smul`: the action on `A` is the restriction of the
  action on `L`.
* `ValuationSubring.decompositionSubgroup_apply_mem_iff`: the decomposition group preserves `A`
  and its complement in `L`.
* `ValuationSubring.mem_decompositionSubgroup_iff`: an automorphism of `L` lies in the
  decomposition group exactly when it preserves `A` and its complement.
* `ValuationSubring.decompositionSubgroup.ext`: two elements of the decomposition group that agree
  on `A` are equal.
* `ValuationSubring.instFaithfulSMulDecompositionSubgroup`: the decomposition group acts
  faithfully on `A`.
* `ValuationSubring.mem_inertiaSubgroup_iff`: an element of the decomposition group lies in the
  inertia group exactly when it fixes the residue of every element of `A`.
* `ValuationSubring.mem_inertiaSubgroup_iff_sub_mem_maximalIdeal`: equivalently, when it moves
  every element of `A` by an element of the maximal ideal.
* `Valuation.mem_decompositionSubgroup_valuationSubring` and
  `Valuation.mem_inertiaSubgroup_valuationSubring_iff`: the same criteria for the valuation subring
  of a valuation `v`, stated through `v`: an automorphism preserving `v` lies in the decomposition
  group, and it lies in the inertia group when `v (g x - x) < 1` whenever `v x ≤ 1`.
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

/-- **The decomposition group, elementwise**: an automorphism of `L` lies in the decomposition
group of a valuation subring `A` exactly when it maps an element of `L` into `A` precisely when
that element lies in `A`. -/
theorem mem_decompositionSubgroup_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.decompositionSubgroup K ↔ ∀ x : L, σ x ∈ A ↔ x ∈ A := by
  refine ⟨fun h x ↦ decompositionSubgroup_apply_mem_iff A ⟨σ, h⟩, fun h ↦ ?_⟩
  rw [← inv_mem_iff, MulAction.mem_stabilizer_iff]
  ext x
  rw [mem_inv_pointwise_smul_iff, AlgEquiv.smul_def, h]

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

/-- An element of the decomposition group of `A` lies in the inertia group exactly when it moves
every element of `A` by an element of the maximal ideal of `A`. -/
theorem mem_inertiaSubgroup_iff_sub_mem_maximalIdeal (A : ValuationSubring L)
    (g : A.decompositionSubgroup K) :
    g ∈ A.inertiaSubgroup K ↔ ∀ x : A, g • x - x ∈ IsLocalRing.maximalIdeal A := by
  refine (mem_inertiaSubgroup_iff A g).trans <| forall_congr' fun x ↦ ?_
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]

end ValuationSubring

namespace Valuation

variable {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L] [LinearOrderedCommGroupWithZero Γ₀]

/-- An automorphism of `L` preserving a valuation `v` lies in the decomposition group of the
valuation subring of `v`. -/
theorem mem_decompositionSubgroup_valuationSubring (v : Valuation L Γ₀) {σ : L ≃ₐ[K] L}
    (hσ : ∀ x, v (σ x) = v x) : σ ∈ v.valuationSubring.decompositionSubgroup K :=
  (ValuationSubring.mem_decompositionSubgroup_iff _ σ).mpr fun x ↦ by
    rw [mem_valuationSubring_iff, mem_valuationSubring_iff, hσ]

/-- An element `g` of the decomposition group of the valuation subring of `v` lies in its inertia
group exactly when `v (g x - x) < 1` for every `x` with `v x ≤ 1`. -/
theorem mem_inertiaSubgroup_valuationSubring_iff (v : Valuation L Γ₀)
    (g : v.valuationSubring.decompositionSubgroup K) :
    g ∈ v.valuationSubring.inertiaSubgroup K ↔
      ∀ x, v x ≤ 1 → v ((g : L ≃ₐ[K] L) x - x) < 1 := by
  rw [ValuationSubring.mem_inertiaSubgroup_iff_sub_mem_maximalIdeal, Subtype.forall]
  refine forall₂_congr fun x hx ↦ ?_
  rw [mem_maximalIdeal_iff, AddSubgroupClass.coe_sub,
    ValuationSubring.coe_decompositionSubgroup_smul]

end Valuation
