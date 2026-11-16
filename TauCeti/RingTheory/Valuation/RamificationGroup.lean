/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
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
* `ValuationSubring.restrictScalars_mem_decompositionSubgroup_iff`: decomposition-group membership
  is unchanged by restricting scalars along a tower of fields `K ⊆ E ⊆ L`.
* `ValuationSubring.decompositionSubgroup.ext`: two elements of the decomposition group that agree
  on `A` are equal.
* `ValuationSubring.instFaithfulSMulDecompositionSubgroup`: the decomposition group acts
  faithfully on `A`.
* `ValuationSubring.mem_inertiaSubgroup_iff`: an element of the decomposition group lies in the
  inertia group exactly when it fixes the residue of every element of `A`.
* `ValuationSubring.mem_inertiaSubgroup_iff_sub_mem_maximalIdeal`: equivalently, when it moves
  every element of `A` by an element of the maximal ideal.
* `ValuationSubring.map_restrictScalarsHom_inertiaSubgroup`: the inertia group of `A` over an
  intermediate field `E`, read as automorphisms over `K`, is the part of the inertia group over `K`
  that fixes `E` pointwise.
* `Valuation.mem_decompositionSubgroup_valuationSubring` and
  `Valuation.mem_inertiaSubgroup_valuationSubring_iff`: the same criteria for the valuation subring
  of a valuation `v`, stated through `v`: an automorphism preserving `v` lies in the decomposition
  group, and it lies in the inertia group exactly when `v (g x - x) < 1` whenever `v x ≤ 1`.
-/

public section

open scoped Pointwise

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The action of a decomposition group on its valuation subring is the restriction of its
action on the fraction field. -/
@[simp]
theorem coe_decompositionSubgroup_smul (A : ValuationSubring L)
    (g : A.decompositionSubgroup K) (x : A) :
    ((g • x : A) : L) = (g : L ≃ₐ[K] L) (x : L) :=
  rfl

/-- An element of the decomposition group of a valuation subring `A` maps an element of the
ambient field into `A` exactly when that element lies in `A`. -/
@[simp]
theorem decompositionSubgroup_apply_mem_iff (A : ValuationSubring L)
    (g : A.decompositionSubgroup K) {x : L} : (g : L ≃ₐ[K] L) x ∈ A ↔ x ∈ A := by
  rw [← AlgEquiv.smul_def, ← smul_mem_pointwise_smul_iff (g := (g : L ≃ₐ[K] L)) (x := x),
    MulAction.mem_stabilizer_iff.mp g.2]

/-- **The decomposition group, elementwise**: an automorphism of `L` lies in the decomposition
group of a valuation subring `A` exactly when it maps an element of `L` into `A` precisely when
that element lies in `A`. -/
theorem mem_decompositionSubgroup_iff (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.decompositionSubgroup K ↔ ∀ x : L, σ x ∈ A ↔ x ∈ A := by
  refine ⟨fun h x ↦ decompositionSubgroup_apply_mem_iff A ⟨σ, h⟩, fun h ↦ ?_⟩
  rw [← inv_mem_iff, MulAction.mem_stabilizer_iff]
  ext x
  rw [mem_inv_pointwise_smul_iff, AlgEquiv.smul_def, h]

/-- **Decomposition-group membership is unchanged by restricting scalars**: for a tower of fields
`K ⊆ E ⊆ L`, an automorphism of `L` over `E` lies in the decomposition group of `A` over `E`
exactly when it lies in the decomposition group of `A` over `K`, read as an automorphism over
`K`. -/
theorem restrictScalars_mem_decompositionSubgroup_iff {E : Type*} [Field E] [Algebra K E]
    [Algebra E L] [IsScalarTower K E L] (A : ValuationSubring L) (τ : L ≃ₐ[E] L) :
    τ.restrictScalars K ∈ A.decompositionSubgroup K ↔ τ ∈ A.decompositionSubgroup E := by
  simp only [mem_decompositionSubgroup_iff, AlgEquiv.restrictScalars_apply]

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
  simp [inertiaSubgroup, RingEquiv.ext_iff, IsLocalRing.residue_surjective.forall]

/-- An element of the decomposition group of `A` lies in the inertia group exactly when it moves
every element of `A` by an element of the maximal ideal of `A`. -/
theorem mem_inertiaSubgroup_iff_sub_mem_maximalIdeal (A : ValuationSubring L)
    (g : A.decompositionSubgroup K) :
    g ∈ A.inertiaSubgroup K ↔ ∀ x : A, g • x - x ∈ IsLocalRing.maximalIdeal A := by
  refine (mem_inertiaSubgroup_iff A g).trans <| forall_congr' fun x ↦ ?_
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]

/-- **The inertia group over an intermediate field**: the inertia group of `A` over an intermediate
field `E` of `L / K`, read as automorphisms over `K`, is the part of the inertia group of `A` over
`K` that fixes `E` pointwise. -/
theorem map_restrictScalarsHom_inertiaSubgroup (A : ValuationSubring L)
    (E : IntermediateField K L) :
    ((A.inertiaSubgroup E).map (A.decompositionSubgroup E).subtype).map
        (AlgEquiv.restrictScalarsHom K) =
      E.fixingSubgroup ⊓ (A.inertiaSubgroup K).map (A.decompositionSubgroup K).subtype := by
  let f : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L) := AlgEquiv.restrictScalarsHom K
  -- Elements of the decomposition groups over `E` and over `K` acting alike on `L` are inertial
  -- together, since inertia is read on residues.
  have hiff {g₁ : A.decompositionSubgroup E} {g₂ : A.decompositionSubgroup K}
      (h : ∀ x, (g₁ : L ≃ₐ[E] L) x = (g₂ : L ≃ₐ[K] L) x) :
      g₁ ∈ A.inertiaSubgroup E ↔ g₂ ∈ A.inertiaSubgroup K := by
    have hx (x : A) : g₁ • x = g₂ • x := Subtype.ext <| by
      rw [coe_decompositionSubgroup_smul, coe_decompositionSubgroup_smul, h]
    simp only [mem_inertiaSubgroup_iff, hx]
  ext σ
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have hZ : f g ∈ A.decompositionSubgroup K :=
      (restrictScalars_mem_decompositionSubgroup_iff A (g : L ≃ₐ[E] L)).mpr g.2
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      fun x hx ↦ (g : L ≃ₐ[E] L).commutes ⟨x, hx⟩, ⟨f g, hZ⟩, (hiff fun _ ↦ rfl).mp hg, rfl⟩
  · rintro ⟨hE, g, hg, rfl⟩
    let τ := E.fixingSubgroupEquiv ⟨g, hE⟩
    have hτ (x : L) : τ x = (g : L ≃ₐ[K] L) x :=
      congrFun (IntermediateField.coe_fixingSubgroupEquiv_apply E ⟨g, hE⟩) x
    have hτg : τ.restrictScalars K = g := AlgEquiv.ext hτ
    have hZ : τ ∈ A.decompositionSubgroup E :=
      (restrictScalars_mem_decompositionSubgroup_iff A τ).mp (hτg ▸ g.2)
    exact ⟨τ, ⟨⟨τ, hZ⟩, (hiff hτ).mpr hg, rfl⟩, AlgEquiv.ext hτ⟩

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
