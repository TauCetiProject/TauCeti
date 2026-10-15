/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Topology.Algebra.RestrictedProduct.Units

import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng

/-!
# The topology on the units of a restricted product

Let `R i` be topological monoids with submonoids `B i`. Mathlib's `RestrictedProduct.unitsEquiv`
identifies, as groups, the units of the restricted product `Πʳ i, [R i, B i]` with the restricted
product `Πʳ i, [(R i)ˣ, (B i)ˣ]` of the unit groups. The two sides carry natural topologies: the
units of a topological monoid have the topology induced by `x ↦ (x, x⁻¹)`, while the restricted
product of the unit groups has its restricted-product topology, built from the units topologies of
the factors. This file shows that these topologies agree for the cofinite filter of indices when
every `B i` is open, so that `RestrictedProduct.unitsEquiv` is then an isomorphism of topological
groups. The inverse comparison map is continuous for every filter of indices, with no openness
assumption.

For the finite adele ring of a Dedekind domain this is the statement that the topology of the
finite ideles, as units of the finite adeles, is the restricted-product topology of the local unit
groups `K_vˣ` with respect to the local integral units `𝒪_vˣ`.

## Main results

* `RestrictedProduct.continuous_unitsEquiv`: for the cofinite filter of indices, the comparison
  map from the units of the restricted product to the restricted product of the units is
  continuous when every `B i` is open.
* `RestrictedProduct.continuous_unitsEquiv_symm`: its inverse is continuous, for every filter of
  indices and arbitrary submonoids `B i`.
* `ContinuousMulEquiv.restrictedProductUnits`: the resulting isomorphism of topological groups
  `(Πʳ i, [R i, B i])ˣ ≃ₜ* Πʳ i, [(R i)ˣ, (B i)ˣ]` (cofinite filter, every `B i` open).

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
* A. Weil, *Basic Number Theory*, Chapter IV, §3.
-/

public section

open Filter Set Topology
open scoped RestrictedProduct

namespace RestrictedProduct

variable {ι : Type*} {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
variable {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)]
variable {B : ∀ i, S i}

/-- The comparison of the units of a restricted product with the restricted product of the unit
groups has a continuous inverse, for every filter of indices. -/
theorem continuous_unitsEquiv_symm {𝓕 : Filter ι} :
    Continuous (unitsEquiv R (B := B) (𝓕 := 𝓕)).symm := by
  -- The two coordinates `x` and `x⁻¹` of the inverse are restricted-product maps of the
  -- continuous maps `u ↦ u` and `u ↦ u⁻¹` from `(R i)ˣ` to `R i`.
  have hval : ∀ᶠ i in 𝓕, MapsTo (fun u : (R i)ˣ ↦ (u : R i))
      (Submonoid.ofClass (B i)).units (B i) := .of_forall fun _ _ hu ↦ hu.1
  have hinv : ∀ᶠ i in 𝓕, MapsTo (fun u : (R i)ˣ ↦ ((u⁻¹ : (R i)ˣ) : R i))
      (Submonoid.ofClass (B i)).units (B i) := .of_forall fun _ _ hu ↦ hu.2
  exact Units.continuous_iff.mpr
    ⟨mapAlong_continuous (fun i ↦ (R i)ˣ) R id tendsto_id _ hval fun _ ↦ Units.continuous_val,
      mapAlong_continuous (fun i ↦ (R i)ˣ) R id tendsto_id _ hinv fun _ ↦
        Units.continuous_coe_inv⟩

/-- **The units topology of a restricted product is the restricted-product topology of the unit
groups**, when every `B i` is open: the comparison map `RestrictedProduct.unitsEquiv` from the
units of `Πʳ i, [R i, B i]` to `Πʳ i, [(R i)ˣ, (B i)ˣ]` is continuous. -/
theorem continuous_unitsEquiv (hB : ∀ i, IsOpen (B i : Set (R i))) :
    Continuous (unitsEquiv R (B := B) (𝓕 := cofinite)) := by
  -- We check continuity at each `x`, by restricting to an open neighbourhood of `x` on which the
  -- map lands in a single principal stage, whose topology is the product topology.
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  -- The indices at which `x` is an integral unit form a cofinite set `T`.
  let T : Set ι := {i | (x : Πʳ i, [R i, B i]) i ∈ B i ∧
    ((x⁻¹ : (Πʳ i, [R i, B i])ˣ) : Πʳ i, [R i, B i]) i ∈ B i}
  have hT : cofinite ≤ 𝓟 T := le_principal_iff.mpr (x.val.2.and x.inv.2)
  -- The units that are integral units at every index of `T` form an open neighbourhood `V` of `x`.
  let W : Set (Πʳ i, [R i, B i]) := {a | ∀ i, i ∈ T → a.1 i ∈ B i}
  have hW : IsOpen W := isOpen_forall_imp_mem hB
  let V : Set (Πʳ i, [R i, B i])ˣ := (fun y ↦ (y : Πʳ i, [R i, B i])) ⁻¹' W ∩
    (fun y ↦ ((y⁻¹ : (Πʳ i, [R i, B i])ˣ) : Πʳ i, [R i, B i])) ⁻¹' W
  have hV : V ∈ 𝓝 x :=
    ((hW.preimage Units.continuous_val).inter (hW.preimage Units.continuous_coe_inv)).mem_nhds
      ⟨fun _ hi ↦ hi.1, fun _ hi ↦ hi.2⟩
  -- On `V` the comparison map takes values in the principal stage at `T`.
  have hmem : ∀ (y : V), ∀ i ∈ T, V.domRestrict (unitsEquiv R) y i ∈
      ((Submonoid.ofClass (B i)).units : Set (R i)ˣ) :=
    fun y i hi ↦ ⟨y.2.1 i hi, y.2.2 i hi⟩
  refine ContinuousOn.continuousAt (continuousOn_iff_continuous_domRestrict.mpr ?_) hV
  rw [TauCeti.continuous_restrictedProduct_iff_of_forall_mem hT hmem]
  exact continuous_pi fun i ↦ Units.continuous_iff.mpr
    ⟨((continuous_eval i).comp Units.continuous_val).comp continuous_subtype_val,
      ((continuous_eval i).comp Units.continuous_coe_inv).comp continuous_subtype_val⟩

end RestrictedProduct

namespace ContinuousMulEquiv

variable {ι : Type*} {R : ι → Type*} [∀ i, Monoid (R i)] [∀ i, TopologicalSpace (R i)]
variable {S : ι → Type*} [∀ i, SetLike (S i) (R i)] [∀ i, SubmonoidClass (S i) (R i)]
variable {B : ∀ i, S i}

/-- **The units of a restricted product are the restricted product of the units**, as
topological groups: when every `B i` is open, `RestrictedProduct.unitsEquiv` is a homeomorphism
from the units of `Πʳ i, [R i, B i]`, with the units topology, to `Πʳ i, [(R i)ˣ, (B i)ˣ]`, with
the restricted-product topology of the units topologies. -/
noncomputable def restrictedProductUnits (hB : ∀ i, IsOpen (B i : Set (R i))) :
    (Πʳ i, [R i, B i])ˣ ≃ₜ* Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units] where
  __ := RestrictedProduct.unitsEquiv R
  continuous_toFun := RestrictedProduct.continuous_unitsEquiv hB
  continuous_invFun := RestrictedProduct.continuous_unitsEquiv_symm

/-- The underlying group isomorphism of `ContinuousMulEquiv.restrictedProductUnits` is
`RestrictedProduct.unitsEquiv`. -/
@[simp]
theorem toMulEquiv_restrictedProductUnits (hB : ∀ i, IsOpen (B i : Set (R i))) :
    (restrictedProductUnits hB : (Πʳ i, [R i, B i])ˣ ≃* _) = RestrictedProduct.unitsEquiv R :=
  (rfl)

/-- `ContinuousMulEquiv.restrictedProductUnits` is computed by `RestrictedProduct.unitsEquiv`. -/
theorem restrictedProductUnits_apply (hB : ∀ i, IsOpen (B i : Set (R i)))
    (x : (Πʳ i, [R i, B i])ˣ) :
    restrictedProductUnits hB x = RestrictedProduct.unitsEquiv R x :=
  (rfl)

/-- The coordinates of the image of a unit under `ContinuousMulEquiv.restrictedProductUnits` are
the coordinates of that unit. -/
@[simp]
theorem coe_restrictedProductUnits_apply (hB : ∀ i, IsOpen (B i : Set (R i)))
    (x : (Πʳ i, [R i, B i])ˣ) (i : ι) :
    (restrictedProductUnits hB x i : R i) = (x : Πʳ i, [R i, B i]) i :=
  (rfl)

/-- The coordinates of the unit attached by `ContinuousMulEquiv.restrictedProductUnits` to a
restricted family of units are the given units. -/
@[simp]
theorem restrictedProductUnits_symm_apply_apply (hB : ∀ i, IsOpen (B i : Set (R i)))
    (y : Πʳ i, [(R i)ˣ, (Submonoid.ofClass (B i)).units]) (i : ι) :
    ((restrictedProductUnits hB).symm y : Πʳ i, [R i, B i]) i = y i :=
  (rfl)

end ContinuousMulEquiv
