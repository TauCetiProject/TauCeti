/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Basic

/-!
# Restricted products over a finite index type

Over a finite index type the cofinite filter is `⊥`, so every element of the plain product is
restricted and the restricted product `Πʳ i, [G i, U i]` is the plain product `Π i, G i`.  This
file records that identification as a multiplicative equivalence with its coordinate formulas,
proves that it is a homeomorphism for every reference family, and identifies the
everywhere-integral subgroup with the product of the reference subgroups.

Everything here is also stated for additive groups (`addRestrictedProductOfFinite`, …).

This is not Mathlib's `RestrictedProduct.homeoTop`, which is the `⊤`-filter statement and
identifies the restricted product with the everywhere-integral product `Π i, U i`.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v

variable {ι : Type u} {G : ι → Type v}
variable [∀ i, Group (G i)] [Finite ι]

/-- Over a finite index type, the restricted product is the plain product, coordinatewise the
identity in both directions. -/
@[to_additive addRestrictedProductOfFinite /-- Over a finite index type, the restricted product of
additive groups is the plain product, coordinatewise the identity in both directions. -/]
def restrictedProductOfFinite (U : ∀ i, Subgroup (G i)) :
    (Πʳ i, [G i, (U i : Set (G i))]) ≃* (∀ i, G i) where
  toFun x := x
  invFun x := ⟨x, eventually_cofinite.mpr (Set.toFinite _)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable (U : ∀ i, Subgroup (G i))

/-- The finite collapse is the identity on coordinates. -/
@[to_additive (attr := simp) addRestrictedProductOfFinite_apply /-- The additive finite collapse is
the identity on coordinates. -/]
theorem restrictedProductOfFinite_apply (x : Πʳ i, [G i, (U i : Set (G i))]) (i : ι) :
    restrictedProductOfFinite U x i = x i := by
  rfl

/-- The inverse of the finite collapse is the identity on coordinates. -/
@[to_additive (attr := simp) addRestrictedProductOfFinite_symm_apply /-- The inverse of the additive
finite collapse is the identity on coordinates. -/]
theorem restrictedProductOfFinite_symm_apply (x : ∀ i, G i) (i : ι) :
    (restrictedProductOfFinite U).symm x i = x i := by
  rfl

/-- Over a finite index type, the everywhere-integral subgroup is carried onto the product of the
reference subgroups. -/
@[to_additive (attr := simp) map_addRestrictedProductOfFinite_integralAddSubgroup /-- Over a finite
index type, the everywhere-integral additive subgroup is carried onto the product of the reference
additive subgroups. -/]
theorem map_restrictedProductOfFinite_integralSubgroup :
    (integralSubgroup U).map (restrictedProductOfFinite U) = Subgroup.pi Set.univ U := by
  rw [Subgroup.map_equiv_eq_comap_symm]
  ext x
  simp [Subgroup.mem_pi]

variable [∀ i, TopologicalSpace (G i)]

/-- The finite collapse is continuous for every reference family. -/
@[to_additive continuous_addRestrictedProductOfFinite /-- The additive finite collapse is continuous
for every reference family. -/]
theorem continuous_restrictedProductOfFinite : Continuous (restrictedProductOfFinite U) :=
  RestrictedProduct.continuous_coe

/-- The inverse of the finite collapse is continuous for every reference family: on a finite
index type the cofinite filter is `⊥`, and the `⊥`-filter restricted product carries the product
topology. -/
@[to_additive continuous_addRestrictedProductOfFinite_symm /-- The inverse of the additive finite
collapse is continuous for every reference family: on a finite index type the cofinite filter is
`⊥`, and the `⊥`-filter restricted product carries the product topology. -/]
theorem continuous_restrictedProductOfFinite_symm :
    Continuous (restrictedProductOfFinite U).symm := by
  have h : (cofinite : Filter ι) ≤ ⊥ := cofinite_eq_bot.le
  have key : ⇑(restrictedProductOfFinite U).symm =
      RestrictedProduct.inclusion G (fun i ↦ (U i : Set (G i))) h ∘
        fun x ↦ RestrictedProduct.mk x eventually_bot := by
    ext x i
    simp only [restrictedProductOfFinite_symm_apply, Function.comp_apply,
      RestrictedProduct.inclusion_apply, RestrictedProduct.mk_apply]
  rw [key]
  refine (RestrictedProduct.continuous_inclusion h).comp ?_
  refine RestrictedProduct.continuous_rng_of_bot.mpr (continuous_pi fun i ↦ ?_)
  simpa only [Function.comp_apply, RestrictedProduct.mk_apply] using continuous_apply i

end TauCeti
