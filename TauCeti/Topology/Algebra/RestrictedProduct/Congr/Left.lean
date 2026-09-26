/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.ContinuousRng

/-!
# Reindexing a restricted product along an equivalence of index types

An equivalence `e : ι' ≃ ι` of index types identifies the restricted product of a family `G` of
types indexed by `ι` with the restricted product of the pulled-back family `j ↦ G (e j)` indexed
by `ι'`, coordinatewise: `x` corresponds to `j ↦ x (e j)`.  This is the restricted-product
analogue of `Equiv.piCongrLeft`.  The restrictedness conditions match because `e` carries the
cofinite filter to the cofinite filter (`Function.Injective.comap_cofinite_eq`), so no filter
compatibility hypothesis is needed.  Both directions are maps out of a single restricted product
and are coordinatewise a homeomorphism of the ambient products on every principal stage, so both
are continuous for every reference family.

The identification is stated at two levels.

* `restrictedProductCongrLeftEquiv A e`, for an arbitrary family `A` of reference sets, is the
  plain equivalence in the orientation of `Equiv.piCongrLeft`, from the pulled-back family over
  `ι'` to the family over `ι`.  It is pinned by `restrictedProductCongrLeftEquiv_apply_apply`,
  the value at `e j` being the value at `j`, and its inverse by
  `restrictedProductCongrLeftEquiv_symm_apply`.
* `restrictedProductCongrLeft U e` is the same equivalence as a multiplicative equivalence, for a
  family `U` of reference sets closed under multiplication, and `restrictedProductReindex U e` is
  its inverse, `x ↦ (j ↦ x (e j))`.  The latter is the orientation in which a restricted product
  is decomposed along a finite set of indices, by reindexing along `Equiv.sumCompl`.

The statement shape and the pinning equation `… y (e j) = y j` follow the declarations
`Equiv.restrictedProductCongrLeft` and `MulEquiv.restrictedProductCongrLeft` of the FLT project
(`ImperialCollegeLondon/FLT`, file `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean`,
source commit `a9efe585de92be60be84ac1d14ced5a1b0944333`, Apache 2.0), by Kevin Buzzard and
Salvatore Mercuri, specialised to the cofinite filter on both sides.  `restrictedProductReindex`
and its coordinate lemmas follow FLT's `Equiv.restrictedProductCongrLeft'`, the same equivalence
in the orientation `x ↦ (j ↦ x (e j))`.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/

public section

namespace TauCeti

open Filter
open scoped RestrictedProduct

universe u v w z

variable {ι : Type u} {ι' : Type v} {G : ι → Type w}

section Sets

variable (A : ∀ i, Set (G i)) (e : ι' ≃ ι)

/-- Reindexing a restricted product along an equivalence `e : ι' ≃ ι` of index types, in the
orientation of `Equiv.piCongrLeft`: from the restricted product of the pulled-back family over
`ι'` to the restricted product over `ι`.  The image of `y` has coordinate `y j` at `e j`, and the
inverse sends `x` to `j ↦ x (e j)`; it is Mathlib's `RestrictedProduct.mapAlong` along `e` with
identity coordinate maps. -/
def restrictedProductCongrLeftEquiv :
    (Πʳ j, [G (e j), A (e j)]) ≃ (Πʳ i, [G i, A i]) where
  toFun y := RestrictedProduct.mk (Equiv.piCongrLeft G e y) <| by
    rw [← e.symm.injective.comap_cofinite_eq, eventually_comap]
    filter_upwards [y.2] with j hj i hi
    obtain rfl : i = e j := e.symm_apply_eq.mp hi
    rwa [Equiv.piCongrLeft_apply_apply]
  invFun := RestrictedProduct.mapAlong G (fun j ↦ G (e j)) e e.injective.tendsto_cofinite
    (fun _ ↦ id) (.of_forall fun _ ↦ Set.mapsTo_id _)
  left_inv y := by
    ext j
    simp
  right_inv x := by
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp

/-- The reindexed element has coordinate `y j` at `e j`; as `e` is surjective, this pins
`restrictedProductCongrLeftEquiv`. -/
@[simp]
theorem restrictedProductCongrLeftEquiv_apply_apply (y : Πʳ j, [G (e j), A (e j)]) (j : ι') :
    restrictedProductCongrLeftEquiv A e y (e j) = y j :=
  Equiv.piCongrLeft_apply_apply G e y j

/-- The inverse of the reindexing equivalence sends `x` to `j ↦ x (e j)`. -/
@[simp]
theorem restrictedProductCongrLeftEquiv_symm_apply (x : Πʳ i, [G i, A i]) (j : ι') :
    (restrictedProductCongrLeftEquiv A e).symm x j = x (e j) :=
  RestrictedProduct.mapAlong_apply G (fun j ↦ G (e j)) e e.injective.tendsto_cofinite
    (fun _ ↦ id) (.of_forall fun _ ↦ Set.mapsTo_id _) x j

variable [∀ i, TopologicalSpace (G i)]

/-- Reindexing is continuous for every reference family. -/
theorem continuous_restrictedProductCongrLeftEquiv :
    Continuous (restrictedProductCongrLeftEquiv A e) := by
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  -- On the principal stage `𝓟 S` the map lands in the stage `𝓟 (e.symm ⁻¹' S)` of the target,
  -- and into the ambient product it is the homeomorphism `Homeomorph.piCongrLeft`.
  have hT : (cofinite : Filter ι) ≤ 𝓟 (e.symm ⁻¹' S) := by
    rw [← comap_principal, ← e.symm.injective.comap_cofinite_eq]
    exact comap_mono hS
  rw [continuous_restrictedProduct_iff_of_forall_mem hT]
  · exact (Homeomorph.piCongrLeft e).continuous.comp RestrictedProduct.continuous_coe
  · intro y i hi
    obtain ⟨j, rfl⟩ := e.surjective i
    simp only [Function.comp_apply, restrictedProductCongrLeftEquiv_apply_apply,
      RestrictedProduct.inclusion_apply]
    exact eventually_principal.mp y.2 j (by simpa using hi)

/-- The inverse of the reindexing equivalence is continuous for every reference family. -/
theorem continuous_restrictedProductCongrLeftEquiv_symm :
    Continuous (restrictedProductCongrLeftEquiv A e).symm :=
  RestrictedProduct.mapAlong_continuous G (fun j ↦ G (e j)) e e.injective.tendsto_cofinite
    (fun _ ↦ id) (.of_forall fun _ ↦ Set.mapsTo_id _) fun _ ↦ continuous_id

end Sets

section Mul

variable {S : ι → Type z} [∀ i, SetLike (S i) (G i)] [∀ i, Mul (G i)]
  [∀ i, MulMemClass (S i) (G i)]
variable (U : ∀ i, S i) (e : ι' ≃ ι)

/-- Reindexing a restricted product along an equivalence `e : ι' ≃ ι` of index types, as a
multiplicative equivalence, from the restricted product of the pulled-back family over `ι'` to
the restricted product over `ι`.  The image of `y` has coordinate `y j` at `e j`. -/
def restrictedProductCongrLeft : (Πʳ j, [G (e j), U (e j)]) ≃* (Πʳ i, [G i, U i]) where
  toEquiv := restrictedProductCongrLeftEquiv (fun i ↦ (U i : Set (G i))) e
  map_mul' y z := by
    ext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp

/-- The underlying equivalence of `restrictedProductCongrLeft` is the reindexing equivalence of
the underlying reference sets. -/
theorem restrictedProductCongrLeft_toEquiv :
    (restrictedProductCongrLeft U e : (Πʳ j, [G (e j), U (e j)]) ≃ (Πʳ i, [G i, U i])) =
      restrictedProductCongrLeftEquiv (fun i ↦ (U i : Set (G i))) e := by
  rfl

/-- The reindexed element has coordinate `y j` at `e j`; as `e` is surjective, this pins
`restrictedProductCongrLeft`. -/
@[simp]
theorem restrictedProductCongrLeft_apply_apply (y : Πʳ j, [G (e j), U (e j)]) (j : ι') :
    restrictedProductCongrLeft U e y (e j) = y j := by
  rw [← MulEquiv.coe_toEquiv, restrictedProductCongrLeft_toEquiv,
    restrictedProductCongrLeftEquiv_apply_apply]

-- Not `@[simp]`: `simp` rewrites the left side by `restrictedProductCongrLeft_symm` and
-- `restrictedProductReindex_apply`.
/-- The inverse of `restrictedProductCongrLeft` sends `x` to `j ↦ x (e j)`. -/
theorem restrictedProductCongrLeft_symm_apply (x : Πʳ i, [G i, U i]) (j : ι') :
    (restrictedProductCongrLeft U e).symm x j = x (e j) := by
  rw [← MulEquiv.coe_toEquiv, MulEquiv.toEquiv_symm, restrictedProductCongrLeft_toEquiv,
    restrictedProductCongrLeftEquiv_symm_apply]

/-- Reindexing a restricted product along an equivalence `e : ι' ≃ ι` of index types, in the
orientation `x ↦ (j ↦ x (e j))`: the inverse of `restrictedProductCongrLeft`. -/
def restrictedProductReindex : (Πʳ i, [G i, U i]) ≃* (Πʳ j, [G (e j), U (e j)]) :=
  (restrictedProductCongrLeft U e).symm

/-- The inverse of `restrictedProductCongrLeft` is `restrictedProductReindex`. -/
@[simp]
theorem restrictedProductCongrLeft_symm :
    (restrictedProductCongrLeft U e).symm = restrictedProductReindex U e :=
  (rfl)

/-- The inverse of `restrictedProductReindex` is `restrictedProductCongrLeft`. -/
@[simp]
theorem restrictedProductReindex_symm :
    (restrictedProductReindex U e).symm = restrictedProductCongrLeft U e :=
  (rfl)

/-- `restrictedProductReindex` sends `x` to `j ↦ x (e j)`. -/
@[simp]
theorem restrictedProductReindex_apply (x : Πʳ i, [G i, U i]) (j : ι') :
    restrictedProductReindex U e x j = x (e j) :=
  restrictedProductCongrLeft_symm_apply U e x j

-- Not `@[simp]`: `simp` rewrites the left side by `restrictedProductReindex_symm` and
-- `restrictedProductCongrLeft_apply_apply`.
/-- The inverse of `restrictedProductReindex` has coordinate `y j` at `e j`; as `e` is
surjective, this pins it. -/
theorem restrictedProductReindex_symm_apply (y : Πʳ j, [G (e j), U (e j)]) (j : ι') :
    (restrictedProductReindex U e).symm y (e j) = y j :=
  restrictedProductCongrLeft_apply_apply U e y j

variable [∀ i, TopologicalSpace (G i)]

/-- `restrictedProductCongrLeft` is continuous for every reference family. -/
theorem continuous_restrictedProductCongrLeft : Continuous (restrictedProductCongrLeft U e) := by
  rw [← MulEquiv.coe_toEquiv, restrictedProductCongrLeft_toEquiv]
  exact continuous_restrictedProductCongrLeftEquiv _ e

/-- The inverse of `restrictedProductCongrLeft` is continuous for every reference family. -/
theorem continuous_restrictedProductCongrLeft_symm :
    Continuous (restrictedProductCongrLeft U e).symm := by
  rw [← MulEquiv.coe_toEquiv, MulEquiv.toEquiv_symm, restrictedProductCongrLeft_toEquiv]
  exact continuous_restrictedProductCongrLeftEquiv_symm _ e

/-- `restrictedProductReindex` is continuous for every reference family. -/
theorem continuous_restrictedProductReindex : Continuous (restrictedProductReindex U e) :=
  continuous_restrictedProductCongrLeft_symm U e

/-- The inverse of `restrictedProductReindex` is continuous for every reference family. -/
theorem continuous_restrictedProductReindex_symm :
    Continuous (restrictedProductReindex U e).symm :=
  continuous_restrictedProductCongrLeft U e

end Mul

end TauCeti
