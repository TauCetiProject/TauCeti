/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Homeomorphisms of products of subspaces and of products of pairs

Two equivalences of Mathlib are homeomorphisms for the product topologies:

* `Homeomorph.Set.univPi`: the subspace `Set.pi univ s` of a product is the product of the
  subspaces `s i`, upgrading `Equiv.Set.univPi`;
* `Homeomorph.arrowProdHomeomorphProdArrow`: a product of pairs is a pair of products,
  `(∀ i, X i × Y i) ≃ₜ (∀ i, X i) × (∀ i, Y i)`, upgrading `Equiv.arrowProdEquivProdArrow`.
-/

public section

open Set

namespace Homeomorph

variable {ι : Type*}

section univPi

variable {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (s : ∀ i, Set (X i))

/-- The subspace `Set.pi univ s` of a product is homeomorphic to the product of the subspaces
`s i`. -/
def Set.univPi : univ.pi s ≃ₜ ∀ i, s i where
  toEquiv := Equiv.Set.univPi s
  continuous_toFun := continuous_pi fun i ↦
    ((continuous_apply i).comp continuous_subtypeVal).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun i ↦ continuous_subtypeVal.comp (continuous_apply i)).subtype_mk _

/-- The underlying equivalence of `Homeomorph.Set.univPi` is `Equiv.Set.univPi`. -/
@[simp]
theorem Set.toEquiv_univPi : (Set.univPi s).toEquiv = Equiv.Set.univPi s :=
  (rfl)

/-- The `i`-th component of the image of a point of `Set.pi univ s` is its `i`-th coordinate. -/
@[simp]
theorem Set.coe_univPi_apply (z : univ.pi s) (i : ι) :
    (Set.univPi s z i : X i) = (z : ∀ i, X i) i :=
  (rfl)

/-- The inverse of `Homeomorph.Set.univPi` assembles the coordinates into a point of the
product. -/
@[simp]
theorem Set.coe_univPi_symm_apply (z : ∀ i, s i) :
    ((Set.univPi s).symm z : ∀ i, X i) = fun i ↦ (z i : X i) :=
  (rfl)

end univPi

section arrowProd

variable (X Y : ι → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]

/-- A product of pairs is homeomorphic to the pair of the products of the components. -/
def arrowProdHomeomorphProdArrow : (∀ i, X i × Y i) ≃ₜ (∀ i, X i) × ∀ i, Y i where
  toEquiv := Equiv.arrowProdEquivProdArrow ι X Y
  continuous_toFun := (continuous_pi fun i ↦ continuous_fst.comp (continuous_apply i)).prodMk
    (continuous_pi fun i ↦ continuous_snd.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i ↦
    ((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd)

/-- The underlying equivalence of `Homeomorph.arrowProdHomeomorphProdArrow` is
`Equiv.arrowProdEquivProdArrow`. -/
@[simp]
theorem toEquiv_arrowProdHomeomorphProdArrow :
    (arrowProdHomeomorphProdArrow X Y).toEquiv = Equiv.arrowProdEquivProdArrow ι X Y :=
  (rfl)

/-- `Homeomorph.arrowProdHomeomorphProdArrow` splits a product of pairs into its two
components. -/
@[simp]
theorem arrowProdHomeomorphProdArrow_apply (z : ∀ i, X i × Y i) :
    arrowProdHomeomorphProdArrow X Y z = (fun i ↦ (z i).1, fun i ↦ (z i).2) :=
  (rfl)

/-- The inverse of `Homeomorph.arrowProdHomeomorphProdArrow` pairs the two components. -/
@[simp]
theorem arrowProdHomeomorphProdArrow_symm_apply (z : (∀ i, X i) × ∀ i, Y i) :
    (arrowProdHomeomorphProdArrow X Y).symm z = fun i ↦ (z.1 i, z.2 i) :=
  (rfl)

end arrowProd

end Homeomorph
