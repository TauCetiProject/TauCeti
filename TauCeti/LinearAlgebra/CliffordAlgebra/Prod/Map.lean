/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.TensorProduct.Graded.Map

/-!
# Naturality of the orthogonal-sum decomposition of Clifford algebras

Mathlib's `CliffordAlgebra.prodEquiv` identifies the Clifford algebra of an orthogonal sum
`Q₁.prod Q₂` with the graded tensor product `evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂`. This file proves that
the identification is natural in the two quadratic spaces. Quadratic isometries `f₁ : Q₁ →qᵢ P₁`
and `f₂ : Q₂ →qᵢ P₂` induce the isometry `f₁.prodMap f₂` of orthogonal sums, hence an algebra map
`CliffordAlgebra.map (f₁.prodMap f₂)`, and they induce homomorphisms `CliffordAlgebra.mapEvenOdd fᵢ`
of `ℤ/2`-graded algebras, hence an algebra map of graded tensor products through
`GradedTensorProduct.map`. These two maps correspond under `prodEquiv`, and under its inverse
`toProd`. On generators this says that `ι (m₁, m₂) ↦ ι m₁ ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ ι m₂` is carried to
`ι (f₁ m₁, f₂ m₂) ↦ ι (f₁ m₁) ᵍ⊗ₜ 1 + 1 ᵍ⊗ₜ ι (f₂ m₂)`.

No hypothesis on the base ring is needed: in particular `2` need not be invertible, and the forms
may be degenerate.

## Main results

* `CliffordAlgebra.ofProd_map_prodMap`: the forward map `ofProd` of `prodEquiv` (to which `simp`
  rewrites `prodEquiv`) intertwines `map (f₁.prodMap f₂)` with
  `GradedTensorProduct.map (mapEvenOdd f₁) (mapEvenOdd f₂)`.
* `CliffordAlgebra.map_prodMap_toProd`: the same naturality for the inverse map `toProd`.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1.
-/

public section

open QuadraticMap
open scoped TensorProduct

namespace CliffordAlgebra

variable {R M₁ M₂ N₁ N₂ : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  {P₁ : QuadraticForm R N₁} {P₂ : QuadraticForm R N₂}

/-- The forward map `ofProd` of `CliffordAlgebra.prodEquiv` is natural: the algebra map induced by
the orthogonal sum `f₁.prodMap f₂` of two isometries corresponds to the graded tensor product of
the graded algebra maps induced by `f₁` and `f₂`. -/
theorem ofProd_comp_map_prodMap (f₁ : Q₁ →qᵢ P₁) (f₂ : Q₂ →qᵢ P₂) :
    (ofProd P₁ P₂).comp (map (f₁.prodMap f₂)) =
      (GradedTensorProduct.map (mapEvenOdd f₁) (mapEvenOdd f₂)).comp (ofProd Q₁ Q₂) := by
  ext m <;> simp

/-- Pointwise form of `CliffordAlgebra.ofProd_comp_map_prodMap`. -/
@[simp]
theorem ofProd_map_prodMap (f₁ : Q₁ →qᵢ P₁) (f₂ : Q₂ →qᵢ P₂) (x : CliffordAlgebra (Q₁.prod Q₂)) :
    ofProd P₁ P₂ (map (f₁.prodMap f₂) x) =
      GradedTensorProduct.map (mapEvenOdd f₁) (mapEvenOdd f₂) (ofProd Q₁ Q₂ x) :=
  DFunLike.congr_fun (ofProd_comp_map_prodMap f₁ f₂) x

/-- The inverse map `toProd` of `CliffordAlgebra.prodEquiv` is natural: it intertwines the graded
tensor product of the graded algebra maps induced by `f₁` and `f₂` with the algebra map induced by
their orthogonal sum. -/
theorem map_prodMap_comp_toProd (f₁ : Q₁ →qᵢ P₁) (f₂ : Q₂ →qᵢ P₂) :
    (map (f₁.prodMap f₂)).comp (toProd Q₁ Q₂) =
      (toProd P₁ P₂).comp (GradedTensorProduct.map (mapEvenOdd f₁) (mapEvenOdd f₂)) := by
  ext <;> simp

/-- Pointwise form of `CliffordAlgebra.map_prodMap_comp_toProd`. -/
@[simp]
theorem map_prodMap_toProd (f₁ : Q₁ →qᵢ P₁) (f₂ : Q₂ →qᵢ P₂)
    (x : evenOdd Q₁ ᵍ⊗[R] evenOdd Q₂) :
    map (f₁.prodMap f₂) (toProd Q₁ Q₂ x) =
      toProd P₁ P₂ (GradedTensorProduct.map (mapEvenOdd f₁) (mapEvenOdd f₂) x) :=
  DFunLike.congr_fun (map_prodMap_comp_toProd f₁ f₂) x

end CliffordAlgebra
