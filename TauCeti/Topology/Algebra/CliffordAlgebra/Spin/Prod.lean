/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Prod
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuity of the Spin homomorphism on orthogonal sums

For quadratic forms `Q₁` and `Q₂` over a topological commutative ring `R`, the orthogonal-sum Spin
homomorphism `CliffordAlgebra.spinGroupProd Q₁ Q₂` multiplies the Spin maps induced by the two
canonical quadratic inclusions `QuadraticMap.Isometry.inl Q₁ Q₂` and
`QuadraticMap.Isometry.inr Q₁ Q₂`. Each inclusion map is continuous for the canonical
Clifford-algebra subtype topologies (`QuadraticMap.Isometry.continuous_spinGroupMap`), so
`spinGroupProd Q₁ Q₂` is continuous whenever multiplication on `CliffordAlgebra (Q₁.prod Q₂)` is
continuous.

## Main definitions

* `CliffordAlgebra.spinGroupProdContinuousMonoidHom`: `spinGroupProd Q₁ Q₂` bundled as a continuous
  monoid homomorphism `spinGroup Q₁ × spinGroup Q₂ →ₜ* spinGroup (Q₁.prod Q₂)`.

## Main results

* `CliffordAlgebra.continuous_spinGroupProd`: continuity of `spinGroupProd Q₁ Q₂`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
-/

public section

namespace CliffordAlgebra

variable {R M₁ M₂ : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
  [ContinuousMul (CliffordAlgebra (Q₁.prod Q₂))]

/-- **The orthogonal-sum Spin homomorphism `spinGroupProd` is continuous** for the canonical
Clifford-algebra subtype topologies whenever multiplication on `CliffordAlgebra (Q₁.prod Q₂)` is
continuous. -/
@[fun_prop]
theorem continuous_spinGroupProd : Continuous (spinGroupProd Q₁ Q₂) :=
  (((QuadraticMap.Isometry.inl Q₁ Q₂).continuous_spinGroupMap.comp continuous_fst).mul
    ((QuadraticMap.Isometry.inr Q₁ Q₂).continuous_spinGroupMap.comp continuous_snd)).congr
      fun x ↦ (spinGroupProd_apply Q₁ Q₂ x).symm

/-- **The orthogonal-sum Spin homomorphism `spinGroupProd`, bundled as a continuous homomorphism**
`spinGroup Q₁ × spinGroup Q₂ →ₜ* spinGroup (Q₁.prod Q₂)`. -/
def spinGroupProdContinuousMonoidHom :
    spinGroup Q₁ × spinGroup Q₂ →ₜ* spinGroup (Q₁.prod Q₂) :=
  ⟨spinGroupProd Q₁ Q₂, continuous_spinGroupProd Q₁ Q₂⟩

/-- The underlying monoid homomorphism of `spinGroupProdContinuousMonoidHom` is `spinGroupProd`. -/
@[simp]
theorem coeMonoidHom_spinGroupProdContinuousMonoidHom :
    (spinGroupProdContinuousMonoidHom Q₁ Q₂ :
        spinGroup Q₁ × spinGroup Q₂ →* spinGroup (Q₁.prod Q₂)) =
      spinGroupProd Q₁ Q₂ :=
  (rfl)

/-- Evaluating `spinGroupProdContinuousMonoidHom` applies `spinGroupProd`. -/
@[simp]
theorem spinGroupProdContinuousMonoidHom_apply (x : spinGroup Q₁ × spinGroup Q₂) :
    spinGroupProdContinuousMonoidHom Q₁ Q₂ x = spinGroupProd Q₁ Q₂ x :=
  (rfl)

end CliffordAlgebra

end
