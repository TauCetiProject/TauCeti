/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.Prod
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Prod
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic

/-!
# Continuity of the `Spinᶜ` homomorphism on orthogonal sums

The homomorphism `CliffordAlgebra.spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ : Spinᶜ(Q₁) × Spinᶜ(Q₂) →*
Spinᶜ(Q₁ ⊕ Q₂)` is continuous for the quotient topologies whenever multiplication is continuous
on `CliffordAlgebra Q₁`, on `CliffordAlgebra Q₂` and on `CliffordAlgebra (Q₁.prod Q₂)`: the
product of the two quotient maps `Spin(Qᵢ) × U(1) → Spinᶜ(Qᵢ)` is a quotient map, since both are
open, and on representatives the homomorphism is `((s, z), (t, w)) ↦ [spinGroupProd (s, t), z w]`.

## Main declarations

* `CliffordAlgebra.continuous_spinCGroupProd`: continuity of `spinCGroupProd`.
* `CliffordAlgebra.spinCGroupProdContinuousMonoidHom`: `spinCGroupProd` as a continuous monoid
  homomorphism.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §2 and Appendix D.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Topology

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℝ M₁] [AddCommGroup M₂] [Module ℝ M₂]
  (Q₁ : QuadraticForm ℝ M₁) (Q₂ : QuadraticForm ℝ M₂) (hQ₁ : Q₁ ≠ 0) (hQ₂ : Q₂ ≠ 0)
  [ContinuousMul (CliffordAlgebra Q₁)] [ContinuousMul (CliffordAlgebra Q₂)]
  [ContinuousMul (CliffordAlgebra (Q₁.prod Q₂))]

/-- `spinCGroupProd` is continuous for the quotient topologies. -/
@[fun_prop]
theorem continuous_spinCGroupProd : Continuous (spinCGroupProd Q₁ Q₂ hQ₁ hQ₂) := by
  have hq : IsQuotientMap (Prod.map (spinCGroup.mk Q₁ hQ₁) (spinCGroup.mk Q₂ hQ₂)) := by
    rw [spinCGroup.coe_mk, spinCGroup.coe_mk]
    exact (QuotientGroup.isOpenQuotientMap_mk.prodMap
      QuotientGroup.isOpenQuotientMap_mk).isQuotientMap
  rw [hq.continuous_iff]
  have h : spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ ∘ Prod.map (spinCGroup.mk Q₁ hQ₁) (spinCGroup.mk Q₂ hQ₂) =
      fun x : (spinGroup Q₁ × Circle) × (spinGroup Q₂ × Circle) ↦
        spinCGroup.mk _ _ (spinGroupProd Q₁ Q₂ (x.1.1, x.2.1), x.1.2 * x.2.2) :=
    funext fun x ↦ spinCGroupProd_mk_mk Q₁ Q₂ hQ₁ hQ₂ x.1 x.2
  rw [h, spinCGroup.coe_mk]
  fun_prop

/-- `spinCGroupProd` as a continuous monoid homomorphism. -/
def spinCGroupProdContinuousMonoidHom :
    spinCGroup Q₁ hQ₁ × spinCGroup Q₂ hQ₂ →ₜ*
      spinCGroup (Q₁.prod Q₂) (QuadraticMap.prod_ne_zero_left hQ₁) :=
  ⟨spinCGroupProd Q₁ Q₂ hQ₁ hQ₂, continuous_spinCGroupProd Q₁ Q₂ hQ₁ hQ₂⟩

/-- The underlying monoid homomorphism of `spinCGroupProdContinuousMonoidHom` is
`spinCGroupProd`. -/
@[simp]
theorem coeMonoidHom_spinCGroupProdContinuousMonoidHom :
    (spinCGroupProdContinuousMonoidHom Q₁ Q₂ hQ₁ hQ₂ :
        spinCGroup Q₁ hQ₁ × spinCGroup Q₂ hQ₂ →* spinCGroup (Q₁.prod Q₂) _) =
      spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ :=
  (rfl)

/-- Evaluating `spinCGroupProdContinuousMonoidHom` applies `spinCGroupProd`. -/
@[simp]
theorem spinCGroupProdContinuousMonoidHom_apply (x : spinCGroup Q₁ hQ₁ × spinCGroup Q₂ hQ₂) :
    spinCGroupProdContinuousMonoidHom Q₁ Q₂ hQ₁ hQ₂ x = spinCGroupProd Q₁ Q₂ hQ₁ hQ₂ x :=
  (rfl)

end CliffordAlgebra
