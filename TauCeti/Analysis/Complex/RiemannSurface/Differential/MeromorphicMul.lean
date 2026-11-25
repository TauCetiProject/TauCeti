/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Germ
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Twist
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Germ

/-!
# Multiplication of sections of `Ω_D` by meromorphic functions

Let `X` be a connected Riemann surface and `f` a meromorphic function on `X` with `ord f ≥ D - E`
for divisors `D` and `E`. Multiplying a global section `s` of `Ω_D` by `f` and normalizing gives
a global section of `Ω_E` (`TauCeti.RiemannSurface.differentialSections.meromorphicMul`). Off a
closed discrete set it is the `1`-form `f s`
(`TauCeti.RiemannSurface.differentialSections.toOneForm_meromorphicMul_eventuallyEq`), and its
coordinate germs are the products of those of `f` and `s`
(`TauCeti.RiemannSurface.differentialSections.toChartGerm_meromorphicMul`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16-17 (the sheaves `Ω_D`).
-/

public noncomputable section

open Filter Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X] {D E : WeilDivisor X}

namespace differentialSections

omit [ConnectedSpace X] in
/-- The product of a meromorphic function with a global section of `Ω_D` is meromorphic. -/
theorem meromorphicAt_finitePart_smul_toOneForm (f : MeromorphicFunction X)
    (s : differentialSections D ⊤) (x : X) : (f.finitePart • toOneForm D s).MeromorphicAt x :=
  OneForm.MeromorphicAt.smul (f.meromorphicAt_finitePart x)
    (isDifferentialSectionAt_toOneForm s x).meromorphicAt

/-- If `ord f ≥ D - E`, the product of `f` with a global section of `Ω_D` has order at least
`-E`. -/
theorem neg_le_order_finitePart_smul_toOneForm {f : MeromorphicFunction X}
    (hf : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    (s : differentialSections D ⊤) (x : X) :
    ((-E x : ℤ) : WithTop ℤ) ≤ (f.finitePart • toOneForm D s).order x := by
  rw [OneForm.order_smul (f.meromorphicAt_finitePart x)
    (isDifferentialSectionAt_toOneForm s x).meromorphicAt, ← MeromorphicFunction.order_apply]
  calc ((-E x : ℤ) : WithTop ℤ) = ((D x - E x : ℤ) : WithTop ℤ) + ((-D x : ℤ) : WithTop ℤ) := by
        norm_cast
        ring
    _ ≤ _ := add_le_add (hf x) (isDifferentialSectionAt_toOneForm s x).neg_le_order

/-- **Multiplication of global sections of `Ω_D` by a meromorphic function** `f` with
`ord f ≥ D - E`, landing in `Ω_E`: the normalization of the `1`-form `f s`. -/
def meromorphicMul (f : MeromorphicFunction X)
    (hf : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f) :
    differentialSections D ⊤ →ₗ[ℂ] differentialSections E ⊤ where
  toFun s := normalize E _ (meromorphicAt_finitePart_smul_toOneForm f s)
    (neg_le_order_finitePart_smul_toOneForm hf s)
  map_add' s t := ext_of_eventually_nhdsNE_toOneForm fun x ↦ by
    filter_upwards [toOneForm_normalize_eventuallyEq _ _ x,
      toOneForm_normalize_eventuallyEq (meromorphicAt_finitePart_smul_toOneForm f s)
        (neg_le_order_finitePart_smul_toOneForm hf s) x,
      toOneForm_normalize_eventuallyEq (meromorphicAt_finitePart_smul_toOneForm f t)
        (neg_le_order_finitePart_smul_toOneForm hf t) x] with y h₁ h₂ h₃
    rw [h₁, map_add, map_add, Pi.add_apply, h₂, h₃]
    exact smul_add (f.finitePart y) (toOneForm D s y) (toOneForm D t y)
  map_smul' c s := ext_of_eventually_nhdsNE_toOneForm fun x ↦ by
    filter_upwards [toOneForm_normalize_eventuallyEq _ _ x,
      toOneForm_normalize_eventuallyEq (meromorphicAt_finitePart_smul_toOneForm f s)
        (neg_le_order_finitePart_smul_toOneForm hf s) x] with y h₁ h₂
    rw [h₁, map_smul, map_smul, RingHom.id_apply, Pi.smul_apply, h₂]
    exact smul_comm (f.finitePart y) c (toOneForm D s y)

/-- Off a closed discrete set, `meromorphicMul f hf s` is the `1`-form `f s`. -/
theorem toOneForm_meromorphicMul_eventuallyEq (f : MeromorphicFunction X)
    (hf : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    (s : differentialSections D ⊤) (x : X) :
    ∀ᶠ y in 𝓝[≠] x, toOneForm E (meromorphicMul f hf s) y = (f.finitePart • toOneForm D s) y :=
  toOneForm_normalize_eventuallyEq _ _ x

/-- The coordinate germ of `f s` is the product of the coordinate germs of `f` and `s`. -/
@[simp]
theorem toChartGerm_meromorphicMul (f : MeromorphicFunction X)
    (hf : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x f)
    (s : differentialSections D ⊤) (x : X) :
    toChartGerm E x (meromorphicMul f hf s) =
      MeromorphicFunction.toChartGerm x f * toChartGerm D x s := by
  rw [toChartGerm_eq_mk (meromorphicAt_finitePart_smul_toOneForm f s x)
    (toOneForm_meromorphicMul_eventuallyEq f hf s x)]
  apply Subtype.ext
  rw [meromorphicGerms.coe_mk, Subring.coe_mul, MeromorphicFunction.coe_toChartGerm,
    coe_toChartGerm, OneForm.coeff_smul, Germ.coe_mul]

end differentialSections

end TauCeti.RiemannSurface
