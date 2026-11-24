/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sheaf
public import TauCeti.Analysis.Meromorphic.OrderFiltration

/-!
# Coordinate germs of sections of `Ω_D`

Let `X` be a Riemann surface and `D` a divisor on `X`. A global section `s` of the sheaf `Ω_D`,
read as a `1`-form, has at each point `x` a coefficient in the preferred chart at `x`; its germ is
a meromorphic germ at `chartAt ℂ x x`, the *coordinate germ* of `s` at `x`
(`TauCeti.RiemannSurface.differentialSections.toChartGerm`). It has the order of the `1`-form, so
it satisfies the order bound of `Ω_D`
(`TauCeti.RiemannSurface.differentialSections.toChartGerm_mem_orderGE`), and it does not change
under the inclusion `Ω_D ⟶ Ω_E` for `D ≤ E`
(`TauCeti.RiemannSurface.differentialSections.toChartGerm_differentialSheafMapOfLE`). It is how
local germ constructions, such as residues, are applied to global sections of `Ω_D`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§9 and 17 (differential forms in local coordinates and the sheaves `Ω_D`).
-/

public noncomputable section

open CategoryTheory Filter Opposite TopologicalSpace Topology
open scoped Manifold

namespace TauCeti.RiemannSurface.differentialSections

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {D : WeilDivisor X}

variable (D) in
/-- The **coordinate germ** of a global section of `Ω_D` at `x`: the germ of its coefficient in
the preferred chart at `x`. -/
def toChartGerm (x : X) : differentialSections D ⊤ →ₗ[ℂ] meromorphicGerms ℂ (chartAt ℂ x x) where
  toFun s := meromorphicGerms.mk ((toOneForm D s).coeff (chartAt ℂ x))
    ((OneForm.meromorphicAt_def _ _).1 (isDifferentialSectionAt_toOneForm s x).meromorphicAt)
  map_add' s t := by
    rw [← meromorphicGerms.mk_add]
    congr 1
    rw [map_add, OneForm.coeff_add]
  map_smul' c s := by
    rw [RingHom.id_apply, ← meromorphicGerms.mk_smul]
    congr 1
    rw [map_smul, OneForm.coeff_const_smul]

/-- The coordinate germ is the germ of the coefficient in the preferred chart. -/
theorem toChartGerm_apply (x : X) (s : differentialSections D ⊤) :
    toChartGerm D x s = meromorphicGerms.mk ((toOneForm D s).coeff (chartAt ℂ x))
      ((OneForm.meromorphicAt_def _ _).1 (isDifferentialSectionAt_toOneForm s x).meromorphicAt) :=
  (rfl)

@[simp]
theorem coe_toChartGerm (x : X) (s : differentialSections D ⊤) :
    (toChartGerm D x s : Germ (𝓝[≠] (chartAt ℂ x x)) ℂ) =
      ((toOneForm D s).coeff (chartAt ℂ x) : ℂ → ℂ) :=
  meromorphicGerms.coe_mk _ _

/-- The coordinate germ has the order of the `1`-form. -/
@[simp]
theorem order_toChartGerm (x : X) (s : differentialSections D ⊤) :
    meromorphicGerms.order (toChartGerm D x s) = (toOneForm D s).order x := by
  rw [toChartGerm_apply, meromorphicGerms.order_mk, OneForm.order_def]

/-- The coordinate germ of a section of `Ω_D` satisfies the order bound of `Ω_D`. -/
theorem toChartGerm_mem_orderGE (x : X) (s : differentialSections D ⊤) :
    toChartGerm D x s ∈ meromorphicGerms.orderGE (chartAt ℂ x x) (-D x) := by
  rw [meromorphicGerms.mem_orderGE, order_toChartGerm]
  exact (isDifferentialSectionAt_toOneForm s x).neg_le_order

/-- The inclusion `Ω_D ⟶ Ω_E` for `D ≤ E` does not change coordinate germs, although it changes
the normalized values at the new poles. -/
theorem toChartGerm_differentialSheafMapOfLE {E : WeilDivisor X} (h : D ≤ E) (x : X)
    (s : (differentialSheaf D).obj.obj (op ⊤)) :
    toChartGerm E x (differentialSheafSectionsEquiv E ⊤
      ((differentialSheafMapOfLE h).hom.app (op ⊤) s)) =
      toChartGerm D x (differentialSheafSectionsEquiv D ⊤ s) := by
  have := ChartedSpace.t1Space ℂ X
  apply Subtype.ext
  rw [coe_toChartGerm, coe_toChartGerm]
  apply Germ.coe_eq.2
  apply OneForm.coeff_chartAt_eventuallyEq
  filter_upwards [E.eventually_eq_zero_nhdsNE x] with y hy
  simp only [toOneForm_apply, differentialSheafMapOfLE_app, hy, le_refl, ite_true]

end TauCeti.RiemannSurface.differentialSections
