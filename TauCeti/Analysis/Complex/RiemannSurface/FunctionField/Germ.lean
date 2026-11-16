/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Order
public import TauCeti.Analysis.Meromorphic.OrderFiltration
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Coordinate germs of meromorphic functions on a Riemann surface

Let `X` be a connected Riemann surface. Reading the finite part of a meromorphic function `f` in
the preferred chart at `x` gives a meromorphic germ at `chartAt ℂ x x`, the *coordinate germ* of
`f` at `x` (`TauCeti.RiemannSurface.MeromorphicFunction.toChartGerm`). This is an algebra map
from the field of meromorphic functions to the field of meromorphic germs, and it preserves
orders (`TauCeti.RiemannSurface.MeromorphicFunction.order_toChartGerm`). It is how local germ
constructions, such as principal parts and residues, are applied to global meromorphic
functions.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§1 and 16 (meromorphic functions in local coordinates).
-/

public noncomputable section

open Filter OnePoint Topology
open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [ConnectedSpace X]

/-- The **coordinate germ** of a meromorphic function at `x`: the germ of its finite part read
in the preferred chart at `x`, as an algebra map to the field of meromorphic germs. -/
def toChartGerm (x : X) : MeromorphicFunction X →ₐ[ℂ] meromorphicGerms ℂ (chartAt ℂ x x) where
  toFun f := meromorphicGerms.mk (f.finitePart ∘ (chartAt ℂ x).symm)
    ((meromorphicAt_def _ _).1 (f.meromorphicAt_finitePart x))
  map_one' := by
    rw [← meromorphicGerms.mk_one, meromorphicGerms.mk_eq_mk_iff, finitePart_one]
    rfl
  map_mul' f g := by
    rw [← meromorphicGerms.mk_mul, meromorphicGerms.mk_eq_mk_iff]
    exact (finitePart_mul_eventuallyEq f g x).comp_tendsto (tendsto_chartAt_symm_nhdsNE x)
  map_zero' := by
    rw [← meromorphicGerms.mk_zero, meromorphicGerms.mk_eq_mk_iff, finitePart_zero]
    rfl
  map_add' f g := by
    rw [← meromorphicGerms.mk_add, meromorphicGerms.mk_eq_mk_iff]
    exact (finitePart_add_eventuallyEq f g x).comp_tendsto (tendsto_chartAt_symm_nhdsNE x)
  commutes' c := by
    rw [← meromorphicGerms.mk_const, meromorphicGerms.mk_eq_mk_iff, finitePart_algebraMap]
    rfl

/-- The coordinate germ is the germ of the finite part read in the preferred chart. -/
theorem toChartGerm_apply (x : X) (f : MeromorphicFunction X) :
    toChartGerm x f = meromorphicGerms.mk (f.finitePart ∘ (chartAt ℂ x).symm)
      ((meromorphicAt_def _ _).1 (f.meromorphicAt_finitePart x)) :=
  (rfl)

@[simp]
theorem coe_toChartGerm (x : X) (f : MeromorphicFunction X) :
    (toChartGerm x f : Germ (𝓝[≠] (chartAt ℂ x x)) ℂ) =
      (f.finitePart ∘ (chartAt ℂ x).symm : ℂ → ℂ) :=
  meromorphicGerms.coe_mk _ _

/-- The coordinate germ has the order of the meromorphic function. -/
@[simp]
theorem order_toChartGerm (x : X) (f : MeromorphicFunction X) :
    meromorphicGerms.order (toChartGerm x f) = order x f := by
  rw [order_apply, meromorphicOrderAt_def, toChartGerm_apply, meromorphicGerms.order_mk]

end TauCeti.RiemannSurface.MeromorphicFunction
