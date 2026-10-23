/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.AlgebraicTopology.Singular.JordanBrouwer

/-!
# Jordan separation on the Riemann sphere

A Jordan curve `J` in the Riemann sphere `OnePoint ℂ` separates it: `Jᶜ` is not preconnected. This
is the Jordan–Brouwer separation theorem for the two-sphere,
`TauCeti.natCard_zerothHomotopy_sphere_compl_range_eq_two`, transported along Mathlib's
stereographic homeomorphism `onePointEquivSphereOfFinrankEq`, in the connected form
`TauCeti.not_isPreconnected_compl_range_sphere` that holds because the sphere is a manifold.

The consequence used for unbounded Jordan domains is an exterior point. If `U ⊆ ℂ` is open and
connected and its frontier, together with the point at infinity, is a Jordan curve of the Riemann
sphere, then some point of `ℂ` lies outside `closure U`. Otherwise `U` is dense, its frontier is
`Uᶜ`, and the complement of the curve is the image of the connected set `U`. Inverting `U` about
such a point turns it into a bounded Jordan domain of the plane.

## Main results

* `TauCeti.IsJordanCurve.not_isPreconnected_compl_onePoint` — a Jordan curve separates the Riemann
  sphere.
* `TauCeti.exists_notMem_closure_of_isJordanCurve_insert_infty` — an open connected set whose
  frontier, together with the point at infinity, is a Jordan curve of the Riemann sphere has a
  point outside its closure.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.B, Corollary 2B.2.
-/

public section

namespace TauCeti

open Metric Set Topology
open scoped OnePoint

/-- **The Jordan separation theorem on the Riemann sphere.** The complement of a Jordan curve in
`OnePoint ℂ` is not preconnected. -/
theorem IsJordanCurve.not_isPreconnected_compl_onePoint {J : Set (OnePoint ℂ)}
    (hJ : IsJordanCurve J) : ¬ IsPreconnected Jᶜ := by
  intro hconn
  obtain ⟨e⟩ := isJordanCurve_iff.mp hJ
  -- stereographic projection carries `J` to an embedded circle of the sphere
  let Φ : OnePoint ℂ ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let φ := sphereCircleHomeomorph (0 : ℂ) one_pos
  refine not_isPreconnected_compl_range_sphere (h := Φ ∘ jordanParam e ∘ φ) (by simp)
    (Φ.continuous.comp ((continuous_jordanParam e).comp φ.continuous))
    (Φ.injective.comp ((jordanParam_injective e).comp φ.injective)) ?_
  rw [range_comp, range_comp, φ.range_coe, image_univ, range_jordanParam, ← Φ.image_compl]
  exact hconn.image _ Φ.continuous.continuousOn

/-- **An unbounded Jordan domain has an exterior point.** If `U ⊆ ℂ` is open and preconnected and
its frontier, together with the point at infinity, is a Jordan curve of the Riemann sphere, then
some point of `ℂ` lies outside the closure of `U`. -/
theorem exists_notMem_closure_of_isJordanCurve_insert_infty {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsPreconnected U)
    (hUJ : IsJordanCurve (insert ∞ (((↑) : ℂ → OnePoint ℂ) '' frontier U))) :
    ∃ q, q ∉ closure U := by
  by_contra! hcl
  -- a dense open `U` has frontier `Uᶜ`, so the complement of the curve is the image of `U`
  have hfr : frontier U = Uᶜ := by
    rw [frontier, hUo.interior_eq, eq_univ_of_forall hcl, compl_eq_univ_sdiff]
  refine hUJ.not_isPreconnected_compl_onePoint ?_
  convert hUc.image _ OnePoint.continuous_coe.continuousOn using 1
  ext z
  induction z using OnePoint.rec <;> simp [hfr]

end TauCeti
