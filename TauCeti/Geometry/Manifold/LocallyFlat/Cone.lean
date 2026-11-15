/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.Conformal.Jordan.Schoenflies
import TauCeti.Geometry.Manifold.LocallyFlat.Linear

/-!
# Cones over Jordan curves in the 2-sphere are locally flat

Let `γ` be an embedding of the unit circle into the unit sphere `S²` of a three-dimensional real
inner product space `E`. The cone over `γ`, the map `r • u ↦ r • γ u` of the plane `ℂ` into `E`
(`TauCeti.sphereCone`), is a **locally flat** embedding with complementary model `ℝ`
(`TauCeti.isLocallyFlat_sphereCone`): around every point of its image, including the cone point
`0`, some chart of `E` carries the image onto the coordinate plane `ℂ × {0}`. Away from the cone
point this is the local flatness of the curve itself, but at the cone point it is a global
statement about the curve, which is where the Schoenflies theorem enters.

By the Schoenflies theorem on the 2-sphere
(`TauCeti.IsJordanCurve.exists_homeomorph_image_inner_eq_zero`), some homeomorphism `H` of `S²`
carries a great circle onto the image of `γ`; a point of `S²` off the curve exists since `S²` is
simply connected and the circle is not
(`TauCeti.not_surjective_of_continuous_injective_circle_sphere`). Reparametrizing the great circle
by a homeomorphism `τ` of the circle, `γ` is `H` composed with a linear isometric embedding `ι` of
the unit circle of `ℂ` as a great circle, precomposed with `τ`
(`TauCeti.exists_homeomorph_comp_eq_of_continuous_injective`). Taking cones
(`Homeomorph.sphereCone`), the cone over `γ` is the homeomorphism `sphereCone H` of `E` applied to
the linear embedding `ι` of the plane, precomposed with the homeomorphism `sphereCone τ` of the
plane, and a linear plane in `E` is flat (`LinearMap.isLocallyFlat_of_injective`).

This is the local model of a piecewise-linear surface in a `3`-manifold: near a vertex such a
surface is the cone over a polygonal Jordan curve in a small sphere around the vertex. The analogue
fails one dimension up, which is why piecewise-linear embeddings need not be locally flat in
codimension two: the cone over a knotted circle in `S³` is a piecewise-linear disc in `ℝ⁴` that is
not locally flat at its cone point.

## Main results

* `TauCeti.isLocallyFlat_sphereCone`: the cone over an embedded circle in the 2-sphere is a locally
  flat embedding of the plane into three-space.

## References

* E. E. Moise, *Geometric Topology in Dimensions 2 and 3*, Springer GTM 47 (1977), for the
  Schoenflies theorem and for tame surfaces in `3`-manifolds.
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, for stars and links of points of polyhedra.
-/

public section

open scoped InnerProductSpace

open Function Metric Module Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 3)]

/-- **The cone over a Jordan curve in the 2-sphere is locally flat.** For an embedding `γ` of the
unit circle into the unit sphere of a three-dimensional real inner product space `E`, the cone
`r • u ↦ r • γ u` is a locally flat embedding of the plane `ℂ` into `E`, with complementary model
`ℝ`. -/
theorem isLocallyFlat_sphereCone {γ : sphere (0 : ℂ) 1 → sphere (0 : E) 1} (hγ : Continuous γ)
    (hγi : Injective γ) : IsLocallyFlat ℂ ℝ (sphereCone fun u => (γ u : E)) := by
  /- By Schoenflies, `γ = H ∘ L ∘ τ` on the circle, for a homeomorphism `H` of the sphere, a
  linear isometric embedding `L` and a homeomorphism `τ` of the circle. -/
  obtain ⟨L, H, τ, hHL⟩ := exists_homeomorph_comp_eq_of_continuous_injective hγ hγi
  /- Taking cones, the cone over `γ` is `sphereCone H ∘ L ∘ sphereCone τ`. -/
  have key : (sphereCone fun u => (γ u : E)) = H.sphereCone ∘ L ∘ τ.sphereCone := by
    funext z
    rcases eq_zero_or_exists_eq_smul_coe_sphere z with rfl | ⟨r, hr, u, rfl⟩
    · simp
    have hτu : L (τ u) = H.symm (γ u) := (congrFun hHL u).symm
    simp only [comp_apply, Homeomorph.coe_sphereCone, sphereCone_smul_coe hr.le]
    rw [map_smul, hτu, sphereCone_smul_coe hr.le]
    simp
  /- The plane `L` is flat, being linear. -/
  have hL : IsLocallyFlat ℂ ℝ L := by
    have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ 2
    refine LinearMap.isLocallyFlat_of_injective L.toLinearMap L.injective ?_
    rw [Complex.finrank_real_complex, Module.finrank_self, Fact.out (p := finrank ℝ E = 3)]
  rw [key]
  exact (hL.comp_homeomorph τ.sphereCone).homeomorph_comp H.sphereCone

end TauCeti
