/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.UpperHalfPlane
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.PolygonalDomain
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Vertex
import Mathlib.Topology.Separation.Connected
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.LocalFrontier

/-!
# The Schwarz--Christoffel theorem for bounded polygonal Jordan domains

Let `U` be a bounded, simply connected domain whose frontier is a Jordan curve, and which is
polygonal: near each boundary point that is not one of the finitely many vertices `v i` it
coincides with an open half-plane, and near `v i` with the open sector of opening `(e i + 1) * π`
at `v i`, where `e i ∈ (-1, 1)`.  Then there are distinct real prevertices `a i` and complex
constants `A ≠ 0` and `B` such that `A * F + B` maps the upper half-plane bijectively onto `U`,
where `F` is the normalized Schwarz--Christoffel primitive for `a` and `e`, and sends each
prevertex to its vertex: `A * vertex i + B = v i`, where `vertex i` is the limit of `F` at `a i`.

The map is the Riemann map of `U` transported to the upper half-plane with infinity sent to a
boundary point `p` that is not a vertex.  Such a `p` exists because a Jordan curve is infinite.
Carathéodory's theorem makes this map a continuous injection of the closed upper half-plane that
tends to `p` at infinity; the prevertices are the real preimages of the vertices.  These are the
global conditions under which
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain` identifies the map
with an affine image of the Schwarz--Christoffel primitive.

## Main result

* `TauCeti.exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier` --
  a bounded polygonal Jordan domain is the image of the upper half-plane under an affine image of
  a Schwarz--Christoffel primitive, with the prevertices sent to the vertices.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

/-- **The Schwarz--Christoffel theorem for a bounded polygonal Jordan domain.**  Let `U` be a
bounded, simply connected open set whose frontier is a Jordan curve.  Suppose that `U` coincides
near each frontier point other than the distinct vertices `v i` with an open half-plane, and near
the vertex `v i` with the open sector of opening `(e i + 1) * π` at `v i`, where `e i ∈ (-1, 1)`.
Then there are distinct real prevertices `a i` and constants `A ≠ 0` and `B` such that
`z ↦ A * F z + B` maps the upper half-plane bijectively onto `U`, where `F` is the normalized
Schwarz--Christoffel primitive for the prevertices `a` and the turning exponents `e`, and such that
the Schwarz--Christoffel vertex at `a i`, the limit of `F` at `a i`, is sent to `v i`. -/
theorem exists_bijOn_const_mul_schwarzChristoffelPrimitive_add_of_isJordanCurve_frontier
    {ι : Type*} [Fintype ι] (e : ι → ℝ) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane)
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsSimplyConnected U) (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {v : ι → ℂ} (hv : Injective v)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2)) :
    ∃ a : ι → ℝ, Injective a ∧ ∃ A : ℂ, A ≠ 0 ∧ ∃ B : ℂ,
      BijOn (fun z => A * schwarzChristoffelPrimitive a e z₀ z + B) upperHalfPlaneSet U ∧
      ∀ i, A * schwarzChristoffelVertex a e z₀ i + B = v i := by
  -- a boundary point `p` which is not a vertex: the frontier is infinite, the vertices finite
  obtain ⟨p, hpU, hpv⟩ : (frontier U \ range v).Nonempty :=
    ((hUJ.isConnected.isPreconnected.infinite_of_nontrivial
      (not_subsingleton_iff.mp hUJ.not_subsingleton)).sdiff (finite_range v)).nonempty
  obtain ⟨f, hfc, hfd, hfH, hfcl, hfR, hfp⟩ :=
    exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier hUo hUc hUb hUJ hpU
  -- every vertex lies on the frontier, so it has a real preimage under `f`
  have hvU (i : ι) : v i ∈ frontier U \ {p} := by
    obtain ⟨ρ, hρ, b, hb, hU⟩ := hcorner i
    have he₁ := he i
    refine ⟨mem_frontier_of_forall_mem_iff_abs_arg_lt hUo hρ hb ?_ ?_ hU, fun h => hpv ⟨i, h⟩⟩
    · nlinarith [Real.pi_pos, he₁.1]
    · nlinarith [Real.pi_pos, he₁.2]
  choose x hx hfx using fun i => hfR.surjOn (hvU i)
  let a : ι → ℝ := fun i => (x i).re
  have hax (i : ι) : ((a i : ℝ) : ℂ) = x i :=
    Complex.ext (by simp [a]) (by simpa [a] using (hx i).symm)
  have hfa (i : ι) : f (a i) = v i := by rw [hax, hfx]
  have ha : Injective a := fun i j h => hv (by rw [← hfa i, ← hfa j, h])
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hform := eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain a e ha he z₀
    hfd hfc hfcl.injOn hfH.image_eq hfa hfp (fun ⟨z, hz, hzp⟩ => (hfcl.mapsTo hz).2 hzp)
    hside hcorner
  refine ⟨a, ha, _, div_ne_zero ?_ (schwarzChristoffelIntegrand_ne_zero a e z₀.im_pos), _,
    hfH.congr hform, fun i => ?_⟩
  · exact deriv_ne_zero_of_injOn hfd isOpen_upperHalfPlaneSet hfH.injOn z₀.im_pos
  -- both sides are limits at the prevertex `a i` from the upper half-plane
  have := Real.nhdsWithin_upperHalfPlaneSet_neBot (a i)
  have hsum : -1 < ∑ l with a l = a i, e l := by
    rw [Finset.sum_eq_single_of_mem i (by simp) fun l hl hli =>
      absurd (ha (Finset.mem_filter.mp hl).2) hli]
    exact (he i).1
  refine tendsto_nhds_unique
    ((((tendsto_schwarzChristoffelPrimitive a e z₀ i hsum).const_mul _).add_const _)) ?_
  rw [← hfa i]
  exact ((hfc _ (by simp)).tendsto.mono_left (nhdsWithin_mono _ hH0)).congr'
    (eventually_nhdsWithin_of_forall hform)

end TauCeti

end
