/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.DoubleTangentCircle
public import TauCeti.AlgebraicTopology.Sphere.TwoFieldFamily
public import TauCeti.Topology.MappingSpace.Sphere.Basic

/-!
# The fibres of the family of two-spheres of two orthonormal tangent fields

Let `Sⁿ` be the unit sphere of a real inner product space `E`, carrying two tangent vector fields
`u` and `v` which are orthonormal at every point, and let `σ : Σ → Map(S², Sⁿ)` be the family of
two-spheres of Barraud–Damian–Humilière–Oancea, Example 6.20 (`TauCeti.twoFieldSphereFamily`),
over the space `Σ` of equators (`TauCeti.twoFieldEquators u v`).

Over `p ∈ Sⁿ`, the fibre of `Σ → Sⁿ` is the equator `Σ_p = E_{u(p)⊥, p, v(p)}` of the unit sphere
of the hyperplane `u(p)⊥` orthogonal to `v(p)`: it is the image of the fibre inclusion
`TauCeti.twoFieldFiberIncl` (`TauCeti.range_twoFieldFiberIncl`). On this fibre the family `σ` is
the family `σ_p : Σ_p → Ω²Sⁿ` of double loops of tangent circles of
`TauCeti.tangentCircleDoubleLoop`, read as based maps `S² → Sⁿ` through
`Map_*(S², Sⁿ) ≃ₜ Ω²Sⁿ` (`TauCeti.twoFieldSphereFamily_twoFieldFiberIncl`). That family carries
the generator of `H_{n-2}(Ω²Sⁿ; ℤ)` for `n ≥ 4`
(`TauCeti.isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop`, the source's
Proposition 6.21), which is the nonvanishing fibre class asked for by the source's
Definition 6.14 for `S^{4k-1}`, `k ≥ 2`.

## Main declarations

* `TauCeti.twoFieldFiberIncl`: the inclusion of the equator `Σ_p` as the fibre over `p`.
* `TauCeti.range_twoFieldFiberIncl`: its range is the fibre over `p`.
* `TauCeti.twoFieldSphereFamily_twoFieldFiberIncl`: on the fibre over `p`, `σ` is `σ_p`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14, Example 6.20 and
  Proposition 6.21.
-/

public section

noncomputable section

open Metric Real Set
open scoped unitInterval RealInnerProductSpace

namespace TauCeti

section Fiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : sphere (0 : E) 1 → E}
  {p : sphere (0 : E) 1} (hp : Orthonormal ℝ ![(p : E), u p, v p])

include hp

/-! The orthonormality relations of `p`, `u p`, `v p`, read off from `hp` by index. -/

private theorem norm_v_eq_one' : ‖v p‖ = 1 := by
  simpa using hp.norm_eq_one 2

private theorem inner_u_eq_zero' : ⟪(p : E), u p⟫ = 0 := by
  simpa using hp.inner_eq_zero (by decide : (0 : Fin 3) ≠ 1)

private theorem inner_v_eq_zero' : ⟪(p : E), v p⟫ = 0 := by
  simpa using hp.inner_eq_zero (by decide : (0 : Fin 3) ≠ 2)

private theorem inner_u_v_eq_zero' : ⟪u p, v p⟫ = 0 := by
  simpa using hp.inner_eq_zero (by decide : (1 : Fin 3) ≠ 2)

/-- The tangent vector `v p`, as a unit vector of the hyperplane `u(p)⊥`. -/
def twoFieldFiberNormal : (ℝ ∙ u p)ᗮ :=
  ⟨v p, Submodule.mem_orthogonal_singleton_iff_inner_right.2 (inner_u_v_eq_zero' hp)⟩

@[simp]
theorem coe_twoFieldFiberNormal : (twoFieldFiberNormal hp : E) = v p :=
  (rfl)

theorem norm_twoFieldFiberNormal : ‖twoFieldFiberNormal hp‖ = 1 := by
  rw [← Submodule.norm_coe, coe_twoFieldFiberNormal, norm_v_eq_one' hp]

/-- The point `p`, as a point of the equator `Σ_p = E_{u(p)⊥, p, v(p)}` of the unit sphere of
`u(p)⊥` orthogonal to `v(p)`: the base point of the double loops over `p`. -/
def twoFieldFiberBasepoint : sphereEquator (twoFieldFiberNormal hp) :=
  ⟨⟨⟨p, Submodule.mem_orthogonal_singleton_iff_inner_left.2 (inner_u_eq_zero' hp)⟩,
      mem_sphere_zero_iff_norm.2 (by rw [← Submodule.norm_coe]; exact norm_eq_of_mem_sphere p)⟩,
    mem_sphereEquator.2 (by simpa using inner_v_eq_zero' hp)⟩

@[simp]
theorem coe_twoFieldFiberBasepoint :
    (((twoFieldFiberBasepoint hp : sphere (0 : (ℝ ∙ u p)ᗮ) 1) : (ℝ ∙ u p)ᗮ) : E) = p :=
  (rfl)

/-- **The inclusion of the fibre over `p`**: a point `q` of the equator `E_{u(p)⊥, p, v(p)}` goes
to the point `(p, q)` of the space of equators. Its range is the fibre over `p`
(`TauCeti.range_twoFieldFiberIncl`). -/
def twoFieldFiberIncl : C(sphereEquator (twoFieldFiberNormal hp), twoFieldEquators u v) where
  toFun q := ⟨(p, ⟨((q : sphere (0 : (ℝ ∙ u p)ᗮ) 1) : E), by
      rw [mem_sphere_zero_iff_norm, Submodule.norm_coe]
      exact norm_eq_of_mem_sphere _⟩),
    mem_twoFieldEquators.2
      ⟨Submodule.mem_orthogonal_singleton_iff_inner_left.1 (q : sphere (0 : (ℝ ∙ u p)ᗮ) 1).1.2,
        by simpa using mem_sphereEquator.1 q.2⟩⟩
  continuous_toFun := by fun_prop

@[simp]
theorem twoFieldFiberIncl_fst (q : sphereEquator (twoFieldFiberNormal hp)) :
    (twoFieldFiberIncl hp q).1.1 = p :=
  (rfl)

@[simp]
theorem coe_twoFieldFiberIncl_snd (q : sphereEquator (twoFieldFiberNormal hp)) :
    ((twoFieldFiberIncl hp q).1.2 : E) = ((q : sphere (0 : (ℝ ∙ u p)ᗮ) 1) : E) :=
  (rfl)

/-- The fibre inclusion is injective. -/
theorem injective_twoFieldFiberIncl : Function.Injective (twoFieldFiberIncl hp) := by
  intro q q' hq
  have h₂ := congrArg (fun y : twoFieldEquators u v ↦ (y.1.2 : E)) hq
  simp only [coe_twoFieldFiberIncl_snd] at h₂
  exact Subtype.ext (Subtype.ext (Subtype.ext h₂))

/-- **The fibre over `p` is the equator** `E_{u(p)⊥, p, v(p)}`. -/
theorem range_twoFieldFiberIncl : range (twoFieldFiberIncl hp) = {y | y.1.1 = p} := by
  ext ⟨⟨p', q⟩, hq⟩
  obtain ⟨hqu, hqv⟩ := mem_twoFieldEquators.1 hq
  refine ⟨?_, fun hp' ↦ ?_⟩
  · rintro ⟨q', hq'⟩
    rw [← hq']
    exact twoFieldFiberIncl_fst hp q'
  · obtain rfl : p' = p := hp'
    refine ⟨⟨⟨⟨q, Submodule.mem_orthogonal_singleton_iff_inner_left.2 hqu⟩,
      mem_sphere_zero_iff_norm.2 (by rw [← Submodule.norm_coe]; exact norm_eq_of_mem_sphere q)⟩,
      mem_sphereEquator.2 (by simpa using hqv)⟩, ?_⟩
    exact Subtype.ext (Prod.ext (twoFieldFiberIncl_fst hp _)
      (Subtype.ext (coe_twoFieldFiberIncl_snd hp _)))

end Fiber

section FiberFamily

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : sphere (0 : E) 1 → E}
  (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![(x : E), u x, v x])
  (hu : Continuous u) (hv : Continuous v) (p : sphere (0 : E) 1)

/-- **On the fibre over `p`, the family of two-spheres is the family `σ_p` of Example 6.20**: the
point `(p, q)` goes to the based sphere map of the double loop `TauCeti.tangentCircleDoubleLoop`
of `q`, through `Map_*(S², Sⁿ) ≃ₜ Ω²Sⁿ`. -/
theorem twoFieldSphereFamily_twoFieldFiberIncl (q : sphereEquator (twoFieldFiberNormal (h p))) :
    twoFieldSphereFamily h hu hv (twoFieldFiberIncl (h p) q) =
      ((BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2
        ⟨sphere (0 : E) 1, orthogonalSphereToEquator (u p) (twoFieldFiberBasepoint (h p)).1⟩
        -- The bare index term `(h p).norm_eq_one 1` has type `‖![p, u p, v p] 1‖ = 1`, as in
        -- `TauCeti.twoFieldSphereFamily_sphereCollapse`.
        Sphere2.north).symm (tangentCircleDoubleLoop (by simpa using (h p).norm_eq_one 1)
          (norm_twoFieldFiberNormal (h p)) (twoFieldFiberBasepoint (h p)) q)).1 := by
  set X : BasedTopologicalSpace :=
    ⟨sphere (0 : E) 1, orthogonalSphereToEquator (u p) (twoFieldFiberBasepoint (h p)).1⟩
  set D := tangentCircleDoubleLoop (by simpa using (h p).norm_eq_one 1)
    (norm_twoFieldFiberNormal (h p)) (twoFieldFiberBasepoint (h p)) q
  have hD' : BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 X Sphere2.north
      ((BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 X Sphere2.north).symm
        D) = D :=
    Homeomorph.apply_symm_apply _ _
  have hD :=
    BasedTopologicalSpace.iteratedLoopSpaceHomeomorph_basedMapSphereHomeomorphIteratedLoopSpace
      2 X Sphere2.north ((BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 X
        Sphere2.north).symm D)
  rw [hD'] at hD
  ext w
  obtain ⟨z, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north w
  rw [← basedMapSphereHomeomorph_apply, ← hD,
    BasedTopologicalSpace.iteratedLoopSpaceHomeomorph_two_apply,
    coe_twoFieldSphereFamily_sphereCollapse]
  refine Eq.trans ?_ (coe_tangentCircleDoubleLoop_apply (by simpa using (h p).norm_eq_one 1)
    (norm_twoFieldFiberNormal (h p)) (twoFieldFiberBasepoint (h p)) q (z 0) (z 1)).symm
  simp

end FiberFamily

end TauCeti
