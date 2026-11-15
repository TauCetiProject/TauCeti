/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.DoubleTangentCircle
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.MappingSpace.Sphere.Basic
public import TauCeti.Topology.Sphere.Suspension

/-!
# The fibered family of two-spheres of a sphere with two orthonormal tangent fields

Let `Sⁿ` be the unit sphere of a real inner product space `E`, carrying two pointwise orthonormal
tangent vector fields `u` and `v`: for every `p ∈ Sⁿ` the triple `(p, u p, v p)` is orthonormal.
On `S^{4k-1} ⊆ ℍᵏ` the quaternionic fields `x ↦ x <• i` and `x ↦ x <• j` are such a pair
(`TauCeti.orthonormal_vecCons_quaternionFrame`).

Over each point `p`, Barraud–Damian–Humilière–Oancea (Example 6.20) consider the equator
`Σ_p = E_{u(p)⊥, p, v(p)}` of the unit sphere of `u(p)⊥` orthogonal to `v(p)`: the unit vectors
orthogonal to both `u p` and `v p`, a sphere of dimension `n - 2` through `p`. They attach to each
`q ∈ Σ_p` the double loop

`σ_p(q)(s)(t) = tangentCircle p (u p) (tangentCircle p (v p) q (2πs)) (2πt)`

of circles tangent to `u p` through the points of the circle tangent to `v p` through `q`
(`TauCeti.tangentCircleDoubleLoop`). Letting `p` vary gives a commutative diagram over `Sⁿ`

```
Σ_p ──σ_p──→ Ω²Sⁿ = Map_*(S², Sⁿ)
 │                 │
 Σ  ───σ───→ Map(S², Sⁿ)
 │π                │ev
 Sⁿ ════════════ Sⁿ
```

which this file constructs.

* The total space `Σ` (`TauCeti.equatorBundle u v`) is the set of pairs `(p, q)` of points of the
  sphere with `q` orthogonal to `u p` and to `v p`, and `π` is the first projection. The fibre over
  `p` is the equator `Σ_p` (`TauCeti.equatorBundleFiberIncl`,
  `TauCeti.range_equatorBundleFiberIncl`), and `(p, p)` is a point of it.
* The family `σ` (`TauCeti.tangentCircleSphereFamily`) sends `(p, q)` to the double loop
  `σ_p(q)`, read as a map `S² → Sⁿ` by collapsing the boundary of the square `I²` onto the north
  pole of `S²` (`TauCeti.tangentCircleSphereFamily_apply_sphereCollapse`). Continuity in `p` as
  well as in `q` comes from the explicit formula, since the collapse times the identity of `Σ` is
  a quotient map (`TauCeti.isQuotientMap_prodMap_sphereCollapse`).
* `σ` lies over the projection, `ev ∘ σ = π`
  (`TauCeti.mappingSpaceEval_comp_tangentCircleSphereFamily`), sends `(p, p)` to the constant map
  at `p` (`TauCeti.tangentCircleSphereFamily_apply_of_snd_eq_fst`), and on the fibre over `p` it is
  the family `σ_p` of based sphere maps of `TauCeti.tangentCircleDoubleLoop`
  (`TauCeti.tangentCircleSphereFamily_equatorBundleFiberIncl`).

The fibre class `σ_{p*}[Σ_p]` generates `H_{n-2}(Ω²Sⁿ; ℤ)` for `n ≥ 4`
(`TauCeti.isIso_singularHomologyFunctor_map_tangentCircleDoubleLoop`, the source's
Proposition 6.21). Together with the diagram above this is what makes these data a fibered family
of two-spheres in the sense of the source's Definition 6.14 for `S^{4k-1}`, `k ≥ 2`; the smooth
bundle structure of `π` is not part of this file.

## Main declarations

* `TauCeti.equatorBundle u v`: the total space `Σ`, with `TauCeti.mem_equatorBundle`.
* `TauCeti.equatorBundleFiberIncl`: the inclusion of the equator `Σ_p` as the fibre over `p`.
* `TauCeti.tangentCircleSphereFamily`: the family `σ : Σ → Map(S², Sⁿ)`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14, Example 6.20 and
  Proposition 6.21.
-/

public section

noncomputable section

open Metric Real Set Topology
open scoped unitInterval RealInnerProductSpace

namespace TauCeti

/-! ### The total space -/

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (u v : sphere (0 : E) 1 → E) in
/-- **The total space `Σ` of the family of equators**: the pairs `(p, q)` of points of the unit
sphere with `q` orthogonal to `u p` and to `v p`. When `(p, u p, v p)` is orthonormal, the fibre
over `p` is the equator `E_{u(p)⊥, p, v(p)}` of the unit sphere of `u(p)⊥` orthogonal to `v(p)`
(`TauCeti.range_equatorBundleFiberIncl`). -/
def equatorBundle : Set (sphere (0 : E) 1 × sphere (0 : E) 1) :=
  {y | ⟪(y.2 : E), u y.1⟫ = 0 ∧ ⟪(y.2 : E), v y.1⟫ = 0}

variable {u v : sphere (0 : E) 1 → E}

@[simp]
theorem mem_equatorBundle {y : sphere (0 : E) 1 × sphere (0 : E) 1} :
    y ∈ equatorBundle u v ↔ ⟪(y.2 : E), u y.1⟫ = 0 ∧ ⟪(y.2 : E), v y.1⟫ = 0 :=
  Iff.rfl

end Space

/-! ### The orthonormality hypothesis -/

section Orthonormal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : sphere (0 : E) 1 → E}
  (h : ∀ p : sphere (0 : E) 1, Orthonormal ℝ ![(p : E), u p, v p]) (p : sphere (0 : E) 1)

include h

private theorem norm_fst_eq_one : ‖u p‖ = 1 := by simpa using (h p).1 1

private theorem norm_snd_eq_one : ‖v p‖ = 1 := by simpa using (h p).1 2

private theorem inner_fst_eq_zero : ⟪(p : E), u p⟫ = 0 := by
  simpa using (h p).2 (show (0 : Fin 3) ≠ 1 by decide)

private theorem inner_snd_eq_zero : ⟪(p : E), v p⟫ = 0 := by
  simpa using (h p).2 (show (0 : Fin 3) ≠ 2 by decide)

private theorem inner_fst_snd_eq_zero : ⟪u p, v p⟫ = 0 := by
  simpa using (h p).2 (show (1 : Fin 3) ≠ 2 by decide)

end Orthonormal

/-! ### The family over the sphere -/

section Family

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : C(sphere (0 : E) 1, E)}
  (h : ∀ p : sphere (0 : E) 1, Orthonormal ℝ ![(p : E), u p, v p])

include h in
/-- The double loop `σ_p(q)` lies on the unit sphere. -/
private theorem norm_tangentCircle_tangentCircle (y : equatorBundle u v) (s t : ℝ) :
    ‖tangentCircle (y.1.1 : E) (u y.1.1)
      (tangentCircle (y.1.1 : E) (v y.1.1) (y.1.2 : E) s) t‖ = 1 := by
  have hp := norm_eq_of_mem_sphere y.1.1
  have hq := norm_eq_of_mem_sphere y.1.2
  obtain ⟨hqu, hqv⟩ := y.2
  refine norm_tangentCircle hp (norm_fst_eq_one h _) (inner_fst_eq_zero h _)
    (norm_tangentCircle hp (norm_snd_eq_one h _) (inner_snd_eq_zero h _) hq hqv s) ?_ t
  exact inner_tangentCircle_eq_zero (inner_fst_eq_zero h _)
    ((real_inner_comm _ _).trans (inner_fst_snd_eq_zero h _)) hqu s

/-- The double loops `σ_p(q)` on the square: `(p, q)` and `z ∈ I²` go to
`tangentCircle p (u p) (tangentCircle p (v p) q (2π z₀)) (2π z₁)`. -/
private def tangentCircleSquareFamily : C(equatorBundle u v × (Fin 2 → I), sphere (0 : E) 1) where
  toFun y := ⟨tangentCircle (y.1.1.1 : E) (u y.1.1.1)
      (tangentCircle (y.1.1.1 : E) (v y.1.1.1) (y.1.1.2 : E) (2 * π * y.2 0)) (2 * π * y.2 1),
    mem_sphere_zero_iff_norm.2 (norm_tangentCircle_tangentCircle h _ _ _)⟩
  continuous_toFun := continuous_induced_rng.2 (by fun_prop)

private theorem coe_tangentCircleSquareFamily_apply (y : equatorBundle u v × (Fin 2 → I)) :
    (tangentCircleSquareFamily h y : E) = tangentCircle (y.1.1.1 : E) (u y.1.1.1)
      (tangentCircle (y.1.1.1 : E) (v y.1.1.1) (y.1.1.2 : E) (2 * π * y.2 0)) (2 * π * y.2 1) :=
  (rfl)

/-- On the boundary of the square the double loops are at their base point `p`. -/
private theorem tangentCircleSquareFamily_of_mem_boundary (y : equatorBundle u v)
    {z : Fin 2 → I} (hz : z ∈ Cube.boundary (Fin 2)) :
    tangentCircleSquareFamily h (y, z) = y.1.1 := by
  obtain ⟨i, hi⟩ := hz
  refine Subtype.ext ?_
  rw [coe_tangentCircleSquareFamily_apply]
  fin_cases i <;> rcases hi with hi | hi <;> simp_all

private theorem factorsThrough_tangentCircleSquareFamily :
    Function.FactorsThrough (tangentCircleSquareFamily h)
      ((ContinuousMap.id (equatorBundle u v)).prodMap (sphereCollapse 2 Sphere2.north)) := by
  rintro ⟨y, z⟩ ⟨y', z'⟩ hyz
  simp only [ContinuousMap.prodMap_apply, ContinuousMap.id_apply, Prod.map_apply,
    Prod.mk.injEq] at hyz
  obtain ⟨rfl, hzz⟩ := hyz
  rcases eq_or_mem_boundary_of_sphereCollapse_eq 2 Sphere2.north hzz with rfl | ⟨hz, hz'⟩
  · rfl
  · rw [tangentCircleSquareFamily_of_mem_boundary h y hz,
      tangentCircleSquareFamily_of_mem_boundary h y hz']

/-- **The family `σ : Σ → Map(S², Sⁿ)` of two-spheres** of Barraud–Damian–Humilière–Oancea,
Example 6.20: a point `(p, q)` of the family of equators goes to the double loop `σ_p(q)` of
circles tangent to `u p` through the points of the circle tangent to `v p` through `q`, read as a
map from `S²` by collapsing the boundary of the square onto the north pole
(`TauCeti.tangentCircleSphereFamily_apply_sphereCollapse`). -/
def tangentCircleSphereFamily : C(equatorBundle u v, C(Sphere2, sphere (0 : E) 1)) :=
  ContinuousMap.curry ((isQuotientMap_prodMap_sphereCollapse 2 Sphere2.north _).lift
    (tangentCircleSquareFamily h) (factorsThrough_tangentCircleSquareFamily h))

/-- On the square `I²`, collapsed onto `S²` by `TauCeti.sphereCollapse`, the sphere of `(p, q)` is
the double loop `σ_p(q)`, the first coordinate being the loop parameter of the loop of loops. -/
@[simp]
theorem coe_tangentCircleSphereFamily_apply_sphereCollapse (y : equatorBundle u v)
    (z : Fin 2 → I) :
    (tangentCircleSphereFamily h y (sphereCollapse 2 Sphere2.north z) : E) =
      tangentCircle (y.1.1 : E) (u y.1.1)
        (tangentCircle (y.1.1 : E) (v y.1.1) (y.1.2 : E) (2 * π * z 0)) (2 * π * z 1) :=
  congrArg Subtype.val (DFunLike.congr_fun ((isQuotientMap_prodMap_sphereCollapse 2 Sphere2.north
    _).lift_comp (tangentCircleSquareFamily h) (factorsThrough_tangentCircleSquareFamily h))
    (y, z))

/-- **The family `σ` lies over the projection**: the north pole of the sphere of `(p, q)` goes to
`p`. -/
@[simp]
theorem tangentCircleSphereFamily_apply_north (y : equatorBundle u v) :
    tangentCircleSphereFamily h y Sphere2.north = y.1.1 := by
  have hz : (0 : Fin 2 → I) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  rw [← (sphereCollapse_eq_basepoint_iff 2 Sphere2.north 0).2 hz]
  refine Subtype.ext ?_
  rw [coe_tangentCircleSphereFamily_apply_sphereCollapse]
  simp

/-- The family `σ` is a map over `Sⁿ`, from the projection `Σ → Sⁿ` to evaluation
`Map(S², Sⁿ) → Sⁿ` at the north pole. -/
theorem mappingSpaceEval_comp_tangentCircleSphereFamily :
    mappingSpaceEval Sphere2.north ∘ tangentCircleSphereFamily h = fun y ↦ y.1.1 :=
  funext fun y ↦ (mappingSpaceEval_apply _ _).trans (tangentCircleSphereFamily_apply_north h y)

/-- **The base point of each fibre goes to a constant sphere**: `σ_p(p)` is the constant map at
`p`. -/
theorem tangentCircleSphereFamily_apply_of_snd_eq_fst {y : equatorBundle u v}
    (hy : y.1.2 = y.1.1) : tangentCircleSphereFamily h y = ContinuousMap.const Sphere2 y.1.1 := by
  ext w
  obtain ⟨z, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north w
  rw [coe_tangentCircleSphereFamily_apply_sphereCollapse, hy]
  simp

end Family

/-! ### The fibres -/

section Fiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : sphere (0 : E) 1 → E}
  (h : ∀ p : sphere (0 : E) 1, Orthonormal ℝ ![(p : E), u p, v p]) (p : sphere (0 : E) 1)

/-- The tangent vector `v p`, as a vector of the hyperplane `u(p)⊥`. -/
def equatorBundleNormal : (ℝ ∙ u p)ᗮ :=
  ⟨v p, Submodule.mem_orthogonal_singleton_iff_inner_right.2 (inner_fst_snd_eq_zero h p)⟩

@[simp]
theorem coe_equatorBundleNormal : (equatorBundleNormal h p : E) = v p :=
  (rfl)

theorem norm_equatorBundleNormal : ‖equatorBundleNormal h p‖ = 1 := by
  rw [← Submodule.norm_coe, coe_equatorBundleNormal, norm_snd_eq_one h p]

/-- The point `p`, as a point of the equator `Σ_p = E_{u(p)⊥, p, v(p)}` of the unit sphere of
`u(p)⊥` orthogonal to `v(p)`: the base point of the double loops over `p`. -/
def equatorBundleBasepoint : sphereEquator (equatorBundleNormal h p) :=
  ⟨⟨⟨p, Submodule.mem_orthogonal_singleton_iff_inner_left.2 (inner_fst_eq_zero h p)⟩,
      mem_sphere_zero_iff_norm.2 (by rw [← Submodule.norm_coe]; exact norm_eq_of_mem_sphere p)⟩,
    mem_sphereEquator.2 (by simpa using inner_snd_eq_zero h p)⟩

@[simp]
theorem coe_equatorBundleBasepoint :
    (((equatorBundleBasepoint h p : sphere (0 : (ℝ ∙ u p)ᗮ) 1) : (ℝ ∙ u p)ᗮ) : E) = p :=
  (rfl)

/-- **The inclusion of the fibre over `p`**: a point `q` of the equator `E_{u(p)⊥, p, v(p)}` goes
to `(p, q)`. Its range is the fibre over `p` (`TauCeti.range_equatorBundleFiberIncl`). -/
def equatorBundleFiberIncl : C(sphereEquator (equatorBundleNormal h p), equatorBundle u v) where
  toFun q := ⟨(p, ⟨((q : sphere (0 : (ℝ ∙ u p)ᗮ) 1) : E), by
      rw [mem_sphere_zero_iff_norm, Submodule.norm_coe]
      exact norm_eq_of_mem_sphere _⟩),
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (q : sphere (0 : (ℝ ∙ u p)ᗮ) 1).1.2,
    by simpa using mem_sphereEquator.1 q.2⟩
  continuous_toFun := by fun_prop

@[simp]
theorem equatorBundleFiberIncl_fst (q : sphereEquator (equatorBundleNormal h p)) :
    (equatorBundleFiberIncl h p q).1.1 = p :=
  (rfl)

@[simp]
theorem coe_equatorBundleFiberIncl_snd (q : sphereEquator (equatorBundleNormal h p)) :
    ((equatorBundleFiberIncl h p q).1.2 : E) = ((q : sphere (0 : (ℝ ∙ u p)ᗮ) 1) : E) :=
  (rfl)

/-- The fibre inclusion is injective. -/
theorem injective_equatorBundleFiberIncl : Function.Injective (equatorBundleFiberIncl h p) := by
  intro q q' hq
  have h₂ := congrArg (fun y : equatorBundle u v ↦ (y.1.2 : E)) hq
  simp only [coe_equatorBundleFiberIncl_snd] at h₂
  exact Subtype.ext (Subtype.ext (Subtype.ext h₂))

/-- **The fibre over `p` is the equator** `E_{u(p)⊥, p, v(p)}`. -/
theorem range_equatorBundleFiberIncl :
    range (equatorBundleFiberIncl h p) = {y | y.1.1 = p} := by
  ext ⟨⟨p', q⟩, hqu, hqv⟩
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro ⟨q', hq'⟩
    rw [← hq']
    exact equatorBundleFiberIncl_fst h p q'
  · obtain rfl : p' = p := hp
    refine ⟨⟨⟨⟨q, Submodule.mem_orthogonal_singleton_iff_inner_left.2 hqu⟩,
      mem_sphere_zero_iff_norm.2 (by rw [← Submodule.norm_coe]; exact norm_eq_of_mem_sphere q)⟩,
      mem_sphereEquator.2 (by simpa using hqv)⟩, ?_⟩
    exact Subtype.ext (Prod.ext (equatorBundleFiberIncl_fst h p' _)
      (Subtype.ext (coe_equatorBundleFiberIncl_snd h p' _)))

end Fiber

section FiberFamily

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u v : C(sphere (0 : E) 1, E)}
  (h : ∀ p : sphere (0 : E) 1, Orthonormal ℝ ![(p : E), u p, v p]) (p : sphere (0 : E) 1)

/-- **On the fibre over `p`, the family `σ` is the family `σ_p` of Example 6.20**: the point
`(p, q)` goes to the based sphere map of the double loop `TauCeti.tangentCircleDoubleLoop` of `q`,
through `Map_*(S², Sⁿ) ≃ₜ Ω²Sⁿ`. -/
theorem tangentCircleSphereFamily_equatorBundleFiberIncl
    (q : sphereEquator (equatorBundleNormal h p)) :
    tangentCircleSphereFamily h (equatorBundleFiberIncl h p q) =
      ((BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2
        ⟨sphere (0 : E) 1, orthogonalSphereToEquator (u p) (equatorBundleBasepoint h p).1⟩
        Sphere2.north).symm (tangentCircleDoubleLoop
          (orthonormal_vecCons_iff.1 (orthonormal_vecCons_iff.1 (h p)).2.2).1
          (norm_equatorBundleNormal h p) (equatorBundleBasepoint h p) q)).1 := by
  set X : BasedTopologicalSpace :=
    ⟨sphere (0 : E) 1, orthogonalSphereToEquator (u p) (equatorBundleBasepoint h p).1⟩
  set D := tangentCircleDoubleLoop
    (orthonormal_vecCons_iff.1 (orthonormal_vecCons_iff.1 (h p)).2.2).1
    (norm_equatorBundleNormal h p) (equatorBundleBasepoint h p) q
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
    coe_tangentCircleSphereFamily_apply_sphereCollapse, coe_tangentCircleDoubleLoop_apply]
  simp

end FiberFamily

end TauCeti
