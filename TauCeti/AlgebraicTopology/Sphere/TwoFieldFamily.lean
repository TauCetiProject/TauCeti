/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.TangentCircle
public import TauCeti.Topology.Homotopy.Cube.Sphere
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.Sphere.Suspension

/-!
# The family of two-spheres of a sphere carrying two orthonormal tangent fields

Let `Sⁿ` be the unit sphere of a real inner product space `E`, and let `u`, `v` be two tangent
vector fields on it which are orthonormal at every point: `x`, `u x` and `v x` are orthonormal for
every `x ∈ Sⁿ`. On the spheres `S^{4k-1}` the quaternionic fields `x <• i` and `x <• j` are such a
pair (`TauCeti.orthonormal_vecCons_quaternionFrame`).

Over each `x ∈ Sⁿ` lies the equator `Σₓ` of points `q ∈ Sⁿ` orthogonal to `u x` and to `v x`, a
sphere of dimension `n - 2` through `x`. These equators form the space
`Σ = {(x, q) | q ∈ Σₓ}` (`TauCeti.twoFieldEquators`), a closed subspace of `Sⁿ × Sⁿ`, compact
when `E` is finite-dimensional. For `(x, q) ∈ Σ`, Barraud–Damian–Humilière–Oancea (Example 6.20)
sweep a two-sphere through `x`: first the circle through `x` and `q` tangent to `v x`,

`s ↦ w(s) = tangentCircle x (v x) q (2π s)`,

which stays in the equator orthogonal to `u x` (`TauCeti.twoFieldInnerLoop`); then, through each
point `w(s)`, the circle through `x` tangent to `u x`,

`(t, s) ↦ tangentCircle x (u x) (w(s)) (2π t)`.

The boundary of the square goes to `x`, so the square descends along the collapse
`I² → S²` (`TauCeti.sphereCollapse`) to a map `S² → Sⁿ` sending the north pole to `x`. This
depends continuously on `(x, q)` and gives the family
(`TauCeti.twoFieldSphereFamily`)

`σ : Σ → Map(S², Sⁿ)`,

which lies over `Sⁿ`: evaluation at the north pole sends `σ (x, q)` to `x`
(`TauCeti.mappingSpaceEval_comp_twoFieldSphereFamily`). This is the commutative square over
`Sⁿ` required of a fibred family of two-spheres in the source's Definition 6.14, for the family
of their Example 6.20; the nonvanishing of the class of a fibre, the other condition of that
definition, is not addressed here. On the square, `σ (x, q)` is the generalized loop
`tangentCircleGenLoop` of the inner circle (`TauCeti.twoFieldSphereFamily_sphereCollapse`), so
the fibre over `x` is read in the same terms as the tangent-circle loops of
`TauCeti.AlgebraicTopology.Sphere.TangentCircle`. The point `x` itself lies on its equator, and
its sphere is constant (`TauCeti.twoFieldSphereFamily_self`).

## Main declarations

* `TauCeti.twoFieldEquators u v`: the space `Σ` of pairs `(x, q)` with `q ⊥ u x, v x`.
* `TauCeti.twoFieldInnerLoop`: the circle through `x` and `q` tangent to `v x`, as a loop in the
  equator orthogonal to `u x`.
* `TauCeti.twoFieldSphereFamily`: the family `σ : Σ → Map(S², Sⁿ)`.
* `TauCeti.twoFieldSphereFamily_sphereCollapse`: on the square, `σ (x, q)` is
  `tangentCircleGenLoop` of the inner loop.
* `TauCeti.mappingSpaceEval_comp_twoFieldSphereFamily`: `σ` lies over the sphere.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14 and
  Example 6.20.
-/

public section

noncomputable section

open Metric Real
open scoped RealInnerProductSpace Topology unitInterval Topology.Homotopy

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The space `Σ` of the equators cut out by two tangent vector fields `u`, `v` of the unit sphere:
the pairs `(x, q)` of points of the sphere with `q` orthogonal to `u x` and to `v x`. When
`x`, `u x`, `v x` are orthonormal, the fibre over `x` is a sphere of codimension two through
`x`. -/
def twoFieldEquators (u v : sphere (0 : E) 1 → E) : Set (sphere (0 : E) 1 × sphere (0 : E) 1) :=
  {xq | ⟪(xq.2 : E), u xq.1⟫ = 0 ∧ ⟪(xq.2 : E), v xq.1⟫ = 0}

variable {u v : sphere (0 : E) 1 → E}

@[simp]
theorem mem_twoFieldEquators {xq : sphere (0 : E) 1 × sphere (0 : E) 1} :
    xq ∈ twoFieldEquators u v ↔ ⟪(xq.2 : E), u xq.1⟫ = 0 ∧ ⟪(xq.2 : E), v xq.1⟫ = 0 :=
  Iff.rfl

theorem isClosed_twoFieldEquators (hu : Continuous u) (hv : Continuous v) :
    IsClosed (twoFieldEquators u v) :=
  (isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) continuous_const)

/-- Over a finite-dimensional space, the space of equators is compact. -/
theorem isCompact_twoFieldEquators [FiniteDimensional ℝ E] (hu : Continuous u)
    (hv : Continuous v) : IsCompact (twoFieldEquators u v) :=
  (isClosed_twoFieldEquators hu hv).isCompact

variable (h : ∀ x : sphere (0 : E) 1, Orthonormal ℝ ![(x : E), u x, v x])
include h

/-- A point of the sphere lies on its own equator. -/
theorem mk_self_mem_twoFieldEquators (x : sphere (0 : E) 1) : (x, x) ∈ twoFieldEquators u v :=
  ⟨(h x).inner_eq_zero (by decide : (0 : Fin 3) ≠ 1),
    (h x).inner_eq_zero (by decide : (0 : Fin 3) ≠ 2)⟩

/-- A point `x` of the sphere lies on the equator orthogonal to `u x`. -/
theorem mem_sphereEquator_self_of_orthonormal (x : sphere (0 : E) 1) :
    x ∈ sphereEquator (u x) :=
  mem_sphereEquator.2 ((h x).inner_eq_zero (by decide : (0 : Fin 3) ≠ 1))

/-- The circle through `x` and `q` tangent to `v x` lies on the unit sphere. -/
private theorem norm_tangentCircle_inner (xq : twoFieldEquators u v) (θ : ℝ) :
    ‖tangentCircle (xq.1.1 : E) (v xq.1.1) (xq.1.2 : E) θ‖ = 1 :=
  norm_tangentCircle (norm_eq_of_mem_sphere xq.1.1) ((h xq.1.1).norm_eq_one 2)
    ((h xq.1.1).inner_eq_zero (by decide : (0 : Fin 3) ≠ 2)) (norm_eq_of_mem_sphere xq.1.2)
    xq.2.2 θ

/-- The circle through `x` and `q` tangent to `v x` is orthogonal to `u x`. -/
private theorem inner_tangentCircle_inner (xq : twoFieldEquators u v) (θ : ℝ) :
    ⟪tangentCircle (xq.1.1 : E) (v xq.1.1) (xq.1.2 : E) θ, u xq.1.1⟫ = 0 :=
  inner_tangentCircle_eq_zero ((h xq.1.1).inner_eq_zero (by decide : (0 : Fin 3) ≠ 1))
    ((h xq.1.1).inner_eq_zero (by decide : (2 : Fin 3) ≠ 1)) xq.2.1 θ

/-- The **inner circle** of the two-sphere of `(x, q)`: the circle through `x` and `q` tangent to
`v x`, `s ↦ tangentCircle x (v x) q (2π s)`, as a loop at `x` in the equator of the sphere
orthogonal to `u x`. -/
def twoFieldInnerLoop (xq : twoFieldEquators u v) :
    Ω^ (Fin 1) (sphereEquator (u xq.1.1))
      ⟨xq.1.1, mem_sphereEquator_self_of_orthonormal h xq.1.1⟩ where
  val :=
    { toFun z := ⟨⟨tangentCircle (xq.1.1 : E) (v xq.1.1) (xq.1.2 : E) (2 * π * z 0),
          mem_sphere_zero_iff_norm.2 (norm_tangentCircle_inner h xq _)⟩,
        mem_sphereEquator.2 (inner_tangentCircle_inner h xq _)⟩
      continuous_toFun := by fun_prop }
  property z hz := by
    refine Subtype.ext (Subtype.ext ?_)
    rcases Cube.boundary_fin_one_iff.1 hz with hz | hz <;> simp [hz]

@[simp]
theorem coe_twoFieldInnerLoop_apply (xq : twoFieldEquators u v) (z : I^(Fin 1)) :
    ((twoFieldInnerLoop h xq z : sphere (0 : E) 1) : E) =
      tangentCircle (xq.1.1 : E) (v xq.1.1) (xq.1.2 : E) (2 * π * z 0) :=
  (rfl)

/-- The two-sphere of `(x, q)` lies on the unit sphere. -/
private theorem norm_tangentCircle_outer (xq : twoFieldEquators u v) (s t : ℝ) :
    ‖tangentCircle (xq.1.1 : E) (u xq.1.1)
      (tangentCircle (xq.1.1 : E) (v xq.1.1) (xq.1.2 : E) s) t‖ = 1 :=
  norm_tangentCircle (norm_eq_of_mem_sphere xq.1.1) ((h xq.1.1).norm_eq_one 1)
    ((h xq.1.1).inner_eq_zero (by decide : (0 : Fin 3) ≠ 1)) (norm_tangentCircle_inner h xq s)
    (inner_tangentCircle_inner h xq s) t

variable (hu : Continuous u) (hv : Continuous v)
include hu hv

/-- The two-spheres on the square: `((x, q), y) ↦ tangentCircle x (u x) (w y₁) (2π y₀)`, where
`w` is the inner circle of `(x, q)`. -/
private def twoFieldSquare : C(twoFieldEquators u v × I^(Fin 2), sphere (0 : E) 1) where
  toFun a := ⟨tangentCircle (a.1.1.1 : E) (u a.1.1.1)
      (tangentCircle (a.1.1.1 : E) (v a.1.1.1) (a.1.1.2 : E) (2 * π * a.2 1)) (2 * π * a.2 0),
    mem_sphere_zero_iff_norm.2 (norm_tangentCircle_outer h a.1 _ _)⟩
  continuous_toFun := by fun_prop

private theorem coe_twoFieldSquare_apply (a : twoFieldEquators u v × I^(Fin 2)) :
    (twoFieldSquare h hu hv a : E) = tangentCircle (a.1.1.1 : E) (u a.1.1.1)
      (tangentCircle (a.1.1.1 : E) (v a.1.1.1) (a.1.1.2 : E) (2 * π * a.2 1)) (2 * π * a.2 0) :=
  (rfl)

/-- The boundary of the square goes to the base point `x`. -/
private theorem twoFieldSquare_of_mem_boundary (xq : twoFieldEquators u v) {y : I^(Fin 2)}
    (hy : y ∈ Cube.boundary (Fin 2)) : twoFieldSquare h hu hv (xq, y) = xq.1.1 := by
  apply Subtype.ext
  rw [coe_twoFieldSquare_apply]
  rcases Cube.boundary_fin_succ_iff.1 hy with hy | hy
  · rcases hy with hy | hy <;> simp [hy]
  · rcases Cube.boundary_fin_one_iff.1 hy with hy | hy <;>
      simp only [Fin.tail, Fin.succ_zero_eq_one] at hy <;> simp [hy]

private theorem factorsThrough_twoFieldSquare :
    Function.FactorsThrough (twoFieldSquare h hu hv)
      ((ContinuousMap.id (twoFieldEquators u v)).prodMap (sphereCollapse 2 Sphere2.north)) := by
  rintro ⟨xq, y⟩ ⟨xq', y'⟩ hyy
  simp only [ContinuousMap.prodMap_apply, ContinuousMap.id_apply, Prod.map, Prod.mk.injEq] at hyy
  obtain ⟨rfl, hyy⟩ := hyy
  rcases eq_or_mem_boundary_of_sphereCollapse_eq 2 Sphere2.north hyy with rfl | ⟨hy, hy'⟩
  · rfl
  · rw [twoFieldSquare_of_mem_boundary h hu hv xq hy,
      twoFieldSquare_of_mem_boundary h hu hv xq hy']

/-- **The family of two-spheres of two orthonormal tangent fields** (Barraud–Damian–Humilière–
Oancea, Example 6.20). For `(x, q)` in the space of equators, `σ (x, q) : S² → Sⁿ` sweeps, through
each point `w` of the circle through `x` and `q` tangent to `v x`, the circle through `x` and `w`
tangent to `u x`; it sends the north pole to `x`. -/
def twoFieldSphereFamily : C(twoFieldEquators u v, C(Sphere2, sphere (0 : E) 1)) :=
  ((isQuotientMap_prodMap_id_sphereCollapse 2 Sphere2.north _).lift _
    (factorsThrough_twoFieldSquare h hu hv)).curry

/-- On the square, the two-sphere of `(x, q)` is
`y ↦ tangentCircle x (u x) (tangentCircle x (v x) q (2π y₁)) (2π y₀)`. -/
theorem coe_twoFieldSphereFamily_sphereCollapse (xq : twoFieldEquators u v) (y : I^(Fin 2)) :
    (twoFieldSphereFamily h hu hv xq (sphereCollapse 2 Sphere2.north y) : E) =
      tangentCircle (xq.1.1 : E) (u xq.1.1)
        (tangentCircle (xq.1.1 : E) (v xq.1.1) (xq.1.2 : E) (2 * π * y 1)) (2 * π * y 0) :=
  congrArg Subtype.val (DFunLike.congr_fun ((isQuotientMap_prodMap_id_sphereCollapse 2
    Sphere2.north _).lift_comp _ (factorsThrough_twoFieldSquare h hu hv)) (xq, y))

/-- On the square, the two-sphere of `(x, q)` is the generalized loop of the circles through `x`
tangent to `u x` and through the points of the inner circle `twoFieldInnerLoop`. -/
theorem twoFieldSphereFamily_sphereCollapse (xq : twoFieldEquators u v) (y : I^(Fin 2)) :
    twoFieldSphereFamily h hu hv xq (sphereCollapse 2 Sphere2.north y) =
      tangentCircleGenLoop (by simpa using (h xq.1.1).norm_eq_one 1)
        (twoFieldInnerLoop h xq) y :=
  Subtype.ext (by
    rw [coe_twoFieldSphereFamily_sphereCollapse, coe_tangentCircleGenLoop_apply,
      coe_twoFieldInnerLoop_apply]
    simp only [Fin.tail, Fin.succ_zero_eq_one])

/-- The two-sphere of `(x, q)` sends the north pole to `x`. -/
@[simp]
theorem twoFieldSphereFamily_north (xq : twoFieldEquators u v) :
    twoFieldSphereFamily h hu hv xq Sphere2.north = xq.1.1 := by
  have h0 : (0 : I^(Fin 2)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  rw [← (sphereCollapse_eq_basepoint_iff 2 Sphere2.north 0).2 h0]
  exact Subtype.ext (by simp [coe_twoFieldSphereFamily_sphereCollapse])

/-- **The family of two-spheres lies over the sphere**: evaluation at the north pole sends the
two-sphere of `(x, q)` to `x`. -/
theorem mappingSpaceEval_comp_twoFieldSphereFamily :
    (mappingSpaceEval Sphere2.north).comp (twoFieldSphereFamily h hu hv) =
      ContinuousMap.fst.comp ⟨Subtype.val, continuous_subtype_val⟩ := by
  ext xq
  simp

/-- The two-sphere of the point `(x, x)` of the space of equators is constant at `x`. -/
@[simp]
theorem twoFieldSphereFamily_self (x : sphere (0 : E) 1) :
    twoFieldSphereFamily h hu hv ⟨(x, x), mk_self_mem_twoFieldEquators h x⟩ =
      ContinuousMap.const Sphere2 x := by
  ext z : 1
  obtain ⟨y, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north z
  exact Subtype.ext (by simp [coe_twoFieldSphereFamily_sphereCollapse])

end TauCeti
