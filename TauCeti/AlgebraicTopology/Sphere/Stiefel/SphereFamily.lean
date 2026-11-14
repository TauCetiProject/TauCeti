/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Stiefel.DoubleLoop
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Geometry.Manifold.Instances.Stiefel.Fiber
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.Topology.MappingSpace.Evaluation
public import TauCeti.Topology.MappingSpace.Sphere.Basic
public import TauCeti.Topology.Sphere.Suspension

/-!
# The fibered family of two-spheres of a sphere

Let `Sⁿ` be the unit sphere of a real inner product space `E`, and let `Σ = V₃(E)`
(`TauCeti.stiefel E 3`) be the space of orthonormal triples `(p, u, v)`: points `p` of the sphere
together with an orthonormal two-frame `(u, v)` of the tangent space `p^⊥`. The fibre of the
projection `π : Σ → Sⁿ` to the first vector over `p` is the Stiefel manifold `Σ_p = V₂(p^⊥)`
(`TauCeti.stiefelFrameIncl`, `TauCeti.range_stiefelFrameIncl`), which parametrizes the double loops
`σ_{p,u,v}` of `TauCeti.stiefelDoubleLoop`. Barraud–Damian–Humilière–Oancea (Example 6.16) let the
point `p` vary and read each double loop as a map from the two-sphere to `Sⁿ`, which gives a
commutative diagram over `Sⁿ`

```
Σ_p ──σ_p──→ Ω²Sⁿ = Map_*(S², Sⁿ)
 │                 │
 Σ  ───σ───→ Map(S², Sⁿ)
 │π                │ev
 Sⁿ ════════════ Sⁿ
```

This file constructs it.

* The family of based sphere maps over `p` is `σ_p` (`TauCeti.stiefelSphereFamilyFiber`): the double
  loops `σ_{p,u,v}` transported along the homeomorphism `Map_*(S², Sⁿ) ≃ₜ Ω^[2] Sⁿ` of
  `TauCeti.BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace`, with `S²`
  (`TauCeti.Sphere2`) based at its north pole.
* The global family is `σ` (`TauCeti.stiefelSphereFamily`). All the double loops are images of a
  single one: the double loop sweeping `S² ⊆ ℝ³` at the north pole `e₀` for the frame `(e₁, e₂)` is
  carried to `σ_{p,u,v}` by the linear map `ℝ³ → E` sending the standard basis to `(p, u, v)`,
  because the meridians and rotations it is built from are linear combinations of `p`, `u` and `v`
  with coefficients that only depend on the times
  (`LinearMap.map_stiefelDoubleLoop`). This makes `σ` continuous in the point `p` as well as in
  the frame, and both families are equivariant under linear maps
  (`LinearMap.map_stiefelSphereFamily`, `LinearMap.map_stiefelSphereFamilyFiber`).
* `σ` lies over the projection, `ev ∘ σ = π` (`TauCeti.mappingSpaceEval_comp_stiefelSphereFamily`),
  and on the fibre over `p` it is `σ_p` (`TauCeti.stiefelSphereFamily_stiefelFrameIncl`).

The class `σ_{p*}[Σ_p]` in `H_{2n-3}(Ω²Sⁿ)` is nonzero for even `n` (the source's
Proposition 6.17), which is what makes these data a fibered family of two-spheres in the sense of
the source's Definition 6.14; that computation is not part of this file.

## Main declarations

* `TauCeti.stiefelSphereFamilyFiber`: the family `σ_p : V₂(p^⊥) → Map_*(S², Sⁿ)`, with
  `TauCeti.stiefelSphereFamilyFiber_apply_sphereCollapse` its values on the cube,
  `TauCeti.basedMapSphereHomeomorphIteratedLoopSpace_stiefelSphereFamilyFiber` its identification
  with the double loops and `LinearMap.map_stiefelSphereFamilyFiber` its equivariance.
* `TauCeti.stiefelSphereFamily`: the family `σ : V₃(E) → Map(S², Sⁿ)`, with
  `TauCeti.stiefelSphereFamily_apply_north`, `TauCeti.mappingSpaceEval_comp_stiefelSphereFamily`,
  `TauCeti.stiefelSphereFamily_stiefelFrameIncl` and `LinearMap.map_stiefelSphereFamily`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14 and
  Example 6.16.
-/

public section

noncomputable section

open Metric Real
open scoped unitInterval RealInnerProductSpace

namespace TauCeti

universe u

/-! ### The family over a point -/

section Fiber

open BasedTopologicalSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- **The family `σ_p` of based two-sphere maps over `p`**: the double loop `σ_{p,u,v}` of a frame
`(u, v)` of `p^⊥` (`TauCeti.stiefelDoubleLoop`), read as a map from `S²` based at its north pole to
the sphere based at `p`, through `Map_*(S², Sⁿ) ≃ₜ Ω^[2] Sⁿ`. -/
def stiefelSphereFamilyFiber :
    C(stiefel (ℝ ∙ (p : E))ᗮ 2, BasedMap Sphere2 (sphere (0 : E) 1) Sphere2.north p) where
  toFun x := (BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2
    ⟨sphere (0 : E) 1, p⟩ Sphere2.north).symm (stiefelDoubleLoop p x)
  continuous_toFun := (Homeomorph.continuous _).comp (continuous_stiefelDoubleLoop p)

/-- The based sphere map of a frame sends the north pole of `S²` to `p`. -/
@[simp]
theorem stiefelSphereFamilyFiber_apply_north (x : stiefel (ℝ ∙ (p : E))ᗮ 2) :
    (stiefelSphereFamilyFiber p x).1 Sphere2.north = p :=
  (stiefelSphereFamilyFiber p x).2

/-- Under `Map_*(S², Sⁿ) ≃ₜ Ω^[2] Sⁿ`, the family `σ_p` is the family of double loops
`σ_{p,u,v}`. -/
@[simp]
theorem basedMapSphereHomeomorphIteratedLoopSpace_stiefelSphereFamilyFiber
    (x : stiefel (ℝ ∙ (p : E))ᗮ 2) :
    BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2 ⟨sphere (0 : E) 1, p⟩
      Sphere2.north (stiefelSphereFamilyFiber p x) = stiefelDoubleLoop p x :=
  Homeomorph.apply_symm_apply _ _

/-- On the cube `I²`, collapsed onto `S²` by `TauCeti.sphereCollapse`, the based sphere map of a
frame `(u, v)` is the double loop `σ_{p,u,v}`, the first coordinate being the loop parameter of
the loop of loops. -/
@[simp]
theorem stiefelSphereFamilyFiber_apply_sphereCollapse (x : stiefel (ℝ ∙ (p : E))ᗮ 2)
    (z : Fin 2 → I) :
    (stiefelSphereFamilyFiber p x).1 (sphereCollapse 2 Sphere2.north z) =
      stiefelDoubleLoop p x (z 0) (z 1) := by
  have h := iteratedLoopSpaceHomeomorph_basedMapSphereHomeomorphIteratedLoopSpace 2
    ⟨sphere (0 : E) 1, p⟩ Sphere2.north (stiefelSphereFamilyFiber p x)
  rw [basedMapSphereHomeomorphIteratedLoopSpace_stiefelSphereFamilyFiber] at h
  rw [← basedMapSphereHomeomorph_apply, ← h, iteratedLoopSpaceHomeomorph_two_apply]

/-- **The family `σ_p` is equivariant under linear maps.** If a linear map `L : E → F` carries
the point `p` and the frame `(u, v)` of `p^⊥` to the point `q` and the frame `(u', v')` of `q^⊥`,
then it carries the based sphere map of `(u, v)` to that of `(u', v')`. -/
theorem _root_.LinearMap.map_stiefelSphereFamilyFiber {F : Type u} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (L : E →ₗ[ℝ] F) {q : sphere (0 : F) 1} (hq : (q : F) = L p)
    {x : stiefel (ℝ ∙ (p : E))ᗮ 2} {y : stiefel (ℝ ∙ (q : F))ᗮ 2}
    (hy : ∀ i, ((y : Fin 2 → (ℝ ∙ (q : F))ᗮ) i : F) = L ((x : Fin 2 → (ℝ ∙ (p : E))ᗮ) i))
    (w : Sphere2) :
    L ((stiefelSphereFamilyFiber p x).1 w) = ((stiefelSphereFamilyFiber q y).1 w : F) := by
  obtain ⟨z, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north w
  rw [stiefelSphereFamilyFiber_apply_sphereCollapse, stiefelSphereFamilyFiber_apply_sphereCollapse]
  exact L.map_stiefelDoubleLoop hq hy _ _

end Fiber

/-! ### The family over the sphere -/

section Family

/-- The standard frame `(e₁, e₂)` of the tangent space of `S² ⊆ ℝ³` at the north pole `e₀`. -/
private def standardFrame : stiefel (ℝ ∙ (Sphere2.north : EuclideanSpace ℝ (Fin 3)))ᗮ 2 :=
  ⟨![⟨!₂[0, 1, 0], Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by
      simp [Sphere2.coe_north, PiLp.inner_apply, Fin.sum_univ_three])⟩,
    ⟨!₂[0, 0, 1], Submodule.mem_orthogonal_singleton_iff_inner_right.2 (by
      simp [Sphere2.coe_north, PiLp.inner_apply, Fin.sum_univ_three])⟩],
    mem_stiefel_two_iff.2 ⟨by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three],
      by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three],
      by simp [PiLp.inner_apply, Fin.sum_univ_three]⟩⟩

private theorem coe_standardFrame_zero :
    ((standardFrame : Fin 2 → (ℝ ∙ (Sphere2.north : EuclideanSpace ℝ (Fin 3)))ᗮ) 0 :
      EuclideanSpace ℝ (Fin 3)) = !₂[0, 1, 0] :=
  (rfl)

private theorem coe_standardFrame_one :
    ((standardFrame : Fin 2 → (ℝ ∙ (Sphere2.north : EuclideanSpace ℝ (Fin 3)))ᗮ) 1 :
      EuclideanSpace ℝ (Fin 3)) = !₂[0, 0, 1] :=
  (rfl)

/-- The double loop sweeping `S² ⊆ ℝ³` at the north pole for the standard frame `(e₁, e₂)`, as a
map `S² → S²`. -/
private def standardSphereMap : C(Sphere2, Sphere2) :=
  (stiefelSphereFamilyFiber Sphere2.north standardFrame).1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The family `σ : V₃(E) → Map(S², Sⁿ)` of two-spheres of the sphere**, sending an
orthonormal triple `(p, u, v)` to the double loop `σ_{p,u,v}`, read as a map from `S²` to the
round two-sphere of `Sⁿ` through `p` spanned by `p`, `u` and `v`. It is the image of the double
loop sweeping `S² ⊆ ℝ³` for the standard frame under the linear isometry `ℝ³ → E` sending the
standard basis to `(p, u, v)` (`Orthonormal.synthesisMapIsometry`). -/
def stiefelSphereFamily : C(stiefel E 3, C(Sphere2, sphere (0 : E) 1)) :=
  ContinuousMap.curry
    { toFun := fun q =>
        (mem_stiefel_iff.1 q.1.2).synthesisMapIsometry.unitSphereMap (standardSphereMap q.2)
      continuous_toFun := continuous_induced_rng.2 <| by
        simp only [Function.comp_def, LinearIsometry.coe_unitSphereMap_apply,
          Orthonormal.synthesisMapIsometry_apply]
        refine continuous_finsetSum _ fun i _ => Continuous.smul ?_ ?_
        · exact (PiLp.continuous_apply 2 _ i).comp (continuous_subtype_val.comp
            (standardSphereMap.continuous.comp continuous_snd))
        · exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst) }

/-- The two-sphere `σ_{p,u,v}` is the image of the standard double loop under the linear map
`ℝ³ → E` sending the standard basis to `(p, u, v)`. -/
private theorem coe_stiefelSphereFamily_apply (x : stiefel E 3) (y : Sphere2) :
    (stiefelSphereFamily x y : E) =
      ∑ i, (standardSphereMap y : EuclideanSpace ℝ (Fin 3)) i • (x : Fin 3 → E) i := by
  simp [stiefelSphereFamily]

private theorem coe_stiefelSphereFamily_apply_three (x : stiefel E 3) {y : Sphere2} {a b c : ℝ}
    (hy : (standardSphereMap y : EuclideanSpace ℝ (Fin 3)) = !₂[a, b, c]) :
    (stiefelSphereFamily x y : E) =
      a • (x : Fin 3 → E) 0 + b • (x : Fin 3 → E) 1 + c • (x : Fin 3 → E) 2 := by
  simp [coe_stiefelSphereFamily_apply, hy, Fin.sum_univ_three]

/-- **The family `σ` lies over the projection to the first vector**: the north pole of the
two-sphere `σ_{p,u,v}` goes to `p`. -/
@[simp]
theorem stiefelSphereFamily_apply_north (x : stiefel E 3) :
    stiefelSphereFamily x Sphere2.north = stiefelProj E 3 0 x := by
  have h : standardSphereMap Sphere2.north = Sphere2.north :=
    stiefelSphereFamilyFiber_apply_north Sphere2.north standardFrame
  refine Subtype.ext ?_
  rw [coe_stiefelSphereFamily_apply_three x (by rw [h, Sphere2.coe_north])]
  simp

/-- The family `σ` is a map over `Sⁿ`, from the projection `V₃(E) → Sⁿ` to the first vector to
evaluation `Map(S², Sⁿ) → Sⁿ` at the north pole. -/
theorem mappingSpaceEval_comp_stiefelSphereFamily :
    mappingSpaceEval Sphere2.north ∘ stiefelSphereFamily = stiefelProj E 3 0 :=
  funext fun x => (mappingSpaceEval_apply _ _).trans (stiefelSphereFamily_apply_north x)

/-- **The family `σ` is equivariant under linear maps**: a linear map `L : E → F` carrying the
orthonormal triple `x` to the orthonormal triple `y` carries the two-sphere `σ_x` to `σ_y`. -/
theorem _root_.LinearMap.map_stiefelSphereFamily {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (L : E →ₗ[ℝ] F) {x : stiefel E 3} {y : stiefel F 3}
    (hy : ∀ i, (y : Fin 3 → F) i = L ((x : Fin 3 → E) i)) (w : Sphere2) :
    L (stiefelSphereFamily x w) = (stiefelSphereFamily y w : F) := by
  simp [coe_stiefelSphereFamily_apply, hy]

/-- **On the fibre over `p`, the family `σ` is the family `σ_p` of based sphere maps**: the triple
`(p, u, v)` goes to the based map of the double loop `σ_{p,u,v}`. -/
@[simp]
theorem stiefelSphereFamily_stiefelFrameIncl (p : sphere (0 : E) 1)
    (y : stiefel (ℝ ∙ (p : E))ᗮ 2) :
    stiefelSphereFamily (stiefelFrameIncl p 2 y) = (stiefelSphereFamilyFiber p y).1 := by
  ext w
  obtain ⟨z, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north w
  rw [stiefelSphereFamilyFiber_apply_sphereCollapse, coe_stiefelSphereFamily_apply,
    standardSphereMap, stiefelSphereFamilyFiber_apply_sphereCollapse]
  rw [← synthesisMap_apply (𝕜 := ℝ)]
  refine LinearMap.map_stiefelDoubleLoop _ ?_ (fun i => ?_) _ _
  · simp [Sphere2.coe_north, Fin.sum_univ_three]
  · fin_cases i <;> simp [coe_standardFrame_zero, coe_standardFrame_one, Fin.sum_univ_three]

end Family

end TauCeti
