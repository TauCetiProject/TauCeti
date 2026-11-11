/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.StiefelDoubleLoop
public import TauCeti.Geometry.Manifold.Instances.Stiefel.Fiber
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
  (`TauCeti.coe_stiefelDoubleLoop_apply_of_linearMap`). This makes `σ` continuous in the point `p`
  as well as in the frame.
* `σ` lies over the projection, `ev ∘ σ = π` (`TauCeti.mappingSpaceEval_comp_stiefelSphereFamily`),
  and on the fibre over `p` it is `σ_p` (`TauCeti.stiefelSphereFamily_stiefelFrameIncl`).

The class `σ_{p*}[Σ_p]` in `H_{2n-3}(Ω²Sⁿ)` is nonzero for even `n` (the source's
Proposition 6.17), which is what makes these data a fibered family of two-spheres in the sense of
the source's Definition 6.14; that computation is not part of this file.

## Main declarations

* `TauCeti.coe_stiefelDoubleLoop_apply_of_linearMap`: a linear map carrying `(p, u, v)` to
  `(q, u', v')` carries `σ_{p,u,v}` to `σ_{q,u',v'}`.
* `TauCeti.stiefelSphereFamilyFiber`: the family `σ_p : V₂(p^⊥) → Map_*(S², Sⁿ)`, with
  `TauCeti.stiefelSphereFamilyFiber_apply_sphereCollapse` its values on the cube and
  `TauCeti.basedMapSphereHomeomorphIteratedLoopSpace_stiefelSphereFamilyFiber` its identification
  with the double loops.
* `TauCeti.stiefelSphereFamily`: the family `σ : V₃(E) → Map(S², Sⁿ)`, with
  `TauCeti.stiefelSphereFamily_apply_north`, `TauCeti.mappingSpaceEval_comp_stiefelSphereFamily`
  and `TauCeti.stiefelSphereFamily_stiefelFrameIncl`.

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

section Equivariance

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : E →ₗ[ℝ] F)
  {p : sphere (0 : E) 1} {q : sphere (0 : F) 1}

private theorem coe_sphereMeridian_of_linearMap (hq : (q : F) = L p)
    {w : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1} {w' : sphere (0 : (ℝ ∙ (q : F))ᗮ) 1}
    (hw : ((w' : (ℝ ∙ (q : F))ᗮ) : F) = L ((w : (ℝ ∙ (p : E))ᗮ) : E)) (t : I) :
    (sphereMeridian q w' t : F) = L (sphereMeridian p w t) := by
  simp [hq, hw]

private theorem coe_meridianLoop_of_linearMap (hq : (q : F) = L p)
    {x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : (ℝ ∙ (p : E))ᗮ) 1}
    {x' : sphere (0 : (ℝ ∙ (q : F))ᗮ) 1 × sphere (0 : (ℝ ∙ (q : F))ᗮ) 1}
    (h₁ : ((x'.1 : (ℝ ∙ (q : F))ᗮ) : F) = L ((x.1 : (ℝ ∙ (p : E))ᗮ) : E))
    (h₂ : ((x'.2 : (ℝ ∙ (q : F))ᗮ) : F) = L ((x.2 : (ℝ ∙ (p : E))ᗮ) : E)) (t : I) :
    (meridianLoop q x' t : F) = L (meridianLoop p x t) := by
  rw [meridianLoop_def, meridianLoop_def, Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact coe_sphereMeridian_of_linearMap L hq h₂ _
  · rw [Path.symm_apply, Path.symm_apply]
    exact coe_sphereMeridian_of_linearMap L hq h₁ _

/-- **The double loops are equivariant under linear maps.** If a linear map `L : E → F` carries
the point `p` and the frame `(u, v)` of `p^⊥` to the point `q` and the frame `(u', v')` of `q^⊥`,
then it carries the double loop `σ_{p,u,v}` to `σ_{q,u',v'}`. The meridians and rotations that
the double loops are built from are linear combinations of `p`, `u` and `v` whose coefficients only
depend on the times. -/
theorem coe_stiefelDoubleLoop_apply_of_linearMap (hq : (q : F) = L p)
    {x : stiefel (ℝ ∙ (p : E))ᗮ 2} {y : stiefel (ℝ ∙ (q : F))ᗮ 2}
    (hy : ∀ i, ((y : Fin 2 → (ℝ ∙ (q : F))ᗮ) i : F) = L ((x : Fin 2 → (ℝ ∙ (p : E))ᗮ) i))
    (s t : I) :
    (stiefelDoubleLoop q y s t : F) = L (stiefelDoubleLoop p x s t) := by
  have h₀ : ((stiefelProj _ 2 0 y : (ℝ ∙ (q : F))ᗮ) : F) =
      L ((stiefelProj _ 2 0 x : (ℝ ∙ (p : E))ᗮ) : E) := by simpa using hy 0
  have hcontr (s' : I) : (meridianContraction q (stiefelProj _ 2 0 y) s' t : F) =
      L (meridianContraction p (stiefelProj _ 2 0 x) s' t) := by
    rw [meridianContraction_apply, meridianContraction_apply]
    -- `Path.Homotopy.reflTransSymm γ` evaluates `γ` at `reflTransSymmAux`.
    exact coe_sphereMeridian_of_linearMap L hq h₀ _
  rw [stiefelDoubleLoop_def, stiefelDoubleLoop_def, Path.trans_apply, Path.trans_apply]
  split_ifs
  · rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · exact hcontr _
    · rw [rotatingMeridianLoop_apply, rotatingMeridianLoop_apply]
      refine coe_meridianLoop_of_linearMap L hq ?_ ?_ _
      · simpa using hy 0
      · simp [hy]
  · rw [Path.symm_apply, Path.symm_apply]
    exact hcontr _

end Equivariance

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
theorem stiefelSphereFamilyFiber_apply_sphereCollapse (x : stiefel (ℝ ∙ (p : E))ᗮ 2)
    (z : Fin 2 → I) :
    (stiefelSphereFamilyFiber p x).1 (sphereCollapse 2 Sphere2.north z) =
      stiefelDoubleLoop p x (z 0) (z 1) := by
  have h := iteratedLoopSpaceHomeomorph_basedMapSphereHomeomorphIteratedLoopSpace 2
    ⟨sphere (0 : E) 1, p⟩ Sphere2.north (stiefelSphereFamilyFiber p x)
  rw [basedMapSphereHomeomorphIteratedLoopSpace_stiefelSphereFamilyFiber] at h
  rw [← basedMapSphereHomeomorph_apply, ← h, iteratedLoopSpaceHomeomorph_two_apply]

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

/-- The linear map `ℝ³ → E` sending the standard basis to an orthonormal triple `x`. -/
private def frameMap (x : stiefel E 3) : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] E :=
  (Fintype.linearCombination ℝ (x : Fin 3 → E)).comp
    (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap

private theorem frameMap_apply (x : stiefel E 3) (c : EuclideanSpace ℝ (Fin 3)) :
    frameMap x c = ∑ i, c i • (x : Fin 3 → E) i :=
  (rfl)

private theorem frameMap_toLp (x : stiefel E 3) (a b c : ℝ) :
    frameMap x !₂[a, b, c] =
      a • (x : Fin 3 → E) 0 + b • (x : Fin 3 → E) 1 + c • (x : Fin 3 → E) 2 := by
  simp [frameMap_apply, Fin.sum_univ_three]

/-- `frameMap x` is an isometry, since it sends the standard basis to the orthonormal family `x`. -/
private theorem norm_frameMap (x : stiefel E 3) (c : EuclideanSpace ℝ (Fin 3)) :
    ‖frameMap x c‖ = ‖c‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, frameMap_apply,
    (mem_stiefel_iff.1 x.2).inner_sum, PiLp.inner_apply]
  simp [pow_two]

private theorem continuous_frameMap :
    Continuous fun q : stiefel E 3 × EuclideanSpace ℝ (Fin 3) => frameMap q.1 q.2 := by
  have hc (i : Fin 3) : Continuous fun q : stiefel E 3 × EuclideanSpace ℝ (Fin 3) => q.2 i :=
    (PiLp.continuous_apply 2 _ i).comp continuous_snd
  have hx (i : Fin 3) : Continuous fun q : stiefel E 3 × EuclideanSpace ℝ (Fin 3) =>
      (q.1 : Fin 3 → E) i :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  simp only [frameMap_apply, Fin.sum_univ_three]
  exact (((hc 0).smul (hx 0)).add ((hc 1).smul (hx 1))).add ((hc 2).smul (hx 2))

/-- **The family `σ : V₃(E) → Map(S², Sⁿ)` of two-spheres of the sphere**, sending an
orthonormal triple `(p, u, v)` to the double loop `σ_{p,u,v}`, read as a map from `S²` to the
round two-sphere of `Sⁿ` through `p` spanned by `p`, `u` and `v`. It is the image of the double
loop sweeping `S² ⊆ ℝ³` for the standard frame under the linear map `ℝ³ → E` sending the standard
basis to `(p, u, v)`. -/
def stiefelSphereFamily : C(stiefel E 3, C(Sphere2, sphere (0 : E) 1)) :=
  ContinuousMap.curry
    { toFun := fun q => ⟨frameMap q.1 (standardSphereMap q.2), by
        rw [mem_sphere_zero_iff_norm, norm_frameMap]
        exact norm_eq_of_mem_sphere _⟩
      continuous_toFun := continuous_induced_rng.2 <| continuous_frameMap.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp
          (standardSphereMap.continuous.comp continuous_snd))) }

/-- The two-sphere `σ_{p,u,v}` is the image of the standard double loop under the linear map
`ℝ³ → E` sending the standard basis to `(p, u, v)`. -/
private theorem coe_stiefelSphereFamily_apply (x : stiefel E 3) (y : Sphere2) :
    (stiefelSphereFamily x y : E) = frameMap x (standardSphereMap y : EuclideanSpace ℝ (Fin 3)) :=
  (rfl)

/-- **The family `σ` lies over the projection to the first vector**: the north pole of the
two-sphere `σ_{p,u,v}` goes to `p`. -/
@[simp]
theorem stiefelSphereFamily_apply_north (x : stiefel E 3) :
    stiefelSphereFamily x Sphere2.north = stiefelProj E 3 0 x := by
  have h : standardSphereMap Sphere2.north = Sphere2.north :=
    (stiefelSphereFamilyFiber Sphere2.north standardFrame).2
  refine Subtype.ext ?_
  rw [coe_stiefelSphereFamily_apply, h, Sphere2.coe_north, frameMap_toLp]
  simp

/-- The family `σ` is a map over `Sⁿ`, from the projection `V₃(E) → Sⁿ` to the first vector to
evaluation `Map(S², Sⁿ) → Sⁿ` at the north pole. -/
theorem mappingSpaceEval_comp_stiefelSphereFamily :
    mappingSpaceEval Sphere2.north ∘ stiefelSphereFamily = stiefelProj E 3 0 :=
  funext fun x => (mappingSpaceEval_apply _ _).trans (stiefelSphereFamily_apply_north x)

/-- **On the fibre over `p`, the family `σ` is the family `σ_p` of based sphere maps**: the triple
`(p, u, v)` goes to the based map of the double loop `σ_{p,u,v}`. -/
theorem stiefelSphereFamily_stiefelFrameIncl (p : sphere (0 : E) 1)
    (y : stiefel (ℝ ∙ (p : E))ᗮ 2) :
    stiefelSphereFamily (stiefelFrameIncl p y) = (stiefelSphereFamilyFiber p y).1 := by
  ext w
  obtain ⟨z, rfl⟩ := sphereCollapse_surjective 2 Sphere2.north w
  rw [stiefelSphereFamilyFiber_apply_sphereCollapse, coe_stiefelSphereFamily_apply,
    standardSphereMap, stiefelSphereFamilyFiber_apply_sphereCollapse]
  refine (coe_stiefelDoubleLoop_apply_of_linearMap _ ?_ (fun i => ?_) _ _).symm
  · rw [Sphere2.coe_north, frameMap_toLp]
    simp
  · match i with
    | 0 =>
      rw [coe_standardFrame_zero, frameMap_toLp]
      simp
    | 1 =>
      rw [coe_standardFrame_one, frameMap_toLp]
      simp

end Family

end TauCeti
