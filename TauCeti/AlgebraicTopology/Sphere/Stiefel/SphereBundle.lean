/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Stiefel.SphereFamily
public import TauCeti.Topology.VectorBundle.SphereBundle.Stiefel
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# The fibered family of two-spheres of a sphere bundle

Let `E → B` be a real vector bundle whose fibres are real inner product spaces, and let
`Q = S(E)` be its unit sphere bundle (`TauCeti.sphereBundle`), a bundle of spheres `Sⁿ` over `B`
when the fibres have dimension `n + 1`. Barraud–Damian–Humilière–Oancea (Proposition 6.23, the
case of even `n`) take as parameter space over a point `q ∈ Q` the Stiefel manifold of
orthonormal two-frames of the tangent space at `q` of the sphere fibre through `q`, and put the
two-spheres of their Example 6.16 into these fibres. Together these frames form the Stiefel
bundle `Σ = V₃(E)` (`TauCeti.StiefelBundle F E 3`) of orthonormal triples `(q, u, v)` in the
fibres of `E`, which lies over `Q` by the first vector (`TauCeti.StiefelBundle.sphereProj`).

To a triple `(q, u, v)` in the fibre `E_b` the round two-sphere family of the sphere `S(E_b)`
(`TauCeti.stiefelSphereFamily`) attaches a map `S² → S(E_b)` sweeping the great two-sphere through
`q` spanned by `q`, `u` and `v`; including the sphere fibre `S(E_b)` into `Q`
(`TauCeti.sphereBundleFiberIncl`) gives the family

`σ : Σ → Map(S², Q)` (`TauCeti.stiefelBundleSphereFamily`).

It is continuous on all of `Σ`, also as the base point moves: the two-sphere of `(q, u, v)` is
the linear combination of `q`, `u`, `v` whose coefficients are the coordinates of the two-sphere
of the standard frame of `ℝ³` (`TauCeti.coe_stiefelSphereFamily_apply`), and fibrewise linear
combinations of continuous maps into a vector bundle are continuous
(`Continuous.add_totalSpace`, `Continuous.smul_totalSpace`). No continuity of the fibre metric is
needed.

The family lies over `Q`: evaluation at the north pole of `S²` is the projection `Σ → Q`
(`TauCeti.mappingSpaceEval_comp_stiefelBundleSphereFamily`). Over a unit vector `p` of the fibre
`E_b`, whose fibre in `Σ` consists of the frames of `p^⊥`
(`TauCeti.StiefelBundle.range_fiberIncl_comp_stiefelFrameIncl`), it is the based family
`σ_p : V₂(p^⊥) → Map_*(S², S(E_b))` of the sphere `S(E_b)` (`TauCeti.stiefelSphereFamilyFiber`)
followed by the inclusion `Map_*(S², S(E_b)) → Map_*(S², Q)` of based maps induced by the sphere
fibre (`TauCeti.stiefelBundleSphereFamily_fiberIncl_stiefelFrameIncl`). This is the compatibility
of the fibre of `σ` with the based loop inclusion `Ω²Sⁿ → Ω²Q` through which the source compares
the fibre class of `σ` with the class of Proposition 6.17.

## Main declarations

* `TauCeti.stiefelBundleSphereFamily`: the family `σ : V₃(E) → Map(S², S(E))`.
* `TauCeti.mappingSpaceEval_comp_stiefelBundleSphereFamily`: it lies over `S(E)`.
* `TauCeti.stiefelBundleSphereFamily_fiberIncl`: on the frames of one fibre it is the family of
  two-spheres of the sphere of that fibre.
* `TauCeti.stiefelBundleSphereFamily_fiberIncl_stiefelFrameIncl`: over a point `p` of `S(E)` it is
  the based family `σ_p` followed by the inclusion of the sphere fibre through `p`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Definition 6.14, Example 6.16
  and Proposition 6.23.
-/

public section

noncomputable section

open Bundle Metric Set

universe w

namespace TauCeti

/-! ### The family over the sphere bundle -/

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The family `σ : V₃(E) → Map(S², S(E))` of two-spheres of a sphere bundle**
(Barraud–Damian–Humilière–Oancea, Proposition 6.23). An orthonormal triple `(q, u, v)` of the
fibre `E_b` goes to the two-sphere `σ_{q,u,v}` of the sphere `S(E_b)`
(`TauCeti.stiefelSphereFamily`) through `q` spanned by `q`, `u` and `v`, included into the
sphere bundle `S(E)`. -/
def stiefelBundleSphereFamily : C(StiefelBundle F E 3, C(Sphere2, sphereBundle F E)) :=
  ContinuousMap.curry
    { toFun := fun q ↦ sphereBundleFiberIncl F E q.1.proj (stiefelSphereFamily q.1.frame q.2)
      continuous_toFun := by
        -- The two-sphere of a frame is the linear combination of the frame whose coefficients
        -- are the coordinates of the standard two-sphere.
        have hc (i : Fin 3) : Continuous fun q : StiefelBundle F E 3 × Sphere2 ↦
            (standardStiefelSphereMap q.2 : EuclideanSpace ℝ (Fin 3)) i :=
          (PiLp.continuous_apply 2 _ i).comp (continuous_subtypeVal.comp
            (standardStiefelSphereMap.continuous.comp continuous_snd))
        have hv (i : Fin 3) : Continuous fun q : StiefelBundle F E 3 × Sphere2 ↦
            TotalSpace.mk' F q.1.proj
              ((standardStiefelSphereMap q.2 : EuclideanSpace ℝ (Fin 3)) i •
                (q.1.frame : Fin 3 → E q.1.proj) i) :=
          (hc i).smul_totalSpace ((StiefelBundle.continuous_totalSpaceMk_frame i).comp
            continuous_fst)
        refine continuous_induced_rng.2
          ((((hv 0).add_totalSpace ℝ (hv 1)).add_totalSpace ℝ (hv 2)).congr fun q ↦ ?_)
        rw [Function.comp_apply, coe_sphereBundleFiberIncl_apply,
          coe_stiefelSphereFamily_apply q.1.frame q.2, Fin.sum_univ_three] }

variable {F E}

/-- The two-sphere of a frame is the two-sphere of the sphere of its fibre, included into the
sphere bundle. -/
theorem stiefelBundleSphereFamily_apply (p : StiefelBundle F E 3) (w : Sphere2) :
    stiefelBundleSphereFamily F E p w =
      sphereBundleFiberIncl F E p.proj (stiefelSphereFamily p.frame w) :=
  (rfl)

/-- **On the frames of one fibre, `σ` is the family of two-spheres of the sphere of that fibre**,
followed by the inclusion of that sphere into the sphere bundle. -/
@[simp]
theorem stiefelBundleSphereFamily_fiberIncl (b : B) (x : stiefel (E b) 3) :
    stiefelBundleSphereFamily F E (StiefelBundle.fiberIncl F E 3 b x) =
      (sphereBundleFiberIncl F E b).comp (stiefelSphereFamily x) := by
  rw [StiefelBundle.fiberIncl_apply]
  rfl

/-- **The family `σ` lies over the projection to the first vector**: the north pole of the
two-sphere of `(q, u, v)` goes to `q`. -/
@[simp]
theorem stiefelBundleSphereFamily_apply_north (p : StiefelBundle F E 3) :
    stiefelBundleSphereFamily F E p Sphere2.north = StiefelBundle.sphereProj F 3 0 p := by
  rw [stiefelBundleSphereFamily_apply, stiefelSphereFamily_apply_north]
  have h := StiefelBundle.sphereProj_fiberIncl (F := F) 0 p.proj p.frame
  -- `p` is the frame `p.frame` of the fibre over `p.proj`, by structure eta.
  rw [StiefelBundle.fiberIncl_apply] at h
  exact h.symm

variable (F E) in
/-- The family `σ` is a map over the sphere bundle `S(E)`, from the projection `V₃(E) → S(E)` to
the first vector to evaluation `Map(S², S(E)) → S(E)` at the north pole. -/
theorem mappingSpaceEval_comp_stiefelBundleSphereFamily :
    mappingSpaceEval Sphere2.north ∘ stiefelBundleSphereFamily F E =
      StiefelBundle.sphereProj F 3 0 :=
  funext fun p ↦ (mappingSpaceEval_apply _ _).trans (stiefelBundleSphereFamily_apply_north p)

/-- **Over a point `p` of the sphere bundle, `σ` is the based family `σ_p` of the sphere fibre
through `p`.** The frames over `p` are the frames `(p, u, v)` with `(u, v)` an orthonormal frame of
`p^⊥` in the fibre `E_b` (`TauCeti.StiefelBundle.range_fiberIncl_comp_stiefelFrameIncl`), and the
two-sphere of such a frame is the based two-sphere `σ_{p,u,v}` of the sphere `S(E_b)`
(`TauCeti.stiefelSphereFamilyFiber`), carried to a based map into `S(E)` by the inclusion of the
sphere fibre. -/
theorem stiefelBundleSphereFamily_fiberIncl_stiefelFrameIncl (b : B) (p : sphere (0 : E b) 1)
    (y : stiefel (ℝ ∙ (p : E b))ᗮ 2) :
    stiefelBundleSphereFamily F E (StiefelBundle.fiberIncl F E 3 b (stiefelFrameIncl p 2 y)) =
      (BasedMap.map (sphereBundleFiberIncl F E b) rfl (stiefelSphereFamilyFiber p y)).val := by
  refine ContinuousMap.ext fun w ↦ ?_
  rw [stiefelBundleSphereFamily_fiberIncl, ContinuousMap.comp_apply,
    stiefelSphereFamily_stiefelFrameIncl, BasedMap.map_apply]

end TauCeti
