/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Stiefel.SphereFamily
public import TauCeti.Topology.VectorBundle.StiefelBundle
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# The Stiefel family of two-spheres of a sphere bundle

Let `E → B` be a real vector bundle whose fibres carry inner products, `S(E)` its unit sphere
bundle (`TauCeti.sphereBundle`), and `Σ = V₃(E)` its Stiefel bundle of orthonormal `3`-frames
(`TauCeti.StiefelBundle F E 3`). Every point `p = (b, q, u, v)` of `V₃(E)` determines a round
two-sphere `σ_{q,u,v} : S² → S(E_b)` inside the sphere fibre `S(E_b)`
(`TauCeti.stiefelSphereFamily`), sending the north pole of `S²` to `q`. Including `S(E_b)` into
`S(E)` as the fibre over `b` (`TauCeti.sphereBundleFiberIncl`) assembles these fibrewise
two-spheres into a continuous family over `S(E)`, fitting into the commutative diagram of
Barraud–Damian–Humilière–Oancea, Proposition 6.23:

```
V₂(q^⊥) ──σ_q──→ Ω²S(E) = Map_*(S², S(E))
   │                       │
 V₃(E)  ───σ───→   Map(S², S(E))
   │vecProj 0              │ev
 S(E)   ════════════════ S(E)
```

Continuity in the bundle direction requires no smoothness or continuous-norm hypothesis on the
inner product: by `LinearMap.map_stiefelSphereFamily`, the two-sphere of `p = (b, v₀, v₁, v₂)` at
`y ∈ S²` is a fixed `y`-dependent linear combination `∑ i, c_i(y) • v_i` in `E_b` with `c(y)` the
standard two-sphere map on `ℝ³`, which is jointly continuous in `(p, y)` inside `TotalSpace F E` by
fibrewise scalar multiplication and addition (`Continuous.smul_totalSpace`,
`Continuous.add_totalSpace`).

Over each unit vector `q ∈ S(E)` with `b = q.1.proj`, the vertical `2`-frame fibre `V₂(q^⊥)` embeds
into `V₃(E)` via `TauCeti.StiefelBundle.sphereFiberIncl q 2`, and the restricted based family
`TauCeti.stiefelBundleSphereFamilyFiber` factors as the model fibre family
`TauCeti.stiefelSphereFamilyFiber` on `S(E_b)` followed by the fibre inclusion `S(E_b) ↪ S(E)`
(`TauCeti.stiefelBundleSphereFamilyFiber_eq_map`). Under `Map_*(S², S(E)) ≃ₜ Ω^[2] S(E)`, it is the
pushforward along `Ω^[2] (S(E_b) ↪ S(E))` of `TauCeti.stiefelDoubleLoop`
(`TauCeti.basedMapSphereHomeomorphIteratedLoopSpace_stiefelBundleSphereFamilyFiber`).

## Main declarations

* `TauCeti.stiefelBundleSphereFamily`: the global family `V₃(E) → Map(S², S(E))`, with
  `TauCeti.stiefelBundleSphereFamily_apply_north`,
  `TauCeti.mappingSpaceEval_comp_stiefelBundleSphereFamily`, and
  `TauCeti.stiefelBundleSphereFamily_fiberIncl`.
* `TauCeti.sphereBundleFiberBasedHom`: the based fibre inclusion `(S(E_b), q) → (S(E), q)`.
* `TauCeti.stiefelBundleSphereFamilyFiber`: the vertical family
  `V₂(q^⊥) → Map_*(S², S(E))` over `q : S(E)`, with
  `TauCeti.stiefelBundleSphereFamily_sphereFiberIncl`,
  `TauCeti.stiefelBundleSphereFamilyFiber_eq_map`, and
  `TauCeti.basedMapSphereHomeomorphIteratedLoopSpace_stiefelBundleSphereFamilyFiber`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Example 6.16 and Proposition 6.23.
-/

public section

noncomputable section

open Bundle Metric
open scoped unitInterval RealInnerProductSpace

namespace TauCeti

universe w

section BundleFamily

variable {B : Type w} [TopologicalSpace B] (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- **The Stiefel family of two-spheres `V₃(E) → Map(S², S(E))` of a sphere bundle.** Every
orthonormal `3`-frame `p` over `b = p.proj` goes to the round two-sphere
`stiefelSphereFamily p.frame : S² → S(E_b)` included into `S(E)` over `b`. -/
def stiefelBundleSphereFamily : C(StiefelBundle F E 3, C(Sphere2, sphereBundle F E)) :=
  ContinuousMap.curry
    { toFun q := sphereBundleFiberIncl F E q.1.proj (stiefelSphereFamily q.1.frame q.2)
      continuous_toFun := by
        let stdTriple : stiefel (EuclideanSpace ℝ (Fin 3)) 3 :=
          ⟨EuclideanSpace.basisFun (Fin 3) ℝ,
            mem_stiefel_iff.2 (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal⟩
        have hterm (i : Fin 3) :
            Continuous fun q : StiefelBundle F E 3 × Sphere2 ↦
              TotalSpace.mk' F q.1.proj
                ((stiefelSphereFamily stdTriple q.2 : EuclideanSpace ℝ (Fin 3)) i •
                  (q.1.frame : Fin 3 → E q.1.proj) i) :=
          ((PiLp.continuous_apply 2 _ i).comp (continuous_subtype_val.comp
            ((stiefelSphereFamily stdTriple).continuous.comp continuous_snd))).smul_totalSpace
            ((StiefelBundle.continuous_totalSpaceMk_frame i).comp continuous_fst)
        have hsum :
            Continuous fun q : StiefelBundle F E 3 × Sphere2 ↦
              (sphereBundleFiberIncl F E q.1.proj (stiefelSphereFamily q.1.frame q.2) :
                TotalSpace F E) := by
          refine (((hterm 0).add_totalSpace ℝ (hterm 1)).add_totalSpace ℝ (hterm 2)).congr
            fun q ↦ ?_
          have hlin := LinearMap.map_stiefelSphereFamily
            (synthesisMap ℝ (q.1.frame : Fin 3 → E q.1.proj)) (x := stdTriple) (y := q.1.frame)
            (fun i ↦ by simp [stdTriple, EuclideanSpace.basisFun_apply]) q.2
          rw [coe_sphereBundleFiberIncl_apply, ← hlin, synthesisMap_apply, Fin.sum_univ_three]
        exact hsum.subtype_mk _ }

variable {F E}

/-- Pointwise value of `stiefelBundleSphereFamily`: the model two-sphere in `S(E_{p.proj})`
included into `S(E)`. -/
theorem stiefelBundleSphereFamily_apply (p : StiefelBundle F E 3) (y : Sphere2) :
    stiefelBundleSphereFamily F E p y =
      sphereBundleFiberIncl F E p.proj (stiefelSphereFamily p.frame y) :=
  (rfl)

/-- **The family `stiefelBundleSphereFamily` sends the north pole of `S²` to the first vector of
the frame.** -/
@[simp]
theorem stiefelBundleSphereFamily_apply_north (p : StiefelBundle F E 3) :
    stiefelBundleSphereFamily F E p Sphere2.north = StiefelBundle.vecProj 0 p := by
  rw [stiefelBundleSphereFamily_apply, stiefelSphereFamily_apply_north,
    ← StiefelBundle.vecProj_fiberIncl]
  simp

/-- **The family `stiefelBundleSphereFamily` lies over `vecProj 0 : V₃(E) → S(E)`** via evaluation
at the north pole `Map(S², S(E)) → S(E)`. -/
theorem mappingSpaceEval_comp_stiefelBundleSphereFamily :
    mappingSpaceEval Sphere2.north ∘ stiefelBundleSphereFamily F E =
      StiefelBundle.vecProj (F := F) (E := E) 0 :=
  funext fun p ↦ (mappingSpaceEval_apply _ _).trans (stiefelBundleSphereFamily_apply_north p)

/-- Every two-sphere in the family `stiefelBundleSphereFamily` projects constantly to the base point
`p.proj` of the frame. -/
theorem sphereBundleProj_comp_stiefelBundleSphereFamily (p : StiefelBundle F E 3) :
    (sphereBundleProj F E).comp (stiefelBundleSphereFamily F E p) =
      ContinuousMap.const Sphere2 p.proj := by
  ext y
  simp [stiefelBundleSphereFamily_apply]

/-- **On the fibre `V₃(E_b)` over `b : B`, `stiefelBundleSphereFamily` is the model sphere family
followed by `S(E_b) ↪ S(E)`.** -/
theorem stiefelBundleSphereFamily_fiberIncl (b : B) (v : stiefel (E b) 3) :
    stiefelBundleSphereFamily F E (StiefelBundle.fiberIncl F E 3 b v) =
      (sphereBundleFiberIncl F E b).comp (stiefelSphereFamily v) :=
  ContinuousMap.ext fun y ↦ by
    rw [StiefelBundle.fiberIncl_apply, stiefelBundleSphereFamily_apply, ContinuousMap.comp_apply]

variable (F E) in
omit [NormedSpace ℝ F] [∀ b, InnerProductSpace ℝ (E b)] [VectorBundle ℝ F E] in
/-- The fibre inclusion `(S(E_{q.1.proj}), q) → (S(E), q)` as a morphism of based topological
spaces. -/
abbrev sphereBundleFiberBasedHom (q : sphereBundle F E) :
    BasedTopologicalSpace.Hom
      ⟨sphere (0 : E q.1.proj) 1, unitSphereOfSphereBundle q⟩
      ⟨sphereBundle F E, q⟩ where
  toContinuousMap := sphereBundleFiberIncl F E q.1.proj
  map_basepoint := sphereBundleFiberIncl_unitSphereOfSphereBundle q

variable (F E) in
/-- **The vertical two-sphere family `V₂(q^⊥) → Map_*(S², S(E))` over a unit vector `q : S(E)`.** -/
def stiefelBundleSphereFamilyFiber (q : sphereBundle F E) :
    C(stiefel (ℝ ∙ q.1.2)ᗮ 2, BasedMap Sphere2 (sphereBundle F E) Sphere2.north q) :=
  BasedMap.lift ((stiefelBundleSphereFamily F E).comp (StiefelBundle.sphereFiberIncl q 2))
    fun x ↦ by simp

/-- The based sphere map associated to a vertical `2`-frame at `q` sends the north pole to `q`. -/
@[simp]
theorem stiefelBundleSphereFamilyFiber_apply_north (q : sphereBundle F E)
    (x : stiefel (ℝ ∙ q.1.2)ᗮ 2) :
    (stiefelBundleSphereFamilyFiber F E q x).1 Sphere2.north = q :=
  (stiefelBundleSphereFamilyFiber F E q x).2

/-- **Restricting `stiefelBundleSphereFamily` to the vertical fibre `V₂(q^⊥)` over `q` recovers
`stiefelBundleSphereFamilyFiber`.** -/
@[simp]
theorem stiefelBundleSphereFamily_sphereFiberIncl (q : sphereBundle F E)
    (x : stiefel (ℝ ∙ q.1.2)ᗮ 2) :
    stiefelBundleSphereFamily F E (StiefelBundle.sphereFiberIncl q 2 x) =
      (stiefelBundleSphereFamilyFiber F E q x).1 := by
  rw [stiefelBundleSphereFamilyFiber, BasedMap.lift_apply_val, ContinuousMap.comp_apply]

/-- **The vertical family over `q ∈ S(E)` is the model fibre family on `S(E_{q.1.proj})`
postcomposed with the fibre inclusion `S(E_{q.1.proj}) ↪ S(E)`.** -/
theorem stiefelBundleSphereFamilyFiber_eq_map (q : sphereBundle F E)
    (x : stiefel (ℝ ∙ q.1.2)ᗮ 2) :
    stiefelBundleSphereFamilyFiber F E q x =
      BasedMap.map (sphereBundleFiberIncl F E q.1.proj)
        (sphereBundleFiberIncl_unitSphereOfSphereBundle q)
        (stiefelSphereFamilyFiber (unitSphereOfSphereBundle q) x) := by
  refine Subtype.ext ?_
  rw [← stiefelBundleSphereFamily_sphereFiberIncl, StiefelBundle.sphereFiberIncl_apply,
    stiefelBundleSphereFamily_fiberIncl, stiefelSphereFamily_stiefelFrameIncl]
  exact ContinuousMap.ext fun y ↦
    (BasedMap.map_apply (sphereBundleFiberIncl F E q.1.proj) _ _ y).symm

/-- On the cube `I²` collapsed onto `S²`, the vertical family over `q` evaluates to the double loop
`stiefelDoubleLoop` inside `S(E_{q.1.proj})` included into `S(E)`. -/
@[simp]
theorem stiefelBundleSphereFamilyFiber_apply_sphereCollapse (q : sphereBundle F E)
    (x : stiefel (ℝ ∙ q.1.2)ᗮ 2) (z : Fin 2 → I) :
    (stiefelBundleSphereFamilyFiber F E q x).1 (sphereCollapse 2 Sphere2.north z) =
      sphereBundleFiberIncl F E q.1.proj
        (stiefelDoubleLoop (unitSphereOfSphereBundle q) x (z 0) (z 1)) := by
  rw [stiefelBundleSphereFamilyFiber_eq_map, BasedMap.map_apply,
    stiefelSphereFamilyFiber_apply_sphereCollapse]

/-- **Factorization through `Ω^[2] S(E_{q.1.proj}) → Ω^[2] S(E)`.** Under
`Map_*(S², S(E)) ≃ₜ Ω^[2] S(E)`, the vertical family over `q` sends a `2`-frame `x` of `q^⊥` to the
double loop `stiefelDoubleLoop q x` pushed forward along the `2`-fold loop map of
`S(E_{q.1.proj}) ↪ S(E)`. -/
theorem basedMapSphereHomeomorphIteratedLoopSpace_stiefelBundleSphereFamilyFiber
    (q : sphereBundle F E) (x : stiefel (ℝ ∙ q.1.2)ᗮ 2) :
    BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace 2
        ⟨sphereBundle F E, q⟩ Sphere2.north (stiefelBundleSphereFamilyFiber F E q x) =
      (sphereBundleFiberBasedHom F E q).iteratedLoopSpace 2
        (stiefelDoubleLoop (unitSphereOfSphereBundle q) x) := by
  let f := sphereBundleFiberBasedHom F E q
  let φ := stiefelSphereFamilyFiber (unitSphereOfSphereBundle q) x
  have hmap :=
    BasedTopologicalSpace.basedMapSphereHomeomorphIteratedLoopSpace_map 2 f Sphere2.north φ
  rw [stiefelBundleSphereFamilyFiber_eq_map]
  exact hmap.trans (by rw [basedMapSphereHomeomorphIteratedLoopSpace_stiefelSphereFamilyFiber])

end BundleFamily

end TauCeti
