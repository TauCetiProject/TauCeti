/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.Stiefel.SphereBundle
public import TauCeti.Topology.VectorBundle.StiefelBundle

/-!
# The vertical two-sphere families of a sphere bundle

Let `E → B` be a real vector bundle whose fibres carry inner products, `S(E)` its unit sphere
bundle (`TauCeti.sphereBundle`), and `σ : V₃(E) → Map(S², S(E))` the Stiefel family of two-spheres
of its Stiefel bundle of orthonormal `3`-frames (`TauCeti.stiefelBundleSphereFamily`, from
`TauCeti.AlgebraicTopology.Sphere.Stiefel.SphereBundle`). It fits into the commutative diagram of
Barraud–Damian–Humilière–Oancea, Proposition 6.23:

```
V₂(q^⊥) ──σ_q──→ Ω²S(E) = Map_*(S², S(E))
   │                       │
 V₃(E)  ───σ───→   Map(S², S(E))
   │sphereProj 0           │ev
 S(E)   ════════════════ S(E)
```

Over each unit vector `q ∈ S(E)` with `b = q.1.proj`, the vertical `2`-frame fibre `V₂(q^⊥)` embeds
into `V₃(E)` via `TauCeti.StiefelBundle.sphereFiberIncl q 2`, and the restricted based family
`TauCeti.stiefelBundleSphereFamilyFiber` factors as the model fibre family
`TauCeti.stiefelSphereFamilyFiber` on `S(E_b)` followed by the fibre inclusion `S(E_b) ↪ S(E)`
(`TauCeti.stiefelBundleSphereFamilyFiber_eq_map`). Under `Map_*(S², S(E)) ≃ₜ Ω^[2] S(E)`, it is the
pushforward along `Ω^[2] (S(E_b) ↪ S(E))` of `TauCeti.stiefelDoubleLoop`
(`TauCeti.basedMapSphereHomeomorphIteratedLoopSpace_stiefelBundleSphereFamilyFiber`).

## Main declarations

* `TauCeti.sphereBundleProj_comp_stiefelBundleSphereFamily`: each two-sphere of `σ` lies in one
  fibre of `S(E) → B`.
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

variable {B : Type w} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- Every two-sphere in the family `stiefelBundleSphereFamily` projects constantly to the base
point `p.proj` of the frame. -/
theorem sphereBundleProj_comp_stiefelBundleSphereFamily (p : StiefelBundle F E 3) :
    (sphereBundleProj F E).comp (stiefelBundleSphereFamily F E p) =
      ContinuousMap.const Sphere2 p.proj := by
  ext y
  simp [stiefelBundleSphereFamily_apply]

variable (F E) in
omit [NormedSpace ℝ F] [∀ b, InnerProductSpace ℝ (E b)] [VectorBundle ℝ F E] in
/-- The fibre inclusion `(S(E_{q.1.proj}), q) → (S(E), q)` as a morphism of based topological
spaces. -/
abbrev sphereBundleFiberBasedHom (q : sphereBundle F E) :
    BasedTopologicalSpace.Hom
      ⟨sphere (0 : E q.val.proj) 1, unitSphereOfSphereBundle q⟩
      ⟨sphereBundle F E, q⟩ where
  toContinuousMap := sphereBundleFiberIncl F E q.val.proj
  map_basepoint := sphereBundleFiberIncl_unitSphereOfSphereBundle q

variable (F E) in
/-- **The vertical two-sphere family `V₂(q^⊥) → Map_*(S², S(E))` over a unit vector `q : S(E)`.** -/
def stiefelBundleSphereFamilyFiber (q : sphereBundle F E) :
    C(stiefel (ℝ ∙ q.val.snd)ᗮ 2, BasedMap Sphere2 (sphereBundle F E) Sphere2.north q) :=
  BasedMap.lift ((stiefelBundleSphereFamily F E).comp (StiefelBundle.sphereFiberIncl q 2))
    fun x ↦ by simp

/-- The based sphere map associated to a vertical `2`-frame at `q` sends the north pole to `q`. -/
@[simp]
theorem stiefelBundleSphereFamilyFiber_apply_north (q : sphereBundle F E)
    (x : stiefel (ℝ ∙ q.val.snd)ᗮ 2) :
    (stiefelBundleSphereFamilyFiber F E q x).val Sphere2.north = q :=
  (stiefelBundleSphereFamilyFiber F E q x).property

/-- **Restricting `stiefelBundleSphereFamily` to the vertical fibre `V₂(q^⊥)` over `q` recovers
`stiefelBundleSphereFamilyFiber`.** -/
@[simp]
theorem stiefelBundleSphereFamily_sphereFiberIncl (q : sphereBundle F E)
    (x : stiefel (ℝ ∙ q.val.snd)ᗮ 2) :
    stiefelBundleSphereFamily F E (StiefelBundle.sphereFiberIncl q 2 x) =
      (stiefelBundleSphereFamilyFiber F E q x).val := by
  rw [stiefelBundleSphereFamilyFiber, BasedMap.lift_apply_val, ContinuousMap.comp_apply]

/-- **The vertical family over `q ∈ S(E)` is the model fibre family on `S(E_{q.1.proj})`
postcomposed with the fibre inclusion `S(E_{q.1.proj}) ↪ S(E)`.** -/
theorem stiefelBundleSphereFamilyFiber_eq_map (q : sphereBundle F E)
    (x : stiefel (ℝ ∙ q.val.snd)ᗮ 2) :
    stiefelBundleSphereFamilyFiber F E q x =
      BasedMap.map (sphereBundleFiberIncl F E q.val.proj)
        (sphereBundleFiberIncl_unitSphereOfSphereBundle q)
        (stiefelSphereFamilyFiber (unitSphereOfSphereBundle q) x) := by
  refine Subtype.ext ?_
  rw [← stiefelBundleSphereFamily_sphereFiberIncl, StiefelBundle.sphereFiberIncl_apply,
    stiefelBundleSphereFamily_fiberIncl, stiefelSphereFamily_stiefelFrameIncl]
  exact ContinuousMap.ext fun y ↦
    (BasedMap.map_apply (sphereBundleFiberIncl F E q.val.proj) _ _ y).symm

/-- On the cube `I²` collapsed onto `S²`, the vertical family over `q` evaluates to the double loop
`stiefelDoubleLoop` inside `S(E_{q.1.proj})` included into `S(E)`. -/
@[simp]
theorem stiefelBundleSphereFamilyFiber_apply_sphereCollapse (q : sphereBundle F E)
    (x : stiefel (ℝ ∙ q.val.snd)ᗮ 2) (z : Fin 2 → I) :
    (stiefelBundleSphereFamilyFiber F E q x).val (sphereCollapse 2 Sphere2.north z) =
      sphereBundleFiberIncl F E q.val.proj
        (stiefelDoubleLoop (unitSphereOfSphereBundle q) x (z 0) (z 1)) := by
  rw [stiefelBundleSphereFamilyFiber_eq_map, BasedMap.map_apply,
    stiefelSphereFamilyFiber_apply_sphereCollapse]

/-- **Factorization through `Ω^[2] S(E_{q.1.proj}) → Ω^[2] S(E)`.** Under
`Map_*(S², S(E)) ≃ₜ Ω^[2] S(E)`, the vertical family over `q` sends a `2`-frame `x` of `q^⊥` to the
double loop `stiefelDoubleLoop q x` pushed forward along the `2`-fold loop map of
`S(E_{q.1.proj}) ↪ S(E)`. -/
theorem basedMapSphereHomeomorphIteratedLoopSpace_stiefelBundleSphereFamilyFiber
    (q : sphereBundle F E) (x : stiefel (ℝ ∙ q.val.snd)ᗮ 2) :
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
