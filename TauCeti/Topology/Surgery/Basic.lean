/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import TauCeti.Topology.ContinuousMap.GlueClosedEmbeddings

/-!
# Surgery on a framed sphere

Let `E` and `F` be normed groups, with unit spheres `S = sphere 0 1` and closed unit balls
`D = closedBall 0 1`. For `E = ℝᵏ⁺¹` and `F = ℝ^q` these are `Sᵏ ⊆ Dᵏ⁺¹` and `S^(q-1) ⊆ D^q`.
Throughout, `int D` and `∂D` name the norm-level subsets `‖y‖ < 1` and `‖y‖ = 1` of `D`, and the
*boundary* of a product of balls and spheres is the subset where the ball coordinate has norm `1`.
These are definitions, not topological statements: when `E` is a real normed space, `int D` and
`∂D` are the topological interior and frontier of `D` in `E` (`interior_closedBall`,
`frontier_closedBall`), and for `E = ℝᵏ⁺¹` they are the manifold interior and boundary of `Dᵏ⁺¹`. A
*framed sphere* in a space `M` is a map `φ : Sᵏ × D^q → M`, typically an embedding: an embedded
`k`-sphere together with a trivialization of a closed tubular neighbourhood. *Surgery* along `φ`
removes the open tube `φ (Sᵏ × int D^q)` from `M` and glues in `D^(k+1) × S^(q-1)` along the
common boundary `Sᵏ × S^(q-1)`, the point `(x, y)` of `∂D^(k+1) × S^(q-1)` being glued to
`φ (x, y)`. For `k = 1` and `q = 2` this is integral Dehn surgery on a framed knot in a
`3`-manifold, and for `k = 0` it removes two balls and joins their boundary spheres by a tube
`D¹ × S^(q-1)`.

Here a surgery is recorded inside the resulting space, without a gluing construction, in the same
way as `TauCeti.DehnFilling` and `TauCeti.HeegaardSplitting`: a `TauCeti.SphereSurgery hφ Y`
consists of closed embeddings into `Y` of the exterior `TauCeti.sphereExterior φ` of the framed
sphere and of `D^(k+1) × S^(q-1)`, whose images cover `Y` and meet only along the boundary of
`D^(k+1) × S^(q-1)`, where they are identified as above. The two pieces being closed, a continuous
map on `Y` is the same as a pair of continuous maps on the pieces agreeing on the boundary
(`TauCeti.SphereSurgery.desc`, `TauCeti.SphereSurgery.desc_unique`), so `Y` is homeomorphic to the
space obtained by gluing.

## Main definitions

* `TauCeti.sphereExterior φ`: the complement in `M` of the open tube `φ (Sᵏ × int D^q)`.
* `TauCeti.sphereExteriorBoundaryInclusion hφ`: the boundary `Sᵏ × S^(q-1)` of the exterior,
  parametrized through `φ`.
* `TauCeti.ballSphereBoundaryInclusion`: the inclusion of `Sᵏ × S^(q-1)` into
  `D^(k+1) × S^(q-1)`.
* `TauCeti.SphereSurgery hφ Y`: a surgery along the framed sphere `φ`, recorded inside `Y`.
* `TauCeti.SphereSurgery.desc`: the continuous map on the result of a surgery glued from
  compatible continuous maps on the two pieces.
* `TauCeti.SphereSurgery.transHomeomorph`: transport of a surgery along a homeomorphism.

## Main results

* `TauCeti.SphereSurgery.range_inter_range`: the two pieces meet exactly in the boundary of
  `D^(k+1) × S^(q-1)`.
* `TauCeti.SphereSurgery.hom_ext` and `TauCeti.SphereSurgery.desc_unique`: a continuous map on the
  result of a surgery is determined by its restrictions to the two pieces.

## References

* J. Milnor, *A procedure for killing homotopy groups of differentiable manifolds*, Proc.
  Sympos. Pure Math. 3 (1961), 39–55, Section 1 (spherical modifications).
* A. Ranicki, *Algebraic and Geometric Surgery*, Oxford Mathematical Monographs (2002),
  Chapter 1 (surgery on a framed embedded sphere).
-/

public section

noncomputable section

open Set Topology Metric

namespace TauCeti

variable {E F M : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-! ### The exterior of a framed sphere -/

/-- The inclusion of `Sᵏ × S^(q-1)` as the boundary `Sᵏ × ∂D^q` of the tube `Sᵏ × D^q`, the points
whose disc coordinate has norm `1`. -/
def sphereBallBoundaryInclusion (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    sphere (0 : E) 1 × closedBall (0 : F) 1 :=
  (q.1, inclusion sphere_subset_closedBall q.2)

/-- The boundary inclusion into the tube is continuous. -/
@[continuity, fun_prop]
theorem continuous_sphereBallBoundaryInclusion :
    Continuous (sphereBallBoundaryInclusion (E := E) (F := F)) :=
  continuous_fst.prodMk ((continuous_inclusion sphere_subset_closedBall).comp continuous_snd)

/-- The sphere coordinate of a boundary point of the tube. -/
@[simp]
theorem sphereBallBoundaryInclusion_fst (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    (sphereBallBoundaryInclusion q).1 = q.1 :=
  (rfl)

/-- The disc coordinate of a boundary point of the tube lies on `∂D^q`. -/
@[simp]
theorem coe_sphereBallBoundaryInclusion_snd (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    ((sphereBallBoundaryInclusion q).2 : F) = q.2 :=
  (rfl)

/-- The inclusion of `Sᵏ × S^(q-1)` as the boundary `∂D^(k+1) × S^(q-1)` of
`D^(k+1) × S^(q-1)`, the points whose disc coordinate has norm `1`. -/
def ballSphereBoundaryInclusion (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    closedBall (0 : E) 1 × sphere (0 : F) 1 :=
  (inclusion sphere_subset_closedBall q.1, q.2)

/-- The boundary inclusion into the replacement piece is continuous. -/
@[continuity, fun_prop]
theorem continuous_ballSphereBoundaryInclusion :
    Continuous (ballSphereBoundaryInclusion (E := E) (F := F)) :=
  ((continuous_inclusion sphere_subset_closedBall).comp continuous_fst).prodMk continuous_snd

/-- The disc coordinate of a boundary point of `D^(k+1) × S^(q-1)` lies on `∂D^(k+1)`. -/
@[simp]
theorem coe_ballSphereBoundaryInclusion_fst (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    ((ballSphereBoundaryInclusion q).1 : E) = q.1 :=
  (rfl)

/-- The sphere coordinate of a boundary point of `D^(k+1) × S^(q-1)`. -/
@[simp]
theorem ballSphereBoundaryInclusion_snd (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    (ballSphereBoundaryInclusion q).2 = q.2 :=
  (rfl)

/-- The boundary of `D^(k+1) × S^(q-1)` is the set of points `(x, y)` with `‖x‖ = 1`. -/
theorem range_ballSphereBoundaryInclusion :
    range (ballSphereBoundaryInclusion (E := E) (F := F)) =
      {p : closedBall (0 : E) 1 × sphere (0 : F) 1 | ‖(p.1 : E)‖ = 1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    simp
  · intro hp
    exact ⟨(⟨p.1, mem_sphere_zero_iff_norm.mpr hp⟩, p.2), rfl⟩

/-- The exterior of a framed sphere `φ : Sᵏ × D^q → M`: the complement of the image of the open
tube `Sᵏ × int D^q`, the points whose disc coordinate has norm less than `1`. -/
def sphereExterior (φ : sphere (0 : E) 1 × closedBall (0 : F) 1 → M) : Set M :=
  (φ '' {p | ‖(p.2 : F)‖ < 1})ᶜ

/-- A point lies in the exterior of a framed sphere when it is outside the open tube. -/
@[simp]
theorem mem_sphereExterior {φ : sphere (0 : E) 1 × closedBall (0 : F) 1 → M} {x : M} :
    x ∈ sphereExterior φ ↔ x ∉ φ '' {p | ‖(p.2 : F)‖ < 1} :=
  Iff.rfl

variable {φ : sphere (0 : E) 1 × closedBall (0 : F) 1 → M}

/-- The boundary `φ (Sᵏ × ∂D^q)` of the tube of an injective framed sphere lies in its
exterior. -/
theorem apply_sphereBallBoundaryInclusion_mem_sphereExterior (hφ : Function.Injective φ)
    (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    φ (sphereBallBoundaryInclusion q) ∈ sphereExterior φ := by
  rintro ⟨p, hp, hpq⟩
  rw [hφ hpq, mem_ofPred_eq, coe_sphereBallBoundaryInclusion_snd,
    mem_sphere_zero_iff_norm.mp q.2.2] at hp
  exact lt_irrefl _ hp

/-- The boundary `φ (Sᵏ × ∂D^q)` of the exterior of an injective framed sphere, parametrized by
`Sᵏ × S^(q-1)` through the framing: `q ↦ φ (q.1, q.2)`. -/
def sphereExteriorBoundaryInclusion (hφ : Function.Injective φ)
    (q : sphere (0 : E) 1 × sphere (0 : F) 1) : sphereExterior φ :=
  ⟨φ (sphereBallBoundaryInclusion q), apply_sphereBallBoundaryInclusion_mem_sphereExterior hφ q⟩

/-- The parametrized boundary of the exterior is `q ↦ φ (q.1, q.2)`. -/
@[simp]
theorem coe_sphereExteriorBoundaryInclusion_apply (hφ : Function.Injective φ)
    (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    (sphereExteriorBoundaryInclusion hφ q : M) = φ (sphereBallBoundaryInclusion q) :=
  (rfl)

/-! ### Surgery -/

variable [TopologicalSpace M]

/-- The parametrized boundary inclusion into the exterior is continuous when the framing is. -/
@[continuity, fun_prop]
theorem continuous_sphereExteriorBoundaryInclusion (hφ : Function.Injective φ)
    (hcont : Continuous φ) : Continuous (sphereExteriorBoundaryInclusion hφ) :=
  (hcont.comp continuous_sphereBallBoundaryInclusion).subtype_mk _

/-- A **surgery** along the injective framed sphere `φ : Sᵏ × D^q → M`, recorded inside the
result `Y`: closed embeddings into `Y` of the exterior of `φ` and of `D^(k+1) × S^(q-1)`, whose
images cover `Y` and meet only along the boundary of `D^(k+1) × S^(q-1)`, the point `(x, y)` of
that boundary being the point `φ (x, y)` of the boundary of the exterior. The two images being
closed, `Y` is homeomorphic to the space obtained by gluing `D^(k+1) × S^(q-1)` to the exterior
along `Sᵏ × S^(q-1)`. -/
@[ext]
structure SphereSurgery (hφ : Function.Injective φ) (Y : Type*) [TopologicalSpace Y] where
  /-- The embedding of the exterior of the framed sphere into the result. -/
  exteriorEmbedding : sphereExterior φ → Y
  isClosedEmbedding_exteriorEmbedding : IsClosedEmbedding exteriorEmbedding
  /-- The embedding of `D^(k+1) × S^(q-1)` into the result. -/
  ballSphereEmbedding : closedBall (0 : E) 1 × sphere (0 : F) 1 → Y
  isClosedEmbedding_ballSphereEmbedding : IsClosedEmbedding ballSphereEmbedding
  exteriorEmbedding_sphereExteriorBoundaryInclusion (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    exteriorEmbedding (sphereExteriorBoundaryInclusion hφ q) =
      ballSphereEmbedding (ballSphereBoundaryInclusion q)
  range_union_range : range exteriorEmbedding ∪ range ballSphereEmbedding = univ
  range_inter_range_subset : range exteriorEmbedding ∩ range ballSphereEmbedding ⊆
    range (ballSphereEmbedding ∘ ballSphereBoundaryInclusion)

namespace SphereSurgery

attribute [simp] exteriorEmbedding_sphereExteriorBoundaryInclusion

variable {hφ : Function.Injective φ} {Y : Type*} [TopologicalSpace Y]

/-- **The two pieces of a surgery meet in the boundary** of `D^(k+1) × S^(q-1)`, which is the
image of the boundary of the exterior. -/
theorem range_inter_range (S : SphereSurgery hφ Y) :
    range S.exteriorEmbedding ∩ range S.ballSphereEmbedding =
      range (S.ballSphereEmbedding ∘ ballSphereBoundaryInclusion) := by
  refine S.range_inter_range_subset.antisymm ?_
  rintro _ ⟨q, rfl⟩
  exact ⟨⟨_, S.exteriorEmbedding_sphereExteriorBoundaryInclusion q⟩, mem_range_self _⟩

/-- A point of the exterior is sent into `D^(k+1) × S^(q-1)` only on the boundary, where the two
are identified through the framing. -/
theorem exteriorEmbedding_eq_ballSphereEmbedding_iff {S : SphereSurgery hφ Y}
    {x : sphereExterior φ} {p : closedBall (0 : E) 1 × sphere (0 : F) 1} :
    S.exteriorEmbedding x = S.ballSphereEmbedding p ↔
      ∃ q, p = ballSphereBoundaryInclusion q ∧ x = sphereExteriorBoundaryInclusion hφ q := by
  constructor
  · intro hxp
    obtain ⟨q, hq⟩ := S.range_inter_range_subset ⟨⟨x, hxp⟩, ⟨p, rfl⟩⟩
    have hp := S.isClosedEmbedding_ballSphereEmbedding.injective hq
    refine ⟨q, hp.symm, S.isClosedEmbedding_exteriorEmbedding.injective ?_⟩
    rw [hxp, S.exteriorEmbedding_sphereExteriorBoundaryInclusion, ← hp]
  · rintro ⟨q, rfl, rfl⟩
    exact S.exteriorEmbedding_sphereExteriorBoundaryInclusion q

section desc

variable {Z : Type*} [TopologicalSpace Z]

/-- **Maps out of the result of a surgery.** Continuous maps `a` on the exterior and `b` on
`D^(k+1) × S^(q-1)` that agree along the boundary descend to a continuous map on the result,
which is the gluing of its two closed pieces (`TauCeti.SphereSurgery.desc_unique`). -/
def desc (S : SphereSurgery hφ Y) (a : C(sphereExterior φ, Z))
    (b : C(closedBall (0 : E) 1 × sphere (0 : F) 1, Z))
    (hab : ∀ q, a (sphereExteriorBoundaryInclusion hφ q) = b (ballSphereBoundaryInclusion q)) :
    C(Y, Z) :=
  ContinuousMap.glueClosedEmbeddings a b S.isClosedEmbedding_exteriorEmbedding
    S.isClosedEmbedding_ballSphereEmbedding S.range_union_range fun _ _ hxp ↦ by
      obtain ⟨q, rfl, rfl⟩ := exteriorEmbedding_eq_ballSphereEmbedding_iff.1 hxp
      exact hab q

/-- The map descended from `a` and `b` restricts to `a` on the exterior. -/
@[simp]
theorem desc_exteriorEmbedding (S : SphereSurgery hφ Y) (a : C(sphereExterior φ, Z))
    (b : C(closedBall (0 : E) 1 × sphere (0 : F) 1, Z))
    (hab : ∀ q, a (sphereExteriorBoundaryInclusion hφ q) = b (ballSphereBoundaryInclusion q))
    (x : sphereExterior φ) : S.desc a b hab (S.exteriorEmbedding x) = a x :=
  ContinuousMap.glueClosedEmbeddings_apply_left _ _ _ _ _ _ x

/-- The map descended from `a` and `b` restricts to `b` on `D^(k+1) × S^(q-1)`. -/
@[simp]
theorem desc_ballSphereEmbedding (S : SphereSurgery hφ Y) (a : C(sphereExterior φ, Z))
    (b : C(closedBall (0 : E) 1 × sphere (0 : F) 1, Z))
    (hab : ∀ q, a (sphereExteriorBoundaryInclusion hφ q) = b (ballSphereBoundaryInclusion q))
    (p : closedBall (0 : E) 1 × sphere (0 : F) 1) :
    S.desc a b hab (S.ballSphereEmbedding p) = b p :=
  ContinuousMap.glueClosedEmbeddings_apply_right _ _ _ _ _ _ p

/-- **Maps out of the result of a surgery are determined by their restrictions** to the two
pieces. -/
theorem hom_ext (S : SphereSurgery hφ Y) {f g : C(Y, Z)}
    (hE : ∀ x, f (S.exteriorEmbedding x) = g (S.exteriorEmbedding x))
    (hB : ∀ p, f (S.ballSphereEmbedding p) = g (S.ballSphereEmbedding p)) : f = g :=
  ContinuousMap.ext_of_range_union_range S.range_union_range hE hB

/-- **Uniqueness of the descended map**: a continuous map on the result of a surgery restricting
to `a` on the exterior and to `b` on `D^(k+1) × S^(q-1)` is `TauCeti.SphereSurgery.desc`. -/
theorem desc_unique (S : SphereSurgery hφ Y) {a : C(sphereExterior φ, Z)}
    {b : C(closedBall (0 : E) 1 × sphere (0 : F) 1, Z)}
    (hab : ∀ q, a (sphereExteriorBoundaryInclusion hφ q) = b (ballSphereBoundaryInclusion q))
    {f : C(Y, Z)} (hE : ∀ x, f (S.exteriorEmbedding x) = a x)
    (hB : ∀ p, f (S.ballSphereEmbedding p) = b p) : f = S.desc a b hab :=
  ContinuousMap.eq_glueClosedEmbeddings hE hB

end desc

/-- A surgery is carried along a homeomorphism of its result. -/
def transHomeomorph (S : SphereSurgery hφ Y) {Y' : Type*} [TopologicalSpace Y'] (e : Y ≃ₜ Y') :
    SphereSurgery hφ Y' where
  exteriorEmbedding := e ∘ S.exteriorEmbedding
  isClosedEmbedding_exteriorEmbedding :=
    e.isClosedEmbedding.comp S.isClosedEmbedding_exteriorEmbedding
  ballSphereEmbedding := e ∘ S.ballSphereEmbedding
  isClosedEmbedding_ballSphereEmbedding :=
    e.isClosedEmbedding.comp S.isClosedEmbedding_ballSphereEmbedding
  exteriorEmbedding_sphereExteriorBoundaryInclusion q :=
    congrArg e (S.exteriorEmbedding_sphereExteriorBoundaryInclusion q)
  range_union_range := by
    rw [range_comp, range_comp, ← image_union, S.range_union_range, image_univ, e.range_coe]
  range_inter_range_subset := by
    rw [range_comp, range_comp, ← image_inter e.injective, Function.comp_assoc, range_comp]
    exact image_mono S.range_inter_range_subset

/-- The exterior embedding of a transported surgery is the composite with the homeomorphism. -/
@[simp]
theorem transHomeomorph_exteriorEmbedding (S : SphereSurgery hφ Y) {Y' : Type*}
    [TopologicalSpace Y'] (e : Y ≃ₜ Y') :
    (S.transHomeomorph e).exteriorEmbedding = e ∘ S.exteriorEmbedding :=
  (rfl)

/-- The embedding of `D^(k+1) × S^(q-1)` of a transported surgery is the composite with the
homeomorphism. -/
@[simp]
theorem transHomeomorph_ballSphereEmbedding (S : SphereSurgery hφ Y) {Y' : Type*}
    [TopologicalSpace Y'] (e : Y ≃ₜ Y') :
    (S.transHomeomorph e).ballSphereEmbedding = e ∘ S.ballSphereEmbedding :=
  (rfl)

end SphereSurgery

end TauCeti
