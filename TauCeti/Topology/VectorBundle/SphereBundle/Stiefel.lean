/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Stiefel.Fiber
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic

/-!
# Orthonormal frames in the fibres of a Euclidean vector bundle

Let `E → B` be a real vector bundle with model fibre `F` whose fibres are real inner product
spaces. The **Stiefel bundle** `V_k(E)` (`TauCeti.StiefelBundle F E k`) consists of the pairs of a
point `b` of the base and an orthonormal `k`-frame of the fibre `E_b`, a point of the Stiefel
manifold `V_k(E_b)` (`TauCeti.stiefel`). It carries the topology in which a frame varies
continuously when its base point and each of its vectors, read in the total space of `E`, do
(`TauCeti.StiefelBundle.continuous_iff`). Its fibre over `b` is the Stiefel manifold of `E_b`,
embedded by `TauCeti.StiefelBundle.fiberIncl` (`TauCeti.StiefelBundle.isEmbedding_fiberIncl`,
`TauCeti.StiefelBundle.range_fiberIncl`). For `k` the rank of `E` these are the full orthonormal
frames of `TauCeti.OrthonormalFrameBundle`, read as orthonormal families rather than as linear
isometric equivalences.

Each vector of a frame is a point of the unit sphere bundle `S(E)` (`TauCeti.sphereBundle`), which
gives the projections `TauCeti.StiefelBundle.sphereProj i : V_k(E) → S(E)`. For `k = n + 1` and
`i = 0` this is a map `V_{n+1}(E) → S(E)` whose fibre over a unit vector `q ∈ S(E_b)` is the
space of orthonormal `n`-frames of `q^⊥ ⊆ E_b`, the tangent space at `q` of the sphere `S(E_b)`
through `q`: the fibre over `q` is the image of the frames of `q^⊥` under
`TauCeti.stiefelFrameIncl` (`TauCeti.StiefelBundle.range_fiberIncl_comp_stiefelFrameIncl`).

No condition is imposed on the fibre metric here: the topology is read in the total space, and
the frames only enter through the fibrewise inner products.

## Main declarations

* `TauCeti.StiefelBundle F E k`: the orthonormal `k`-frames in the fibres of `E`.
* `TauCeti.StiefelBundle.continuous_iff`: maps into it are continuous exactly when the base point
  and the frame vectors are.
* `TauCeti.StiefelBundle.fiberIncl`: the inclusion of the frames of one fibre, an embedding by
  `TauCeti.StiefelBundle.isEmbedding_fiberIncl`.
* `TauCeti.StiefelBundle.sphereProj`: the projection to the `i`th vector, a point of the unit
  sphere bundle.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Chapter 5 (Stiefel manifolds) and §12 (sphere bundles).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23.
-/

public section

noncomputable section

open Bundle Metric Set Topology

universe w

namespace TauCeti

/-- The **Stiefel bundle** `V_k(E)` of a vector bundle `E` with model fibre `F` whose fibres are
real inner product spaces: the pairs of a point of the base and an orthonormal `k`-frame of the
fibre over it. The model fibre `F` enters only through the topology, which is read in the total
space of `E`. -/
structure StiefelBundle {B : Type*} (F : Type*) (E : B → Type*) [∀ b, NormedAddCommGroup (E b)]
    [∀ b, InnerProductSpace ℝ (E b)] (k : ℕ) where
  /-- The base point. -/
  proj : B
  /-- The orthonormal frame of the fibre over the base point. -/
  frame : stiefel (E proj) k

namespace StiefelBundle

section General

variable {B F : Type*} {E : B → Type*} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {k : ℕ}

/-- Two frames over the same base point are equal exactly when they are equal as frames of that
fibre. -/
theorem mk_eq_mk_iff {b : B} {x y : stiefel (E b) k} :
    (⟨b, x⟩ : StiefelBundle F E k) = ⟨b, y⟩ ↔ x = y := by
  constructor
  · exact fun h ↦ eq_of_heq (StiefelBundle.mk.inj h).2
  · rintro rfl
    rfl

/-- Two frames are equal when their base points are equal and their vectors, read in the total
space of `E`, are equal. -/
@[ext]
theorem ext {p q : StiefelBundle F E k} (hproj : p.proj = q.proj)
    (hframe : ∀ i, (⟨p.proj, (p.frame : Fin k → E p.proj) i⟩ : TotalSpace F E) =
      ⟨q.proj, (q.frame : Fin k → E q.proj) i⟩) : p = q := by
  obtain ⟨b, x⟩ := p
  obtain ⟨b', y⟩ := q
  obtain rfl : b = b' := hproj
  exact mk_eq_mk_iff.2 (Subtype.ext (funext fun i ↦ TotalSpace.mk_inj.1 (hframe i)))

variable [TopologicalSpace B] [TopologicalSpace (TotalSpace F E)]

/-- The topology of the Stiefel bundle: the coarsest topology for which the base point and each
vector of the frame, read in the total space of `E`, are continuous. -/
instance : TopologicalSpace (StiefelBundle F E k) :=
  .induced (fun p ↦ (p.proj, fun i ↦ (⟨p.proj, (p.frame : Fin k → E p.proj) i⟩ : TotalSpace F E)))
    inferInstance

/-- A map into the Stiefel bundle is continuous exactly when its base point and each vector of its
frame, read in the total space of `E`, are continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → StiefelBundle F E k} :
    Continuous f ↔ Continuous (fun x ↦ (f x).proj) ∧
      ∀ i, Continuous fun x ↦
        (⟨(f x).proj, ((f x).frame : Fin k → E (f x).proj) i⟩ : TotalSpace F E) := by
  rw [continuous_induced_rng, continuous_prodMk, continuous_pi_iff]
  rfl

/-- The projection of the Stiefel bundle to the base is continuous. -/
@[fun_prop]
theorem continuous_proj : Continuous (proj : StiefelBundle F E k → B) :=
  (continuous_iff.1 continuous_id).1

/-- Each vector of the frame, read in the total space of `E`, depends continuously on the frame. -/
@[fun_prop]
theorem continuous_totalSpaceMk_frame (i : Fin k) :
    Continuous fun p : StiefelBundle F E k ↦
      (⟨p.proj, (p.frame : Fin k → E p.proj) i⟩ : TotalSpace F E) :=
  (continuous_iff.1 continuous_id).2 i

section Fiber

variable (F E k) [TopologicalSpace F] [FiberBundle F E]

/-- The inclusion `V_k(E_b) → V_k(E)` of the orthonormal `k`-frames of the fibre over `b`. -/
def fiberIncl (b : B) : C(stiefel (E b) k, StiefelBundle F E k) where
  toFun x := ⟨b, x⟩
  continuous_toFun := continuous_iff.2 ⟨continuous_const, fun i ↦
    (FiberBundle.continuous_totalSpaceMk F E b).comp
      ((continuous_apply i).comp continuous_subtypeVal)⟩

variable {F E k}

theorem fiberIncl_apply (b : B) (x : stiefel (E b) k) : fiberIncl F E k b x = ⟨b, x⟩ :=
  (rfl)

@[simp]
theorem proj_fiberIncl (b : B) (x : stiefel (E b) k) : (fiberIncl F E k b x).proj = b :=
  (rfl)

variable (F E k)

/-- The frames of the fibre over `b` are exactly the fibre over `b` of the projection to the
base. -/
theorem range_fiberIncl (b : B) : range (fiberIncl F E k b) =
    (proj : StiefelBundle F E k → B) ⁻¹' {b} := by
  refine Subset.antisymm (range_subset_iff.2 fun x ↦ rfl) fun p hp ↦ ?_
  obtain ⟨b', x⟩ := p
  obtain rfl : b' = b := hp
  exact ⟨x, rfl⟩

/-- **The fibre of the Stiefel bundle over `b` is the Stiefel manifold of `E_b`**: the inclusion
of the frames of the fibre is an embedding. -/
theorem isEmbedding_fiberIncl (b : B) : IsEmbedding (fiberIncl F E k b) := by
  -- Read in the total space, the frame vectors of an included frame are its vectors.
  have hv : IsInducing fun x : stiefel (E b) k ↦
      fun i ↦ (⟨b, (x : Fin k → E b) i⟩ : TotalSpace F E) :=
    (IsInducing.piMap fun _ ↦ FiberBundle.totalSpaceMk_isInducing F E b).comp
      IsInducing.subtypeVal
  have hbv : IsInducing fun x : stiefel (E b) k ↦
      (b, fun i ↦ (⟨b, (x : Fin k → E b) i⟩ : TotalSpace F E)) :=
    IsInducing.of_comp (continuous_const.prodMk hv.continuous) continuous_snd hv
  exact ⟨IsInducing.of_comp (fiberIncl F E k b).continuous continuous_induced_dom hbv,
    fun _ _ h ↦ mk_eq_mk_iff.1 h⟩

end Fiber

end General

section Sphere

variable {B : Type w} {F : Type*} {E : B → Type w} [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] {k : ℕ} [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F E)]

variable (F k) in
/-- The `i`th vector of a frame, as a point of the unit sphere bundle `S(E)`. -/
def sphereProj (i : Fin k) : C(StiefelBundle F E k, sphereBundle F E) where
  toFun p := ⟨⟨p.proj, (p.frame : Fin k → E p.proj) i⟩,
    mem_sphereBundle.2 (norm_eq_one_of_mem_stiefel p.frame.property i)⟩
  continuous_toFun := (continuous_totalSpaceMk_frame i).subtype_mk _

@[simp]
theorem coe_sphereProj_apply (i : Fin k) (p : StiefelBundle F E k) :
    (sphereProj F k i p : TotalSpace F E) = ⟨p.proj, (p.frame : Fin k → E p.proj) i⟩ :=
  (rfl)

variable [NormedAddCommGroup F] [FiberBundle F E]

/-- On the frames of one fibre, the projection to the `i`th vector is the projection
`TauCeti.stiefelProj` of the Stiefel manifold of that fibre, followed by the inclusion of its unit
sphere into the sphere bundle. -/
@[simp]
theorem sphereProj_fiberIncl (i : Fin k) (b : B) (x : stiefel (E b) k) :
    sphereProj F k i (fiberIncl F E k b x) =
      sphereBundleFiberIncl F E b (stiefelProj (E b) k i x) :=
  Subtype.ext (by rw [coe_sphereProj_apply, coe_sphereBundleFiberIncl_apply, coe_stiefelProj]; rfl)

variable (F) in
/-- **The fibre of `V_{n+1}(E) → S(E)`.** The frames whose first vector is a unit vector `p` of
the fibre `E_b` are exactly the frames `(p, u₁, …, uₙ)` of `E_b` with `(u₁, …, uₙ)` an orthonormal
frame of `p^⊥`. -/
theorem range_fiberIncl_comp_stiefelFrameIncl {n : ℕ} (b : B) (p : sphere (0 : E b) 1) :
    range (fiberIncl F E (n + 1) b ∘ stiefelFrameIncl p n) =
      sphereProj F (n + 1) 0 ⁻¹' {sphereBundleFiberIncl F E b p} := by
  rw [range_comp, range_stiefelFrameIncl]
  ext q
  simp only [mem_image, mem_preimage, mem_singleton_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [sphereProj_fiberIncl, hx]
  · intro hq
    obtain ⟨b', x⟩ := q
    have h := congrArg Subtype.val hq
    rw [coe_sphereProj_apply, coe_sphereBundleFiberIncl_apply] at h
    obtain rfl : b' = b := congrArg TotalSpace.proj h
    refine ⟨x, Subtype.ext ?_, rfl⟩
    exact (coe_stiefelProj 0 x).trans (TotalSpace.mk_inj.1 h)

end Sphere

end StiefelBundle

end TauCeti
