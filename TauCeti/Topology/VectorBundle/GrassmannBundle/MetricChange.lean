/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.GrassmannBundle.LinearEquiv
public import TauCeti.Topology.VectorBundle.Riemannian.WithFiberMetric

/-!
# The Grassmann bundle under a change of fibre metric

Let `E → B` be a real vector bundle of finite rank and let `g`, `h` be two continuous Riemannian
metrics on `E`. The fibres of `E` carrying `g` or `h` as their inner product are the copies
`TauCeti.WithFiberMetric g` and `TauCeti.WithFiberMetric h` of `E`, with Grassmann bundles
`G_k^g(E)` and `G_k^h(E)` (`TauCeti.grassmannBundle`), whose points `(x, P)` record a `k`-plane `S`
of `E_x` by its `g`-orthogonal, respectively `h`-orthogonal, projection `P^g_S`, `P^h_S`.

The **canonical homeomorphism** `G_k^g(E) ≃ₜ G_k^h(E)`
(`TauCeti.grassmannBundle.metricChangeHomeomorph`) keeps the plane and changes its presentation:
it sends `(x, P^g_S)` to `(x, P^h_S)` (`TauCeti.grassmannBundle.metricChangeHomeomorph_fiberIncl`,
`TauCeti.WithFiberMetric.grassmannianMap_metricChange_starProjection`). It is the map of
Grassmann bundles induced by the identity of the fibres, seen as continuous linear equivalences
`WithFiberMetric g x ≃L[ℝ] WithFiberMetric h x` (`TauCeti.WithFiberMetric.metricChange`), which
are constant in coordinates (`TauCeti.grassmannBundle.mapLinearEquivHomeomorph`). The
homeomorphisms are functorial: `G_k^g → G_k^g` is the identity
(`TauCeti.grassmannBundle.metricChangeHomeomorph_self`), and `G_k^g → G_k^h → G_k^{h'}` is
`G_k^g → G_k^{h'}` (`TauCeti.grassmannBundle.metricChangeHomeomorph_trans`).
It differs from the homeomorphism `TauCeti.grassmannBundle.map` induced by the metric change
isometries `Bundle.ContinuousRiemannianMetric.metricChangeIsometry` of a continuous Riemannian
bundle, which identifies its Grassmann bundle with `G_k^h` but moves the planes.

The canonical homeomorphism is not the identity on projections: the `h`-orthogonal projection onto
a plane is in general not the `g`-orthogonal one. It is when `h = c² g` for a constant `c`
(`TauCeti.grassmannBundle.coe_metricChangeHomeomorph_of_inner_eq`): orthogonal projections only
depend on the inner product up to a constant factor.

On a Riemannian manifold `(M, g)` these are the Grassmann bundles `G_k(M)` of tangent `k`-planes
for two Riemannian metrics, on which varifolds are measures (W. K. Allard, *On the first variation
of a varifold*, Section 3).

## Main declarations

* `TauCeti.WithFiberMetric.metricChange`: the identity of a fibre, from the metric `g` to `h`.
* `TauCeti.grassmannBundle.metricChangeHomeomorph`: the canonical homeomorphism
  `G_k^g(E) ≃ₜ G_k^h(E)`, `(x, P^g_S) ↦ (x, P^h_S)`.

## Main results

* `TauCeti.WithFiberMetric.grassmannianMap_metricChange_starProjection`: the canonical map sends
  the `g`-orthogonal projection onto `S` to the `h`-orthogonal projection onto `S`.
* `TauCeti.grassmannBundle.metricChangeHomeomorph_trans`: functoriality in the metrics.
* `TauCeti.grassmannBundle.coe_metricChangeHomeomorph_of_inner_eq`: for `h = c² g` the canonical
  homeomorphism is the identity on projections.

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. (2) 95 (1972), 417–491,
  Section 3.
-/

public section

noncomputable section

open Bundle Filter Set Topology ContinuousLinearMap Module
open scoped InnerProductSpace

namespace TauCeti

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

namespace WithFiberMetric

/-- The fibres of the copy carrying a metric are finite-dimensional when those of `E` are. -/
instance instFiniteDimensional [∀ b, FiniteDimensional ℝ (E b)]
    (g : ContinuousRiemannianMetric F E) (b : B) : FiniteDimensional ℝ (WithFiberMetric g b) :=
  inferInstanceAs (FiniteDimensional ℝ (E b))

variable (g h h' : ContinuousRiemannianMetric F E)

/-- The **change of metric** on the fibre over `b`: the identity of `E b`, as a continuous linear
equivalence from the copy carrying `g` to the copy carrying `h`. It is not an isometry unless
`g = h` on the fibre. -/
def metricChange (b : B) : WithFiberMetric g b ≃L[ℝ] WithFiberMetric h b :=
  ContinuousLinearEquiv.refl ℝ (E b)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- The change of metric preserves the underlying vector. -/
theorem metricChange_apply (b : B) (v : WithFiberMetric g b) : metricChange g h b v = v :=
  (rfl)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- The inverse of the change of metric from `g` to `h` is the change of metric from `h` to `g`. -/
@[simp]
theorem metricChange_symm (b : B) : (metricChange g h b).symm = metricChange h g b :=
  (rfl)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- Changing the metric from `g` to itself is the identity. -/
@[simp]
theorem metricChange_self (b : B) :
    metricChange g g b = ContinuousLinearEquiv.refl ℝ (WithFiberMetric g b) :=
  (rfl)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- Changing the metric from `g` to `h` and then to `h'` is changing it from `g` to `h'`. -/
@[simp]
theorem metricChange_trans (b : B) :
    (metricChange g h b).trans (metricChange h h' b) = metricChange g h' b :=
  (rfl)

/-- The `h`-inner product of the images under the change of metric is the `h`-inner product of
the vectors. -/
theorem inner_metricChange (b : B) (u v : WithFiberMetric g b) :
    ⟪metricChange g h b u, metricChange g h b v⟫_ℝ = h.inner b u v :=
  (rfl)

/-- The `g`-inner product on the copy carrying `g`. -/
theorem inner_eq (b : B) (u v : WithFiberMetric g b) : ⟪u, v⟫_ℝ = g.inner b u v :=
  (rfl)

variable [∀ b, FiniteDimensional ℝ (E b)] {k : ℕ}

/-- **The change of metric sends `P^g_S` to `P^h_S`**: the map of Grassmannians induced by the
change of metric sends the `g`-orthogonal projection onto a `k`-plane `S` to the `h`-orthogonal
projection onto the same plane. -/
theorem grassmannianMap_metricChange_starProjection (b : B)
    (S : Submodule ℝ (WithFiberMetric g b))
    (hS : S.starProjection ∈ Euclidean.grassmannian ℝ (WithFiberMetric g b) k) :
    (metricChange g h b).grassmannianMap k ⟨S.starProjection, hS⟩ =
      ⟨(S.map (metricChange g h b : WithFiberMetric g b →ₗ[ℝ] WithFiberMetric h b)).starProjection,
        Euclidean.grassmannian.starProjection_mem (by
          rw [← Euclidean.grassmannian.finrank_range hS, Submodule.range_starProjection]
          exact (LinearEquiv.finrank_map_eq (metricChange g h b).toLinearEquiv S))⟩ := by
  refine Euclidean.grassmannian.ext_range ?_
  rw [ContinuousLinearEquiv.range_coe_grassmannianMap_apply]
  simp only [Submodule.range_starProjection]

/-- The plane of the image of `P` under the change of metric is the plane of `P`. -/
theorem range_coe_grassmannianMap_metricChange (b : B)
    (P : Euclidean.grassmannian ℝ (WithFiberMetric g b) k) :
    ((metricChange g h b).grassmannianMap k P :
        WithFiberMetric h b →L[ℝ] WithFiberMetric h b).range =
      (P : WithFiberMetric g b →L[ℝ] WithFiberMetric g b).range.map
        (metricChange g h b : WithFiberMetric g b →ₗ[ℝ] WithFiberMetric h b) :=
  (metricChange g h b).range_coe_grassmannianMap_apply P

end WithFiberMetric

namespace grassmannBundle

open WithFiberMetric

variable [∀ b, FiniteDimensional ℝ (E b)] (g h h' : ContinuousRiemannianMetric F E)

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [∀ b, FiniteDimensional ℝ (E b)] in
/-- Read in the common coordinates of the two copies, the change of metric is the identity of the
model fibre near each point. -/
theorem continuousAt_inCoordinates_metricChange (x₀ : B) :
    ContinuousAt (fun x ↦ inCoordinates F (WithFiberMetric g) F (WithFiberMetric h) x₀ x x₀ x
      (metricChange g h x : WithFiberMetric g x →L[ℝ] WithFiberMetric h x)) x₀ := by
  refine continuousAt_const (y := ContinuousLinearMap.id ℝ F) |>.congr ?_
  filter_upwards [(trivializationAt F E x₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt F E x₀)] with x hx
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [inCoordinates, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, metricChange_apply, ContinuousLinearMap.id_apply]
  exact ((trivializationAt F E x₀).continuousLinearMapAt_symmL (R := ℝ) hx v).symm

variable (k : ℕ)

/-- The **canonical homeomorphism between the Grassmann bundles of two fibre metrics** `g` and
`h`: a `k`-plane `S` of `E_x`, recorded by its `g`-orthogonal projection `P^g_S`, goes to the same
plane recorded by its `h`-orthogonal projection `P^h_S`. It is the map induced by the changes of
metric, which are the identity in coordinates. -/
def metricChangeHomeomorph :
    grassmannBundle F (WithFiberMetric g) k ≃ₜ grassmannBundle F (WithFiberMetric h) k :=
  mapLinearEquivHomeomorph k (metricChange g h) (continuousAt_inCoordinates_metricChange g h)

theorem coe_metricChangeHomeomorph :
    (metricChangeHomeomorph g h k :
        grassmannBundle F (WithFiberMetric g) k → grassmannBundle F (WithFiberMetric h) k) =
      mapLinearEquiv id (metricChange g h) :=
  coe_mapLinearEquivHomeomorph _ _

/-- The inverse of the canonical homeomorphism from `g` to `h` is the canonical homeomorphism from
`h` to `g`. -/
@[simp]
theorem metricChangeHomeomorph_symm :
    (metricChangeHomeomorph g h k).symm = metricChangeHomeomorph h g k := by
  refine Homeomorph.ext fun p ↦ ?_
  rw [coe_metricChangeHomeomorph, metricChangeHomeomorph, coe_mapLinearEquivHomeomorph_symm]
  simp only [metricChange_symm]

variable {k} in
/-- The canonical homeomorphism keeps the base point. -/
@[simp]
theorem proj_metricChangeHomeomorph (p : grassmannBundle F (WithFiberMetric g) k) :
    proj (metricChangeHomeomorph g h k p) = proj p := by
  rw [coe_metricChangeHomeomorph, proj_mapLinearEquiv, id_eq]

variable {k} in
/-- **The canonical homeomorphism sends `(x, P)` to `(x, P^h_{range P})`**: over each point it is
the map of Grassmannians induced by the change of metric, which sends the `g`-orthogonal
projection onto a plane to the `h`-orthogonal projection onto the same plane
(`TauCeti.WithFiberMetric.grassmannianMap_metricChange_starProjection`). -/
@[simp]
theorem metricChangeHomeomorph_fiberIncl (b : B)
    (P : Euclidean.grassmannian ℝ (WithFiberMetric g b) k) :
    metricChangeHomeomorph g h k (fiberIncl F (WithFiberMetric g) k b P) =
      fiberIncl F (WithFiberMetric h) k b ((metricChange g h b).grassmannianMap k P) := by
  rw [coe_metricChangeHomeomorph, mapLinearEquiv_fiberIncl]
  rfl

/-- Changing the metric from `g` to itself is the identity of the Grassmann bundle. -/
@[simp]
theorem metricChangeHomeomorph_self :
    metricChangeHomeomorph g g k = Homeomorph.refl _ :=
  Homeomorph.ext fun p ↦ by
    rw [coe_metricChangeHomeomorph]
    exact congrFun (mapLinearEquiv_id (F := F) (E := WithFiberMetric g) (k := k)) p

/-- **Functoriality in the metric.** Changing the metric from `g` to `h` and then to `h'` is
changing it from `g` to `h'`. -/
theorem metricChangeHomeomorph_trans :
    (metricChangeHomeomorph g h k).trans (metricChangeHomeomorph h h' k) =
      metricChangeHomeomorph g h' k :=
  Homeomorph.ext fun p ↦ by
    rw [Homeomorph.trans_apply, coe_metricChangeHomeomorph, coe_metricChangeHomeomorph,
      coe_metricChangeHomeomorph, ← Function.comp_apply (f := mapLinearEquiv id _),
      ← mapLinearEquiv_comp]
    exact congrArg (fun L ↦ mapLinearEquiv id L p) (funext fun x ↦ metricChange_trans g h h' x)

variable {g h k} in
/-- **For `h = c² g` the canonical homeomorphism is the identity on projections**: when
`h = c² g` with a constant `c`, the `h`-orthogonal projection onto a plane is its
`g`-orthogonal projection, so `(x, P) ↦ (x, P)`, the projection read through the change of
metric, which is the identity of the fibre. -/
theorem coe_metricChangeHomeomorph_of_inner_eq {c : ℝ}
    (hgh : ∀ b u v, h.inner b u v = c ^ 2 * g.inner b u v)
    (p : grassmannBundle F (WithFiberMetric g) k) :
    (metricChangeHomeomorph g h k p).val =
      ⟨p.val.proj, (metricChange g h p.val.proj : _ →L[ℝ] _) ∘L p.val.snd ∘L
        (metricChange h g p.val.proj : _ →L[ℝ] _)⟩ :=
  by
  rw [coe_metricChangeHomeomorph, coe_mapLinearEquiv_of_inner_map_map id (metricChange g h)
    (fun b u v ↦ hgh b u v) p, metricChange_symm]
  rfl

end grassmannBundle

end TauCeti
