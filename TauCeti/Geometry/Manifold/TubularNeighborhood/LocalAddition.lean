/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.NormalizeAtZero
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.LocalAddition
public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.TubularNeighborhood.NormalFrame

/-!
# The local addition adapted to a submanifold of a Euclidean space

Let `f : M → V` be an immersion of a boundaryless manifold into a finite-dimensional real inner
product space, and let `r : V → M` be a retraction onto it with normal displacement near a point
of its image: `r (f y) = y`, and `q - f (r q)` is normal to `f` at `r q`. Write `P_N(y)` and
`P_T(y) = 1 - P_N(y)` for the orthogonal projections of `V` onto the normal space
`TauCeti.normalSubspace I f y` and onto its orthogonal complement, the tangent space of the
immersed manifold at `f y`. For a point `q` near the image, with base point `y = r q` and normal
displacement `ν = q - f y`, and a vector `v : V`, the **adapted local addition** is

`B(q, v) = f y' + P_N(y') (ν + P_N(y) v)`, where `y' = r (f y + P_T(y) v)`

(`TauCeti.adaptedLocalAddition`). The tangential part of `v` moves the base point along the
submanifold, through the retraction, and the normal part of `v` is added to the normal
displacement and transported to the new base point by its normal projection. Unlike the straight
addition `q + v`, it is adapted to the submanifold: starting at a point `f x` of the submanifold,
for small `v` it stays in the image of a neighbourhood of `x` exactly along tangent vectors.

`B` is not yet a local addition in the sense of Kriegl and Michor, since away from the
submanifold the derivative `J_q = D_v B(q, 0)` need not be the identity. The **normalized adapted
local addition** `A(q, v) = B(q, J_q⁻¹ v)` (`TauCeti.normalizedAdaptedLocalAddition`) corrects
this. A local addition gives charts on spaces of maps, and an adapted one gives charts on maps
whose boundary values lie on the submanifold, the boundary condition being linear in the chart, as
for discs with boundary on a Lagrangian or totally real submanifold. This file proves the basic
properties of `B` and that, for a compact submanifold, `A` is a local addition near the
submanifold which extends to a local addition on all of `V`; it does not construct the charts on
spaces of maps.

* `TauCeti.adaptedLocalAddition_zero`: `B(q, 0) = q`.
* `TauCeti.adaptedLocalAddition_apply_of_retract`: at a point `f x` fixed by the retraction,
  `B(f x, v) = f y' + P_N(y') (P_N(x) v)`, where `y' = r (f x + P_T(x) v)`.
* `TauCeti.adaptedLocalAddition_of_mem_orthogonal`: along a tangent vector `v` at `f x`,
  `B(f x, v) = f (r (f x + v))` lies on the submanifold.
* `TauCeti.contDiffAt_adaptedLocalAddition`: `B` is jointly `C^n` when `f` is `C^(n + 1)` and `r`
  is `C^n`, by the smoothness of the normal projections along the retraction,
  `TauCeti.contDiffAt_normalSubspace_starProjection_comp`.
* `TauCeti.hasFDerivAt_adaptedLocalAddition`: at a point `f x` of the submanifold, the derivative
  of `v ↦ B(f x, v)` at `0` is the identity, since the differential of `f ∘ r` there is the
  tangential projection `P_T(x)` (`TauCeti.hasFDerivAt_comp_of_eventually_sub_mem_normalSubspace`).
* `TauCeti.eventually_adaptedLocalAddition_mem_image_iff`: on a tubular neighbourhood on which
  normal addition `(y, ν) ↦ f y + ν` is injective at the points of a neighbourhood `W` of `x`,
  `B(f x, v)` lies in `f '' W`, for small `v`, exactly when `v` is tangent at `f x`.
* `TauCeti.hasFDerivAt_normalizedAdaptedLocalAddition_zero`: where `J_q` is invertible,
  `v ↦ A(q, v)` has derivative the identity at `0`.
* `TauCeti.normalizedAdaptedLocalAddition_of_retract`: at a point `f x` of the submanifold,
  `J_{f x}` is the identity and `A(f x, ·) = B(f x, ·)`, so `A` is adapted to the submanifold in
  the same sense (`TauCeti.eventually_normalizedAdaptedLocalAddition_mem_image_iff`).
* `TauCeti.exists_isOpen_contDiffOn_adaptedLocalAddition`: when `f` is a `C^(n + 1)` immersion and
  `r` is `C^n` on an open set `T` containing its image, `B` is jointly `C^n` on an open set
  containing `T ×ˢ {0}`.
* `TauCeti.exists_localAddition_eventuallyEq_normalizedAdaptedLocalAddition`: for a compact
  submanifold, there is a local addition `A'` on `V`, equal to `A` near the submanifold and to
  `q + v` outside a compact set, for which `(q, v) ↦ (q, A'(q, v))` is a diffeomorphism from
  `univ ×ˢ ball 0 ε` onto an open neighbourhood of the diagonal. This combines the normalization
  of `TauCeti.Analysis.Calculus.FDeriv.NormalizeAtZero`, `J_q` being invertible near the
  submanifold, with the local-addition theorems of
  `TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.LocalAddition`.

Here the retraction is only required near the points considered: a smooth local retraction with
normal displacement exists near every point of an immersion
(`TauCeti.exists_contMDiffOn_normalRetraction`), and normal addition is injective on a tube near
every point (`TauCeti.exists_injOn_isOpen_image_normalTube`). For a compact embedded submanifold,
the nearest-point retraction `TauCeti.exists_contMDiffOn_nearestPoint_retraction_of_injective` is
smooth with normal displacement on a whole tube.

## References

* A. Kriegl and P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys
  and Monographs 53, American Mathematical Society, 1997, Section 42.4 (local additions and the
  charts they give on spaces of maps).
-/

public section

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : WithTop ℕ∞} {f : M → V} {r : V → M}

variable (I) in
/-- The **adapted local addition** for the submanifold `f` and a retraction `r` onto it:
`B(q, v) = f y' + P_N(y') (q - f y + P_N(y) v)`, where `y = r q`, `y' = r (f y + P_T(y) v)`, and
`P_N`, `P_T` are the orthogonal projections onto the normal space of `f` and onto its orthogonal
complement, the tangent space. It is the candidate for a local addition adapted to the
submanifold; the local-addition property itself (a diffeomorphism onto a neighbourhood of the
diagonal after normalization) is not established here. -/
def adaptedLocalAddition (f : M → V) (r : V → M) (q v : V) : V :=
  let y := r q
  let y' := r (f y + (normalSubspace I f y)ᗮ.starProjection v)
  f y' + (normalSubspace I f y').starProjection (q - f y + (normalSubspace I f y).starProjection v)

/-- The defining formula of the adapted local addition. -/
theorem adaptedLocalAddition_apply (q v : V) :
    adaptedLocalAddition I f r q v =
      f (r (f (r q) + (normalSubspace I f (r q))ᗮ.starProjection v)) +
        (normalSubspace I f
            (r (f (r q) + (normalSubspace I f (r q))ᗮ.starProjection v))).starProjection
          (q - f (r q) + (normalSubspace I f (r q)).starProjection v) :=
  (rfl)

/-- The adapted local addition of the zero vector is the identity, at every point `q` such that `r`
fixes the base point `r q` (`r (f (r q)) = r q`) and whose normal displacement from the
submanifold is normal there. -/
theorem adaptedLocalAddition_zero {q : V} (hrq : r (f (r q)) = r q)
    (hq : q - f (r q) ∈ normalSubspace I f (r q)) : adaptedLocalAddition I f r q 0 = q := by
  simp [adaptedLocalAddition, hrq, Submodule.starProjection_eq_self_iff.mpr hq]

/-- At a point `f x` of the submanifold fixed by the retraction, the adapted local addition is
`B(f x, v) = f y' + P_N(y') (P_N(x) v)`, where `y' = r (f x + P_T(x) v)`. -/
theorem adaptedLocalAddition_apply_of_retract {x : M} (hrx : r (f x) = x) (v : V) :
    adaptedLocalAddition I f r (f x) v =
      f (r (f x + (normalSubspace I f x)ᗮ.starProjection v)) +
        (normalSubspace I f (r (f x + (normalSubspace I f x)ᗮ.starProjection v))).starProjection
          ((normalSubspace I f x).starProjection v) := by
  rw [adaptedLocalAddition_apply, hrx, sub_self, zero_add]

/-- Along a tangent vector `v` at a point `f x` of the submanifold, the adapted local addition is
the retraction of the straight addition: `B(f x, v) = f (r (f x + v))`. In particular it lies on
the submanifold. -/
theorem adaptedLocalAddition_of_mem_orthogonal {x : M} (hrx : r (f x) = x) {v : V}
    (hv : v ∈ (normalSubspace I f x)ᗮ) :
    adaptedLocalAddition I f r (f x) v = f (r (f x + v)) := by
  have h0 : (normalSubspace I f x).starProjection v = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff _).mpr hv
  rw [adaptedLocalAddition_apply_of_retract hrx, h0, map_zero, add_zero,
    Submodule.starProjection_eq_self_iff.mpr hv]

variable (I) in
/-- The **normalized adapted local addition** `A(q, v) = B(q, J_q⁻¹ v)`, where `B` is the adapted
local addition `TauCeti.adaptedLocalAddition` and `J_q` is the derivative of `v ↦ B(q, v)` at `0`.
Where `J_q` is invertible, `v ↦ A(q, v)` has derivative the identity at `0`; at the points of the
submanifold `J_q` is already the identity, and `A` agrees with `B` there. -/
def normalizedAdaptedLocalAddition (f : M → V) (r : V → M) (q v : V) : V :=
  adaptedLocalAddition I f r q ((fderiv ℝ (adaptedLocalAddition I f r q) 0).inverse v)

/-- The defining formula of the normalized adapted local addition. -/
theorem normalizedAdaptedLocalAddition_apply (q v : V) :
    normalizedAdaptedLocalAddition I f r q v =
      adaptedLocalAddition I f r q ((fderiv ℝ (adaptedLocalAddition I f r q) 0).inverse v) :=
  (rfl)

/-- The normalized adapted local addition of the zero vector is the identity, at every point `q`
such that `r` fixes the base point `r q` and whose normal displacement from the submanifold is
normal there. -/
theorem normalizedAdaptedLocalAddition_zero {q : V} (hrq : r (f (r q)) = r q)
    (hq : q - f (r q) ∈ normalSubspace I f (r q)) :
    normalizedAdaptedLocalAddition I f r q 0 = q := by
  rw [normalizedAdaptedLocalAddition_apply, map_zero, adaptedLocalAddition_zero hrq hq]

/-- Where the derivative `J_q` of `v ↦ B(q, v)` at `0` is invertible, the normalized adapted local
addition `v ↦ A(q, v)` has derivative the identity at `0`. -/
theorem hasFDerivAt_normalizedAdaptedLocalAddition_zero {q : V}
    (h : (fderiv ℝ (adaptedLocalAddition I f r q) 0).IsInvertible) :
    HasFDerivAt (normalizedAdaptedLocalAddition I f r q) (ContinuousLinearMap.id ℝ V) 0 :=
  hasFDerivAt_comp_inverse_fderiv_zero h

section Smooth

variable [I.Boundaryless]

/-- The adapted local addition is jointly `C^n` at `(q, v)` when `f` is a `C^(n + 1)` immersion
and `r` is `C^n` at `q` and at the moved base point `f (r q) + P_T(r q) v`, the smoothness and
immersion conditions on `f` being needed only at the images of these two points under `r`. -/
theorem contDiffAt_adaptedLocalAddition [IsManifold I (n + 1) M] {q v : V}
    (hfq : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f (r q))
    (hfw : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f
      (r (f (r q) + (normalSubspace I f (r q))ᗮ.starProjection v)))
    (himmq : Injective (mfderiv I 𝓘(ℝ, V) f (r q)))
    (himmw : Injective (mfderiv I 𝓘(ℝ, V) f
      (r (f (r q) + (normalSubspace I f (r q))ᗮ.starProjection v))))
    (hrq : ContMDiffAt 𝓘(ℝ, V) I n r q)
    (hrw : ContMDiffAt 𝓘(ℝ, V) I n r (f (r q) + (normalSubspace I f (r q))ᗮ.starProjection v)) :
    ContDiffAt ℝ n (fun p : V × V ↦ adaptedLocalAddition I f r p.1 p.2) (q, v) := by
  have hg {q : V} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f (r q))
      (h : ContMDiffAt 𝓘(ℝ, V) I n r q) : ContDiffAt ℝ n (f ∘ r) q :=
    contMDiffAt_iff_contDiffAt.mp ((hf.of_le le_self_add).comp q h)
  have hNq := contDiffAt_normalSubspace_starProjection_comp hfq himmq hrq
  have hT : ContDiffAt ℝ n (fun q ↦ (normalSubspace I f (r q))ᗮ.starProjection) q :=
    contDiffAt_normalSubspace_orthogonal_starProjection_comp hfq himmq hrq
  have hW : ContDiffAt ℝ n
      (fun p : V × V ↦ f (r p.1) + (normalSubspace I f (r p.1))ᗮ.starProjection p.2) (q, v) :=
    ((hg hfq hrq).comp (q, v) contDiffAt_fst).add ((hT.comp (q, v) contDiffAt_fst).clm_apply
      contDiffAt_snd)
  exact ((hg hfw hrw).comp (q, v) hW).add
    (((contDiffAt_normalSubspace_starProjection_comp hfw himmw hrw).comp (q, v) hW).clm_apply
      ((contDiffAt_fst.sub ((hg hfq hrq).comp (q, v) contDiffAt_fst)).add
        ((hNq.comp (q, v) contDiffAt_fst).clm_apply contDiffAt_snd)))

/-- At a point `f x` of the submanifold, the derivative in the vector variable of the adapted
local addition at the zero vector is the identity. -/
theorem hasFDerivAt_adaptedLocalAddition [IsManifold I (n + 1) M]
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x) (hn : 1 ≤ n)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) (hr : ContMDiffAt 𝓘(ℝ, V) I n r (f x))
    (hrx : r (f x) = x)
    (hnormal : ∀ᶠ q in 𝓝 (f x), q - f (r q) ∈ normalSubspace I f (r q)) :
    HasFDerivAt (adaptedLocalAddition I f r (f x)) (ContinuousLinearMap.id ℝ V) 0 := by
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  set P := (normalSubspace I f x).starProjection
  set T := (normalSubspace I f x)ᗮ.starProjection
  have hB : adaptedLocalAddition I f r (f x) =
      fun v ↦ (f ∘ r) (f x + T v) + (normalSubspace I f (r (f x + T v))).starProjection (P v) :=
    funext (adaptedLocalAddition_apply_of_retract hrx)
  rw [hB]
  have hw : HasFDerivAt (fun v ↦ f x + T v) T 0 := T.hasFDerivAt.const_add (f x)
  have hw0 : f x + T 0 = f x := by simp
  have hg : HasFDerivAt (f ∘ r) T (f x + T 0) := by
    rw [hw0]
    exact hasFDerivAt_comp_of_eventually_sub_mem_normalSubspace hf hn himm hr hrx hnormal
  have hN :
      DifferentiableAt ℝ (fun q ↦ (normalSubspace I f (r q)).starProjection) (f x + T 0) := by
    rw [hw0]
    exact (contDiffAt_normalSubspace_starProjection_comp_of_retract hf himm hr
      hrx).differentiableAt hn0
  refine ((hg.comp 0 hw).add ((hN.hasFDerivAt.comp 0 hw).clm_apply P.hasFDerivAt)).congr_fderiv
    (ContinuousLinearMap.ext fun h ↦ ?_)
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, map_zero, add_zero, hrx,
    ContinuousLinearMap.coe_id', id_eq]
  rw [Submodule.starProjection_starProjection_apply, Submodule.starProjection_starProjection_apply,
    add_comm]
  exact Submodule.starProjection_add_starProjection_orthogonal h

/-- Let normal addition `(y, ν) ↦ f y + ν` be injective on the normal vectors of length less than
`δ` at the points of a neighbourhood `W` of `x`. Then, for every small enough vector `v`, the
adapted local addition `B(f x, v)` lies in `f '' W` exactly when `v` is tangent to the submanifold
at `f x`, that is, orthogonal to its normal space. -/
theorem eventually_adaptedLocalAddition_mem_image_iff [IsManifold I (n + 1) M]
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) (hr : ContMDiffAt 𝓘(ℝ, V) I n r (f x))
    (hrx : r (f x) = x) {W : Set M} (hW : W ∈ 𝓝 x) {δ : ℝ} (hδ : 0 < δ)
    (hinj : InjOn (fun p : M × V ↦ f p.1 + p.2) {p | p.1 ∈ W ∧ p ∈ normalTube I f δ}) :
    ∀ᶠ v in 𝓝 (0 : V), adaptedLocalAddition I f r (f x) v ∈ f '' W ↔
      v ∈ (normalSubspace I f x)ᗮ := by
  set P := (normalSubspace I f x).starProjection
  set T := (normalSubspace I f x)ᗮ.starProjection
  set N := fun q ↦ (normalSubspace I f (r q)).starProjection
  have hB (v : V) :
      adaptedLocalAddition I f r (f x) v = f (r (f x + T v)) + N (f x + T v) (P v) :=
    adaptedLocalAddition_apply_of_retract hrx v
  have hwc : ContinuousAt (fun v : V ↦ f x + T v) 0 := (T.continuous.const_add (f x)).continuousAt
  have hw0 : f x + T 0 = f x := by simp
  have hNc : ContinuousAt (fun v ↦ N (f x + T v)) 0 :=
    (contDiffAt_normalSubspace_starProjection_comp_of_retract hf himm hr
      hrx).continuousAt.comp_of_eq hwc hw0
  have hrc : ContinuousAt (fun v ↦ r (f x + T v)) 0 := hr.continuousAt.comp_of_eq hwc hw0
  have hnc : ContinuousAt (fun v ↦ N (f x + T v) (P v)) 0 :=
    hNc.clm_apply P.continuous.continuousAt
  have hN0 : N (f x + T 0) = P := by simp [N, P, hrx]
  have hr0 : r (f x + T 0) = x := by simp [hrx]
  have hnP0 : N (f x + T 0) (P 0) = 0 := by simp
  filter_upwards [hrc.preimage_mem_nhds (by rwa [hr0]),
    hnc.preimage_mem_nhds (by rw [hnP0]; exact Metric.ball_mem_nhds 0 hδ),
    hNc.preimage_mem_nhds (by rw [hN0]; exact Metric.ball_mem_nhds P one_pos)]
    with v hvW hvδ hv1
  rw [hB, ← Submodule.starProjection_apply_eq_zero_iff]
  constructor
  · rintro ⟨z, hz, hfz⟩
    have hmem : N (f x + T v) (P v) ∈ normalSubspace I f (r (f x + T v)) :=
      Submodule.starProjection_apply_mem _ _
    have heq := hinj (x₁ := (z, 0)) (x₂ := (r (f x + T v), N (f x + T v) (P v)))
      ⟨hz, mem_normalTube.mpr ⟨zero_mem _, by simpa using hδ⟩⟩
      ⟨hvW, mem_normalTube.mpr ⟨hmem, by simpa using hvδ⟩⟩ (by simpa using hfz)
    have hNPv : N (f x + T v) (P v) = 0 := (congrArg Prod.snd heq).symm
    -- `P v` is normal and `N (f x + T v)` is close to `P`, so it cannot kill a nonzero `P v`.
    by_contra hPv
    have hle : ‖P v‖ ≤ ‖P - N (f x + T v)‖ * ‖P v‖ := by
      calc ‖P v‖ = ‖(P - N (f x + T v)) (P v)‖ := by
            rw [sub_apply, hNPv, sub_zero, Submodule.starProjection_starProjection_apply]
        _ ≤ ‖P - N (f x + T v)‖ * ‖P v‖ := ContinuousLinearMap.le_opNorm _ _
    have hlt : ‖P - N (f x + T v)‖ < 1 := by
      simpa [dist_eq_norm, norm_sub_rev] using hv1
    have hpos : 0 < ‖P v‖ := norm_pos_iff.mpr hPv
    nlinarith
  · intro hPv
    exact ⟨r (f x + T v), hvW, by rw [hPv, map_zero, add_zero]⟩

/-- At a point `f x` of the submanifold, the normalized adapted local addition is the adapted
local addition, since there the derivative of `v ↦ B(f x, v)` at `0` is the identity. -/
theorem normalizedAdaptedLocalAddition_of_retract [IsManifold I (n + 1) M]
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x) (hn : 1 ≤ n)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) (hr : ContMDiffAt 𝓘(ℝ, V) I n r (f x))
    (hrx : r (f x) = x)
    (hnormal : ∀ᶠ q in 𝓝 (f x), q - f (r q) ∈ normalSubspace I f (r q)) :
    normalizedAdaptedLocalAddition I f r (f x) = adaptedLocalAddition I f r (f x) := by
  ext v
  rw [normalizedAdaptedLocalAddition_apply,
    (hasFDerivAt_adaptedLocalAddition hf hn himm hr hrx hnormal).fderiv,
    ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]

/-- **The normalized adapted local addition is adapted to the submanifold.** In the setting of
`TauCeti.eventually_adaptedLocalAddition_mem_image_iff`, for every small enough vector `v`, the
point `A(f x, v)` lies in `f '' W` exactly when `v` is tangent to the submanifold at `f x`. -/
theorem eventually_normalizedAdaptedLocalAddition_mem_image_iff [IsManifold I (n + 1) M]
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x) (hn : 1 ≤ n)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) (hr : ContMDiffAt 𝓘(ℝ, V) I n r (f x))
    (hrx : r (f x) = x)
    (hnormal : ∀ᶠ q in 𝓝 (f x), q - f (r q) ∈ normalSubspace I f (r q))
    {W : Set M} (hW : W ∈ 𝓝 x) {δ : ℝ} (hδ : 0 < δ)
    (hinj : InjOn (fun p : M × V ↦ f p.1 + p.2) {p | p.1 ∈ W ∧ p ∈ normalTube I f δ}) :
    ∀ᶠ v in 𝓝 (0 : V), normalizedAdaptedLocalAddition I f r (f x) v ∈ f '' W ↔
      v ∈ (normalSubspace I f x)ᗮ := by
  rw [normalizedAdaptedLocalAddition_of_retract hf hn himm hr hrx hnormal]
  exact eventually_adaptedLocalAddition_mem_image_iff hf himm hr hrx hW hδ hinj

/-- If `f` is a `C^(n + 1)` immersion and the retraction `r` is `C^n` on an open set `T`
containing the image of `f`, then the adapted local addition is jointly `C^n` on an open set
containing every `(q, 0)` with `q ∈ T`. -/
theorem exists_isOpen_contDiffOn_adaptedLocalAddition [IsManifold I (n + 1) M]
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f) (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    {T : Set V} (hT : IsOpen T) (hfT : range f ⊆ T) (hr : ContMDiffOn 𝓘(ℝ, V) I n r T) :
    ∃ s : Set (V × V), IsOpen s ∧ (∀ q ∈ T, (q, 0) ∈ s) ∧
      ContDiffOn ℝ n (uncurry (adaptedLocalAddition I f r)) s := by
  -- `B(q, v)` is `C^n` wherever both `q` and the moved base point `g (q, v)` lie in `T`.
  set g : V × V → V := fun p ↦ f (r p.1) + (normalSubspace I f (r p.1))ᗮ.starProjection p.2
  have hrT : ∀ q ∈ T, ContMDiffAt 𝓘(ℝ, V) I n r q := fun q hq ↦ hr.contMDiffAt (hT.mem_nhds hq)
  have hP : ∀ q ∈ T, ContinuousAt (fun q ↦ (normalSubspace I f (r q))ᗮ.starProjection) q :=
    fun q hq ↦ (contDiffAt_normalSubspace_orthogonal_starProjection_comp (hf (r q)) (himm (r q))
      (hrT q hq)).continuousAt
  have hg : ContinuousOn g (T ×ˢ univ) := fun p hp ↦
    (((hf.continuous.continuousAt.comp (hrT p.1 hp.1).continuousAt).comp continuousAt_fst).add
      (((hP p.1 hp.1).comp continuousAt_fst).clm_apply continuousAt_snd)).continuousWithinAt
  refine ⟨(T ×ˢ univ) ∩ g ⁻¹' T, hg.isOpen_inter_preimage (hT.prod isOpen_univ) hT,
    fun q hq ↦ ⟨⟨hq, mem_univ _⟩, by simpa [g] using hfT (mem_range_self (r q))⟩, fun p hp ↦ ?_⟩
  exact (contDiffAt_adaptedLocalAddition (hf _) (hf _) (himm _) (himm _) (hrT _ hp.1.1)
    (hrT _ hp.2)).contDiffWithinAt

/-- **The normalized adapted local addition of a compact submanifold is a local addition.** Let
`f` be a `C^(n + 2)` immersion of a compact boundaryless manifold, `1 ≤ n ≤ ∞`, and let `r` be a
`C^(n + 1)` retraction onto it with normal displacement on an open set `T` containing its image.
Then there are `A` and `ε > 0` such that `A` is a local addition on all of `V`: it is jointly `C^n`
on `univ ×ˢ ball 0 ε`, `A q 0 = q` and `v ↦ A q v` has derivative the identity at `0` for every
`q`, and `(q, v) ↦ (q, A q v)` is injective and a `C^n` local diffeomorphism on `univ ×ˢ ball 0 ε`,
hence a diffeomorphism onto an open neighbourhood of the diagonal. Near the image of `f` it is the
normalized adapted local addition, and outside a compact set it is `(q, v) ↦ q + v`.

So, by `TauCeti.eventually_normalizedAdaptedLocalAddition_mem_image_iff`, at the points of the
submanifold `A` stays on the submanifold exactly along tangent vectors. -/
theorem exists_localAddition_eventuallyEq_normalizedAdaptedLocalAddition [CompactSpace M]
    [FiniteDimensional ℝ V] [IsManifold I (n + 1 + 1) M]
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1 + 1) f) (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hn : 1 ≤ n) (hn' : n ≤ ∞) {T : Set V} (hT : IsOpen T) (hfT : range f ⊆ T)
    (hr : ContMDiffOn 𝓘(ℝ, V) I (n + 1) r T) (hrf : ∀ x, r (f x) = x)
    (hnormal : ∀ q ∈ T, q - f (r q) ∈ normalSubspace I f (r q)) :
    ∃ A : V → V → V, ∃ ε > 0, ContDiffOn ℝ n (uncurry A) (univ ×ˢ Metric.ball 0 ε) ∧
      (∀ q, A q 0 = q) ∧ (∀ q, HasFDerivAt (A q) (ContinuousLinearMap.id ℝ V) 0) ∧
      (∀ᶠ q in 𝓝ˢ (range f), A q = normalizedAdaptedLocalAddition I f r q) ∧
      (∀ᶠ q in cocompact V, A q = (q + ·)) ∧
      InjOn (fun p : V × V ↦ (p.1, A p.1 p.2)) (univ ×ˢ Metric.ball 0 ε) ∧
      IsLocalDiffeomorphOn 𝓘(ℝ, V × V) 𝓘(ℝ, V × V) n (fun p : V × V ↦ (p.1, A p.1 p.2))
        (univ ×ˢ Metric.ball 0 ε) := by
  obtain ⟨s, hs, hTs, hB⟩ := exists_isOpen_contDiffOn_adaptedLocalAddition hf himm hT hfT hr
  obtain ⟨s', hs', hs's, hs'J, hA⟩ := exists_isOpen_contDiffOn_comp_inverse_fderiv_zero hB hs
  -- On the image of `f` the derivative of `v ↦ B(q, v)` at `0` is the identity, so the points
  -- `q ∈ T` with `(q, 0) ∈ s'` form an open neighbourhood of the image.
  have hJf : ∀ x, (fderiv ℝ (adaptedLocalAddition I f r (f x)) 0).IsInvertible := fun x ↦ by
    have hx : T ∈ 𝓝 (f x) := hT.mem_nhds (hfT (mem_range_self x))
    rw [(hasFDerivAt_adaptedLocalAddition (hf x) le_add_self (himm x) (hr.contMDiffAt hx)
      (hrf x) (eventually_of_mem hx hnormal)).fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ V, rfl⟩
  have hT' : T ∩ {q | (q, 0) ∈ s'} ∈ 𝓝ˢ (range f) := by
    refine (hT.inter (hs'.preimage (continuous_id.prodMk continuous_const))).mem_nhdsSet.2 ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨hfT (mem_range_self x), hs's _ (hTs _ (hfT (mem_range_self x))) (hJf x)⟩
  exact (isCompact_range hf.continuous).exists_localAddition_eventuallyEq hA hs' hn hn'
    (mem_of_superset hT' fun q hq ↦ ⟨hq.2, normalizedAdaptedLocalAddition_zero (hrf _)
      (hnormal q hq.1), hasFDerivAt_normalizedAdaptedLocalAddition_zero (hs'J _ hq.2)⟩)

end Smooth

end TauCeti
