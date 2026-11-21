/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
public import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
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

`B` is the candidate for a local addition in the sense of Kriegl and Michor adapted to the
submanifold. A local addition gives charts on spaces of maps, and an adapted one would give charts
on maps whose boundary values lie on the submanifold, the boundary condition being linear in the
chart, as for discs with boundary on a Lagrangian or totally real submanifold. This file does not
establish the local-addition property, that `(q, v) ↦ (q, B(q, J_q⁻¹ v))` with
`J_q = D_v B(q, 0)` is a diffeomorphism onto a neighbourhood of the diagonal, nor any charts on
spaces of maps. It proves the basic properties of `B`.

* `TauCeti.adaptedLocalAddition_zero`: `B(q, 0) = q`.
* `TauCeti.adaptedLocalAddition_apply_of_retract`: at a point `f x` fixed by the retraction,
  `B(f x, v) = f y' + P_N(y') (P_N(x) v)`, where `y' = r (f x + P_T(x) v)`.
* `TauCeti.adaptedLocalAddition_of_mem_orthogonal`: along a tangent vector `v` at `f x`,
  `B(f x, v) = f (r (f x + v))` lies on the submanifold.
* `TauCeti.contDiffAt_adaptedLocalAddition`: `B` is jointly `C^n` when `f` is `C^(n + 1)` and `r`
  is `C^n`, by the smoothness of the normal projections along the retraction,
  `TauCeti.contDiffAt_starProjection_normalSubspace_comp`.
* `TauCeti.hasFDerivAt_comp_of_eventually_sub_mem_normalSubspace`: the differential of `f ∘ r` at
  a point `f x` of the submanifold is the tangential projection `P_T(x)`.
* `TauCeti.hasFDerivAt_adaptedLocalAddition`: at a point `f x` of the submanifold, the derivative
  of `v ↦ B(f x, v)` at `0` is the identity.
* `TauCeti.eventually_adaptedLocalAddition_mem_image_iff`: on a tubular neighbourhood on which
  normal addition `(y, ν) ↦ f y + ν` is injective at the points of a neighbourhood `W` of `x`,
  `B(f x, v)` lies in `f '' W`, for small `v`, exactly when `v` is tangent at `f x`.

Here the retraction is only required near the points considered: a smooth local retraction with
normal displacement exists near every point of an immersion
(`TauCeti.exists_contMDiffOn_normalRetraction`), and normal addition is injective on a tube near
every point (`TauCeti.exists_injOn_isOpen_image_normalTube`).

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

/-- An orthogonal projection is idempotent, evaluated at a vector. -/
private theorem starProjection_starProjection (K : Submodule ℝ V) [K.HasOrthogonalProjection]
    (v : V) : K.starProjection (K.starProjection v) = K.starProjection v :=
  Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem v)

section Smooth

variable [I.Boundaryless]

/-- The orthogonal projection onto the normal space of an immersion `f` at `r q` is `C^n` in `q`
at a point where `r` is `C^n`, when `f` is `C^(n + 1)` at `r q`. -/
theorem contDiffAt_starProjection_normalSubspace_comp [IsManifold I (n + 1) M] {q : V}
    (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f (r q))
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f (r q))) (hr : ContMDiffAt 𝓘(ℝ, V) I n r q) :
    ContDiffAt ℝ n (fun q ↦ (normalSubspace I f (r q)).starProjection) q :=
  contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_normalSubspace_starProjection hf himm).comp q hr)

/-- At a point `f x` whose base point `x` is fixed by the retraction `r`, the orthogonal projection
onto the normal space of an immersion `f` at `r q` is `C^n` in `q` at `f x`, when `f` is `C^(n + 1)`
at `x` and `r` is `C^n` at `f x`. -/
theorem contDiffAt_starProjection_normalSubspace_comp_of_retract [IsManifold I (n + 1) M]
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x) (himm : Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hr : ContMDiffAt 𝓘(ℝ, V) I n r (f x)) (hrx : r (f x) = x) :
    ContDiffAt ℝ n (fun q ↦ (normalSubspace I f (r q)).starProjection) (f x) :=
  contDiffAt_starProjection_normalSubspace_comp (by rwa [hrx]) (by rwa [hrx]) hr

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
  have hNq := contDiffAt_starProjection_normalSubspace_comp hfq himmq hrq
  have hT : ContDiffAt ℝ n (fun q ↦ (normalSubspace I f (r q))ᗮ.starProjection) q := by
    refine ((contDiffAt_const (c := (1 : V →L[ℝ] V))).sub hNq).congr_of_eventuallyEq
      (Eventually.of_forall fun q ↦ ?_)
    exact Submodule.starProjection_orthogonal' _
  have hW : ContDiffAt ℝ n
      (fun p : V × V ↦ f (r p.1) + (normalSubspace I f (r p.1))ᗮ.starProjection p.2) (q, v) :=
    ((hg hfq hrq).comp (q, v) contDiffAt_fst).add ((hT.comp (q, v) contDiffAt_fst).clm_apply
      contDiffAt_snd)
  exact ((hg hfw hrw).comp (q, v) hW).add
    (((contDiffAt_starProjection_normalSubspace_comp hfw himmw hrw).comp (q, v) hW).clm_apply
      ((contDiffAt_fst.sub ((hg hfq hrq).comp (q, v) contDiffAt_fst)).add
        ((hNq.comp (q, v) contDiffAt_fst).clm_apply contDiffAt_snd)))

/-- Let `r` be a `C^n` retraction, `n ≥ 1`, onto a map `f` near `f x`, with normal displacement,
where `f` is `C^(n + 1)` and immersive at `x`. Then the differential of `f ∘ r` at `f x` is the
orthogonal projection onto the tangent space of the immersed manifold at `f x`. -/
theorem hasFDerivAt_comp_of_eventually_sub_mem_normalSubspace [IsManifold I (n + 1) M]
    {x : M} (hf : ContMDiffAt I 𝓘(ℝ, V) (n + 1) f x) (hn : 1 ≤ n)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x)) (hr : ContMDiffAt 𝓘(ℝ, V) I n r (f x))
    (hrx : r (f x) = x)
    (hnormal : ∀ᶠ q in 𝓝 (f x), q - f (r q) ∈ normalSubspace I f (r q)) :
    HasFDerivAt (f ∘ r) (normalSubspace I f x)ᗮ.starProjection (f x) := by
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  have hfx : MDifferentiableAt I 𝓘(ℝ, V) f (r (f x)) := by
    rw [hrx]
    exact hf.mdifferentiableAt (by simp)
  have hrd : MDifferentiableAt 𝓘(ℝ, V) I r (f x) := hr.mdifferentiableAt hn0
  have hg : DifferentiableAt ℝ (f ∘ r) (f x) :=
    mdifferentiableAt_iff_differentiableAt.mp (hfx.comp _ hrd)
  have hN :=
    (contDiffAt_starProjection_normalSubspace_comp_of_retract hf himm hr hrx).differentiableAt hn0
  set D := fderiv ℝ (f ∘ r) (f x)
  -- `D` takes values in the tangent space, since it factors through the differential of `f`.
  have hrange (h : V) : D h ∈ (normalSubspace I f x)ᗮ := by
    have hD : D h = mfderiv I 𝓘(ℝ, V) f (r (f x)) (mfderiv 𝓘(ℝ, V) I r (f x) h) :=
      (mvfderiv_eq_fderiv_apply (f ∘ r) (f x) h).symm.trans
        ((mvfderiv_apply_eq_mfderiv_apply (f ∘ r) (f x) h).trans
          (mfderiv_comp_apply (f x) hfx hrd h))
    have : D h ∈ (normalSubspace I f (r (f x)))ᗮ := fun u hu ↦ by
      rw [hD]
      exact mem_normalSubspace_iff.mp hu _
    rwa [hrx] at this
  -- Differentiating `P_N(r q) (q - f (r q)) = q - f (r q)` shows that `h - D h` is normal.
  have hzero : (fun q ↦ (normalSubspace I f (r q)).starProjection (q - (f ∘ r) q) -
      (q - (f ∘ r) q)) =ᶠ[𝓝 (f x)] fun _ ↦ 0 := by
    filter_upwards [hnormal] with q hq
    rw [Function.comp_apply, Submodule.starProjection_eq_self_iff.mpr hq, sub_self]
  have hderiv := ((hN.hasFDerivAt.clm_apply ((hasFDerivAt_id _).sub hg.hasFDerivAt)).sub
    ((hasFDerivAt_id _).sub hg.hasFDerivAt)).unique
    ((hasFDerivAt_const 0 (f x)).congr_of_eventuallyEq hzero)
  have hnormalD (h : V) : h - D h ∈ normalSubspace I f x := by
    -- Evaluated at `h`, the derivative is `P_N(x) (h - D h) + N' h (f x - (f ∘ r) (f x)) -
    -- (h - D h)`, where `N' h` is the derivative of `q ↦ P_N(r q)` along `h`. The middle term
    -- vanishes, since `(f ∘ r) (f x) = f x`.
    have hev : (normalSubspace I f (r (f x))).starProjection (h - D h) +
        fderiv ℝ (fun q ↦ (normalSubspace I f (r q)).starProjection) (f x) h
          (f x - (f ∘ r) (f x)) - (h - D h) = 0 :=
      DFunLike.congr_fun hderiv h
    have hP : (normalSubspace I f x).starProjection (h - D h) = h - D h := by
      rwa [Function.comp_apply, hrx, sub_self, map_zero, add_zero, sub_eq_zero] at hev
    exact Submodule.starProjection_eq_self_iff.mp hP
  refine hg.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
  calc D h = (normalSubspace I f x)ᗮ.starProjection (D h) +
        (normalSubspace I f x)ᗮ.starProjection (h - D h) := by
        rw [Submodule.starProjection_eq_self_iff.mpr (hrange h),
          (Submodule.starProjection_apply_eq_zero_iff _).mpr
            (Submodule.le_orthogonal_orthogonal _ (hnormalD h)), add_zero]
    _ = (normalSubspace I f x)ᗮ.starProjection h := by rw [← map_add, add_sub_cancel]

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
    exact (contDiffAt_starProjection_normalSubspace_comp_of_retract hf himm hr
      hrx).differentiableAt hn0
  refine ((hg.comp 0 hw).add ((hN.hasFDerivAt.comp 0 hw).clm_apply P.hasFDerivAt)).congr_fderiv
    (ContinuousLinearMap.ext fun h ↦ ?_)
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, map_zero, add_zero, hrx,
    ContinuousLinearMap.coe_id', id_eq]
  rw [starProjection_starProjection, starProjection_starProjection, add_comm]
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
    (contDiffAt_starProjection_normalSubspace_comp_of_retract hf himm hr
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
            rw [sub_apply, hNPv, sub_zero, starProjection_starProjection]
        _ ≤ ‖P - N (f x + T v)‖ * ‖P v‖ := ContinuousLinearMap.le_opNorm _ _
    have hlt : ‖P - N (f x + T v)‖ < 1 := by
      simpa [dist_eq_norm, norm_sub_rev] using hv1
    have hpos : 0 < ‖P v‖ := norm_pos_iff.mpr hPv
    nlinarith
  · intro hPv
    exact ⟨r (f x + T v), hvW, by rw [hPv, map_zero, add_zero]⟩

end Smooth

end TauCeti
