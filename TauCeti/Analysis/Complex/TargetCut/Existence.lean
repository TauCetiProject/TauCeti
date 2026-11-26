/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.TargetCut
public import TauCeti.LinearAlgebra.AffineSpace.MarkingStabilizer
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
import TauCeti.Analysis.Calculus.Sard.EqualDimension
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Existence of stabilizing target cuts

A sphere component `u : ℂ → M` of a pseudoholomorphic curve with a single special point at `∞` is
stabilized by the full preimage `u⁻¹(D)` of a *target cut* `D`, a closed set of the target that
`u` meets transversally at each point of `u⁻¹(D)` (`TauCeti.IsTransverseCutAt`). That preimage is
finite (`TauCeti.finite_preimage_of_isTransverseCutAt`), and as soon as it has two points the
isotropy of `u` is finite (`TauCeti.card_markedIsotropy_dvd_factorial`). This file proves that such
cuts exist for every component of rank two somewhere, that is, with a point `z₀` at which the
derivative of `u` is injective. For a pseudoholomorphic map the derivative is complex linear, so it
is injective wherever it is nonzero: every nonconstant pseudoholomorphic sphere has rank two
somewhere.

Let `M` be a finite-dimensional Hausdorff `C¹` manifold, possibly with boundary or corners, and let
`u : ℂ → M` be `C¹` with injective derivative at `z₀`. For every point `y ≠ u z₀`, every `n` and
every `ε > 0` there is a closed set `D ⊆ M`, not containing `y`, which `u` meets transversally at
every point of `u⁻¹(D)` and which `u` meets in at least `n` points within `ε` of `z₀`
(`TauCeti.exists_isTransverseCutAt_of_injective_mfderiv`). When `u` has a limit `y` at `∞` the
full preimage of such a cut is finite, and with `n = 2` it stabilizes `u`: its points together with
`∞` make the sphere stable, and the isotropy of `u` is finite
(`TauCeti.exists_isTransverseCutAt_finite_nontrivial_preimage`,
`TauCeti.finite_markedIsotropy_of_injective_mfderiv`).

The cut lies in one chart `φ = extChartAt I (u z₀)` of `M` around `u z₀`. Choose a real linear
map `ℓ : E → ℂ` which is a left inverse of the derivative of `φ ∘ u` at `z₀`, so that
`f = ℓ ∘ φ ∘ u` is a local diffeomorphism of `ℂ` near `z₀`. For a finite set `C` of values and a
radius `r` the cut is the image under `φ⁻¹` of the compact set of points `v` of the chart with
`‖v - φ (u z₀)‖ ≤ r` and `ℓ v ∈ C`. Three choices make it a transverse cut.

* **Regular values.** By Sard's theorem in equal dimensions
  (`TauCeti.dense_setOf_forall_surjective_fderiv`) the values of `f` at whose preimages `f` has
  surjective, hence invertible, derivative are dense. Since `f` maps neighbourhoods of `z₀` onto
  neighbourhoods of `f z₀` (`HasStrictFDerivAt.map_nhds_eq_of_equiv`), there are `n` such values
  taken by `f` close to `z₀`; they are the set `C`. Near a point of `u⁻¹(D)` the cut is then the
  zero set of `ℓ ∘ φ - c` for one `c ∈ C`, and `f - c` has invertible derivative there.
* **The radius.** The points of `u⁻¹(D)` must not lie on the boundary sphere `‖v - φ (u z₀)‖ = r`,
  where the cut is not cut out by a single equation. The candidates for such points are isolated,
  since `f` has invertible derivative there, hence countably many
  (`TauCeti.countable_of_forall_injective_fderiv`), so all but countably many radii avoid them.
* **The point `y`.** The radius is small enough that the inverse of the chart does not take the
  value `y` on the closed ball around `φ (u z₀)`.

No properness of `u` and no limit at `∞` is needed for the existence of the cut; the limit only
enters the finiteness of the full preimage.

## Main results

* `TauCeti.exists_isTransverseCutAt_of_injective_mfderiv`: existence of a transverse target cut
  with at least `n` intersection points near a point of rank two, avoiding a given point.
* `TauCeti.exists_isTransverseCutAt_finite_nontrivial_preimage`: for a sphere with a limit at `∞`,
  a transverse target cut whose full preimage is finite and has at least two points.
* `TauCeti.finite_markedIsotropy_of_injective_mfderiv`: a `C¹` sphere of rank two somewhere with a
  limit at `∞` has finite isotropy.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Section 9.2, on the existence of target
  cuts stabilizing every point of the moduli space.
* K. Cieliebak and K. Mohnke, *Symplectic hypersurfaces and transversality in Gromov–Witten
  theory*, J. Symplectic Geom. 5 (2007), 281–356, on stabilizing domains by the intersection
  points with a hypersurface.
-/

public section

noncomputable section

open Filter Function Metric Set Topology
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The cut of a chart: the image under the inverse of the chart `extChartAt I x₀` of the points `v`
of the model with `‖v - φ x₀‖ ≤ r` and `ℓ v ∈ C`. If the chart is defined on all these points,
then a point lies on the cut exactly when it lies in the chart and its image satisfies these
conditions. -/
private lemma mem_extChartAt_symm_image_iff {x₀ x : M} {ℓ : E →L[ℝ] ℂ} {C : Set ℂ} {r : ℝ}
    (hK : closedBall (extChartAt I x₀ x₀) r ∩ range I ∩ ℓ ⁻¹' C ⊆ (extChartAt I x₀).target) :
    x ∈ (extChartAt I x₀).symm '' (closedBall (extChartAt I x₀ x₀) r ∩ range I ∩ ℓ ⁻¹' C) ↔
      x ∈ (chartAt H x₀).source ∧ dist (extChartAt I x₀ x) (extChartAt I x₀ x₀) ≤ r ∧
        ℓ (extChartAt I x₀ x) ∈ C := by
  rw [PartialEquiv.symm_image_eq_source_inter_preimage _ hK, extChartAt_source]
  simp only [mem_inter_iff, mem_preimage, mem_closedBall]
  refine ⟨fun h ↦ ⟨h.1, h.2.1.1, h.2.2⟩, fun h ↦ ⟨h.1, ⟨h.2.1, ?_⟩, h.2.2⟩⟩
  exact extChartAt_target_subset_range x₀
    ((extChartAt I x₀).map_source (by rw [extChartAt_source]; exact h.1))

/-- The points of a closed ball of radius `r < r₀` in the model range with `ℓ v ∈ C` lie in every
set containing the open ball of radius `r₀` in the model range. -/
private lemma closedBall_inter_range_inter_preimage_subset {c : E} {r r₀ : ℝ} (hr : r < r₀)
    {T : Set E} (hT : ball c r₀ ∩ range I ⊆ T) (ℓ : E →L[ℝ] ℂ) (C : Set ℂ) :
    closedBall c r ∩ range I ∩ ℓ ⁻¹' C ⊆ T :=
  fun _ hv ↦ hT ⟨closedBall_subset_ball hr hv.1.1, hv.1.2⟩

/-- A point of the cut of a chart whose image lies strictly inside the ball, and at which
`ℓ ∘ φ ∘ u` has invertible derivative, is a transverse intersection point of `u` with the cut:
near it the cut is the zero set of `ℓ ∘ φ - c` for the value `c ∈ C` taken there. -/
private lemma isTransverseCutAt_extChartAt_symm_image {u : ℂ → M} {z : ℂ} {x₀ : M}
    {ℓ : E →L[ℝ] ℂ} {C : Set ℂ} (hC : C.Finite) {r : ℝ}
    (hK : closedBall (extChartAt I x₀ x₀) r ∩ range I ∩ ℓ ⁻¹' C ⊆ (extChartAt I x₀).target)
    (hz : u z ∈ (chartAt H x₀).source)
    (hzr : dist (extChartAt I x₀ (u z)) (extChartAt I x₀ x₀) < r)
    (hzC : ℓ (extChartAt I x₀ (u z)) ∈ C) {L : ℂ ≃L[ℝ] ℂ}
    (hL : HasFDerivAt (fun w ↦ ℓ (extChartAt I x₀ (u w))) (L : ℂ →L[ℝ] ℂ) z) :
    IsTransverseCutAt u
      ((extChartAt I x₀).symm '' (closedBall (extChartAt I x₀ x₀) r ∩ range I ∩ ℓ ⁻¹' C)) z := by
  set c := ℓ (extChartAt I x₀ (u z))
  have hφ : ContinuousAt (extChartAt I x₀) (u z) :=
    continuousAt_extChartAt' (by rwa [extChartAt_source])
  refine IsTransverseCutAt.intro (g := fun x ↦ ℓ (extChartAt I x₀ x) - c) ?_ (hL.sub_const c)
  have hC' : (C \ {c})ᶜ ∈ 𝓝 c :=
    ((hC.subset sdiff_subset).isClosed.isOpen_compl).mem_nhds fun h ↦ h.2 rfl
  filter_upwards [(chartAt H x₀).open_source.mem_nhds hz,
    hφ.eventually (isOpen_ball.mem_nhds (mem_ball.2 hzr)),
    (ℓ.continuous.continuousAt.comp hφ).eventually hC'] with x hxs hxr hxC
  rw [mem_extChartAt_symm_image_iff hK, sub_eq_zero]
  exact ⟨fun h ↦ by_contra fun hne ↦ hxC ⟨h.2.2, hne⟩,
    fun h ↦ ⟨hxs, (mem_ball.1 hxr).le, h ▸ hzC⟩⟩

variable [IsManifold I 1 M]

/-- A map `u` into `M` which is differentiable at `z` and sends `z` into the source of a chart `φ`
gives a map `ℓ ∘ φ ∘ u` differentiable at `z`, for every real linear `ℓ : E → ℂ`. -/
private lemma differentiableAt_comp_extChartAt_comp {u : ℂ → M} {z : ℂ} {x₀ : M}
    (hu : MDifferentiableAt 𝓘(ℝ, ℂ) I u z) (hz : u z ∈ (chartAt H x₀).source) (ℓ : E →L[ℝ] ℂ) :
    DifferentiableAt ℝ (fun w ↦ ℓ (extChartAt I x₀ (u w))) z :=
  ℓ.differentiableAt.comp z
    (mdifferentiableAt_iff_differentiableAt.1 ((mdifferentiableAt_extChartAt hz).comp z hu))

/-- Near a point `z₀` at which the derivative of `u` is injective, a real linear map `ℓ` from the
model to `ℂ` turns `u`, read in the chart centred at `u z₀`, into a local diffeomorphism of `ℂ`:
`ℓ ∘ φ ∘ u` has the identity as strict derivative at `z₀`. -/
private lemma exists_hasStrictFDerivAt_extChartAt_comp [FiniteDimensional ℝ E] {u : ℂ → M}
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) {z₀ : ℂ} (hz₀ : Injective (mfderiv 𝓘(ℝ, ℂ) I u z₀)) :
    ∃ ℓ : E →L[ℝ] ℂ, HasStrictFDerivAt (fun w ↦ ℓ (extChartAt I (u z₀) (u w)))
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z₀ := by
  set A := fderiv ℝ (extChartAt I (u z₀) ∘ u) z₀
  -- The chart centred at `u z₀` has the identity as derivative there.
  have hA (v : ℂ) : A v = mfderiv 𝓘(ℝ, ℂ) I u z₀ v := by
    rw [hu.continuous.continuousAt.fderiv_extChartAt_comp_apply
      (mem_extChartAt_source (I := I) (u z₀)), mfderiv_extChartAt_self]
    -- The identity of the tangent space at `u z₀` applied to `mfderiv u z₀ v`; it is not
    -- rewritten by `ContinuousLinearMap.id_apply`, since its codomain is the tangent space of the
    -- model at `extChartAt I (u z₀) (u z₀)`, identified with `E` only definitionally.
    rfl
  have hinj : Injective A := fun a b hab ↦ hz₀ (by rwa [← hA, ← hA])
  obtain ⟨g, hg⟩ :=
    LinearMap.exists_leftInverse_of_injective (A : ℂ →ₗ[ℝ] E) (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : E →L[ℝ] ℂ, ℓ.comp A = ContinuousLinearMap.id ℝ ℂ :=
    ⟨LinearMap.toContinuousLinearMap g,
      ContinuousLinearMap.ext fun w ↦ by simpa using LinearMap.congr_fun hg w⟩
  have hcd : ContDiffAt ℝ 1 (extChartAt I (u z₀) ∘ u) z₀ :=
    contMDiffAt_iff_contDiffAt.1
      ((contMDiffAt_extChartAt' (mem_chart_source H (u z₀))).comp z₀ hu.contMDiffAt)
  have hfd : HasFDerivAt (fun w ↦ ℓ (extChartAt I (u z₀) (u w))) (ℓ.comp A) z₀ :=
    ℓ.hasFDerivAt.comp z₀ (hcd.differentiableAt one_ne_zero).hasFDerivAt
  rw [hℓ] at hfd
  exact ⟨ℓ, (ℓ.contDiff.contDiffAt.comp z₀ hcd).hasStrictFDerivAt hfd one_ne_zero⟩

/-- Let `C` be a finite set of regular values of `f = ℓ ∘ φ ∘ u` on the source of the chart `φ`.
Then for all but countably many radii `r` the cut of the chart of radius `r` and values `C` is met
transversally by `u` at every point of its full preimage: no point of the preimage lies on the
sphere of radius `r`, because the candidates are isolated. -/
private lemma exists_mem_Ioo_forall_isTransverseCutAt {u : ℂ → M}
    (hu : ∀ z, MDifferentiableAt 𝓘(ℝ, ℂ) I u z) {x₀ : M} {ℓ : E →L[ℝ] ℂ} {C : Finset ℂ}
    (hC : ∀ c ∈ C, ∀ z ∈ u ⁻¹' (chartAt H x₀).source, ℓ (extChartAt I x₀ (u z)) = c →
      Surjective (fderiv ℝ (fun w ↦ ℓ (extChartAt I x₀ (u w))) z))
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hr₀K : ball (extChartAt I x₀ x₀) r₀ ∩ range I ⊆ (extChartAt I x₀).target) :
    ∃ r ∈ Ioo (r₀ / 2) r₀, ∀ z ∈ u ⁻¹'
      ((extChartAt I x₀).symm '' (closedBall (extChartAt I x₀ x₀) r ∩ range I ∩ ℓ ⁻¹' C)),
        IsTransverseCutAt u ((extChartAt I x₀).symm ''
          (closedBall (extChartAt I x₀ x₀) r ∩ range I ∩ ℓ ⁻¹' C)) z := by
  set φ := extChartAt I x₀
  set f : ℂ → ℂ := fun w ↦ ℓ (φ (u w))
  have hfd (z : ℂ) (hz : u z ∈ (chartAt H x₀).source) : DifferentiableAt ℝ f z :=
    differentiableAt_comp_extChartAt_comp (hu z) hz ℓ
  have hinv (z : ℂ) (hz : u z ∈ (chartAt H x₀).source) (hzC : f z ∈ (C : Set ℂ)) :
      (fderiv ℝ f z).IsInvertible :=
    ((fderiv ℝ f z).isInvertible_iff_injective_of_finrank_eq rfl).2
      (LinearMap.injective_iff_surjective.2 (hC _ hzC z hz rfl))
  set Z := u ⁻¹' (chartAt H x₀).source ∩ {z | dist (φ (u z)) (φ x₀) ≤ r₀ ∧ f z ∈ (C : Set ℂ)}
  have hZ : Z.Countable := countable_of_forall_injective_fderiv C.countable_toSet
    fun z hz ↦ ⟨hfd z hz.1, (hinv z hz.1 hz.2.2).injective, hz.2.2⟩
  obtain ⟨r, hr, hrZ⟩ : ∃ r ∈ Ioo (r₀ / 2) r₀, ∀ z ∈ Z, dist (φ (u z)) (φ x₀) ≠ r := by
    by_contra! h
    have hcount : (Ioo (r₀ / 2) r₀).Countable :=
      (hZ.image fun z ↦ dist (φ (u z)) (φ x₀)).mono fun r hr ↦ h r hr
    exact (half_lt_self hr₀).not_ge (Cardinal.Real.Ioo_countable_iff.1 hcount)
  have hK := closedBall_inter_range_inter_preimage_subset hr.2 hr₀K ℓ C
  refine ⟨r, hr, fun z hz ↦ ?_⟩
  rw [mem_preimage, mem_extChartAt_symm_image_iff hK] at hz
  obtain ⟨hzs, hzr, hzC⟩ := hz
  obtain ⟨L, hL⟩ := hinv z hzs hzC
  exact isTransverseCutAt_extChartAt_symm_image C.finite_toSet hK hzs
    (lt_of_le_of_ne hzr (hrZ z ⟨hzs, hzr.trans hr.2.le, hzC⟩)) hzC (hL ▸ (hfd z hzs).hasFDerivAt)

variable [FiniteDimensional ℝ E] [T2Space M]

omit [IsManifold I 1 M] in
/-- The cut of a chart is closed: it is the image of a compact set of the model under the inverse
of the chart, which is continuous on the target. -/
private lemma isClosed_extChartAt_symm_image {x₀ : M} {ℓ : E →L[ℝ] ℂ} {C : Set ℂ} (hC : C.Finite)
    {r : ℝ}
    (hK : closedBall (extChartAt I x₀ x₀) r ∩ range I ∩ ℓ ⁻¹' C ⊆ (extChartAt I x₀).target) :
    IsClosed ((extChartAt I x₀).symm '' (closedBall (extChartAt I x₀ x₀) r ∩ range I ∩ ℓ ⁻¹' C)) :=
  ((((isCompact_closedBall _ _).inter_right I.isClosed_range).inter_right
    (hC.isClosed.preimage ℓ.continuous)).image_of_continuousOn
      ((continuousOn_extChartAt_symm x₀).mono hK)).isClosed

/-- **Existence of transverse target cuts.** Let `u : ℂ → M` be a `C¹` map into a
finite-dimensional Hausdorff manifold, possibly with boundary or corners, whose derivative at
`z₀` is injective. For every point `y ≠ u z₀`, every `n` and every `ε > 0` there is a closed set
`D ⊆ M` not containing `y` such that `u` meets `D` transversally at every point of the full
preimage `u⁻¹(D)` (`TauCeti.IsTransverseCutAt`), and `u⁻¹(D)` contains `n` distinct points within
`ε` of `z₀`. -/
theorem exists_isTransverseCutAt_of_injective_mfderiv {u : ℂ → M}
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) {z₀ : ℂ} (hz₀ : Injective (mfderiv 𝓘(ℝ, ℂ) I u z₀)) {y : M}
    (hy : u z₀ ≠ y) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : Set M, IsClosed D ∧ y ∉ D ∧ (∀ z ∈ u ⁻¹' D, IsTransverseCutAt u D z) ∧
      ∃ s : Finset ℂ, s.card = n ∧ ∀ z ∈ s, u z ∈ D ∧ dist z z₀ < ε := by
  set x₀ := u z₀
  set φ := extChartAt I x₀
  have hmd (z : ℂ) : MDifferentiableAt 𝓘(ℝ, ℂ) I u z := hu.mdifferentiableAt one_ne_zero
  have hx₀ : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  -- `f = ℓ ∘ φ ∘ u` is a local diffeomorphism at `z₀`, and the open ball of radius `r₀` of the
  -- chart lies in the chart and avoids `y`.
  obtain ⟨ℓ, hstrict⟩ := exists_hasStrictFDerivAt_extChartAt_comp hu hz₀
  set f : ℂ → ℂ := fun w ↦ ℓ (φ (u w))
  obtain ⟨r₀, hr₀, hr₀K⟩ :=
    exists_ball_inter_range_subset_extChartAt (I := I) (isOpen_ne.mem_nhds hy)
  -- `f` maps the points `W` near `z₀` well inside the chart onto a neighbourhood of `f z₀`.
  set W := ball z₀ ε ∩ (u ⁻¹' (chartAt H x₀).source ∩ {z | dist (φ (u z)) (φ x₀) < r₀ / 2})
  have hW : W ∈ 𝓝 z₀ := by
    have hc : ContinuousAt (fun w ↦ φ (u w)) z₀ :=
      (continuousAt_extChartAt' (by rwa [extChartAt_source])).comp hu.continuous.continuousAt
    exact inter_mem (ball_mem_nhds z₀ hε) (inter_mem
      (hu.continuous.continuousAt.preimage_mem_nhds ((chartAt H x₀).open_source.mem_nhds hx₀))
      (hc.preimage_mem_nhds (ball_mem_nhds _ (half_pos hr₀))))
  have hfW : interior (f '' W) ∈ 𝓝 (f z₀) := by
    rw [interior_mem_nhds, ← hstrict.map_nhds_eq_of_equiv]
    exact image_mem_map hW
  -- By Sard's theorem the regular values of `f` are dense, so `n` of them are taken on `W`.
  set R := {c | ∀ z ∈ u ⁻¹' (chartAt H x₀).source, f z = c → Surjective (fderiv ℝ f z)}
  have hR : Dense R := dense_setOf_forall_surjective_fderiv
    (fun z hz ↦ differentiableAt_comp_extChartAt_comp (hmd z) hz ℓ) rfl
  obtain ⟨C, hCR, hCn⟩ : ∃ C : Finset ℂ, ↑C ⊆ R ∩ interior (f '' W) ∧ C.card = n := by
    refine Set.Infinite.exists_subset_card_eq (fun hfin ↦ ?_) n
    obtain ⟨c, hc⟩ := ((infinite_of_mem_nhds _ hfW).sdiff hfin).nonempty
    obtain ⟨c', hc'U, hc'R⟩ := hR.inter_open_nonempty _
      (isOpen_interior.sdiff hfin.isClosed) ⟨c, hc⟩
    exact hc'U.2 ⟨hc'R, hc'U.1⟩
  have hw (c : ℂ) (hc : c ∈ C) : ∃ z ∈ W, f z = c := interior_subset (hCR hc).2
  choose! w hwW hwf using hw
  -- A radius `r` at which the cut is transverse.
  obtain ⟨r, hr, htr⟩ := exists_mem_Ioo_forall_isTransverseCutAt hmd (fun c hc ↦ (hCR hc).1) hr₀
    fun v hv ↦ (hr₀K hv).1
  have hD := closedBall_inter_range_inter_preimage_subset hr.2 hr₀K ℓ C
  have hK : closedBall (φ x₀) r ∩ range I ∩ ℓ ⁻¹' C ⊆ φ.target := fun v hv ↦ (hD hv).1
  refine ⟨φ.symm '' (closedBall (φ x₀) r ∩ range I ∩ ℓ ⁻¹' C), ?_, ?_, htr, C.image w, ?_,
    fun z hz ↦ ?_⟩
  · exact isClosed_extChartAt_symm_image C.finite_toSet hK
  · rintro ⟨v, hv, hvy⟩
    exact (hD hv).2 hvy
  · refine Finset.card_image_of_injOn (fun a ha b hb hab ↦ ?_) |>.trans hCn
    rw [← hwf a ha, ← hwf b hb, hab]
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hz
    obtain ⟨hwz, hws, hwr⟩ := hwW c hc
    exact ⟨(mem_extChartAt_symm_image_iff hK).2 ⟨hws, hwr.le.trans hr.1.le,
      (congrArg (· ∈ (C : Set ℂ)) (hwf c hc)).mpr hc⟩, mem_ball.1 hwz⟩

/-- **Stabilizing target cuts.** Let `u : ℂ → M` be a `C¹` sphere component into a
finite-dimensional Hausdorff manifold, with a limit `y` at `∞` and a point `z₀` with `u z₀ ≠ y` at
which its derivative is injective. Then there is a closed set `D ⊆ M` which `u` meets transversally
at every point of `u⁻¹(D)`, and whose full preimage `u⁻¹(D)` is finite and contains two distinct
points. These points together with `∞` make the sphere a stable curve, and the isotropy of `u` is
finite (`TauCeti.finite_markedIsotropy_of_injective_mfderiv`). -/
theorem exists_isTransverseCutAt_finite_nontrivial_preimage {u : ℂ → M}
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) {y : M} (hy : Tendsto u (cocompact ℂ) (𝓝 y)) {z₀ : ℂ}
    (hz₀ : Injective (mfderiv 𝓘(ℝ, ℂ) I u z₀)) (hz₀y : u z₀ ≠ y) :
    ∃ D : Set M, IsClosed D ∧ (∀ z ∈ u ⁻¹' D, IsTransverseCutAt u D z) ∧
      (u ⁻¹' D).Finite ∧ (u ⁻¹' D).Nontrivial := by
  obtain ⟨D, hD, hyD, htr, t, ht, htD⟩ :=
    exists_isTransverseCutAt_of_injective_mfderiv hu hz₀ hz₀y 2 one_pos
  refine ⟨D, hD, htr, finite_preimage_of_isTransverseCutAt hu.continuous hD
    (hy.eventually (hD.isOpen_compl.mem_nhds hyD)) htr, ?_⟩
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 ht
  exact ⟨a, (htD a (by simp)).1, b, (htD b (by simp)).1, hab⟩

/-- **Finite isotropy of sphere components of rank two.** A `C¹` map `u : ℂ → M` into a
finite-dimensional Hausdorff manifold, with a limit `y` at `∞` and a point `z₀` with `u z₀ ≠ y` at
which its derivative is injective, is invariant under only finitely many automorphisms of the
sphere fixing `∞` and a given set `P` of further special points. Finiteness follows from the
stabilizing target cut of `TauCeti.exists_isTransverseCutAt_finite_nontrivial_preimage`. -/
theorem finite_markedIsotropy_of_injective_mfderiv {u : ℂ → M}
    (hu : ContMDiff 𝓘(ℝ, ℂ) I 1 u) {y : M} (hy : Tendsto u (cocompact ℂ) (𝓝 y)) {z₀ : ℂ}
    (hz₀ : Injective (mfderiv 𝓘(ℝ, ℂ) I u z₀)) (hz₀y : u z₀ ≠ y) (P : Set ℂ) :
    Finite (markedIsotropy u P) := by
  obtain ⟨D, -, -, hfin, hnt⟩ :=
    exists_isTransverseCutAt_finite_nontrivial_preimage hu hy hz₀ hz₀y
  exact finite_markedIsotropy hfin (hnt.mono subset_union_right)

end TauCeti
