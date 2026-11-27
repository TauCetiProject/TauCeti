/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalSobolev
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SobolevWaveFrontSet
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Closure
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Smoothness
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.ModelSpace
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# Sobolev wave front sets and singular supports of functionals on bundle tests

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a finite-dimensional
real inner product space `E`, and let `T` be a real continuous linear functional on the bundle tests
`TauCeti.BundleTest I F V`, for instance a distributional section of a bundle. This file relates
the `H^s` wave front set of `T` (`TauCeti.BundleTest.sobolevWaveFrontSet`) to its `H^s` singular
support (`TauCeti.BundleTest.sobolevSingularSupport`), and the Sobolev scale to the wave front
set and the singular support (`TauCeti.BundleTest.waveFrontSet`,
`TauCeti.BundleTest.singularSupport`).

* **The projection of the `H^s` wave front set is the `H^s` singular support**
  (`TauCeti.BundleTest.proj_image_sobolevWaveFrontSet`): on a manifold without boundary, `T` is
  `H^s` near `x` exactly when it is microlocally `H^s` at every nonzero covector at `x`
  (`TauCeti.BundleTest.isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt`). At the zero
  covector, microlocal `H^s` regularity is local `H^s` regularity
  (`TauCeti.BundleTest.isMicrolocallySobolevAt_zero_covector_iff`).
* **The wave front set is the closure of the `H^s` wave front sets**: `T` is microlocally smooth at
  a covector exactly when it is microlocally `H^s`, for every `s`, at every covector of a
  neighbourhood independent of `s`
  (`TauCeti.BundleTest.isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt`), so
  that

  `WF(T) = (T*M \ 0) ∩ closure (⋃ s, WF_s(T))`

  (`TauCeti.BundleTest.waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet`). The closure is
  needed: covectors at which `T` has singularities of ever higher Sobolev regularity can
  accumulate at a covector at which `T` is microlocally `H^s` for every `s`.
* **The singular support is the closure of the `H^s` singular supports**: on a manifold without
  boundary, `T` is smooth near `x` exactly when, for every `s`, it is `H^s` near every point of a
  neighbourhood of `x` independent of `s`
  (`TauCeti.BundleTest.notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt`), so that
  `singsupp T = closure (⋃ s, singsupp_s T)`
  (`TauCeti.BundleTest.singularSupport_eq_closure_iUnion_sobolevSingularSupport`).
* **Point masses**: on a manifold without boundary of dimension `d`, the point mass `δ_x ℓ` with
  `ℓ ≠ 0` has `H^s` wave front set the nonzero covectors at `x` for `s ≥ -d / 2`
  (`TauCeti.BundleTest.sobolevWaveFrontSet_delta`), and empty `H^s` wave front set for `s < -d / 2`
  (`TauCeti.BundleTest.sobolevWaveFrontSet_delta_eq_empty`).

Together with a microlocal elliptic estimate `WF_{s+m}(T) ⊆ WF_s(P T) ∪ Char(P)` valid for every
`s`, the closure statement gives `WF(T) ⊆ WF(P T) ∪ Char(P)`, since `WF(P T) ∪ Char(P)` is closed
in the complement of the zero section. This is how microlocal regularity on the Sobolev scale
yields microlocal smoothness on a manifold.

## The argument

Each statement holds for the components of `T` in a chart and a frame, by the Euclidean theorems
`Distribution.isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt`,
`Distribution.isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt`,
`Distribution.notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt` and
`Distribution.sobolevWaveFrontSet_delta`. Reading covectors at `x` in a chart `c` is a bijection
onto the covectors of `E` that sends only the zero covector to zero, so the nonzero covectors at
`x` correspond to the nonzero directions at `c x`
(`TauCeti.BundleTest.forall_chartComponent_iff_forall_isMicrolocallyAt`), and the projections are
instances of `TauCeti.BundleTest.proj_image_microlocalSingularSet`. For the neighbourhoods in the
cotangent bundle, the pullback `(y, p) ↦ p ∘ Dc(c⁻¹ y)` of a point `y` of the chart target and a
covector `p ∈ E*` to a covector of `M` at `c⁻¹ y` is continuous on `E × E*`
(`TauCeti.CotangentBundle.continuousAt_mk_symm_comp_mfderiv`) and inverts the reading of covectors
in the chart, so a neighbourhood of a covector of `M` pulls back to a neighbourhood of its reading
(`TauCeti.CotangentBundle.eventually_mk_symm_comp_mfderiv_of_eventually`). Vectors `η` of `E`
are read as covectors `⟪η, ·⟫` through `toDual`.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1
  (the `H^s` wave front set, its projection, and its relation to the wave front set).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (the wave front set on a manifold).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Distribution
open scoped Manifold ContDiff Distributions Topology CompactConvergenceCLM

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization InnerProductSpace

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} {s : ℝ}

/-! ### The projection of the `H^s` wave front set -/

/-- Being `H^s` near `x` implies being microlocally `H^s` at every covector at `x`. -/
theorem IsLocallySobolevAt.isMicrolocallySobolevAt (h : IsLocallySobolevAt s T x)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : IsMicrolocallySobolevAt s T x ξ := by
  obtain ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := isLocallyAt_def.1 (isLocallySobolevAt_def.1 h)
  exact isMicrolocallySobolevAt_def.2 <| isMicrolocallyAt_def.2
    ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ (h v).isMicrolocallySobolevAt _⟩

/-- At the zero covector, being microlocally `H^s` is being `H^s` near the point. -/
theorem isMicrolocallySobolevAt_zero_covector_iff :
    IsMicrolocallySobolevAt s T x 0 ↔ IsLocallySobolevAt s T x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.isMicrolocallySobolevAt 0⟩
  obtain ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := isMicrolocallyAt_def.1 (isMicrolocallySobolevAt_def.1 h)
  refine isLocallySobolevAt_def.2 <| isLocallyAt_def.2 ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  have hv := h v
  rw [(c.toDual_symm_comp_mfderiv_symm_eq_zero_iff hc hcs hx).2 rfl] at hv
  exact Distribution.isMicrolocallySobolevAt_zero_covector_iff.1 hv

/-- On a manifold without boundary, `T` is `H^s` near `x` exactly when it is microlocally `H^s` at
every nonzero covector at `x`. -/
theorem isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt [I.Boundaryless] :
    IsLocallySobolevAt s T x ↔
      ∀ ξ : TangentSpace I x →L[ℝ] ℝ, ξ ≠ 0 → IsMicrolocallySobolevAt s T x ξ := by
  refine ⟨fun h ξ _ ↦ h.isMicrolocallySobolevAt ξ, fun h ↦ ?_⟩
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  have hcx : c x ∈ (⟨c.target, c.open_target⟩ : Opens E) := c.map_source hx
  refine (isLocallySobolevAt_iff T hc hcs hct hx).2 fun v ↦
    (Distribution.isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt hcx).2 ?_
  exact (forall_chartComponent_iff_forall_isMicrolocallyAt
    (isInvariantMicrolocalRegularity_isMicrolocallySobolevAt s) T hc hcs hct hx).2
      (fun ξ hξ ↦ isMicrolocallySobolevAt_def.1 (h ξ hξ)) v

/-- **The projection of the `H^s` wave front set is the `H^s` singular support** (Hörmander,
*Lectures on Nonlinear Hyperbolic Differential Equations*, §11.1), on a manifold without
boundary. -/
theorem proj_image_sobolevWaveFrontSet [I.Boundaryless] (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    TotalSpace.proj '' sobolevWaveFrontSet I s T = sobolevSingularSupport I s T := by
  rw [sobolevWaveFrontSet_eq_microlocalSingularSet]
  refine proj_image_microlocalSingularSet fun _ ↦ ?_
  rw [mem_sobolevSingularSupport_iff, not_not]
  simpa only [isMicrolocallySobolevAt_def] using
    isLocallySobolevAt_iff_forall_isMicrolocallySobolevAt (T := T)

/-- On a manifold without boundary, a functional has empty `H^s` singular support exactly when it
has empty `H^s` wave front set. -/
theorem sobolevSingularSupport_eq_empty_iff_sobolevWaveFrontSet_eq_empty [I.Boundaryless] :
    sobolevSingularSupport I s T = ∅ ↔ sobolevWaveFrontSet I s T = ∅ := by
  rw [← proj_image_sobolevWaveFrontSet, image_eq_empty]

/-! ### The wave front set as the closure of the `H^s` wave front sets -/

/-- **Microlocal smoothness from every Sobolev order.** A real functional on bundle tests is
microlocally smooth at a covector `p` exactly when, for every `s`, it is microlocally `H^s` at
every covector of a neighbourhood of `p` that does not depend on `s`. -/
theorem isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt
    {p : CotangentBundle I M} :
    IsMicrolocallySmoothAt T p.proj p.snd ↔
      ∀ᶠ q in 𝓝 p, ∀ s, IsMicrolocallySobolevAt s T q.proj q.snd := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · filter_upwards [(isOpen_setOf_isMicrolocallySmoothAt T).mem_nhds h] with q hq s
    exact hq.isMicrolocallySobolevAt s
  -- Read in a chart at `p.proj`, every component is microlocally `H^s` near the reading of `p`.
  obtain ⟨t, _, c, hc, hcs, hct, hx, -⟩ :=
    isMicrolocallyAt_def.1 (isMicrolocallySobolevAt_def.1 (h.self_of_nhds 0))
  refine (isMicrolocallySmoothAt_iff T hc hcs hct hx _).2 fun v ↦
    Distribution.isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt.2 ?_
  have hcd : c.MDifferentiable I 𝓘(ℝ, E) :=
    ⟨hc.mdifferentiableOn (by simp), hcs.mdifferentiableOn (by simp)⟩
  have hev := CotangentBundle.eventually_mk_symm_comp_mfderiv_of_eventually hcd hx
    (((hc _ hx).contMDiffAt (c.open_source.mem_nhds hx)).of_le (by simp)) h
  -- The covectors of `E` are read as vectors of `E` through `toDual`.
  have hread := (continuous_fst.prodMk ((toDual ℝ E).continuous.comp continuous_snd)).tendsto
    (c p.proj, (toDual ℝ E).symm (p.snd ∘L mfderiv 𝓘(ℝ, E) I c.symm (c p.proj)))
  simp only [comp_apply, LinearIsometryEquiv.apply_symm_apply] at hread
  filter_upwards [hread.eventually hev] with q ⟨hq, hQ⟩ s
  have hv := (isMicrolocallySobolevAt_iff T hc hcs hct (c.map_target hq) _).1 (hQ s) v
  -- The point and the covector of `hv` are read back as `q.1` and `q.2`.
  convert hv using 2
  · exact (c.right_inv hq).symm
  · exact ((congrArg (toDual ℝ E).symm
      (hcd.comp_mfderiv_comp_mfderiv_symm hq (toDual ℝ E q.2))).trans
        ((toDual ℝ E).symm_apply_apply q.2)).symm

/-- **The wave front set is the closure of the union of the `H^s` wave front sets**, inside the
complement of the zero section of the cotangent bundle. The closure is needed, because covectors at
which `T` has singularities of ever higher Sobolev regularity can accumulate. -/
theorem waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet
    (T : BundleTest I F V →L_c[ℝ] ℝ) :
    waveFrontSet I T = zeroSectionCompl (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ∩
      closure (⋃ s, sobolevWaveFrontSet I s T) := by
  ext p
  rw [mem_waveFrontSet_iff, mem_inter_iff, mem_zeroSectionCompl]
  refine ⟨fun ⟨hp, hT⟩ ↦ ⟨hp, mem_closure_iff_nhds.2 fun W hW ↦ ?_⟩,
    fun ⟨hp, hcl⟩ ↦ ⟨hp, fun hT ↦ ?_⟩⟩
  · -- Otherwise `T` is microlocally `H^s` for every `s` on a neighbourhood of `p`.
    by_contra hW'
    refine hT (isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt.2 ?_)
    filter_upwards [hW, (isOpen_zeroSectionCompl (E →L[ℝ] ℝ)
      (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).mem_nhds (mem_zeroSectionCompl.2 hp)]
      with q hqW hq s
    by_contra hs
    exact hW' ⟨q, hqW, mem_iUnion.2 ⟨s, mem_sobolevWaveFrontSet_iff.2
      ⟨mem_zeroSectionCompl.1 hq, hs⟩⟩⟩
  · obtain ⟨q, hq, hqS⟩ := mem_closure_iff_nhds.1 hcl _
      (isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt.1 hT)
    obtain ⟨s, hs⟩ := mem_iUnion.1 hqS
    exact (mem_sobolevWaveFrontSet_iff.1 hs).2 (hq s)

/-- A real functional on bundle tests has empty wave front set exactly when all its `H^s` wave
front sets are empty. -/
theorem waveFrontSet_eq_empty_iff_forall_sobolevWaveFrontSet_eq_empty
    (T : BundleTest I F V →L_c[ℝ] ℝ) :
    waveFrontSet I T = ∅ ↔ ∀ s, sobolevWaveFrontSet I s T = ∅ := by
  refine ⟨fun h s ↦ subset_empty_iff.1 (h ▸ sobolevWaveFrontSet_subset_waveFrontSet s T),
    fun h ↦ ?_⟩
  rw [waveFrontSet_eq_inter_closure_iUnion_sobolevWaveFrontSet]
  simp [h]

/-! ### The singular support as the closure of the `H^s` singular supports -/

/-- The `H^s` singular support lies in the singular support. -/
theorem sobolevSingularSupport_subset_singularSupport (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s T ⊆ singularSupport I T := by
  intro x hx
  rw [mem_singularSupport_iff]
  rintro ⟨t, ht, c, hc, hcs, hct, hxc, h⟩
  -- In the chart witnessing smoothness near `x`, every component is also `H^s` near `c x`.
  refine (mem_sobolevSingularSupport_iff.1 hx) <| isLocallySobolevAt_def.2 <|
    isLocallyAt_def.2 ⟨t, ht, c, hc, hcs, hct, hxc, fun v ↦ ?_⟩
  exact (Distribution.notMem_sobolevSingularSupport_iff (c.map_source hxc)).1 fun hv ↦
    h v (Distribution.sobolevSingularSupport_subset_singularSupport s _ hv)

section Boundaryless

variable [I.Boundaryless]

/-- **Smoothness from every Sobolev order.** On a manifold without boundary, a real functional on
bundle tests is smooth near `x` exactly when, for every `s`, it is `H^s` near every point of a
neighbourhood of `x` that does not depend on `s`. -/
theorem notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt :
    x ∉ singularSupport I T ↔ ∀ᶠ y in 𝓝 x, ∀ s, IsLocallySobolevAt s T y := by
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  have hcx : c x ∈ (⟨c.target, c.open_target⟩ : Opens E) := c.map_source hx
  rw [notMem_singularSupport_iff T hc hcs hct hx]
  simp_rw [Distribution.notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt hcx]
  refine ⟨fun h ↦ ?_, fun h v ↦ ?_⟩
  · -- Finitely many components, along a basis of `F`, control all of them.
    let b := Module.finBasis ℝ F
    have hb := eventually_all.2 fun i ↦ h (b i)
    filter_upwards [(c.continuousAt hx).eventually hb, c.open_source.mem_nhds hx]
      with y hy hyc s
    exact (isLocallySobolevAt_iff T hc hcs hct hyc).2 <|
      chartComponent_of_basis (isInvariantLocalRegularity_isLocallySobolevAt s).toIsLocalRegularity
        b T (c.map_source hyc) fun i ↦ hy i s
  · have hx' : ∀ᶠ y in 𝓝 (c.symm (c x)), ∀ s, IsLocallySobolevAt s T y := by
      rwa [c.left_inv hx]
    filter_upwards [(c.continuousAt_symm (c.map_source hx)).eventually hx',
      c.open_target.mem_nhds (c.map_source hx)] with y hy hyt s
    have hv := (isLocallySobolevAt_iff T hc hcs hct (c.map_target hyt)).1 (hy s) v
    rwa [c.right_inv hyt] at hv

/-- **The singular support is the closure of the `H^s` singular supports.** On a manifold without
boundary, the singular support of a real functional on bundle tests is the closure of the union
over all real `s` of its `H^s` singular supports. -/
theorem singularSupport_eq_closure_iUnion_sobolevSingularSupport (T : BundleTest I F V →L_c[ℝ] ℝ) :
    singularSupport I T = closure (⋃ s, sobolevSingularSupport I s T) := by
  ext x
  rw [← not_iff_not, notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt,
    mem_closure_iff_frequently, not_frequently]
  simp only [mem_iUnion, mem_sobolevSingularSupport_iff, not_exists, not_not]

/-- On a manifold without boundary, a real functional on bundle tests is smooth near every point
exactly when it is `H^s` near every point, for every real `s`. -/
theorem singularSupport_eq_empty_iff_forall_sobolevSingularSupport_eq_empty :
    singularSupport I T = ∅ ↔ ∀ s, sobolevSingularSupport I s T = ∅ := by
  refine ⟨fun h s ↦ subset_empty_iff.1 (h ▸ sobolevSingularSupport_subset_singularSupport s T),
    fun h ↦ ?_⟩
  simp [singularSupport_eq_closure_iUnion_sobolevSingularSupport, h]

/-! ### Point masses -/

/-- **Point masses are microlocally `H^s` below the critical order.** On a manifold without boundary
of dimension `d`, the point mass `δ_x ℓ` has empty `H^s` wave front set for `s < -d / 2`. -/
theorem sobolevWaveFrontSet_delta_eq_empty (hs : (Module.finrank ℝ E : ℝ) < -2 * s) (x : M)
    (ℓ : V x →L[ℝ] ℝ) :
    sobolevWaveFrontSet I s (delta (I := I) (F := F) x ℓ) = ∅ := by
  rw [← image_eq_empty (f := TotalSpace.proj), proj_image_sobolevWaveFrontSet,
    sobolevSingularSupport_delta_eq_empty hs]

/-- **The `H^s` wave front set of a point mass.** On a manifold without boundary of dimension `d`,
the point mass `δ_x ℓ : σ ↦ ℓ (σ x)` with a nonzero covector `ℓ` on the fibre `V x` has `H^s` wave
front set the nonzero covectors of `M` at `x`, for `s ≥ -d / 2`. -/
theorem sobolevWaveFrontSet_delta (hs : -2 * s ≤ Module.finrank ℝ E) {x : M} {ℓ : V x →L[ℝ] ℝ}
    (hℓ : ℓ ≠ 0) :
    sobolevWaveFrontSet I s (delta (I := I) (F := F) x ℓ) = {p | p.proj = x ∧ p.snd ≠ 0} := by
  refine ((sobolevWaveFrontSet_subset_waveFrontSet s _).trans
    (waveFrontSet_delta hℓ).subset).antisymm ?_
  rintro ⟨y, ξ⟩ ⟨rfl, hξ⟩
  refine mem_sobolevWaveFrontSet_iff.2 ⟨hξ, fun h ↦ ?_⟩
  -- At `x`, the component along a vector `v` with `ℓ (t⁻¹ v) ≠ 0` is a nonzero multiple of the
  -- point mass at `c x`, which is not microlocally `H^s` in any direction.
  obtain ⟨c, hc, hcs, hct, hy⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) y
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hℓ
  set t := trivializationAt F V y
  have hv := (isMicrolocallySobolevAt_iff _ hc hcs hct hy ξ).1 h (t.continuousLinearMapAt ℝ y w)
  rw [chartComponent_delta_of_mem _ _ _ _ hy, t.symmL_continuousLinearMapAt (hct hy)] at hv
  have hmem : (c y, (toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c y))) ∈
      ((ℓ w : ℂ) • mapCLM Complex.ofRealCLM
        (Distribution.delta (c y) : 𝓓'(⟨c.target, c.open_target⟩, ℝ))).sobolevWaveFrontSet s := by
    rw [Distribution.sobolevWaveFrontSet_smul s (Complex.ofReal_ne_zero.2 hw),
      Distribution.sobolevWaveFrontSet_delta hs (c.map_source hy)]
    exact ⟨rfl, mt (c.toDual_symm_comp_mfderiv_symm_eq_zero_iff hc hcs hy).1 hξ⟩
  exact (Distribution.mem_sobolevWaveFrontSet_iff.1 hmem).2.2 hv

end Boundaryless

end TauCeti.BundleTest
