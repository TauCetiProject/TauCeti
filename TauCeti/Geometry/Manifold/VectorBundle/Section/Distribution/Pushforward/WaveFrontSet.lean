/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Pushforward
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Pushforward
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Algebra.GroupWithZero.Indicator
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.Geometry.Manifold.VectorBundle.Section.TestFunction

/-!
# The wave front set of a pushforward along a smooth map of manifolds

Let `f : X → Y` be a smooth map of manifolds without boundary, modelled on finite-dimensional real
inner product spaces, and let `T` be a continuous linear functional on the tests on `X` with values
in a finite-dimensional space `G` (`TauCeti.BundleTest I G (Bundle.Trivial X G)`); for `G = ℝ` these
functionals are the distribution densities on `X`. For a smooth cutoff `χ` with compact support,
the pushforward `f_* (χ T) : s ↦ T (χ (s ∘ f))` is a functional on the tests on `Y`
(`TauCeti.BundleTest.cutoffPushforwardCLM`). This file proves Hörmander's bound for its wave front
set (`TauCeti.BundleTest.waveFrontSet`):

`WF(f_* (χ T)) ⊆ {(f x, η) | x ∈ supp χ ∩ supp T, η ∘ df_x = 0 or (x, η ∘ df_x) ∈ WF(T)}`

(`TauCeti.BundleTest.waveFrontSet_cutoffPushforwardCLM_subset`), and the same bound, with `x`
ranging over the support of `T`, for the pushforward `f_* T` along a map proper on the support of
`T` (`TauCeti.BundleTest.waveFrontSet_pushforward_subset`). The covectors with `η ∘ df_x = 0`
record the critical points of `f` and cannot be omitted; when the differential of `f` is surjective
they do not occur (`TauCeti.BundleTest.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`).

## The argument

The bound is the Euclidean one (`Distribution.IsMicrolocallySmoothAt.cutoffPushforwardCLM`), read
in charts. Fix a chart `c'` at `y` with smooth inverse. The points of `supp χ ∩ supp T` over `y`
form a compact set `K`, with a compact neighbourhood `L` mapped into the source of `c'`. A
partition of unity `ρᵢ` on `L` subordinate to charts `cᵢ` of `X` whose sources `f` maps into the
source of `c'` splits the pushforward as

`f_* (χ T) = ∑ᵢ f_* (ρᵢ χ T) + f_* ((1 - ∑ᵢ ρᵢ) χ T)`.

The last term vanishes near `y`, since no point of the support of its cutoff lies over `y`, so it
is microlocally smooth there (`TauCeti.BundleTest.isMicrolocallySmoothAt_of_notMem_dsupport`). In
the charts `cᵢ` and `c'`, and the trivial frames, the components of `f_* (ρᵢ χ T)` are the Euclidean
pushforwards of the components of `T` along the coordinate expression `Φᵢ = c' ∘ f ∘ cᵢ⁻¹` of `f`,
with the cutoff `ρᵢ χ` read in `cᵢ`. The transpose of the derivative of `Φᵢ` sends `η` read in
`c'` to the covector `η ∘ df_x` read in `cᵢ`, so the Euclidean bound applies.

## Main results

* `TauCeti.BundleTest.isMicrolocallySmoothAt_of_notMem_dsupport`: a functional on bundle tests is
  microlocally smooth at every covector over a point outside its support.
* `TauCeti.BundleTest.IsMicrolocallySmoothAt.cutoffPushforwardCLM`: `f_* (χ T)` is microlocally
  smooth at `(y, η)` if `T` is microlocally smooth at the nonzero covectors `η ∘ df_x` for the
  points `x` of `supp χ ∩ supp T` over `y`.
* `TauCeti.BundleTest.waveFrontSet_cutoffPushforwardCLM_subset`,
  `TauCeti.BundleTest.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`: the wave front set
  of `f_* (χ T)`, and its form for submersions.
* `TauCeti.BundleTest.waveFrontSet_pushforward_subset`: the wave front set of the pushforward
  `f_* T` along a map proper on the support of `T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.13 and §6.3 (distributions and densities on manifolds).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, Studia Math. 232 (2016), arXiv:1409.7662v2, §3
  (pushforward along maps proper on the support).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open Bundle Bundle.Trivialization InnerProductSpace
open scoped Manifold ContDiff Distributions Topology InnerProduct CompactConvergenceCLM

namespace TauCeti.BundleTest

/-! ### Microlocal smoothness off the support -/

section Support

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- If a functional `T` on bundle tests vanishes on a set `U`, then its components in a chart `c`
and a frame `t` vanish on the part `c.target ∩ c⁻¹ ⁻¹' U` of the chart target read from `U`. -/
theorem _root_.Bundle.Trivialization.isVanishingOn_chartComponent (t : Trivialization F (π F V))
    [MemTrivializationAtlas t] (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
    {T : BundleTest I F V →L_c[ℝ] ℝ} {U : Set M} (hTU : IsVanishingOn ⇑T U) (v : F) :
    Distribution.IsVanishingOn (t.chartComponent c hc hct T v) (c.target ∩ c.symm ⁻¹' U) := by
  intro φ hφ
  rw [chartComponent_apply, isVanishingOn_iff.1 hTU _ ?_, Complex.ofReal_zero]
  have h := tsupport_chartTestSection (n := ⊤) t c hc hct
    (TestFunction.postcompCLM (toSpanSingleton ℝ v) φ)
  rw [ContMDiffSection.tsupport_def] at h
  rw [coe_chartTestCLM, h]
  rintro _ ⟨z, hz, rfl⟩
  have hsupp : tsupport (TestFunction.postcompCLM (toSpanSingleton ℝ v) φ) ⊆ tsupport φ := by
    refine closure_mono fun w hw ↦ ?_
    simp only [mem_support, ne_eq] at hw ⊢
    intro hφw
    apply hw
    simp [hφw]
  have hzφ : z ∈ tsupport φ := hsupp hz
  exact (hφ hzφ).2

/-- **A functional is microlocally smooth off its support.** On a manifold without boundary, a
functional `T` on bundle tests is microlocally smooth at every covector over a point outside its
support. -/
theorem isMicrolocallySmoothAt_of_notMem_dsupport [I.Boundaryless]
    {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} (hx : x ∉ dsupport ⇑T)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : IsMicrolocallySmoothAt T x ξ := by
  obtain ⟨U, hU, hxU, hTU⟩ := notMem_dsupport_iff.1 hx
  obtain ⟨c, hc, hcs, hct, hxc⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  refine (isMicrolocallySmoothAt_iff T hc hcs hct hxc ξ).2 fun v ↦
    Distribution.isMicrolocallySmoothAt_of_notMem_dsupport (c.map_source hxc)
      ((Distribution.notMem_dsupport_iff _).2 ⟨_, isVanishingOn_chartComponent _ c hc hct hTU v,
        c.isOpen_inter_preimage_symm hU, c.map_source hxc, by simpa [c.left_inv hxc] using hxU⟩) _

/-- If a component of `T` in a chart `c` has the point `z` of the chart target in its support, then
`c⁻¹ z` lies in the support of `T`. -/
theorem _root_.Bundle.Trivialization.symm_mem_dsupport_of_mem_dsupport_chartComponent
    (t : Trivialization F (π F V))
    [MemTrivializationAtlas t] (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
    (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) {z : E} (hz : z ∈ c.target)
    (h : z ∈ Distribution.dsupport (t.chartComponent c hc hct T v)) : c.symm z ∈ dsupport ⇑T := by
  by_contra hzT
  obtain ⟨U, hU, hzU, hTU⟩ := notMem_dsupport_iff.1 hzT
  exact (Distribution.notMem_dsupport_iff _).2 ⟨_, isVanishingOn_chartComponent _ c hc hct hTU v,
    c.isOpen_inter_preimage_symm hU, hz, hzU⟩ h

end Support

/-! ### Reading cutoffs and pushforwards in charts -/

section Pushforward

variable {E H X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [T2Space X] [IsManifold I ∞ X]
  {E' H' Y : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Y] [ChartedSpace H' Y]
  [T2Space Y] [IsManifold J ∞ Y]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

omit [T2Space X] [IsManifold I ∞ X] in
/-- A smooth function `ψ` with compact support in the source of a chart `c` with smooth inverse is
read in the chart as a test function on the chart target, supported in the image of the support
of `ψ`. -/
private theorem exists_testFunction_apply_eq {c : OpenPartialHomeomorph X E}
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) {ψ : C^∞⟮I, X; ℝ⟯}
    (hψc : HasCompactSupport ψ) (hψ : tsupport ψ ⊆ c.source) :
    ∃ ψ' : 𝓓(⟨c.target, c.open_target⟩, ℝ), tsupport ψ' ⊆ c '' tsupport ψ ∧
      ∀ x ∈ c.source, ψ' (c x) = ψ x := by
  -- A cutoff `θ` equal to `1` near the compact set `c (supp ψ)`, and `ψ' = θ · (ψ ∘ c⁻¹)`.
  have hC : IsCompact (c '' tsupport ψ) :=
    hψc.isCompact.image_of_continuousOn (c.continuousOn.mono hψ)
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one
    (Ω := ⟨c.target, c.open_target⟩) (n := ⊤) hC
    (image_subset_iff.2 fun p hp ↦ c.map_source (hψ hp))
  have hsmooth : ContDiff ℝ ∞ fun z ↦ θ z * ψ (c.symm z) := by
    have h := ContMDiffOn.contMDiff_smul_of_tsupport_subset
      (ψ.contMDiff.comp_contMDiffOn hcs) c.open_target θ.contDiff.contMDiff.contMDiffOn
      θ.tsupport_subset
    simpa only [smul_eq_mul, Function.comp_apply] using contMDiff_iff_contDiff.1 h
  refine ⟨⟨fun z ↦ θ z * ψ (c.symm z), hsmooth, θ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans θ.tsupport_subset⟩, ?_, fun x hx ↦ ?_⟩
  · refine closure_minimal (fun z hz ↦ ?_) hC.isClosed
    have hzt : z ∈ c.target := θ.tsupport_subset (subset_tsupport _ (left_ne_zero_of_mul hz))
    exact ⟨c.symm z, subset_tsupport _ (right_ne_zero_of_mul hz), c.right_inv hzt⟩
  · rw [TestFunction.coe_mk, c.left_inv hx]
    exact mul_eq_right_of_ne_zero_imp_eq_one fun hψx ↦
      hθ.self_of_nhdsSet _ (mem_image_of_mem c (subset_tsupport _ hψx))

/-- **The pushforward read in charts.** Let `c` be a smooth chart of `X` and `c'` one of `Y`, and
let `ψ` be a smooth cutoff with compact support in `c.source ∩ f⁻¹(c'.source)`, read in `c` as the
test function `ψ'`. In the trivial frames, the component along `v` of `f_* (ψ T)` in the chart
`c'` is the Euclidean pushforward, along the coordinate expression `c' ∘ f ∘ c⁻¹` of `f` and with
the cutoff `ψ'`, of the component along `v` of `T` in the chart `c`. -/
private theorem chartComponent_cutoffPushforwardCLM {c : OpenPartialHomeomorph X E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) {c' : OpenPartialHomeomorph Y E'}
    (hc' : ContMDiffOn J 𝓘(ℝ, E') ∞ c' c'.source) (t : Trivialization G (π G (Trivial X G)))
    [MemTrivializationAtlas t] (hct : c.source ⊆ t.baseSet)
    (t' : Trivialization G (π G (Trivial Y G))) [MemTrivializationAtlas t']
    (hct' : c'.source ⊆ t'.baseSet) {f : C^∞⟮I, X; J, Y⟯} {ψ : C^∞⟮I, X; ℝ⟯}
    (hψc : HasCompactSupport ψ) (hψ : tsupport ψ ⊆ c.source ∩ f ⁻¹' c'.source)
    {ψ' : 𝓓(⟨c.target, c.open_target⟩, ℝ)} (hψ' : ∀ x ∈ c.source, ψ' (c x) = ψ x)
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (c' ∘ f ∘ c.symm) c.target)
    (T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ) (v : G) :
    t'.chartComponent c' hc' hct' (cutoffPushforwardCLM ψ hψc f T) v =
      Distribution.cutoffPushforwardCLM ψ' (c' ∘ f ∘ c.symm) hΦ
        (t.chartComponent c hc hct T v) := by
  obtain rfl := Trivial.eq_trivialization X G t
  obtain rfl := Trivial.eq_trivialization Y G t'
  ext φ
  rw [Distribution.cutoffPushforwardCLM_apply, chartComponent_apply, chartComponent_apply,
    cutoffPushforwardCLM_apply]
  refine congrArg (fun s ↦ ((T s : ℝ) : ℂ)) (BundleTest.ext fun x ↦ ?_)
  rw [cutoffCompCLM_apply]
  by_cases hx : x ∈ c.source
  · rw [chartTestCLM_apply_of_mem _ _ _ _ _ hx]
    by_cases hψx : ψ x = 0
    · simp [hψx, hψ' x hx]
    have hfx : f x ∈ c'.source := (hψ (subset_tsupport _ hψx)).2
    rw [chartTestCLM_apply_of_mem _ _ _ _ _ hfx]
    simp [hψ' x hx, c.left_inv hx, smul_smul]
  · rw [chartTestCLM_apply_of_notMem _ _ _ _ _ hx,
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (hψ h).1, zero_smul]

omit [T2Space X] [IsManifold I ∞ X] [T2Space Y] [IsManifold J ∞ Y] in
/-- **Covectors along a smooth map, read in charts.** For a smooth map `f : X → Y`, charts `c` at
`x` and `c'` at `f x` with smooth inverses, and a covector `η` at `f x`, the transpose of the
derivative of the coordinate expression `Φ = c' ∘ f ∘ c⁻¹` of `f` sends `η` read in `c'` to the
pulled back covector `η ∘ df_x` read in `c`. -/
private theorem adjoint_fderiv_toDual_symm_comp_mfderiv_symm {c : OpenPartialHomeomorph X E}
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) {c' : OpenPartialHomeomorph Y E'}
    (hc' : ContMDiffOn J 𝓘(ℝ, E') ∞ c' c'.source)
    (hc's : ContMDiffOn 𝓘(ℝ, E') J ∞ c'.symm c'.target) (f : C^∞⟮I, X; J, Y⟯) {x : X}
    (hx : x ∈ c.source) (hfx : f x ∈ c'.source) (η : TangentSpace J (f x) →L[ℝ] ℝ) :
    ((fderiv ℝ (c' ∘ f ∘ c.symm) (c x))†)
        ((toDual ℝ E').symm (η ∘L mfderiv 𝓘(ℝ, E') J c'.symm (c' (f x)))) =
      (toDual ℝ E).symm ((η ∘L mfderiv I J f x) ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)) := by
  have hcx : MDifferentiableAt 𝓘(ℝ, E) I c.symm (c x) :=
    (hcs.contMDiffAt (c.open_target.mem_nhds (c.map_source hx))).mdifferentiableAt (by simp)
  have hc'x : MDifferentiableAt J 𝓘(ℝ, E') c' (f x) :=
    (hc'.contMDiffAt (c'.open_source.mem_nhds hfx)).mdifferentiableAt (by simp)
  have hc'sx : MDifferentiableAt 𝓘(ℝ, E') J c'.symm (c' (f x)) :=
    (hc's.contMDiffAt (c'.open_target.mem_nhds (c'.map_source hfx))).mdifferentiableAt (by simp)
  -- The chain rule for `Φ = c' ∘ f ∘ c⁻¹` at `c x`.
  have hf : HasMFDerivAt I J f (c.symm (c x)) (mfderiv I J f x) := by
    rw [c.left_inv hx]
    exact (f.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt
  have hc'f : HasMFDerivAt J 𝓘(ℝ, E') c' (f (c.symm (c x))) (mfderiv J 𝓘(ℝ, E') c' (f x)) := by
    rw [c.left_inv hx]
    exact hc'x.hasMFDerivAt
  have hΦ : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E') (c' ∘ f ∘ c.symm) (c x)
      ((mfderiv J 𝓘(ℝ, E') c' (f x)).comp ((mfderiv I J f x).comp
        (mfderiv 𝓘(ℝ, E) I c.symm (c x)))) :=
    hc'f.comp (c x) (hf.comp (c x) hcx.hasMFDerivAt)
  apply (toDual ℝ E).injective
  ext w
  have key : fderiv ℝ (c' ∘ f ∘ c.symm) (c x) w =
      mfderiv J 𝓘(ℝ, E') c' (f x) (mfderiv I J f x (mfderiv 𝓘(ℝ, E) I c.symm (c x) w)) := by
    have h := DFunLike.congr_fun hΦ.mfderiv w
    rw [mfderiv_eq_fderiv] at h
    -- The casts `NormedSpace.fromTangentSpace` inserted by `mfderiv_eq_fderiv` act as the identity
    -- by definition.
    exact h
  rw [LinearIsometryEquiv.apply_symm_apply, toDual_apply_apply,
    ContinuousLinearMap.adjoint_inner_left, toDual_symm_apply, key]
  exact congrArg η (c'.mfderiv_symm_apply_mfderiv_apply hfx hc'x hc'sx _)

/-! ### Microlocal smoothness of a pushforward -/

/-- The pushforward with a cutoff `ψ` supported in the source of a chart `c` whose source `f` maps
into the source of a chart `c'` at `y` is microlocally smooth at `(y, η)`, if `T` is microlocally
smooth at the pullbacks `η ∘ df_x ≠ 0` for the points `x` of `supp ψ ∩ supp T` over `y`. -/
private theorem isMicrolocallySmoothAt_cutoffPushforwardCLM_of_chart {c : OpenPartialHomeomorph X E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (t : Trivialization G (π G (Trivial X G))) [MemTrivializationAtlas t]
    (hct : c.source ⊆ t.baseSet) {y : Y} {c' : OpenPartialHomeomorph Y E'}
    (hc' : ContMDiffOn J 𝓘(ℝ, E') ∞ c' c'.source)
    (hc's : ContMDiffOn 𝓘(ℝ, E') J ∞ c'.symm c'.target)
    (hct' : c'.source ⊆ (trivializationAt G (Trivial Y G) y).baseSet) (hy : y ∈ c'.source)
    {f : C^∞⟮I, X; J, Y⟯} (hf : MapsTo f c.source c'.source) {ψ : C^∞⟮I, X; ℝ⟯}
    (hψc : HasCompactSupport ψ) (hψ : tsupport ψ ⊆ c.source)
    {T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ} {η : TangentSpace J y →L[ℝ] ℝ}
    (h : ∀ x ∈ tsupport ψ ∩ dsupport ⇑T, f x = y →
      η ∘L mfderiv I J f x ≠ 0 ∧ IsMicrolocallySmoothAt T x (η ∘L mfderiv I J f x)) :
    IsMicrolocallySmoothAt (cutoffPushforwardCLM ψ hψc f T) y η := by
  obtain ⟨ψ', hψ's, hψ'⟩ := exists_testFunction_apply_eq hcs hψc hψ
  have hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (c' ∘ f ∘ c.symm) c.target :=
    contMDiffOn_iff_contDiffOn.1 (hc'.comp (f.contMDiff.comp_contMDiffOn hcs)
      fun z hz ↦ hf (c.map_target hz))
  refine (isMicrolocallySmoothAt_iff _ hc' hc's hct' hy η).2 fun v ↦ ?_
  rw [chartComponent_cutoffPushforwardCLM hc hc' t hct _ hct' hψc
    (fun x hx ↦ ⟨hψ hx, hf (hψ hx)⟩) hψ' hΦ T v]
  refine Distribution.IsMicrolocallySmoothAt.cutoffPushforwardCLM (c'.map_source hy)
    fun z hz hzy ↦ ?_
  -- The point `z` is `c x` for a point `x` of `supp ψ ∩ supp T` over `y`.
  obtain ⟨x, hxψ, rfl⟩ := hψ's hz.1
  have hx : x ∈ c.source := hψ hxψ
  have hxT : x ∈ dsupport ⇑T := by
    simpa [c.left_inv hx] using t.symm_mem_dsupport_of_mem_dsupport_chartComponent c hc hct T v
      (c.map_source hx) hz.2
  have hfx : f x = y := c'.injOn (hf hx) hy (by simpa [c.left_inv hx] using hzy)
  subst hfx
  obtain ⟨hne, hT⟩ := h x ⟨hxψ, hxT⟩ rfl
  rw [adjoint_fderiv_toDual_symm_comp_mfderiv_symm hcs hc' hc's f hx (hf hx) η]
  refine ⟨fun h0 ↦ hne ?_, (isMicrolocallySmoothAt_iff T hc hcs hct hx _).1 hT v⟩
  -- A covector read as the zero vector in the chart `c` is zero.
  exact ((OpenPartialHomeomorph.MDifferentiable.comp_mfderiv_symm_bijective
    ⟨hc.mdifferentiableOn (by simp), hcs.mdifferentiableOn (by simp)⟩ hx).1.eq_iff'
      (zero_comp _)).1 ((toDual ℝ E).symm.map_eq_zero_iff.1 h0)

omit [T2Space X] [T2Space Y] [FiniteDimensional ℝ G] in
/-- Splitting a cutoff `χ` along finitely many functions `ρ i`: the pushforward with the cutoff `χ`
is the sum of the pushforwards with the cutoffs `ρ i χ` and `(1 - ∑ i, ρ i) χ`. -/
private theorem cutoffPushforwardCLM_eq_sum_add {ι : Type*} [Fintype ι] (ρ : ι → C^∞⟮I, X; ℝ⟯)
    {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ) :
    cutoffPushforwardCLM χ hχ f T = ∑ i, cutoffPushforwardCLM (ρ i * χ) hχ.mul_left f T +
      cutoffPushforwardCLM ((1 - ∑ i, ρ i) * χ) hχ.mul_left f T := by
  have hsum : smulLeftDualCLM (∑ i, ρ i) =
      (∑ i, smulLeftDualCLM (ρ i) : (BundleTest I G (Trivial X G) →L_c[ℝ] ℝ) →L[ℝ] _) :=
    map_sum (AddMonoidHom.mk' (fun g : C^∞⟮I, X; ℝ⟯ ↦
      (smulLeftDualCLM g : (BundleTest I G (Trivial X G) →L_c[ℝ] ℝ) →L[ℝ] _))
      smulLeftDualCLM_add) _ _
  conv_lhs => rw [← smulLeftDualCLM_one T, ← add_sub_cancel (∑ i, ρ i) 1, smulLeftDualCLM_add,
    _root_.add_apply, hsum, _root_.sum_apply, map_add, map_sum]
  simp only [cutoffPushforwardCLM_smulLeftDualCLM]

variable [I.Boundaryless] [J.Boundaryless]

omit [I.Boundaryless] in
/-- If no point of `supp ψ ∩ supp T` lies over `y`, the pushforward `f_* (ψ T)` vanishes near `y`,
so it is microlocally smooth at every covector at `y`. -/
private theorem isMicrolocallySmoothAt_cutoffPushforwardCLM_of_forall_ne {ψ : C^∞⟮I, X; ℝ⟯}
    (hψ : HasCompactSupport ψ) {f : C^∞⟮I, X; J, Y⟯} {T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ}
    {y : Y} (hy : ∀ x ∈ tsupport ψ ∩ dsupport ⇑T, f x ≠ y) (η : TangentSpace J y →L[ℝ] ℝ) :
    IsMicrolocallySmoothAt (cutoffPushforwardCLM ψ hψ f T) y η := by
  refine isMicrolocallySmoothAt_of_notMem_dsupport (notMem_dsupport_iff.2 ?_) η
  -- The pushforward vanishes off the compact image `f (supp ψ ∩ supp T)`, which misses `y`.
  have hC : IsCompact (f '' (tsupport ψ ∩ dsupport ⇑T)) :=
    (hψ.isCompact.inter_right (isClosed_dsupport _)).image f.contMDiff.continuous
  refine ⟨_, hC.isClosed.isOpen_compl, fun ⟨x, hx, hxy⟩ ↦ hy x hx hxy,
    isVanishingOn_iff.2 fun s hs ↦ ?_⟩
  refine cutoffPushforwardCLM_apply_eq_zero_of_disjoint _ f
    (isVanishingOn_iff.1 (isVanishingOn_compl_dsupport _)) ?_
  rw [sdiff_compl]
  exact subset_compl_iff_disjoint_right.1 hs

/-- **Microlocal smoothness of a pushforward along a smooth map of manifolds.** Let `f : X → Y` be
a smooth map of manifolds without boundary, `χ` a smooth cutoff with compact support on `X` and
`T` a functional on the tests on `X`, for instance a distribution density. Let `η` be a covector
at `y ∈ Y`. If for every point `x` of `supp χ ∩ supp T` with `f x = y` the pulled back covector
`η ∘ df_x` is nonzero and `T` is microlocally smooth at it, then the pushforward `f_* (χ T)` is
microlocally smooth at `η`. -/
theorem IsMicrolocallySmoothAt.cutoffPushforwardCLM {χ : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) {f : C^∞⟮I, X; J, Y⟯} {T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ}
    {y : Y} {η : TangentSpace J y →L[ℝ] ℝ}
    (h : ∀ x ∈ tsupport χ ∩ dsupport ⇑T, f x = y →
      η ∘L mfderiv I J f x ≠ 0 ∧ IsMicrolocallySmoothAt T x (η ∘L mfderiv I J f x)) :
    IsMicrolocallySmoothAt (cutoffPushforwardCLM χ hχ f T) y η := by
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H X
  obtain ⟨c', hc', hc's, hct', hy⟩ :=
    exists_chart_source_subset_baseSet G J (Trivial Y G) (n := ∞) y
  -- The compact set `K` of the points of `supp χ ∩ supp T` over `y` has a compact neighbourhood
  -- `L` that `f` maps into the chart source `c'.source`.
  set W := f ⁻¹' c'.source
  have hW : IsOpen W := c'.open_source.preimage f.contMDiff.continuous
  have hK : IsCompact (tsupport χ ∩ dsupport ⇑T ∩ f ⁻¹' {y}) :=
    (hχ.isCompact.inter_right (isClosed_dsupport _)).inter_right
      (isClosed_singleton.preimage f.contMDiff.continuous)
  obtain ⟨L, hL, hKL, hLW⟩ := exists_compact_between hK hW fun x hx ↦ by
    rw [mem_preimage, show f x = y from hx.2]
    exact hy
  -- Charts at the points of `X`, restricted to `W`, and a partition of unity `ρ` on `L`
  -- subordinate to them.
  choose c₀ hc₀ hcs₀ hct₀ hxc₀ using fun x : X ↦
    exists_chart_source_subset_baseSet G I (Trivial X G) (n := ∞) x
  set c : X → OpenPartialHomeomorph X E := fun x ↦ (c₀ x).restrOpen W hW
  obtain ⟨ι, _, ρb, hρb⟩ := hL.exists_smoothBumpCovering_isSubordinate I
    (U := fun x ↦ (c x).source) fun x hx ↦ (c x).open_source.mem_nhds ⟨hxc₀ x, hLW hx⟩
  set ρ := ρb.toSmoothPartitionOfUnity
  rw [cutoffPushforwardCLM_eq_sum_add ρ hχ f T]
  refine IsMicrolocallySmoothAt.add (Finset.sum_induction _ (fun S ↦ IsMicrolocallySmoothAt S y η)
    (fun _ _ ↦ IsMicrolocallySmoothAt.add)
    (isMicrolocallySmoothAt_def.2
      (isMicrolocallyAt_zero _ isInvariantMicrolocalRegularity_isMicrolocallySmoothAt y η))
    fun i _ ↦ ?_) (isMicrolocallySmoothAt_cutoffPushforwardCLM_of_forall_ne _
      (fun x hx hxy ↦ ?_) η)
  · -- A piece `ρ i χ` of the cutoff is supported in a chart.
    refine isMicrolocallySmoothAt_cutoffPushforwardCLM_of_chart (c := c (ρb.c i))
      ((hc₀ _).mono inter_subset_left) ((hcs₀ _).mono inter_subset_left) _
      (inter_subset_left.trans (hct₀ _)) hc' hc's hct' hy (fun x hx ↦ hx.2) hχ.mul_left
      (tsupport_mul_subset_left.trans (hρb.toSmoothPartitionOfUnity i))
      fun x hx hxy ↦ h x ⟨tsupport_mul_subset_right hx.1, hx.2⟩ hxy
  · -- The remainder `(1 - ∑ i, ρ i) χ` vanishes on `L`, hence near `K ⊆ interior L`.
    have hxL : x ∈ interior L := hKL ⟨⟨tsupport_mul_subset_right hx.1, hx.2⟩, hxy⟩
    refine (notMem_tsupport_iff_eventuallyEq.2 ?_) hx.1
    filter_upwards [isOpen_interior.mem_nhds hxL] with z hz
    have h1 : ∑ i, ρ i z = 1 := by
      rw [← finsum_eq_sum_of_fintype]
      exact ρ.sum_eq_one (interior_subset hz)
    simp [h1]

/-- **The wave front set of a pushforward along a smooth map of manifolds** (Hörmander I,
Theorem 8.2.13). Every covector `η` at `y` in the wave front set of the pushforward `f_* (χ T)` lies
over a point `x` of `supp χ ∩ supp T` with `f x = y`, at which either the pulled back covector
`η ∘ df_x` vanishes or it lies in the wave front set of `T`. The covectors with `η ∘ df_x = 0`
cannot be omitted: they record the critical points of `f`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ) :
    waveFrontSet J (cutoffPushforwardCLM χ hχ f T) ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport ⇑T, f x = p.proj ∧
        (p.snd ∘L mfderiv I J f x = 0 ∨ ⟨x, p.snd ∘L mfderiv I J f x⟩ ∈ waveFrontSet I T)} := by
  rintro ⟨y, η⟩ hp
  by_contra hne
  refine (mem_waveFrontSet_iff.1 hp).2 (IsMicrolocallySmoothAt.cutoffPushforwardCLM hχ
    fun x hx hxy ↦ ?_)
  by_cases h0 : η ∘L mfderiv I J f x = 0
  · exact absurd ⟨x, hx, hxy, Or.inl h0⟩ hne
  exact ⟨h0, not_not.1 fun hT ↦ hne ⟨x, hx, hxy, Or.inr (mem_waveFrontSet_iff.2 ⟨h0, hT⟩)⟩⟩

/-- **Pushforward along a submersion.** If the differential of `f` is surjective at every point of
`supp χ ∩ supp T`, every covector `η` at `y` in the wave front set of `f_* (χ T)` lies over a point
`x` of `supp χ ∩ supp T` with `f x = y` at which `η ∘ df_x` lies in the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_of_surjective {χ : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) {f : C^∞⟮I, X; J, Y⟯} {T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ}
    (hf : ∀ x ∈ tsupport χ ∩ dsupport ⇑T, Surjective (mfderiv I J f x)) :
    waveFrontSet J (cutoffPushforwardCLM χ hχ f T) ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport ⇑T, f x = p.proj ∧
        ⟨x, p.snd ∘L mfderiv I J f x⟩ ∈ waveFrontSet I T} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨x, hx, hxy, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset hχ f T hp
  refine ⟨x, hx, hxy, h.resolve_left fun h0 ↦ (mem_waveFrontSet_iff.1 hp).1 ?_⟩
  -- A covector vanishing on the range of a surjective differential vanishes.
  ext w
  obtain ⟨u, rfl⟩ := hf x hx w
  exact congr($h0 u)

/-- **Hörmander's wave front bound for a pushforward along a map proper on the support.** If the
smooth map `f` is proper on the support of `T`, every covector `η` at `y` in the wave front set of
the pushforward `f_* T` lies over a point `x` of the support of `T` with `f x = y`, at which either
`η ∘ df_x` vanishes or it lies in the wave front set of `T`. -/
theorem waveFrontSet_pushforward_subset {f : C^∞⟮I, X; J, Y⟯}
    {T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ} (hT : IsProperOnSupport ⇑T f) :
    waveFrontSet J (pushforward T f hT) ⊆
      {p | ∃ x ∈ dsupport ⇑T, f x = p.proj ∧
        (p.snd ∘L mfderiv I J f x = 0 ∨ ⟨x, p.snd ∘L mfderiv I J f x⟩ ∈ waveFrontSet I T)} := by
  have := J.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H' Y
  rintro ⟨y, η⟩ hp
  -- Near `y`, `f_* T` is the pushforward of `T` with a cutoff `χ` equal to `1` near the part of
  -- the support of `T` over a compact neighbourhood `K` of `y`.
  obtain ⟨K, hK, hyK⟩ := exists_compact_mem_nhds y
  obtain ⟨σ, hσ, hσ1, hσc, -, -⟩ := (hT.isCompact hK).exists_contMDiff_one_nhds_tsupport_subset I
    isOpen_univ (subset_univ _)
  set χ : C^∞⟮I, X; ℝ⟯ := ⟨σ, hσ⟩
  have hvan : IsVanishingOn ⇑(pushforward T f hT - cutoffPushforwardCLM χ hσc f T) (interior K) :=
    isVanishingOn_iff.2 fun s hs ↦ by
      rw [_root_.sub_apply, cutoffPushforwardCLM_apply,
        pushforward_apply_eq_cutoffCompCLM hT s (χ := χ) hσc (hσ1.filter_mono (nhdsSet_mono
          (inter_subset_inter_right _ (preimage_mono (hs.trans interior_subset))))), sub_self]
  have hsmooth := isMicrolocallySmoothAt_of_notMem_dsupport (notMem_dsupport_iff.2
    ⟨_, isOpen_interior, mem_interior_iff_mem_nhds.2 hyK, hvan⟩) η
  have hχp : (⟨y, η⟩ : CotangentBundle J Y) ∈ waveFrontSet J (cutoffPushforwardCLM χ hσc f T) :=
    mem_waveFrontSet_iff.2 ⟨(mem_waveFrontSet_iff.1 hp).1, fun h ↦ (mem_waveFrontSet_iff.1 hp).2
      (by simpa using h.add hsmooth)⟩
  obtain ⟨x, hx, hxy, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset hσc f T hχp
  exact ⟨x, hx.2, hxy, h⟩

end Pushforward

end TauCeti.BundleTest
