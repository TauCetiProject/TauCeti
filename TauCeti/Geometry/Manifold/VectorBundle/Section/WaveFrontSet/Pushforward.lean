/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Pushforward
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Pushforward
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# The wave front set of a pushforward of distribution densities

Let `f : X → Y` be a smooth map of manifolds without boundary modelled on finite-dimensional real
inner product spaces, and let `T` be a continuous linear functional on the tests
`TauCeti.BundleTest I G (Bundle.Trivial X G)`, the compactly supported smooth maps `X → G` for a
finite-dimensional `G`: for `G = ℝ`, a distribution density on `X`. Such a functional is pushed
forward along `f` with a compactly supported smooth cutoff `χ`, as
`f_* (χ T) : s ↦ T (χ (s ∘ f))` (`TauCeti.BundleTest.cutoffPushforwardCLM`), and, when `f` is
proper on the support of `T`, without a cutoff (`TauCeti.BundleTest.pushforward`). This file proves
Hörmander's bound for their wave front sets (`TauCeti.BundleTest.waveFrontSet`):

`WF(f_* (χ T)) ⊆ {(f x, η) | x ∈ supp χ ∩ supp T, η ∘ D f(x) = 0 or (x, η ∘ D f(x)) ∈ WF(T)}`.

Covectors are pulled back along the differential `D f(x) = mfderiv I J f x`, and the covectors
`η ≠ 0` with `η ∘ D f(x) = 0`, which occur at the critical points of `f`, cannot be omitted: along
a constant map the pushforward of a smooth density is a point mass, whose wave front set is all of
the nonzero covectors at the point (`Distribution.waveFrontSet_cutoffPushforwardCLM_const`, in
coordinates). When `D f(x)` is surjective on `supp χ ∩ supp T`, they do not occur.

## The argument

The statement is local in `Y`. Fix a chart `c'` at `y`. The points of `supp χ ∩ supp T` over `y`
form a compact set, which a finite smooth partition of unity `ρ` splits among charts `c` of `X`
whose sources `f` maps into the source of `c'`. The piece `(1 - ∑ ρ) χ` of the cutoff vanishes near
all these points, so its pushforward vanishes near `y`
(`TauCeti.BundleTest.dsupport_cutoffPushforwardCLM_subset`) and is microlocally smooth there
(`TauCeti.BundleTest.isMicrolocallySmoothAt_of_notMem_dsupport`). For a piece supported in the
source of a chart `c`, the components of `f_* (ρ χ T)` in `c'` are the Euclidean pushforwards of the
components of `T` in `c` along `Φ = c' ∘ f ∘ c⁻¹`, with the cutoff `(ρ χ) ∘ c⁻¹`, so the Euclidean
theorem `Distribution.IsMicrolocallySmoothAt.cutoffPushforwardCLM` applies to them. Covectors
match: the transpose of `DΦ` takes `η` read in `c'` to `η ∘ D f(x)` read in `c`
(`OpenPartialHomeomorph.adjoint_fderiv_toDual_symm_comp_mfderiv_symm`). The supports correspond as
well (`Bundle.Trivialization.dsupport_chartComponent_inter_target_subset`).

## Main results

* `TauCeti.BundleTest.IsMicrolocallySmoothAt.cutoffPushforwardCLM`: if for every
  `x ∈ supp χ ∩ supp T` with `f x = y` the covector `η ∘ D f(x)` is nonzero and `T` is microlocally
  smooth at it, then `f_* (χ T)` is microlocally smooth at `(y, η)`.
* `TauCeti.BundleTest.waveFrontSet_cutoffPushforwardCLM_subset`: the wave front bound above.
* `TauCeti.BundleTest.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`: when `D f(x)` is
  surjective on `supp χ ∩ supp T`, the bound
  `WF(f_* (χ T)) ⊆ {(f x, η) | x ∈ supp χ ∩ supp T, (x, η ∘ D f(x)) ∈ WF(T)}`.
* `TauCeti.BundleTest.waveFrontSet_pushforward_subset`: the same bound for the pushforward `f_* T`
  along a map proper on the support of `T`, with `x` ranging over the support of `T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.13 (the wave front set of a pushforward) and §8.2 (the wave front set
  on a manifold, after Theorem 8.2.4).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, Studia Math. 232 (2016), arXiv:1409.7662v2, §3 (pushforward
  along maps proper on the support).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology InnerProduct CompactConvergenceCLM

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization InnerProductSpace

variable {E H X E' H' Y G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [T2Space X] [IsManifold I ∞ X]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y] [IsManifold J ∞ Y]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

section Chart

variable {c : OpenPartialHomeomorph X E} {c' : OpenPartialHomeomorph Y E'}
  (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
  (hc' : ContMDiffOn J 𝓘(ℝ, E') ∞ c' c'.source)
  (hcs' : ContMDiffOn 𝓘(ℝ, E') J ∞ c'.symm c'.target)
  (f : C^∞⟮I, X; J, Y⟯)

/-- The open set of the points of the target of `c` that `f ∘ c⁻¹` maps into the source of
`c'`. -/
private def chartPreimage (c : OpenPartialHomeomorph X E) (c' : OpenPartialHomeomorph Y E')
    (f : C^∞⟮I, X; J, Y⟯) : Opens E :=
  ⟨c.target ∩ c.symm ⁻¹' (f ⁻¹' c'.source),
    c.isOpen_inter_preimage_symm (c'.open_source.preimage f.contMDiff.continuous)⟩

omit [FiniteDimensional ℝ E] [T2Space X] [IsManifold I ∞ X] [FiniteDimensional ℝ E'] [T2Space Y]
  [IsManifold J ∞ Y] in
private theorem chartPreimage_le : chartPreimage c c' f ≤ ⟨c.target, c.open_target⟩ :=
  fun _ hz ↦ hz.1

omit [FiniteDimensional ℝ E] [T2Space X] [IsManifold I ∞ X] [FiniteDimensional ℝ E'] [T2Space Y]
  [IsManifold J ∞ Y] in
include hcs hc' in
/-- The reading `c' ∘ f ∘ c⁻¹` of `f` in the charts is smooth on `chartPreimage c c' f`. -/
private theorem contDiffOn_chartPreimage :
    ContDiffOn ℝ (⊤ : ℕ∞) (c' ∘ f ∘ c.symm) (chartPreimage c c' f) := by
  rw [← contMDiffOn_iff_contDiffOn]
  have hf : ContMDiffOn 𝓘(ℝ, E) J ∞ (f ∘ c.symm) (chartPreimage c c' f) :=
    f.contMDiff.comp_contMDiffOn (hcs.mono fun z hz ↦ hz.1)
  exact (hc'.comp hf fun z hz ↦ hz.2).of_le (by simp)

omit [T2Space X] [IsManifold I ∞ X] [FiniteDimensional ℝ E'] [T2Space Y] [IsManifold J ∞ Y] in
include hcs in
/-- The reading `z ↦ χ (c⁻¹ z)` of a cutoff `χ` supported in the source of `c` and over the source
of `c'` is a test function on `chartPreimage c c' f`, supported in `c (supp χ)`. -/
private theorem exists_testFunction_eq_comp_symm {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ)
    (hχc : tsupport χ ⊆ c.source ∩ f ⁻¹' c'.source) :
    ∃ χ' : 𝓓(chartPreimage c c' f, ℝ), (∀ z ∈ chartPreimage c c' f, χ' z = χ (c.symm z)) ∧
      tsupport χ' ⊆ c '' tsupport χ := by
  set L := c '' tsupport χ
  have hL : IsCompact L := hχ.image_of_continuousOn (c.continuousOn.mono fun x hx ↦ (hχc hx).1)
  have hLΩ : L ⊆ chartPreimage c c' f := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨c.map_source (hχc hx).1, by simpa [c.left_inv (hχc hx).1] using (hχc hx).2⟩
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hL hLΩ
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (χ ∘ c.symm) (chartPreimage c c' f) := by
    rw [← contMDiffOn_iff_contDiffOn]
    have hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm (chartPreimage c c' f) :=
      hcs.mono fun z hz ↦ hz.1
    exact (χ.contMDiff.comp_contMDiffOn hcs').of_le (by simp)
  obtain ⟨χ', hχ'⟩ := TestFunction.exists_coe_eq_smul_of_contDiffOn hg θ
  -- Off `L`, the reading of `χ` vanishes on the chart target.
  have hzero {z : E} (hz : z ∈ c.target) (hzL : z ∉ L) : χ (c.symm z) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hzL ⟨_, h, c.right_inv hz⟩
  refine ⟨χ', fun z hz ↦ ?_, closure_minimal (fun z hz ↦ ?_) hL.isClosed⟩
  · rw [hχ']
    by_cases hzL : z ∈ L
    · simp [hθ.self_of_nhdsSet z hzL]
    · simp [hzero hz.1 hzL]
  · by_contra hzL
    have hzΩ : z ∈ chartPreimage c c' f := by
      by_contra h
      exact hz (by
        rw [hχ']
        simp [image_eq_zero_of_notMem_tsupport fun h' ↦ h (θ.tsupport_subset h')])
    exact hz (by rw [hχ']; simp [hzero hzΩ.1 hzL])

variable {t : Trivialization G (π G (Trivial X G))} [MemTrivializationAtlas t]
  {t' : Trivialization G (π G (Trivial Y G))} [MemTrivializationAtlas t']
  (hct : c.source ⊆ t.baseSet) (hct' : c'.source ⊆ t'.baseSet)

include hcs in
/-- For a cutoff `χ` supported in the source of `c` and over the source of `c'`, the components of
`f_* (χ T)` in `c'` are the Euclidean pushforwards of the components of `T` in `c` along
`c' ∘ f ∘ c⁻¹`, with the cutoff `χ ∘ c⁻¹`. -/
private theorem chartComponent_cutoffPushforwardCLM_eq {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ)
    (hχc : tsupport χ ⊆ c.source ∩ f ⁻¹' c'.source) {χ' : 𝓓(chartPreimage c c' f, ℝ)}
    (hχ' : ∀ z ∈ chartPreimage c c' f, χ' z = χ (c.symm z))
    (T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ) (v : G) :
    t'.chartComponent c' hc' hct' (cutoffPushforwardCLM χ hχ f T) v =
      Distribution.cutoffPushforwardCLM χ' (c' ∘ f ∘ c.symm) (contDiffOn_chartPreimage hcs hc' f)
        (restrictCLM (t.chartComponent c hc hct T v)) := by
  obtain rfl := Bundle.Trivial.eq_trivialization X G t
  obtain rfl := Bundle.Trivial.eq_trivialization Y G t'
  ext φ
  simp only [chartComponent_apply, Distribution.cutoffPushforwardCLM_apply, restrictCLM_apply,
    cutoffPushforwardCLM_apply]
  congr 2
  refine BundleTest.ext fun x ↦ ?_
  have hχx (hx : x ∉ c.source ∩ f ⁻¹' c'.source) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχc h)
  rw [cutoffCompCLM_apply]
  by_cases hx : x ∈ c.source
  · rw [chartTestCLM_apply_of_mem _ _ _ _ _ hx]
    by_cases hfx : f x ∈ c'.source
    · have hz : c x ∈ chartPreimage c c' f :=
        ⟨c.map_source hx, by simpa [c.left_inv hx] using hfx⟩
      rw [chartTestCLM_apply_of_mem _ _ _ _ _ hfx]
      simp [TestFunction.coe_monoCLM_of_le le_rfl (chartPreimage_le f),
        TestFunction.cutoffCompCLM_apply, hχ' _ hz, c.left_inv hx, smul_smul]
    · have hz : c x ∉ chartPreimage c c' f := fun h ↦ hfx (by simpa [c.left_inv hx] using h.2)
      rw [chartTestCLM_apply_of_notMem _ _ _ _ _ hfx]
      simp [TestFunction.coe_monoCLM_of_le le_rfl (chartPreimage_le f),
        image_eq_zero_of_notMem_tsupport fun h ↦ hz (χ'.tsupport_subset h)]
  · rw [chartTestCLM_apply_of_notMem _ _ _ _ _ hx, hχx fun h ↦ hx h.1]
    simp

include hc hcs hc' hcs' hct hct' in
/-- **Microlocal smoothness of a pushforward, in charts.** Let `χ` be a cutoff supported in the
source of a chart `c` of `X` and over the source of a chart `c'` of `Y`, and let `y` lie in the
source of `c'`. If for every `x ∈ supp χ ∩ supp T` with `f x = y` the pullback `η ∘ D f(x)` is
nonzero and `T` is microlocally smooth at it, then `f_* (χ T)` is microlocally smooth at
`(y, η)`. -/
private theorem isMicrolocallySmoothAt_cutoffPushforwardCLM_of_tsupport_subset {χ : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) (hχc : tsupport χ ⊆ c.source ∩ f ⁻¹' c'.source)
    {T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ} {y : Y} (hy : y ∈ c'.source)
    {η : TangentSpace J y →L[ℝ] ℝ}
    (h : ∀ x ∈ tsupport χ ∩ dsupport T, f x = y →
      η ∘L mfderiv I J f x ≠ 0 ∧ IsMicrolocallySmoothAt T x (η ∘L mfderiv I J f x)) :
    IsMicrolocallySmoothAt (cutoffPushforwardCLM χ hχ f T) y η := by
  obtain ⟨χ', hχ', hχ'L⟩ := exists_testFunction_eq_comp_symm hcs f hχ hχc
  refine (isMicrolocallySmoothAt_iff _ hc' hcs' hct' hy η).2 fun v ↦ ?_
  rw [chartComponent_cutoffPushforwardCLM_eq hc hcs hc' f hct hct' hχ hχc hχ' T v]
  refine IsMicrolocallySmoothAt.cutoffPushforwardCLM (c'.map_source hy) fun z hz hzy ↦ ?_
  -- The point `z` is `c x` for some `x ∈ supp χ ∩ supp T` with `f x = y`.
  obtain ⟨x, hxχ, rfl⟩ := hχ'L hz.1
  have hxc : x ∈ c.source := (hχc hxχ).1
  have hfx : f x ∈ c'.source := (hχc hxχ).2
  have hxy : f x = y := c'.injOn hfx hy (by simpa [c.left_inv hxc] using hzy)
  have hxT : x ∈ dsupport T := by
    have hz₂ := hz.2
    rw [funext (restrictCLM_apply (t.chartComponent c hc hct T v))] at hz₂
    simpa [c.left_inv hxc] using t.dsupport_chartComponent_inter_target_subset c hc hct T v
      ⟨Distribution.dsupport_comp_monoCLM_subset _ hz₂, c.map_source hxc⟩
  subst hxy
  obtain ⟨hne, hT⟩ := h x ⟨hxχ, hxT⟩ rfl
  rw [OpenPartialHomeomorph.adjoint_fderiv_toDual_symm_comp_mfderiv_symm hxc hfx
    ((hcs.contMDiffAt (c.open_target.mem_nhds (c.map_source hxc))).mdifferentiableAt (by simp))
    (f.contMDiff.mdifferentiableAt (by simp))
    ((hc'.contMDiffAt (c'.open_source.mem_nhds hfx)).mdifferentiableAt (by simp))
    ((hcs'.contMDiffAt (c'.open_target.mem_nhds (c'.map_source hfx))).mdifferentiableAt
      (by simp)) η]
  refine ⟨mt (c.toDual_symm_comp_mfderiv_symm_eq_zero_iff hc hcs hxc).1 hne, ?_⟩
  rw [isInvariantMicrolocalRegularity_isMicrolocallySmoothAt.restrictCLM_iff (chartPreimage_le f)
    (χ'.tsupport_subset hz.1)]
  exact (isMicrolocallySmoothAt_iff T hc hcs hct hxc _).1 hT v

end Chart


section Global

variable [I.Boundaryless] [J.Boundaryless] {f : C^∞⟮I, X; J, Y⟯}
  {T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ}

omit [I.Boundaryless] in
/-- If no point of `supp χ ∩ supp T` lies over `y`, then `f_* (χ T)` vanishes near `y`, so it is
microlocally smooth at every covector at `y`. -/
private theorem isMicrolocallySmoothAt_cutoffPushforwardCLM_of_forall_ne {χ : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) {y : Y} (h : ∀ x ∈ tsupport χ ∩ dsupport T, f x ≠ y)
    (η : TangentSpace J y →L[ℝ] ℝ) :
    IsMicrolocallySmoothAt (cutoffPushforwardCLM χ hχ f T) y η :=
  isMicrolocallySmoothAt_of_notMem_dsupport (fun hy ↦
    let ⟨x, hx, hxy⟩ := dsupport_cutoffPushforwardCLM_subset hχ hy
    h x hx hxy) η

omit [T2Space X] [T2Space Y] [FiniteDimensional ℝ G] [I.Boundaryless] [J.Boundaryless] in
/-- A cutoff pushforward splits along a finite family `ρ` of smooth functions and the remainder
`1 - ∑ ρ`. -/
private theorem cutoffPushforwardCLM_eq_sum_add {ι : Type*} [Fintype ι] (ρ : ι → C^∞⟮I, X; ℝ⟯)
    {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ) :
    cutoffPushforwardCLM χ hχ f T = ∑ i, cutoffPushforwardCLM (ρ i * χ) hχ.mul_left f T +
      cutoffPushforwardCLM ((1 - ∑ i, ρ i) * χ) hχ.mul_left f T := by
  conv_lhs => rw [← smulLeftDualCLM_one T, ← add_sub_cancel (∑ i, ρ i) 1, smulLeftDualCLM_add,
    _root_.add_apply, smulLeftDualCLM_sum, _root_.sum_apply, map_add, map_sum]
  simp only [cutoffPushforwardCLM_smulLeftDualCLM]

/-- **Microlocal smoothness of a pushforward along a smooth map.** Let `χ` be a compactly
supported smooth function on `X`, `y ∈ Y` and `η` a covector at `y`. If for every
`x ∈ supp χ ∩ supp T` with `f x = y` the pulled-back covector `η ∘ D f(x)` is nonzero and `T` is
microlocally smooth at it, then the pushforward `f_* (χ T)` is microlocally smooth at `(y, η)`. -/
theorem IsMicrolocallySmoothAt.cutoffPushforwardCLM {χ : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) {y : Y} {η : TangentSpace J y →L[ℝ] ℝ}
    (h : ∀ x ∈ tsupport χ ∩ dsupport T, f x = y →
      η ∘L mfderiv I J f x ≠ 0 ∧ IsMicrolocallySmoothAt T x (η ∘L mfderiv I J f x)) :
    IsMicrolocallySmoothAt (cutoffPushforwardCLM χ hχ f T) y η := by
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H X
  obtain ⟨c', hc', hcs', hct', hyc'⟩ :=
    exists_chart_source_subset_baseSet G J (Trivial Y G) (n := ∞) y
  -- The points of `supp χ ∩ supp T` over `y` lie in the interior of a compact subset `L` of
  -- `f⁻¹(c'.source)`.
  have hO : IsOpen (f ⁻¹' c'.source) := c'.open_source.preimage f.contMDiff.continuous
  have hK : IsCompact (tsupport χ ∩ dsupport T ∩ f ⁻¹' {y}) :=
    (hχ.inter_right (isClosed_dsupport _)).inter_right
      (isClosed_singleton.preimage f.contMDiff.continuous)
  obtain ⟨L, hL, hKL, hLO⟩ := exists_compact_between hK hO fun x hx ↦ by
    rw [mem_preimage, mem_singleton_iff.1 hx.2]
    exact hyc'
  -- A finite smooth partition of unity `ρ` on `L` subordinate to chart sources.
  choose c hc hcs hct hxc using fun x : X ↦
    exists_chart_source_subset_baseSet G I (Trivial X G) (n := ∞) x
  obtain ⟨ι, _, fs, hfs⟩ := hL.exists_smoothBumpCovering_isSubordinate (I := I)
    (U := fun x ↦ (c x).source ∩ f ⁻¹' c'.source)
    fun x hx ↦ inter_mem ((c x).open_source.mem_nhds (hxc x)) (hO.mem_nhds (hLO hx))
  set ρ := fs.toSmoothPartitionOfUnity
  have hρ := hfs.toSmoothPartitionOfUnity
  rw [cutoffPushforwardCLM_eq_sum_add (fun i ↦ ρ i)]
  refine (IsMicrolocallySmoothAt.sum _ fun i _ ↦ ?_).add ?_
  · -- Each piece `ρ i χ` is supported in a chart source over the source of `c'`.
    have hsupp : tsupport ⇑(ρ i * χ) ⊆ tsupport (ρ i) := by
      rw [ContMDiffMap.coe_mul]
      exact tsupport_mul_subset_left
    refine isMicrolocallySmoothAt_cutoffPushforwardCLM_of_tsupport_subset (hc _) (hcs _) hc' hcs'
      f (hct _) hct' _ (hsupp.trans (hρ i)) hyc' fun x hx hxy ↦ h x ⟨?_, hx.2⟩ hxy
    rw [ContMDiffMap.coe_mul] at hx
    exact tsupport_mul_subset_right hx.1
  · -- The remainder `(1 - ∑ ρ) χ` vanishes near the points of `supp χ ∩ supp T` over `y`.
    refine isMicrolocallySmoothAt_cutoffPushforwardCLM_of_forall_ne _ (fun x hx hxy ↦ ?_) η
    rw [ContMDiffMap.coe_mul] at hx
    have hxL : x ∈ interior L := hKL ⟨⟨tsupport_mul_subset_right hx.1, hx.2⟩, hxy⟩
    refine (notMem_tsupport_iff_eventuallyEq.2 ?_) (tsupport_mul_subset_left hx.1)
    filter_upwards [isOpen_interior.mem_nhds hxL] with w hw
    have h1 := ρ.sum_eq_one (interior_subset hw)
    rw [finsum_eq_sum_of_fintype] at h1
    simp [h1]

/-- **The wave front set of a pushforward along a smooth map** (Hörmander I, Theorem 8.2.13).
Every covector `(y, η)` in the wave front set of the pushforward `f_* (χ T)` lies over a point
`x ∈ supp χ ∩ supp T` with `f x = y`, at which either `η ∘ D f(x) = 0` or `(x, η ∘ D f(x))` lies
in the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (T : BundleTest I G (Trivial X G) →L_c[ℝ] ℝ) :
    waveFrontSet J (cutoffPushforwardCLM χ hχ f T) ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, f x = p.proj ∧ (p.snd ∘L mfderiv I J f x = 0 ∨
        TotalSpace.mk x (p.snd ∘L mfderiv I J f x) ∈ waveFrontSet I T)} := by
  intro p hp
  by_contra hp'
  refine (mem_waveFrontSet_iff.1 hp).2
    (IsMicrolocallySmoothAt.cutoffPushforwardCLM hχ fun x hx hxy ↦ ?_)
  by_cases h0 : p.snd ∘L mfderiv I J f x = 0
  · exact absurd ⟨x, hx, hxy, Or.inl h0⟩ hp'
  exact ⟨h0, by_contra fun hT ↦ hp' ⟨x, hx, hxy, Or.inr (mem_waveFrontSet_iff.2 ⟨h0, hT⟩)⟩⟩

/-- **Pushforward along a submersion.** If the differential of `f` is surjective at every point
of `supp χ ∩ supp T`, every covector `(y, η)` in the wave front set of `f_* (χ T)` lies over a
point `x ∈ supp χ ∩ supp T` with `f x = y` and `(x, η ∘ D f(x))` in the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_of_surjective {χ : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ)
    (hf : ∀ x ∈ tsupport χ ∩ dsupport T, Surjective (mfderiv I J f x)) :
    waveFrontSet J (cutoffPushforwardCLM χ hχ f T) ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, f x = p.proj ∧
        TotalSpace.mk x (p.snd ∘L mfderiv I J f x) ∈ waveFrontSet I T} := by
  intro p hp
  obtain ⟨x, hx, hxy, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset hχ f T hp
  refine ⟨x, hx, hxy, h.resolve_left fun h0 ↦ (mem_waveFrontSet_iff.1 hp).1 ?_⟩
  ext w
  obtain ⟨u, rfl⟩ := hf x hx w
  exact congr($h0 u)

/-- **Hörmander's wave front bound for a pushforward along a map proper on the support.**
If `f` is proper on the support of `T`, every covector `(y, η)` in the wave front set of the
pushforward `f_* T` lies over a point `x ∈ supp T` with `f x = y`, at which either
`η ∘ D f(x) = 0` or `(x, η ∘ D f(x))` lies in the wave front set of `T`. -/
theorem waveFrontSet_pushforward_subset (hT : IsProperOnSupport ⇑T f) :
    waveFrontSet J (pushforward T f hT) ⊆
      {p | ∃ x ∈ dsupport T, f x = p.proj ∧ (p.snd ∘L mfderiv I J f x = 0 ∨
        TotalSpace.mk x (p.snd ∘L mfderiv I J f x) ∈ waveFrontSet I T)} := by
  have := J.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H' Y
  intro p hp
  by_contra hp'
  -- Over the interior of a compact neighbourhood `K` of `p.proj`, `f_* T` is the pushforward of
  -- `T` with a cutoff `χ` equal to one near `supp T ∩ f⁻¹(K)`.
  obtain ⟨K, hK, hKp⟩ := exists_compact_mem_nhds p.proj
  obtain ⟨χ, hχs, hχ1, hχc, -, -⟩ :=
    (hT.isCompact hK).exists_contMDiff_one_nhds_tsupport_subset I isOpen_univ (subset_univ _)
  let χ' : C^∞⟮I, X; ℝ⟯ := ⟨χ, hχs⟩
  have hD : p.proj ∉ dsupport ⇑(pushforward T f hT - cutoffPushforwardCLM χ' hχc f T) := by
    refine notMem_dsupport_iff.2 ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.2 hKp,
      isVanishingOn_iff.2 fun s hs ↦ ?_⟩
    rw [_root_.sub_apply, sub_eq_zero, cutoffPushforwardCLM_apply]
    exact pushforward_apply_eq_cutoffCompCLM hT s hχc (hχ1.filter_mono (nhdsSet_mono
      (inter_subset_inter_right _ (preimage_mono (hs.trans interior_subset)))))
  refine (mem_waveFrontSet_iff.1 hp).2 ?_
  rw [← sub_add_cancel (pushforward T f hT) (cutoffPushforwardCLM χ' hχc f T)]
  refine (isMicrolocallySmoothAt_of_notMem_dsupport hD _).add
    (IsMicrolocallySmoothAt.cutoffPushforwardCLM hχc fun x hx hxy ↦ ?_)
  by_cases h0 : p.snd ∘L mfderiv I J f x = 0
  · exact absurd ⟨x, hx.2, hxy, Or.inl h0⟩ hp'
  exact ⟨h0, by_contra fun hT' ↦ hp' ⟨x, hx.2, hxy, Or.inr (mem_waveFrontSet_iff.2 ⟨h0, hT'⟩)⟩⟩

end Global

end TauCeti.BundleTest
