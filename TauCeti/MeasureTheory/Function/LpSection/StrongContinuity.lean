/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.LpSection.BundleMap
public import TauCeti.MeasureTheory.Function.LpSection.Dense
import TauCeti.Topology.VectorBundle.Section
import TauCeti.Topology.VectorBundle.Smul

/-!
# Strong continuity of transport along continuous families of bundle maps

Let `E → M` and `E' → N` be vector bundles with continuous fibre norms, and let
`A g y : E (ψ g y) →ₗᵢ[𝕜] E' y` be a family of isometric bundle maps, depending on a parameter `g`
in a topological space `G`, each covering a measure-preserving map `ψ g : (N, ν) → (M, μ)`.
Transport along `A g` is a linear isometry `U g : Lᵖ(E, μ) → Lᵖ(E', ν)`,
`(U g s)(y) = A g y (s (ψ g y))` (`TauCeti.LpSection.compBundleMapₗᵢ`). This file proves that it
depends continuously on `g` in the strong operator topology, for `p < ∞`, when the family varies
continuously: `(f, g) ↦ U g f` is jointly continuous
(`TauCeti.LpSection.continuous_compBundleMapₗᵢ`), so in particular every orbit `g ↦ U g f` is
continuous (`TauCeti.LpSection.continuous_compBundleMapₗᵢ_apply`).

The base `M` is a finite-dimensional manifold and `E` a smooth bundle, so that compactly supported
smooth sections are dense in `Lᵖ(E, μ)` (`TauCeti.LpSection.denseRange_ofCompactlySupported`). The
base `N` is compact and `ν` finite. The continuity of the family is asked in the form in which it is
used and in which a continuous group action supplies it: transporting a continuous section `s` of
`E` gives a continuous family of vectors `(g, y) ↦ A g y (s (ψ g y)) ∈ E' y`.

For a topological group `G` acting continuously on a smooth bundle over a compact manifold,
preserving a finite measure and a continuous Hermitian metric, the operators `U g` are the
unitaries of the `L²`-section action, and this is its strong continuity. The restriction `p < ∞`
is needed: for the translations of the circle `ℝ / ℤ` acting on the trivial line, the indicator
function of an arc moves at constant distance `1` in `L^∞` under every nonzero translation small
enough.

## The argument

Each `U g` is an isometry, so the maps `f ↦ U g f` are uniformly Lipschitz, and joint continuity
follows from continuity of the orbits `g ↦ U g s` of a dense set of `s`
(`continuous_prod_of_dense_continuous_lipschitzWith`), the compactly supported smooth sections.
This is the argument of Mathlib's `MeasureTheory.Lp.compMeasurePreserving_continuous` for
composition of functions with measure-preserving maps, whose dense set is the simple functions.
For a compactly supported smooth `s`, the fibre norm `‖A g y (s (ψ g y)) - A g₀ y (s (ψ g₀ y))‖`
of the difference of two continuous families of vectors (`Continuous.add_totalSpace`,
`Continuous.smul_totalSpace`) is continuous in `(g, y)` and vanishes at `g = g₀`. Since `N` is
compact, it is uniformly small for `g` near `g₀`, and so is the `Lᵖ` norm of `U g s - U g₀ s`,
since `ν` is finite (`TauCeti.LpSection.norm_le_of_ae_bound`).

## Main results

* `TauCeti.LpSection.continuous_compBundleMapₗᵢ`: joint continuity of `(f, g) ↦ U g f`.
* `TauCeti.LpSection.continuous_compBundleMapₗᵢ_apply`: strong continuity, `g ↦ U g f` is
  continuous for every `f`.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968), §2
  and §6 (the action of a compact group on the sections of an equivariant bundle).
-/

public section

noncomputable section

open Bundle MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff

namespace TauCeti.LpSection

variable {𝕜 M N F F' EM HM : Type*} [RCLike 𝕜]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [FiniteDimensional 𝕜 F]
  {E : M → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace 𝕜 (E x)] [∀ x, Module ℝ (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [VectorBundle ℝ F E] [ContMDiffVectorBundle ∞ F E I] [ContinuousFiberNorm F E]
  [TopologicalSpace N] [CompactSpace N] [MeasurableSpace N] [OpensMeasurableSpace N]
  [SecondCountableTopology N]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {E' : N → Type*} [TopologicalSpace (TotalSpace F' E')] [∀ y, NormedAddCommGroup (E' y)]
  [∀ y, NormedSpace 𝕜 (E' y)] [FiberBundle F' E'] [VectorBundle 𝕜 F' E']
  [ContinuousFiberNorm F' E']
  {μ : Measure M} {ν : Measure N} [IsFiniteMeasure ν]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {G : Type*} [TopologicalSpace G] {ψ : G → N → M} (hψ : ∀ g, MeasurePreserving (ψ g) ν μ)
  {A : ∀ g y, E (ψ g y) →ₗᵢ[𝕜] E' y}
  (hA : ∀ g, IsContinuousBundleMap 𝕜 F F' (ψ g) fun y ↦ (A g y).toContinuousLinearMap)

omit [FiniteDimensional ℝ EM] [IsManifold I ∞ M] [T2Space M] [FiniteDimensional 𝕜 F]
  [ContMDiffVectorBundle ∞ F E I] in
include hψ in
/-- The transport of a compactly supported smooth section `s` along a continuous family of
isometric bundle maps depends continuously on the parameter. -/
private theorem continuous_compBundleMapₗᵢ_ofCompactlySupported [IsFiniteMeasureOnCompacts μ]
    (hcont : ∀ s : ∀ x, E x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) →
      Continuous fun q : G × N ↦ TotalSpace.mk' F' q.2 (A q.1 q.2 (s (ψ q.1 q.2))))
    (s : ContMDiffSection.compactlySupported I F (∞ : ℕ∞ω) E) :
    Continuous fun g ↦ compBundleMapₗᵢ p (hψ g) (A g) (hA g) (ofCompactlySupported 𝕜 I p μ s) := by
  set f := ofCompactlySupported 𝕜 I p μ s
  have hfs : ∀ᵐ x ∂μ, f x = s.val x := coeFn_ofCompactlySupported s
  have hΦ := hcont s.val s.val.contMDiff.continuous
  refine continuous_iff_continuousAt.2 fun g₀ ↦ Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  -- The fibre norm of the difference of the transported sections is continuous in `(g, y)`.
  have hsub : Continuous fun q : G × N ↦ TotalSpace.mk' F' q.2
      (A q.1 q.2 (s.val (ψ q.1 q.2)) + (-1 : 𝕜) • A g₀ q.2 (s.val (ψ g₀ q.2))) :=
    hΦ.add_totalSpace 𝕜 (Continuous.smul_totalSpace (c := fun _ ↦ (-1 : 𝕜)) continuous_const
      (hΦ.comp (continuous_const.prodMk continuous_snd)))
  have hD : Continuous fun q : G × N ↦
      ‖A q.1 q.2 (s.val (ψ q.1 q.2)) - A g₀ q.2 (s.val (ψ g₀ q.2))‖ := by
    simpa [neg_one_smul, ← sub_eq_add_neg, Function.comp_def] using
      (ContinuousFiberNorm.continuous_norm (F := F') (E := E')).comp hsub
  -- The constant relating uniform bounds to `Lᵖ` norms.
  set C : ℝ := (measureUnivNNReal ν : ℝ) ^ p.toReal⁻¹
  have hC : 0 ≤ C := by positivity
  set δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  -- By compactness of `N`, the difference is uniformly small for `g` near `g₀`.
  have hunif : ∀ᶠ g in 𝓝 g₀, ∀ y ∈ (univ : Set N),
      ‖A g y (s.val (ψ g y)) - A g₀ y (s.val (ψ g₀ y))‖ < δ :=
    isCompact_univ.eventually_forall_of_forall_eventually fun y _ ↦
      hD.continuousAt.eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [hunif] with g hg
  rw [dist_eq_norm]
  -- Almost everywhere the difference of the classes is the difference of the transports.
  have hae : ∀ᵐ y ∂ν, ‖(compBundleMapₗᵢ p (hψ g) (A g) (hA g) f -
      compBundleMapₗᵢ p (hψ g₀) (A g₀) (hA g₀) f) y‖ ≤ δ := by
    filter_upwards [coeFn_sub (compBundleMapₗᵢ p (hψ g) (A g) (hA g) f)
        (compBundleMapₗᵢ p (hψ g₀) (A g₀) (hA g₀) f),
      coeFn_compBundleMapₗᵢ (hψ g) (hA g) f, coeFn_compBundleMapₗᵢ (hψ g₀) (hA g₀) f,
      (hψ g).quasiMeasurePreserving.ae hfs, (hψ g₀).quasiMeasurePreserving.ae hfs]
      with y h h₁ h₂ h₃ h₄
    rw [h, h₁, h₂, h₃, h₄]
    exact (hg y (mem_univ y)).le
  calc _ ≤ C * δ := norm_le_of_ae_bound _ hδ.le hae
    _ < (C + 1) * δ := by nlinarith
    _ = ε := by
      simp only [δ]
      field_simp

variable (I) in
include I hψ in
/-- **Joint continuity of transport along a continuous family of bundle maps.** Let
`A g y : E (ψ g y) →ₗᵢ[𝕜] E' y` be isometric bundle maps continuous in charts, covering
measure-preserving maps `ψ g` from `(N, ν)` to `(M, μ)`, for `g` in a topological space `G`, with
`N` compact and `ν` finite. If transporting any continuous section `s` of `E` gives a continuous
family of vectors `(g, y) ↦ A g y (s (ψ g y))`, then for `p < ∞` the transport
`(f, g) ↦ (y ↦ A g y (f (ψ g y)))` is jointly continuous from `Lᵖ(E, μ) × G` to `Lᵖ(E', ν)`. -/
theorem continuous_compBundleMapₗᵢ (hp : p ≠ ⊤)
    (hcont : ∀ s : ∀ x, E x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) →
      Continuous fun q : G × N ↦ TotalSpace.mk' F' q.2 (A q.1 q.2 (s (ψ q.1 q.2)))) :
    Continuous fun q : LpSection 𝕜 F E p μ × G ↦
      compBundleMapₗᵢ p (hψ q.2) (A q.2) (hA q.2) q.1 := by
  refine continuous_iff_continuousAt.2 fun q ↦ ?_
  -- `μ` is the image of the finite measure `ν` under `ψ q.2`, hence finite.
  have : IsFiniteMeasure μ := (hψ q.2).map_eq ▸ ν.isFiniteMeasure_map (ψ q.2)
  refine Continuous.continuousAt ?_
  refine continuous_prod_of_dense_continuous_lipschitzWith _ 1
    (denseRange_ofCompactlySupported (I := I) hp) ?_ fun g ↦
      (compBundleMapₗᵢ p (hψ g) (A g) (hA g)).isometry.lipschitzWith
  rintro _ ⟨s, rfl⟩
  exact continuous_compBundleMapₗᵢ_ofCompactlySupported hψ hA hcont s

variable (I) in
include I hψ in
/-- **Strong continuity of transport along a continuous family of bundle maps.** Under the
hypotheses of `TauCeti.LpSection.continuous_compBundleMapₗᵢ`, for `p < ∞` the transport of every
`f ∈ Lᵖ(E, μ)` along `A g` depends continuously on `g`. For a topological group acting
continuously on a smooth bundle over a compact manifold, preserving a finite measure and a
Hermitian metric, this is the strong continuity of the induced unitary action on `L²` sections. -/
theorem continuous_compBundleMapₗᵢ_apply (hp : p ≠ ⊤)
    (hcont : ∀ s : ∀ x, E x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) →
      Continuous fun q : G × N ↦ TotalSpace.mk' F' q.2 (A q.1 q.2 (s (ψ q.1 q.2))))
    (f : LpSection 𝕜 F E p μ) :
    Continuous fun g ↦ compBundleMapₗᵢ p (hψ g) (A g) (hA g) f :=
  (continuous_compBundleMapₗᵢ I hψ hA hp hcont).comp (continuous_const.prodMk continuous_id)

end TauCeti.LpSection
