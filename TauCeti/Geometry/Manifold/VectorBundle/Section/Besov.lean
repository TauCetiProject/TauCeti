/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local.ChangeOfVariables
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartComponent
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# Local Besov regularity of distributions on manifolds

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a finite-dimensional
real inner product space `E`, and let `T` be a real continuous linear functional on the bundle tests
`TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, the component of `T` along `v : F` (`Bundle.Trivialization.chartComponent`) is
the complex distribution `ψ ↦ T (ψ • v)` on the chart target, the test function `ψ • v` being
extended to a bundle test through the chart and the frame.

Fix the bump function `φ` of a Littlewood–Paley partition of `E`, a real order `s` and exponents
`1 ≤ p, q ≤ ∞`. The functional `T` is **`B^s_{p,q}` near `x`**
(`TauCeti.BundleTest.IsLocallyMemBesovAt`) when, in some such chart at `x` and frame, all its
components are `B^s_{p,q}` near `c x` (`Distribution.IsLocallyMemBesovAt`). For `p = q = ∞` this is
membership of `T` in the local Hölder–Zygmund space `𝒞^s_loc` near `x`, for every real `s`,
including negative orders. Neither the bump function
(`TauCeti.BundleTest.IsLocallyMemBesovAt.of_bump`) nor the chart and the frame matter: for two
charts `c`, `c'` with frames `t`, `t'` and a point `x` of both chart sources, all components in
`(t', c')` are `B^s_{p,q}` near `c' x` exactly when all components in `(t, c)` are `B^s_{p,q}`
near `c x` (`Bundle.Trivialization.forall_isLocallyMemBesovAt_chartComponent_iff`). Hence `T` is
`B^s_{p,q}` near `x` exactly when its components are `B^s_{p,q}` near `c x` in any chart `c` at
`x` and any frame (`TauCeti.BundleTest.isLocallyMemBesovAt_iff`).

## The argument

Near `c' x`, the component along `v` in `(t', c')` is

`S'_v = ∑ⱼ gⱼ κ^* S_{bⱼ}`, with `gⱼ = |det Dκ| · bⱼ*(G(c'⁻¹ ·) v)`,

where `κ = c ∘ c'⁻¹` is the chart transition, `G = t ∘ t'⁻¹` the change of frame, `S_{bⱼ}` the
components in `(t, c)` along a basis `(bⱼ)` of `F` and `κ^*` the pullback of distributions
(`Bundle.Trivialization.restrictCLM_chartComponent_eq_sum`). The pullback preserves local Besov
regularity (`Distribution.isLocallyMemBesovAt_compCLMOfOpenPartialHomeomorph_iff`), and so do
restriction to open sets, smooth multiples and finite sums. Exchanging the roles of the two charts
gives the converse. This is the argument for the Sobolev scale `H^s`
(`Bundle.Trivialization.forall_isLocallySobolevAt_chartComponent_iff`).

## Main declarations

* `Bundle.Trivialization.forall_isLocallyMemBesovAt_chartComponent_iff`: local Besov regularity of
  all components does not depend on the chart and the frame.
* `TauCeti.BundleTest.IsLocallyMemBesovAt`: the functional `T` is `B^s_{p,q}` near a point of `M`,
  and `TauCeti.BundleTest.isLocallyMemBesovAt_iff`, its characterization in every chart and frame.
* `TauCeti.BundleTest.isOpen_setOf_isLocallyMemBesovAt`: the points near which `T` is
  `B^s_{p,q}` form an open set, and the rules for sums, differences, negatives and real multiples.
* `TauCeti.BundleTest.exists_forall_isLocallyMemBesovAt`: on a manifold without boundary and for
  `1 < p` and `1 ≤ q`, every functional on bundle tests has a finite Besov order near every compact
  set.

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §3.2.2 (Besov spaces on manifolds,
  defined chart by chart, and their independence of the charts).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (the local Sobolev spaces on manifolds, defined chart by chart).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology CompactConvergenceCLM ENNReal

namespace Bundle.Trivialization

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  {t t' : Trivialization F (π F V)} [MemTrivializationAtlas t] [MemTrivializationAtlas t']
  {c c' : OpenPartialHomeomorph M E}
  {hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source} {hct : c.source ⊆ t.baseSet}
  {hc' : ContMDiffOn I 𝓘(ℝ, E) ∞ c' c'.source} {hct' : c'.source ⊆ t'.baseSet}
  {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finitely many components, along a basis of `F`, control the local Besov regularity of all
components. -/
private theorem isLocallyMemBesovAt_chartComponent_of_basis {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ F) (T : BundleTest I F V →L_c[ℝ] ℝ) {y : E} (hy : y ∈ c.target)
    (h : ∀ i, (t.chartComponent c hc hct T (b i)).IsLocallyMemBesovAt φ s p q y) (v : F) :
    (t.chartComponent c hc hct T v).IsLocallyMemBesovAt φ s p q y := by
  have := Fintype.ofFinite ι
  rw [chartComponent_eq_sum _ _ _ _ b]
  exact Distribution.IsLocallyMemBesovAt.sum hy fun i _ ↦ (h i).smul _

variable [Fact (1 ≤ q)]

/-- If every component of the local representative in `(t, c)` is `B^s_{p,q}` near `κ y`, for the
transition `κ = c ∘ c'⁻¹`, then every component in `(t', c')` is `B^s_{p,q}` near `y`. -/
private theorem isLocallyMemBesovAt_chartComponent_of_forall
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ (c'.symm.trans c).source)
    (h : ∀ w, (t.chartComponent c hc hct T w).IsLocallyMemBesovAt φ s p q (c'.symm.trans c y))
    (v : F) : (t'.chartComponent c' hc' hct' T v).IsLocallyMemBesovAt φ s p q y := by
  obtain ⟨he, he'⟩ :=
    OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hc' hcs' hc hcs
  obtain ⟨B, hB, hBc, g, hg, hyB, hS⟩ := exists_restrictCLM_chartComponent_eq_sum (hc := hc)
    (hct := hct) (hc' := hc') (hct' := hct') hcs' he he' T v hy
  rw [← isLocallyMemBesovAt_restrictCLM_iff (fun z hz ↦ (hB hz).1) hyB, hS]
  exact Distribution.IsLocallyMemBesovAt.sum hyB fun j _ ↦
    ((isLocallyMemBesovAt_compCLMOfOpenPartialHomeomorph_iff hyB).2 (h _)).smulLeftCLM (hg j)

/-- **Independence of the chart and the frame.** Let `c` and `c'` be smooth charts with smooth
inverses, with frames `t` and `t'` over their sources, and let `x` be a point of both chart
sources. All components of the local representative of `T` in `(t', c')` are `B^s_{p,q}` near
`c' x` exactly when all components in `(t, c)` are `B^s_{p,q}` near `c x`. -/
theorem forall_isLocallyMemBesovAt_chartComponent_iff
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {x : M} (hx : x ∈ c.source) (hx' : x ∈ c'.source) :
    (∀ v, (t'.chartComponent c' hc' hct' T v).IsLocallyMemBesovAt φ s p q (c' x)) ↔
      ∀ v, (t.chartComponent c hc hct T v).IsLocallyMemBesovAt φ s p q (c x) := by
  have key {t₁ t₂ : Trivialization F (π F V)} [MemTrivializationAtlas t₁]
      [MemTrivializationAtlas t₂] {c₁ c₂ : OpenPartialHomeomorph M E}
      (hc₁ : ContMDiffOn I 𝓘(ℝ, E) ∞ c₁ c₁.source) (hct₁ : c₁.source ⊆ t₁.baseSet)
      (hc₂ : ContMDiffOn I 𝓘(ℝ, E) ∞ c₂ c₂.source) (hct₂ : c₂.source ⊆ t₂.baseSet)
      (hcs₁ : ContMDiffOn 𝓘(ℝ, E) I ∞ c₁.symm c₁.target)
      (hcs₂ : ContMDiffOn 𝓘(ℝ, E) I ∞ c₂.symm c₂.target) (hx₁ : x ∈ c₁.source)
      (hx₂ : x ∈ c₂.source)
      (h : ∀ v, (t₁.chartComponent c₁ hc₁ hct₁ T v).IsLocallyMemBesovAt φ s p q (c₁ x)) (v : F) :
      (t₂.chartComponent c₂ hc₂ hct₂ T v).IsLocallyMemBesovAt φ s p q (c₂ x) := by
    have hy : c₂ x ∈ (c₂.symm.trans c₁).source := by
      simpa [c₂.left_inv hx₂] using ⟨c₂.map_source hx₂, hx₁⟩
    have hyx : c₂.symm.trans c₁ (c₂ x) = c₁ x := by simp [c₂.left_inv hx₂]
    exact isLocallyMemBesovAt_chartComponent_of_forall (t := t₁) (hc := hc₁)
      (hct := hct₁) (t' := t₂) (hc' := hc₂) (hct' := hct₂) hcs₁ hcs₂ T hy (hyx ▸ h) v
  exact ⟨key hc' hct' hc hct hcs' hcs hx' hx, key hc hct hc' hct' hcs hcs' hx hx'⟩

end Bundle.Trivialization

/-! ### Local Besov regularity on the manifold -/

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- A real functional `T` on bundle tests is **`B^s_{p,q}` near `x`**, for the Besov spaces built
from the Littlewood–Paley partition of `φ`, if, in some smooth chart `c` at `x` with smooth inverse
and some frame `t` over its source, the component `ψ ↦ T (ψ • v)` of the local representative of
`T` along every `v : F` is `B^s_{p,q}` near `c x`. For `1 ≤ q`, the chart and the frame do not
matter (`TauCeti.BundleTest.isLocallyMemBesovAt_iff`), and neither does the bump function
(`TauCeti.BundleTest.IsLocallyMemBesovAt.of_bump`). For `p = q = ∞` this is membership in the
local Hölder–Zygmund space `𝒞^s_loc` near `x`.

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` is never
`B^s_{p,q}` there. -/
def IsLocallyMemBesovAt (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M) : Prop :=
  ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t) (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet), x ∈ c.source ∧
    ∀ v, (t.chartComponent c hc hct T v).IsLocallyMemBesovAt φ s p q (c x)

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]
  {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M}

/-- **Local Besov regularity in any chart and frame.** For a smooth chart `c` at `x` with smooth
inverse and a frame `t` over its source, `T` is `B^s_{p,q}` near `x` exactly when every component
of its local representative in `(t, c)` is `B^s_{p,q}` near `c x`. -/
theorem isLocallyMemBesovAt_iff [Fact (1 ≤ q)] (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) (hx : x ∈ c.source) :
    IsLocallyMemBesovAt φ s p q T x ↔
      ∀ v, (t.chartComponent c hc hct T v).IsLocallyMemBesovAt φ s p q (c x) :=
  ⟨fun ⟨t₀, _, _, hc₀, hcs₀, hct₀, hx₀, h⟩ ↦
    (forall_isLocallyMemBesovAt_chartComponent_iff (t' := t₀) (hc' := hc₀) (hct' := hct₀)
      (hc := hc) (hct := hct) hcs hcs₀ T hx hx₀).1 h,
    fun h ↦ ⟨t, inferInstance, c, hc, hcs, hct, hx, h⟩⟩

/-- **Monotonicity.** Being `B^s_{p,q}` near `x` implies being `B^{s'}_{p,q'}` near `x` for
`s' ≤ s` and `q ≤ q'`. -/
theorem IsLocallyMemBesovAt.mono (h : IsLocallyMemBesovAt φ s p q T x) {s' : ℝ} {q' : ℝ≥0∞}
    (hs : s' ≤ s) (hq : q ≤ q') : IsLocallyMemBesovAt φ s' p q' T x :=
  let ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ (h v).mono hs hq⟩

/-- **Independence of the bump function.** A functional `B^s_{p,q}` near `x` for the
Littlewood–Paley partition of `φ` is `B^s_{p,q}` near `x` for that of any other bump function. -/
theorem IsLocallyMemBesovAt.of_bump (h : IsLocallyMemBesovAt φ s p q T x)
    (φ' : ContDiffBump (0 : E)) : IsLocallyMemBesovAt φ' s p q T x :=
  let ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ (h v).of_bump φ'⟩

variable (φ s p q T) in
/-- The points near which `T` is `B^s_{p,q}` form an open set. -/
theorem isOpen_setOf_isLocallyMemBesovAt : IsOpen {x : M | IsLocallyMemBesovAt φ s p q T x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨t, ht, c, hc, hcs, hct, hx, h⟩ ↦ ?_
  -- Finitely many components, along a basis of `F`, determine all of them.
  set b := Module.finBasis ℝ F
  have hopen : IsOpen (c.source ∩ c ⁻¹' ⋂ j,
      {y | (t.chartComponent c hc hct T (b j)).IsLocallyMemBesovAt φ s p q y}) :=
    c.isOpen_inter_preimage (isOpen_iInter_of_finite fun j ↦
      Distribution.isOpen_setOf_isLocallyMemBesovAt _ _ _ _ _)
  exact Filter.mem_of_superset (hopen.mem_nhds ⟨hx, mem_iInter.2 fun j ↦ h (b j)⟩)
    fun y ⟨hy, hyj⟩ ↦ ⟨t, ht, c, hc, hcs, hct, hy,
      isLocallyMemBesovAt_chartComponent_of_basis b T (c.map_source hy) (mem_iInter.1 hyj)⟩

/-- A real multiple of a functional `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.smul (h : IsLocallyMemBesovAt φ s p q T x) (a : ℝ) :
    IsLocallyMemBesovAt φ s p q (a • T) x := by
  obtain ⟨t, _, c, hc, hcs, hct, hx, hT⟩ := h
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_smul]
  exact (hT v).smul _

/-- The negative of a functional `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.neg (h : IsLocallyMemBesovAt φ s p q T x) :
    IsLocallyMemBesovAt φ s p q (-T) x := by
  simpa using h.smul (-1)

/-- A nonzero real multiple of `T` is `B^s_{p,q}` near `x` exactly when `T` is. -/
theorem isLocallyMemBesovAt_smul_iff {a : ℝ} (ha : a ≠ 0) :
    IsLocallyMemBesovAt φ s p q (a • T) x ↔ IsLocallyMemBesovAt φ s p q T x :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ ha] using h.smul a⁻¹, fun h ↦ h.smul a⟩

/-- The negative of `T` is `B^s_{p,q}` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallyMemBesovAt_neg_iff :
    IsLocallyMemBesovAt φ s p q (-T) x ↔ IsLocallyMemBesovAt φ s p q T x := by
  rw [← neg_one_smul ℝ T, isLocallyMemBesovAt_smul_iff (neg_ne_zero.2 one_ne_zero)]

variable [Fact (1 ≤ q)]

/-- A sum of functionals `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.add (h : IsLocallyMemBesovAt φ s p q T x)
    (h' : IsLocallyMemBesovAt φ s p q T' x) : IsLocallyMemBesovAt φ s p q (T + T') x := by
  obtain ⟨t, _, c, hc, hcs, hct, hx, hT⟩ := h
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_add]
  exact (hT v).add ((isLocallyMemBesovAt_iff T' hc hcs hct hx).1 h' v)

/-- A difference of functionals `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.sub (h : IsLocallyMemBesovAt φ s p q T x)
    (h' : IsLocallyMemBesovAt φ s p q T' x) : IsLocallyMemBesovAt φ s p q (T - T') x := by
  simpa [sub_eq_add_neg] using h.add h'.neg

/-! ### Manifolds without boundary -/

section Boundaryless

variable [I.Boundaryless]

omit [Fact (1 ≤ q)] in
variable (φ s p q) in
/-- On a manifold without boundary, the zero functional is `B^s_{p,q}` near every point. -/
theorem isLocallyMemBesovAt_zero (x : M) :
    IsLocallyMemBesovAt φ s p q (0 : BundleTest I F V →L_c[ℝ] ℝ) x := by
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  refine ⟨trivializationAt F V x, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_zero]
  exact isLocallyMemBesovAt_zero_iff.2 (c.map_source hx)

variable (φ q) in
/-- **Functionals on bundle tests have finite Besov order locally.** On a manifold without
boundary and for `1 < p` and `1 ≤ q`, for every compact set `K ⊆ M` there is an order `s` such
that `T` is `B^s_{p,q}` near every point of `K`. -/
theorem exists_forall_isLocallyMemBesovAt (hp : 1 < p) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {K : Set M} (hK : IsCompact K) : ∃ s : ℝ, ∀ x ∈ K, IsLocallyMemBesovAt φ s p q T x := by
  -- At each point, the finitely many basis components have a common finite order.
  have hpt (x : M) : ∃ s : ℝ, IsLocallyMemBesovAt φ s p q T x := by
    obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
    set b := Module.finBasis ℝ F
    choose s hs using fun j ↦ Distribution.exists_isLocallyMemBesovAt (q := q) φ hp
      ((trivializationAt F V x).chartComponent c hc hct T (b j)) (c.map_source hx)
    refine ⟨-∑ j, |s j|, trivializationAt F V x, inferInstance, c, hc, hcs, hct, hx,
      isLocallyMemBesovAt_chartComponent_of_basis b T (c.map_source hx) fun j ↦
        (hs j).mono ?_ le_rfl⟩
    have := Finset.single_le_sum (f := fun j ↦ |s j|) (fun j _ ↦ abs_nonneg _)
      (Finset.mem_univ j)
    linarith [neg_abs_le (s j)]
  -- Patch the orders over a finite cover of `K`, using that each order holds on an open set.
  refine hK.induction_on (p := fun S ↦ ∃ s : ℝ, ∀ x ∈ S, IsLocallyMemBesovAt φ s p q T x)
    ⟨0, by simp⟩ (fun S S' hS ⟨s, hs⟩ ↦ ⟨s, fun x hx ↦ hs x (hS hx)⟩)
    (fun S S' ⟨s, hs⟩ ⟨s', hs'⟩ ↦ ⟨min s s', fun x hx ↦ hx.elim
      (fun hx ↦ (hs x hx).mono (min_le_left _ _) le_rfl)
      fun hx ↦ (hs' x hx).mono (min_le_right _ _) le_rfl⟩)
    fun x _ ↦ ?_
  obtain ⟨s, hs⟩ := hpt x
  exact ⟨_, mem_nhdsWithin_of_mem_nhds
    ((isOpen_setOf_isLocallyMemBesovAt φ s p q T).mem_nhds hs), s, fun _ hy ↦ hy⟩

end Boundaryless

end TauCeti.BundleTest
