/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LocalRegularity
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartComponent
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# Local regularity of distributions on manifolds, chart by chart

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a finite-dimensional
real inner product space `E`, and let `T` be a real continuous linear functional on the bundle tests
`TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, the component of `T` along `v : F` (`Bundle.Trivialization.chartComponent`) is
the complex distribution `ψ ↦ T (ψ • v)` on the chart target, the test function `ψ • v` being
extended to a bundle test through the chart and the frame.

Let `P` be a notion of local regularity of distributions on open subsets of `E`
(`Distribution.IsLocalRegularity`), such as being `H^s` or `B^s_{p,q}` near a point. The functional
`T` **satisfies `P` near `x`** (`TauCeti.BundleTest.IsLocallyAt`) when, in some such chart at `x`
and frame, all its components satisfy `P` near `c x`. If `P` is invariant under smooth multiples,
restriction and smooth changes of variables (`Distribution.IsInvariantLocalRegularity`), the chart
and the frame do not matter: for two charts `c`, `c'` with frames `t`, `t'` and a point `x` of
both chart sources, all components in `(t', c')` satisfy `P` near `c' x` exactly when all
components in `(t, c)` satisfy `P` near `c x`
(`Bundle.Trivialization.forall_chartComponent_iff`). Hence `T` satisfies `P` near `x` exactly
when its components do near `c x` in any chart `c` at `x` and any frame
(`TauCeti.BundleTest.isLocallyAt_iff`).

This is the common construction behind the local Sobolev spaces on bundles
(`TauCeti.BundleTest.IsLocallySobolevAt`) and the local Besov spaces on bundles
(`TauCeti.BundleTest.IsLocallyMemBesovAt`).

## The argument

Near `c' x`, the component along `v` in `(t', c')` is

`S'_v = ∑ⱼ gⱼ κ^* S_{bⱼ}`, with `gⱼ = |det Dκ| · bⱼ*(G(c'⁻¹ ·) v)`,

where `κ = c ∘ c'⁻¹` is the chart transition, `G = t ∘ t'⁻¹` the change of frame, `S_{bⱼ}` the
components in `(t, c)` along a basis `(bⱼ)` of `F` and `κ^*` the pullback of distributions
(`Bundle.Trivialization.restrictCLM_chartComponent_eq_sum`). An invariant notion of local
regularity is preserved by the pullback
(`Distribution.IsInvariantLocalRegularity.compCLMOfOpenPartialHomeomorph_iff`), restriction to
open sets, smooth multiples and finite sums. Exchanging the roles of the two charts gives the
converse.

## Main declarations

* `Bundle.Trivialization.forall_chartComponent_iff`: for an invariant notion of local regularity,
  the regularity of all components does not depend on the chart and the frame.
* `Bundle.Trivialization.chartComponent_of_basis`: the components along a basis of `F` control
  the local regularity of all components.
* `TauCeti.BundleTest.IsLocallyAt`: the functional `T` satisfies `P` near a point of `M`, and
  `TauCeti.BundleTest.isLocallyAt_iff`, its characterization in every chart and frame.
* `TauCeti.BundleTest.isOpen_setOf_isLocallyAt`: the points near which `T` satisfies `P` form an
  open set, and the rules for sums, differences, negatives and real multiples.
* `TauCeti.BundleTest.exists_forall_isLocallyAt`: on a manifold without boundary, for a scale of
  notions of local regularity in which every distribution has a finite order near each point,
  every functional on bundle tests has a finite order near every compact set.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (the local Sobolev spaces on manifolds, defined chart by chart).
* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §3.2.2 (Besov spaces on manifolds,
  defined chart by chart, and their independence of the charts).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology CompactConvergenceCLM

namespace Bundle.Trivialization

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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
  {P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop}

/-- Finitely many components, along a basis of `F`, control the local regularity of all
components. -/
theorem chartComponent_of_basis (hP : IsLocalRegularity P) {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ F) (T : BundleTest I F V →L_c[ℝ] ℝ) {y : E} (hy : y ∈ c.target)
    (h : ∀ i, P _ (t.chartComponent c hc hct T (b i)) y) (v : F) :
    P _ (t.chartComponent c hc hct T v) y := by
  have := Fintype.ofFinite ι
  rw [chartComponent_eq_sum _ _ _ _ b]
  exact hP.sum hy fun i _ ↦ hP.smul _ (h i)

/-- If every component of the local representative in `(t, c)` satisfies `P` near `κ y`, for the
transition `κ = c ∘ c'⁻¹`, then every component in `(t', c')` satisfies `P` near `y`. -/
private theorem chartComponent_of_forall (hP : IsInvariantLocalRegularity P)
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ (c'.symm.trans c).source)
    (h : ∀ w, P _ (t.chartComponent c hc hct T w) (c'.symm.trans c y)) (v : F) :
    P _ (t'.chartComponent c' hc' hct' T v) y := by
  obtain ⟨he, he'⟩ :=
    OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hc' hcs' hc hcs
  obtain ⟨B, hB, hBc, g, hg, hyB, hS⟩ := exists_restrictCLM_chartComponent_eq_sum (hc := hc)
    (hct := hct) (hc' := hc') (hct' := hct') hcs' he he' T v hy
  rw [← hP.restrictCLM_iff (fun z hz ↦ (hB hz).1) hyB, hS]
  exact hP.sum hyB fun j _ ↦
    hP.smulLeftCLM (hg j) ((hP.compCLMOfOpenPartialHomeomorph_iff hyB).2 (h _))

/-- **Independence of the chart and the frame.** Let `P` be an invariant notion of local
regularity, let `c` and `c'` be smooth charts with smooth inverses, with frames `t` and `t'` over
their sources, and let `x` be a point of both chart sources. All components of the local
representative of `T` in `(t', c')` satisfy `P` near `c' x` exactly when all components in `(t, c)`
satisfy `P` near `c x`. -/
theorem forall_chartComponent_iff (hP : IsInvariantLocalRegularity P)
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {x : M} (hx : x ∈ c.source) (hx' : x ∈ c'.source) :
    (∀ v, P _ (t'.chartComponent c' hc' hct' T v) (c' x)) ↔
      ∀ v, P _ (t.chartComponent c hc hct T v) (c x) := by
  have key {t₁ t₂ : Trivialization F (π F V)} [MemTrivializationAtlas t₁]
      [MemTrivializationAtlas t₂] {c₁ c₂ : OpenPartialHomeomorph M E}
      (hc₁ : ContMDiffOn I 𝓘(ℝ, E) ∞ c₁ c₁.source) (hct₁ : c₁.source ⊆ t₁.baseSet)
      (hc₂ : ContMDiffOn I 𝓘(ℝ, E) ∞ c₂ c₂.source) (hct₂ : c₂.source ⊆ t₂.baseSet)
      (hcs₁ : ContMDiffOn 𝓘(ℝ, E) I ∞ c₁.symm c₁.target)
      (hcs₂ : ContMDiffOn 𝓘(ℝ, E) I ∞ c₂.symm c₂.target) (hx₁ : x ∈ c₁.source)
      (hx₂ : x ∈ c₂.source) (h : ∀ v, P _ (t₁.chartComponent c₁ hc₁ hct₁ T v) (c₁ x)) (v : F) :
      P _ (t₂.chartComponent c₂ hc₂ hct₂ T v) (c₂ x) := by
    have hy : c₂ x ∈ (c₂.symm.trans c₁).source := by
      simpa [c₂.left_inv hx₂] using ⟨c₂.map_source hx₂, hx₁⟩
    have hyx : c₂.symm.trans c₁ (c₂ x) = c₁ x := by simp [c₂.left_inv hx₂]
    exact chartComponent_of_forall (t := t₁) (hc := hc₁) (hct := hct₁) (t' := t₂) (hc' := hc₂)
      (hct' := hct₂) hP hcs₁ hcs₂ T hy (hyx ▸ h) v
  exact ⟨key hc' hct' hc hct hcs' hcs hx' hx, key hc hct hc' hct' hcs hcs' hx hx'⟩

end Bundle.Trivialization

/-! ### Local regularity on the manifold -/

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- A real functional `T` on bundle tests **satisfies the notion of local regularity `P` near
`x`** if, in some smooth chart `c` at `x` with smooth inverse and some frame `t` over its source,
the component `ψ ↦ T (ψ • v)` of the local representative of `T` along every `v : F` satisfies `P`
near `c x`. For an invariant notion of local regularity `P`, the chart and the frame do not matter
(`TauCeti.BundleTest.isLocallyAt_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` never satisfies `P`
there. -/
def IsLocallyAt (P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop) (T : BundleTest I F V →L_c[ℝ] ℝ)
    (x : M) : Prop :=
  ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t) (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet), x ∈ c.source ∧ ∀ v, P _ (t.chartComponent c hc hct T v) (c x)

variable {P Q : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop} {T T' : BundleTest I F V →L_c[ℝ] ℝ}
  {x : M}

/-- Unfolding `TauCeti.BundleTest.IsLocallyAt`: `T` satisfies `P` near `x` exactly when, in some
smooth chart `c` at `x` with smooth inverse and some frame `t` over its source, every component of
the local representative of `T` satisfies `P` near `c x`. No property of `P` is needed. -/
theorem isLocallyAt_def :
    IsLocallyAt P T x ↔ ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t)
      (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
      (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct : c.source ⊆ t.baseSet),
      x ∈ c.source ∧ ∀ v, P _ (t.chartComponent c hc hct T v) (c x) :=
  Iff.rfl

/-- **Introduction rule.** If, in a smooth chart `c` at `x` with smooth inverse and a frame `t`
over its source, every component of the local representative of `T` satisfies `P` near `c x`, then
`T` satisfies `P` near `x`. No property of `P` is needed. -/
theorem IsLocallyAt.intro (T : BundleTest I F V →L_c[ℝ] ℝ) {t : Trivialization F (π F V)}
    [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) (hx : x ∈ c.source)
    (h : ∀ v, P _ (t.chartComponent c hc hct T v) (c x)) : IsLocallyAt P T x :=
  ⟨t, inferInstance, c, hc, hcs, hct, hx, h⟩

/-- **Local regularity in any chart and frame.** Let `P` be an invariant notion of local
regularity. For a smooth chart `c` at `x` with smooth inverse and a frame `t` over its source, `T`
satisfies `P` near `x` exactly when every component of its local representative in `(t, c)`
satisfies `P` near `c x`. -/
theorem isLocallyAt_iff (hP : IsInvariantLocalRegularity P) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) (hx : x ∈ c.source) :
    IsLocallyAt P T x ↔ ∀ v, P _ (t.chartComponent c hc hct T v) (c x) :=
  ⟨fun ⟨t₀, _, _, hc₀, hcs₀, hct₀, hx₀, h⟩ ↦
    (forall_chartComponent_iff (t' := t₀) (hc' := hc₀) (hct' := hct₀) (hc := hc) (hct := hct) hP
      hcs hcs₀ T hx hx₀).1 h,
    IsLocallyAt.intro T hc hcs hct hx⟩

/-- **Monotonicity in the notion.** If `P` implies `Q`, then satisfying `P` near `x` implies
satisfying `Q` near `x`. -/
theorem IsLocallyAt.mono (h : IsLocallyAt P T x)
    (hPQ : ∀ (Ω : Opens E) (S : 𝓓'(Ω, ℂ)) (y : E), P Ω S y → Q Ω S y) : IsLocallyAt Q T x :=
  let ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ hPQ _ _ _ (h v)⟩

/-- The points near which `T` satisfies a notion of local regularity `P` form an open set. -/
theorem isOpen_setOf_isLocallyAt (hP : IsLocalRegularity P) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsOpen {x : M | IsLocallyAt P T x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨t, ht, c, hc, hcs, hct, hx, h⟩ ↦ ?_
  -- Finitely many components, along a basis of `F`, determine all of them.
  set b := Module.finBasis ℝ F
  have hopen : IsOpen (c.source ∩ c ⁻¹' ⋂ j, {y | P _ (t.chartComponent c hc hct T (b j)) y}) :=
    c.isOpen_inter_preimage (isOpen_iInter_of_finite fun j ↦ hP.isOpen_setOf _ _)
  exact Filter.mem_of_superset (hopen.mem_nhds ⟨hx, mem_iInter.2 fun j ↦ h (b j)⟩)
    fun y ⟨hy, hyj⟩ ↦ ⟨t, ht, c, hc, hcs, hct, hy,
      chartComponent_of_basis hP b T (c.map_source hy) (mem_iInter.1 hyj)⟩

/-- A real multiple of a functional satisfying a notion of local regularity `P` near `x` satisfies
`P` near `x`. -/
theorem IsLocallyAt.smul (hP : IsLocalRegularity P) (h : IsLocallyAt P T x) (a : ℝ) :
    IsLocallyAt P (a • T) x := by
  obtain ⟨t, _, c, hc, hcs, hct, hx, hT⟩ := h
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_smul]
  exact hP.smul _ (hT v)

/-- The negative of a functional satisfying a notion of local regularity `P` near `x` satisfies
`P` near `x`. -/
theorem IsLocallyAt.neg (hP : IsLocalRegularity P) (h : IsLocallyAt P T x) :
    IsLocallyAt P (-T) x := by
  simpa using h.smul hP (-1)

/-- For a notion of local regularity `P`, a nonzero real multiple of `T` satisfies `P` near `x`
exactly when `T` does. -/
theorem isLocallyAt_smul_iff (hP : IsLocalRegularity P) {a : ℝ} (ha : a ≠ 0) :
    IsLocallyAt P (a • T) x ↔ IsLocallyAt P T x :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ ha] using h.smul hP a⁻¹, fun h ↦ h.smul hP a⟩

/-- For a notion of local regularity `P`, the negative of `T` satisfies `P` near `x` exactly when
`T` does. -/
theorem isLocallyAt_neg_iff (hP : IsLocalRegularity P) :
    IsLocallyAt P (-T) x ↔ IsLocallyAt P T x := by
  rw [← neg_one_smul ℝ T, isLocallyAt_smul_iff hP (neg_ne_zero.2 one_ne_zero)]

/-- For an invariant notion of local regularity `P`, a sum of functionals satisfying `P` near `x`
satisfies `P` near `x`. -/
theorem IsLocallyAt.add (hP : IsInvariantLocalRegularity P) (h : IsLocallyAt P T x)
    (h' : IsLocallyAt P T' x) : IsLocallyAt P (T + T') x := by
  obtain ⟨t, _, c, hc, hcs, hct, hx, hT⟩ := h
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_add]
  exact hP.add (hT v) ((isLocallyAt_iff hP T' hc hcs hct hx).1 h' v)

/-- For an invariant notion of local regularity `P`, a difference of functionals satisfying `P`
near `x` satisfies `P` near `x`. -/
theorem IsLocallyAt.sub (hP : IsInvariantLocalRegularity P) (h : IsLocallyAt P T x)
    (h' : IsLocallyAt P T' x) : IsLocallyAt P (T - T') x := by
  simpa [sub_eq_add_neg] using h.add hP (h'.neg hP.toIsLocalRegularity)

/-! ### Manifolds without boundary -/

section Boundaryless

variable [I.Boundaryless]

variable (P) in
/-- On a manifold without boundary, the zero functional satisfies every notion of local regularity
near every point. -/
theorem isLocallyAt_zero (hP : IsLocalRegularity P) (x : M) :
    IsLocallyAt P (0 : BundleTest I F V →L_c[ℝ] ℝ) x := by
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  refine ⟨trivializationAt F V x, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_zero]
  exact hP.zero (c.map_source hx)

/-- **Functionals on bundle tests have finite order locally.** Let `P s` be notions of local
regularity, weaker as the order `s` decreases, such that every distribution satisfies some `P s`
near each point of its domain. On a manifold without boundary, for every compact set `K ⊆ M` there
is an order `s` such that `T` satisfies `P s` near every point of `K`. -/
theorem exists_forall_isLocallyAt {P : ℝ → (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop}
    (hP : ∀ s, IsLocalRegularity (P s))
    (hmono : ∀ {s s' : ℝ} {Ω : Opens E} {S : 𝓓'(Ω, ℂ)} {y : E}, s' ≤ s → P s Ω S y → P s' Ω S y)
    (hfin : ∀ {Ω : Opens E} (S : 𝓓'(Ω, ℂ)) {y : E}, y ∈ Ω → ∃ s, P s Ω S y)
    (T : BundleTest I F V →L_c[ℝ] ℝ) {K : Set M} (hK : IsCompact K) :
    ∃ s : ℝ, ∀ x ∈ K, IsLocallyAt (P s) T x := by
  -- At each point, the finitely many basis components have a common finite order.
  have hpt (x : M) : ∃ s : ℝ, IsLocallyAt (P s) T x := by
    obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
    set b := Module.finBasis ℝ F
    choose s hs using fun j ↦
      hfin ((trivializationAt F V x).chartComponent c hc hct T (b j)) (c.map_source hx)
    refine ⟨-∑ j, |s j|, trivializationAt F V x, inferInstance, c, hc, hcs, hct, hx,
      chartComponent_of_basis (hP _) b T (c.map_source hx) fun j ↦ hmono ?_ (hs j)⟩
    have := Finset.single_le_sum (f := fun j ↦ |s j|) (fun j _ ↦ abs_nonneg _)
      (Finset.mem_univ j)
    linarith [neg_abs_le (s j)]
  -- The open sets where the orders hold grow as the order decreases, and cover `K`.
  exact hK.elim_directed_cover _ (fun s ↦ isOpen_setOf_isLocallyAt (hP s) T)
    (fun x _ ↦ mem_iUnion.2 (hpt x))
    (Antitone.directed_le fun _ _ hs _ hx ↦ IsLocallyAt.mono hx fun _ _ _ ↦ hmono hs)

end Boundaryless

end TauCeti.BundleTest
