/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.BesselPotential.Local
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalRegularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# Local Sobolev regularity of distributions on manifolds

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a finite-dimensional
real inner product space `E`, and let `T` be a real continuous linear functional on the bundle tests
`TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, `T` has a local representative on the chart target
(`Bundle.Trivialization.chartDistributionCLM`), a distribution with values in the dual of the model
fibre `F`. Its component along `v : F` (`Bundle.Trivialization.chartComponent`) is the complex
distribution `φ ↦ T (φ • v)` on the chart target, the test function `φ • v` being extended to a
bundle test through the chart and the frame.
The functional `T` is **`H^s` near `x`** (`TauCeti.BundleTest.IsLocallySobolevAt`) when, in some
such chart at `x` and frame, all these components are `H^s` near `c x`
(`Distribution.IsLocallySobolevAt`). This is the local Sobolev space `H^s_loc` of distributions
on a manifold with values in a bundle, defined pointwise; its complement is the **`H^s` singular
support** of `T` (`TauCeti.BundleTest.sobolevSingularSupport`).

The main result is that the chart and the frame do not matter: `T` is `H^s` near `x` exactly when
its components are `H^s` near `c x` in any chart `c` at `x` and any frame
(`TauCeti.BundleTest.isLocallySobolevAt_iff`). This is the case `P = H^s` of the construction of
local regularity on bundles from an invariant notion `P` of local regularity on `E`
(`TauCeti.BundleTest.IsLocallyAt`), since being `H^s` near a point is invariant under smooth
multiples, restriction and smooth changes of variables
(`Distribution.isInvariantLocalRegularity_isLocallySobolevAt`).

The same holds on the `Lᵖ` scale of the Bessel-potential spaces `H^{s,p}`, `1 < p < ∞`: `T` is
**`H^{s,p}` near `x`** (`TauCeti.BundleTest.IsLocallyMemSobolevAt`) when, in some chart at `x` and
frame, all its components are `H^{s,p}` near `c x` (`Distribution.IsLocallyMemSobolevAt`), and
the chart and the frame do not matter (`TauCeti.BundleTest.isLocallyMemSobolevAt_iff`), since
being `H^{s,p}` near a point is an invariant notion of local regularity for `1 < p < ∞`
(`Distribution.isInvariantLocalRegularity_isLocallyMemSobolevAt`). This is the local space
`H^{s,p}_loc` of distributions on a manifold with values in a bundle; for `p = 2` it is the local
Sobolev space `H^s_loc` above (`TauCeti.BundleTest.isLocallyMemSobolevAt_two_iff`).

## Main declarations

* `TauCeti.BundleTest.IsLocallySobolevAt`: the functional `T` is `H^s` near a point of `M`, and
  `TauCeti.BundleTest.isLocallySobolevAt_iff`, its characterization in every chart and frame.
* `TauCeti.BundleTest.sobolevSingularSupport`: the `H^s` singular support, a closed subset of `M`
  (`TauCeti.BundleTest.isClosed_sobolevSingularSupport`) growing with `s`, with the rules for
  sums, differences, negatives and scalar multiples.
* `TauCeti.BundleTest.exists_forall_isLocallySobolevAt`: on a manifold without boundary every
  functional on bundle tests has a finite Sobolev order near every compact set.
* `TauCeti.BundleTest.IsLocallyMemSobolevAt`: the functional `T` is `H^{s,p}` near a point of `M`,
  and `TauCeti.BundleTest.isLocallyMemSobolevAt_iff`, its characterization in every chart and
  frame for `1 < p < ∞`; `TauCeti.BundleTest.isLocallyMemSobolevAt_two_iff` compares it with
  `TauCeti.BundleTest.IsLocallySobolevAt` for `p = 2`.
* `TauCeti.BundleTest.exists_forall_isLocallyMemSobolevAt`: on a manifold without boundary every
  functional on bundle tests has, for `1 < p < ∞`, a finite `H^{s,p}` order near every compact
  set.
* `TauCeti.BundleTest.sobolevSingularSupport_delta`,
  `TauCeti.BundleTest.sobolevSingularSupport_delta_eq_empty`: in dimension `d > 0` the point mass
  `δ_x ℓ` with `ℓ ≠ 0` has `H^s` singular support `{x}` for `s ≥ -d / 2`, and it is `H^s`
  everywhere for `s < -d / 2`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (the local Sobolev spaces `H^s_loc` on manifolds, defined chart by chart).
* M. Taylor, *Partial Differential Equations I*, second edition, Springer, 2011, Chapter 4, §3
  (Sobolev spaces on manifolds and their invariance under coordinate changes).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped ENNReal Manifold ContDiff Distributions Topology CompactConvergenceCLM

/-! ### Local Sobolev regularity on the manifold -/

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

/-- A real functional `T` on bundle tests is **`H^s` near `x`** if, in some smooth chart `c` at `x`
with smooth inverse and some frame `t` over its source, the component `φ ↦ T (φ • v)` of the local
representative of `T` along every `v : F` is `H^s` near `c x`
(`TauCeti.BundleTest.IsLocallyAt` for `Distribution.IsLocallySobolevAt`). The chart and the frame
do not matter (`TauCeti.BundleTest.isLocallySobolevAt_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` is never `H^s`
there. -/
def IsLocallySobolevAt (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M) : Prop :=
  IsLocallyAt (fun _ S y ↦ S.IsLocallySobolevAt s y) T x

/-- Being `H^s` near `x` is `TauCeti.BundleTest.IsLocallyAt` for
`Distribution.IsLocallySobolevAt`. -/
theorem isLocallySobolevAt_def {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    IsLocallySobolevAt s T x ↔ IsLocallyAt (fun _ S y ↦ S.IsLocallySobolevAt s y) T x :=
  Iff.rfl

/-- **Local Sobolev regularity in any chart and frame.** For a smooth chart `c` at `x` with smooth
inverse and a frame `t` over its source, `T` is `H^s` near `x` exactly when every component of
its local representative in `(t, c)` is `H^s` near `c x`. -/
theorem isLocallySobolevAt_iff {s : ℝ} (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) {x : M} (hx : x ∈ c.source) :
    IsLocallySobolevAt s T x ↔
      ∀ v, (t.chartComponent c hc hct T v).IsLocallySobolevAt s (c x) :=
  isLocallyAt_iff (isInvariantLocalRegularity_isLocallySobolevAt s) T hc hcs hct hx

/-- Being `H^s` near `x` gets weaker as `s` decreases. -/
theorem IsLocallySobolevAt.mono {s s' : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (hs : s' ≤ s) : IsLocallySobolevAt s' T x :=
  IsLocallyAt.mono h fun _ _ _ h ↦ h.mono hs

/-- The points near which `T` is `H^s` form an open set. -/
theorem isOpen_setOf_isLocallySobolevAt (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsOpen {x : M | IsLocallySobolevAt s T x} :=
  isOpen_setOf_isLocallyAt (isInvariantLocalRegularity_isLocallySobolevAt s).toIsLocalRegularity T

/-- A sum of functionals `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.add {s : ℝ} {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (h' : IsLocallySobolevAt s T' x) :
    IsLocallySobolevAt s (T + T') x :=
  IsLocallyAt.add (isInvariantLocalRegularity_isLocallySobolevAt s) h h'

/-- A real multiple of a functional `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.smul {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (a : ℝ) : IsLocallySobolevAt s (a • T) x :=
  IsLocallyAt.smul (isInvariantLocalRegularity_isLocallySobolevAt s).toIsLocalRegularity h a

/-- The negative of a functional `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.neg {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) : IsLocallySobolevAt s (-T) x :=
  IsLocallyAt.neg (isInvariantLocalRegularity_isLocallySobolevAt s).toIsLocalRegularity h

/-- A nonzero real multiple of `T` is `H^s` near `x` exactly when `T` is. -/
theorem isLocallySobolevAt_smul_iff {s : ℝ} {a : ℝ} (ha : a ≠ 0)
    {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    IsLocallySobolevAt s (a • T) x ↔ IsLocallySobolevAt s T x :=
  isLocallyAt_smul_iff (isInvariantLocalRegularity_isLocallySobolevAt s).toIsLocalRegularity ha

/-- The negative of `T` is `H^s` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallySobolevAt_neg_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    IsLocallySobolevAt s (-T) x ↔ IsLocallySobolevAt s T x :=
  isLocallyAt_neg_iff (isInvariantLocalRegularity_isLocallySobolevAt s).toIsLocalRegularity

/-- A difference of functionals `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.sub {s : ℝ} {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (h' : IsLocallySobolevAt s T' x) :
    IsLocallySobolevAt s (T - T') x :=
  IsLocallyAt.sub (isInvariantLocalRegularity_isLocallySobolevAt s) h h'

/-! ### Local `H^{s,p}` regularity on the manifold -/

section MemSobolev

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real functional `T` on bundle tests is **`H^{s,p}` near `x`** if, in some smooth chart `c` at
`x` with smooth inverse and some frame `t` over its source, the component `φ ↦ T (φ • v)` of the
local representative of `T` along every `v : F` is `H^{s,p}` near `c x`
(`TauCeti.BundleTest.IsLocallyAt` for `Distribution.IsLocallyMemSobolevAt`). For `1 < p < ∞` the
chart and the frame do not matter (`TauCeti.BundleTest.isLocallyMemSobolevAt_iff`), and for `p = 2`
this is `TauCeti.BundleTest.IsLocallySobolevAt`
(`TauCeti.BundleTest.isLocallyMemSobolevAt_two_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` is never `H^{s,p}`
there. -/
def IsLocallyMemSobolevAt (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : BundleTest I F V →L_c[ℝ] ℝ)
    (x : M) : Prop :=
  IsLocallyAt (fun _ S y ↦ S.IsLocallyMemSobolevAt s p y) T x

/-- Being `H^{s,p}` near `x` is `TauCeti.BundleTest.IsLocallyAt` for
`Distribution.IsLocallyMemSobolevAt`, for every `p`. -/
theorem isLocallyMemSobolevAt_def {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    IsLocallyMemSobolevAt s p T x ↔ IsLocallyAt (fun _ S y ↦ S.IsLocallyMemSobolevAt s p y) T x :=
  Iff.rfl

/-- **Local `H^{s,p}` regularity in any chart and frame.** Let `1 < p < ∞`. For a smooth chart `c`
at `x` with smooth inverse and a frame `t` over its source, `T` is `H^{s,p}` near `x` exactly when
every component of its local representative in `(t, c)` is `H^{s,p}` near `c x`. -/
theorem isLocallyMemSobolevAt_iff (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {s : ℝ}
    (T : BundleTest I F V →L_c[ℝ] ℝ) {t : Trivialization F (π F V)} [MemTrivializationAtlas t]
    {c : OpenPartialHomeomorph M E} (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct : c.source ⊆ t.baseSet) {x : M}
    (hx : x ∈ c.source) :
    IsLocallyMemSobolevAt s p T x ↔
      ∀ v, (t.chartComponent c hc hct T v).IsLocallyMemSobolevAt s p (c x) :=
  isLocallyAt_iff (isInvariantLocalRegularity_isLocallyMemSobolevAt s hp hp_top) T hc hcs hct hx

/-- For `p = 2`, being `H^{s,2}` near `x` is being `H^s` near `x` in the sense of
`TauCeti.BundleTest.IsLocallySobolevAt`. -/
theorem isLocallyMemSobolevAt_two_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    IsLocallyMemSobolevAt s 2 T x ↔ IsLocallySobolevAt s T x := by
  simp only [IsLocallyMemSobolevAt, IsLocallySobolevAt, Distribution.isLocallyMemSobolevAt_two_iff]

/-- Being `H^{s,p}` near `x` is inherited by lower orders. -/
theorem IsLocallyMemSobolevAt.of_le {s s' : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallyMemSobolevAt s p T x) (hs : s' ≤ s) : IsLocallyMemSobolevAt s' p T x :=
  IsLocallyAt.mono h fun _ _ _ h ↦ h.of_le hs

/-- The points near which `T` is `H^{s,p}` form an open set. -/
theorem isOpen_setOf_isLocallyMemSobolevAt (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : BundleTest I F V →L_c[ℝ] ℝ) : IsOpen {x : M | IsLocallyMemSobolevAt s p T x} :=
  isOpen_setOf_isLocallyAt (isLocalRegularity_isLocallyMemSobolevAt s p) T

/-- For `1 < p < ∞`, a sum of functionals `H^{s,p}` near `x` is `H^{s,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.add (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {s : ℝ}
    {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M} (h : IsLocallyMemSobolevAt s p T x)
    (h' : IsLocallyMemSobolevAt s p T' x) : IsLocallyMemSobolevAt s p (T + T') x :=
  IsLocallyAt.add (isInvariantLocalRegularity_isLocallyMemSobolevAt s hp hp_top) h h'

/-- A real multiple of a functional `H^{s,p}` near `x` is `H^{s,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.smul {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallyMemSobolevAt s p T x) (a : ℝ) : IsLocallyMemSobolevAt s p (a • T) x :=
  IsLocallyAt.smul (isLocalRegularity_isLocallyMemSobolevAt s p) h a

/-- The negative of a functional `H^{s,p}` near `x` is `H^{s,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.neg {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallyMemSobolevAt s p T x) : IsLocallyMemSobolevAt s p (-T) x :=
  IsLocallyAt.neg (isLocalRegularity_isLocallyMemSobolevAt s p) h

/-- A nonzero real multiple of `T` is `H^{s,p}` near `x` exactly when `T` is. -/
theorem isLocallyMemSobolevAt_smul_iff {s : ℝ} {a : ℝ} (ha : a ≠ 0)
    {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    IsLocallyMemSobolevAt s p (a • T) x ↔ IsLocallyMemSobolevAt s p T x :=
  isLocallyAt_smul_iff (isLocalRegularity_isLocallyMemSobolevAt s p) ha

/-- The negative of `T` is `H^{s,p}` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallyMemSobolevAt_neg_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    IsLocallyMemSobolevAt s p (-T) x ↔ IsLocallyMemSobolevAt s p T x :=
  isLocallyAt_neg_iff (isLocalRegularity_isLocallyMemSobolevAt s p)

/-- For `1 < p < ∞`, a difference of functionals `H^{s,p}` near `x` is `H^{s,p}` near `x`. -/
theorem IsLocallyMemSobolevAt.sub (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞)) {s : ℝ}
    {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M} (h : IsLocallyMemSobolevAt s p T x)
    (h' : IsLocallyMemSobolevAt s p T' x) : IsLocallyMemSobolevAt s p (T - T') x :=
  IsLocallyAt.sub (isInvariantLocalRegularity_isLocallyMemSobolevAt s hp hp_top) h h'

section Boundaryless

variable [I.Boundaryless]

/-- On a manifold without boundary, the zero functional is `H^{s,p}` near every point. -/
theorem isLocallyMemSobolevAt_zero (s : ℝ) (x : M) :
    IsLocallyMemSobolevAt s p (0 : BundleTest I F V →L_c[ℝ] ℝ) x :=
  isLocallyAt_zero _ (isLocalRegularity_isLocallyMemSobolevAt s p) x

/-- **Functionals on bundle tests have finite `H^{s,p}` order locally.** Let `1 < p < ∞`. On a
manifold without boundary, for every compact set `K ⊆ M` there is an order `s` such that `T` is
`H^{s,p}` near every point of `K`. -/
theorem exists_forall_isLocallyMemSobolevAt (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (T : BundleTest I F V →L_c[ℝ] ℝ) {K : Set M} (hK : IsCompact K) :
    ∃ s : ℝ, ∀ x ∈ K, IsLocallyMemSobolevAt s p T x :=
  exists_forall_isLocallyAt (fun s ↦ isLocalRegularity_isLocallyMemSobolevAt s p)
    (fun hs h ↦ h.of_le hs)
    (fun S _ hy ↦ (Distribution.exists_forall_isLocallyMemSobolevAt hp hp_top S
      isCompact_singleton (singleton_subset_iff.2 hy)).imp fun _ h ↦ h _ rfl)
    T hK

end Boundaryless

end MemSobolev

/-! ### The `H^s` singular support -/

variable (I) in
/-- The **`H^s` singular support** of a real functional `T` on bundle tests: the points of `M` near
which `T` is not `H^s`. -/
def sobolevSingularSupport (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) : Set M :=
  {x | ¬ IsLocallySobolevAt s T x}

@[simp]
theorem mem_sobolevSingularSupport_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    x ∈ sobolevSingularSupport I s T ↔ ¬ IsLocallySobolevAt s T x :=
  Iff.rfl

/-- The `H^s` singular support is closed. -/
theorem isClosed_sobolevSingularSupport (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsClosed (sobolevSingularSupport I s T) :=
  (isOpen_setOf_isLocallySobolevAt s T).isClosed_compl

/-- The `H^s` singular support grows with `s`. -/
theorem sobolevSingularSupport_mono {s s' : ℝ} (hs : s' ≤ s) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s' T ⊆ sobolevSingularSupport I s T :=
  fun _ hx h ↦ hx (h.mono hs)

/-- The `H^s` singular support of a sum lies in the union of the `H^s` singular supports. -/
theorem sobolevSingularSupport_add_subset (s : ℝ) (T T' : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (T + T') ⊆
      sobolevSingularSupport I s T ∪ sobolevSingularSupport I s T' := by
  intro x hx
  by_contra h
  simp only [mem_union, mem_sobolevSingularSupport_iff, not_or, not_not] at h
  exact hx (h.1.add h.2)

/-- The `H^s` singular support of a real multiple lies in the `H^s` singular support. -/
theorem sobolevSingularSupport_smul_subset (s : ℝ) (a : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (a • T) ⊆ sobolevSingularSupport I s T :=
  fun _ hx h ↦ hx (h.smul a)

/-- A nonzero real multiple of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem sobolevSingularSupport_smul (s : ℝ) {a : ℝ} (ha : a ≠ 0)
    (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (a • T) = sobolevSingularSupport I s T := by
  ext x
  simp [isLocallySobolevAt_smul_iff ha]

/-- The negative of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem sobolevSingularSupport_neg (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (-T) = sobolevSingularSupport I s T := by
  ext x
  simp

/-- The `H^s` singular support of a difference lies in the union of the `H^s` singular
supports. -/
theorem sobolevSingularSupport_sub_subset (s : ℝ) (T T' : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (T - T') ⊆
      sobolevSingularSupport I s T ∪ sobolevSingularSupport I s T' := by
  simpa [sub_eq_add_neg] using sobolevSingularSupport_add_subset s T (-T')

/-! ### Manifolds without boundary -/

section Boundaryless

variable [I.Boundaryless]

/-- On a manifold without boundary, the zero functional is `H^s` near every point. -/
theorem isLocallySobolevAt_zero (s : ℝ) (x : M) :
    IsLocallySobolevAt s (0 : BundleTest I F V →L_c[ℝ] ℝ) x :=
  isLocallyAt_zero _ (isInvariantLocalRegularity_isLocallySobolevAt s).toIsLocalRegularity x

/-- On a manifold without boundary, the zero functional has empty `H^s` singular support. -/
@[simp]
theorem sobolevSingularSupport_zero (s : ℝ) :
    sobolevSingularSupport I s (0 : BundleTest I F V →L_c[ℝ] ℝ) = ∅ :=
  eq_empty_iff_forall_notMem.2 fun x hx ↦ hx (isLocallySobolevAt_zero s x)

/-- **Functionals on bundle tests have finite Sobolev order locally.** On a manifold without
boundary, for every compact set `K ⊆ M` there is an order `s` such that `T` is `H^s` near every
point of `K`. -/
theorem exists_forall_isLocallySobolevAt (T : BundleTest I F V →L_c[ℝ] ℝ) {K : Set M}
    (hK : IsCompact K) : ∃ s : ℝ, ∀ x ∈ K, IsLocallySobolevAt s T x :=
  exists_forall_isLocallyAt
    (fun s ↦ (isInvariantLocalRegularity_isLocallySobolevAt s).toIsLocalRegularity)
    (fun hs h ↦ h.mono hs)
    (fun S _ hy ↦ (Distribution.exists_forall_isLocallySobolevAt S isCompact_singleton
      (singleton_subset_iff.2 hy)).imp fun _ h ↦ h _ rfl)
    T hK

/-! ### Point masses -/

/-- **Point masses are `H^s` below the critical order.** On a manifold without boundary of
dimension `d`, the point mass `δ_x ℓ` has empty `H^s` singular support for `s < -d / 2`. -/
theorem sobolevSingularSupport_delta_eq_empty {s : ℝ}
    (hs : (Module.finrank ℝ E : ℝ) < -2 * s) (x : M) (ℓ : V x →L[ℝ] ℝ) :
    sobolevSingularSupport I s (BundleTest.delta x ℓ : BundleTest I F V →L_c[ℝ] ℝ) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun p hp ↦ hp ?_
  obtain ⟨c, hc, hcs, hct, hp⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) p
  refine (isLocallySobolevAt_iff (t := trivializationAt F V p) _ hc hcs hct hp).2 fun v ↦ ?_
  by_cases hx : x ∈ c.source
  · rw [chartComponent_delta_of_mem _ _ _ _ hx]
    exact ((notMem_sobolevSingularSupport_iff (c.map_source hp)).1
      (by simp [Distribution.sobolevSingularSupport_delta_eq_empty hs])).smul _
  · rw [chartComponent_delta_of_notMem _ _ _ _ hx]
    exact isLocallySobolevAt_zero_iff.2 (c.map_source hp)

/-- **The `H^s` singular support of a point mass.** On a manifold without boundary of positive
dimension `d`, the point mass `δ_x ℓ` with `ℓ ≠ 0` has `H^s` singular support `{x}` for
`s ≥ -d / 2`. -/
theorem sobolevSingularSupport_delta [Nontrivial E] {s : ℝ}
    (hs : -2 * s ≤ Module.finrank ℝ E) {x : M} {ℓ : V x →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    sobolevSingularSupport I s (BundleTest.delta x ℓ : BundleTest I F V →L_c[ℝ] ℝ) = {x} := by
  ext p
  obtain ⟨c, hc, hcs, hct, hp⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) p
  rw [mem_sobolevSingularSupport_iff, isLocallySobolevAt_iff _ hc hcs hct hp, mem_singleton_iff]
  have hdelta (y : E) (hy : y ∈ c.target) := Distribution.sobolevSingularSupport_delta
    (Ω := ⟨c.target, c.open_target⟩) (x₀ := y) hs hy
  constructor
  · -- Away from `x`, the local representative is a multiple of a point mass elsewhere, or zero.
    intro h
    by_contra hpx
    refine h fun v ↦ ?_
    by_cases hx : x ∈ c.source
    · rw [chartComponent_delta_of_mem _ _ _ _ hx]
      refine ((notMem_sobolevSingularSupport_iff (c.map_source hp)).1 ?_).smul _
      rw [hdelta _ (c.map_source hx), mem_singleton_iff]
      exact fun h' ↦ hpx (c.injOn hp hx h')
    · rw [chartComponent_delta_of_notMem _ _ _ _ hx]
      exact isLocallySobolevAt_zero_iff.2 (c.map_source hp)
  · -- At `x`, some component is a nonzero multiple of the point mass at `c x`.
    rintro rfl h
    obtain ⟨u, hu⟩ : ∃ u, ℓ u ≠ 0 := by
      by_contra! h0
      exact hℓ (ContinuousLinearMap.ext h0)
    have hv := h ((trivializationAt F V p).continuousLinearMapAt ℝ p u)
    rw [chartComponent_delta_of_mem _ _ _ _ hp,
      (trivializationAt F V p).symmL_continuousLinearMapAt (hct hp),
      Distribution.isLocallySobolevAt_smul_iff (Complex.ofReal_ne_zero.2 hu)] at hv
    exact (notMem_sobolevSingularSupport_iff (c.map_source hp)).2 hv
      (by simp [hdelta _ (c.map_source hp)])

end Boundaryless

end TauCeti.BundleTest
