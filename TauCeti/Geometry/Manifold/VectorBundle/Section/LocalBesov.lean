/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local.ChangeOfVariables
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalRegularity

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
(`TauCeti.BundleTest.IsLocallyMemBesovAt.of_bump`) nor the chart and the frame matter: `T` is
`B^s_{p,q}` near `x` exactly when its components are `B^s_{p,q}` near `c x` in any chart `c` at
`x` and any frame (`TauCeti.BundleTest.isLocallyMemBesovAt_iff`).

This is the case `P = B^s_{p,q}` of the construction of local regularity on bundles from an
invariant notion `P` of local regularity on `E` (`TauCeti.BundleTest.IsLocallyAt`), since being
`B^s_{p,q}` near a point is invariant under smooth multiples, restriction and smooth changes of
variables (`Distribution.isInvariantLocalRegularity_isLocallyMemBesovAt`). The same construction
gives the local Sobolev spaces on bundles (`TauCeti.BundleTest.IsLocallySobolevAt`).

## Main declarations

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

open Set TopologicalSpace Distribution
open scoped Manifold ContDiff Distributions CompactConvergenceCLM ENNReal

namespace TauCeti.BundleTest

open Bundle

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
`T` along every `v : F` is `B^s_{p,q}` near `c x` (`TauCeti.BundleTest.IsLocallyAt` for
`Distribution.IsLocallyMemBesovAt`). For `1 ≤ q`, the chart and the frame do not matter
(`TauCeti.BundleTest.isLocallyMemBesovAt_iff`), and neither does the bump function
(`TauCeti.BundleTest.IsLocallyMemBesovAt.of_bump`). For `p = q = ∞` this is membership in the
local Hölder–Zygmund space `𝒞^s_loc` near `x`.

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` is never
`B^s_{p,q}` there. -/
def IsLocallyMemBesovAt (φ : ContDiffBump (0 : E)) (s : ℝ) (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M) : Prop :=
  IsLocallyAt (fun _ S y ↦ S.IsLocallyMemBesovAt φ s p q y) T x

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
  isLocallyAt_iff (isInvariantLocalRegularity_isLocallyMemBesovAt φ p q s) T hc hcs hct hx

/-- **Monotonicity.** Being `B^s_{p,q}` near `x` implies being `B^{s'}_{p,q'}` near `x` for
`s' ≤ s` and `q ≤ q'`. -/
theorem IsLocallyMemBesovAt.mono (h : IsLocallyMemBesovAt φ s p q T x) {s' : ℝ} {q' : ℝ≥0∞}
    (hs : s' ≤ s) (hq : q ≤ q') : IsLocallyMemBesovAt φ s' p q' T x :=
  IsLocallyAt.mono h fun _ _ _ h ↦ h.mono hs hq

/-- **Independence of the bump function.** A functional `B^s_{p,q}` near `x` for the
Littlewood–Paley partition of `φ` is `B^s_{p,q}` near `x` for that of any other bump function. -/
theorem IsLocallyMemBesovAt.of_bump (h : IsLocallyMemBesovAt φ s p q T x)
    (φ' : ContDiffBump (0 : E)) : IsLocallyMemBesovAt φ' s p q T x :=
  IsLocallyAt.mono h fun _ _ _ h ↦ h.of_bump φ'

variable (φ s p q T) in
/-- The points near which `T` is `B^s_{p,q}` form an open set. -/
theorem isOpen_setOf_isLocallyMemBesovAt : IsOpen {x : M | IsLocallyMemBesovAt φ s p q T x} :=
  isOpen_setOf_isLocallyAt (isLocalRegularity_isLocallyMemBesovAt φ p q s) T

/-- A real multiple of a functional `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.smul (h : IsLocallyMemBesovAt φ s p q T x) (a : ℝ) :
    IsLocallyMemBesovAt φ s p q (a • T) x :=
  IsLocallyAt.smul (isLocalRegularity_isLocallyMemBesovAt φ p q s) h a

/-- The negative of a functional `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.neg (h : IsLocallyMemBesovAt φ s p q T x) :
    IsLocallyMemBesovAt φ s p q (-T) x :=
  IsLocallyAt.neg (isLocalRegularity_isLocallyMemBesovAt φ p q s) h

/-- A nonzero real multiple of `T` is `B^s_{p,q}` near `x` exactly when `T` is. -/
theorem isLocallyMemBesovAt_smul_iff {a : ℝ} (ha : a ≠ 0) :
    IsLocallyMemBesovAt φ s p q (a • T) x ↔ IsLocallyMemBesovAt φ s p q T x :=
  isLocallyAt_smul_iff (isLocalRegularity_isLocallyMemBesovAt φ p q s) ha

/-- The negative of `T` is `B^s_{p,q}` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallyMemBesovAt_neg_iff :
    IsLocallyMemBesovAt φ s p q (-T) x ↔ IsLocallyMemBesovAt φ s p q T x :=
  isLocallyAt_neg_iff (isLocalRegularity_isLocallyMemBesovAt φ p q s)

variable [Fact (1 ≤ q)]

/-- A sum of functionals `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.add (h : IsLocallyMemBesovAt φ s p q T x)
    (h' : IsLocallyMemBesovAt φ s p q T' x) : IsLocallyMemBesovAt φ s p q (T + T') x :=
  IsLocallyAt.add (isInvariantLocalRegularity_isLocallyMemBesovAt φ p q s) h h'

/-- A difference of functionals `B^s_{p,q}` near `x` is `B^s_{p,q}` near `x`. -/
theorem IsLocallyMemBesovAt.sub (h : IsLocallyMemBesovAt φ s p q T x)
    (h' : IsLocallyMemBesovAt φ s p q T' x) : IsLocallyMemBesovAt φ s p q (T - T') x :=
  IsLocallyAt.sub (isInvariantLocalRegularity_isLocallyMemBesovAt φ p q s) h h'

/-! ### Manifolds without boundary -/

section Boundaryless

variable [I.Boundaryless]

omit [Fact (1 ≤ q)] in
variable (φ s p q) in
/-- On a manifold without boundary, the zero functional is `B^s_{p,q}` near every point. -/
theorem isLocallyMemBesovAt_zero (x : M) :
    IsLocallyMemBesovAt φ s p q (0 : BundleTest I F V →L_c[ℝ] ℝ) x :=
  isLocallyAt_zero _ (isLocalRegularity_isLocallyMemBesovAt φ p q s) x

variable (φ q) in
/-- **Functionals on bundle tests have finite Besov order locally.** On a manifold without
boundary and for `1 < p` and `1 ≤ q`, for every compact set `K ⊆ M` there is an order `s` such
that `T` is `B^s_{p,q}` near every point of `K`. -/
theorem exists_forall_isLocallyMemBesovAt (hp : 1 < p) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {K : Set M} (hK : IsCompact K) : ∃ s : ℝ, ∀ x ∈ K, IsLocallyMemBesovAt φ s p q T x :=
  exists_forall_isLocallyAt (isLocalRegularity_isLocallyMemBesovAt φ p q)
    (fun hs h ↦ h.mono hs le_rfl)
    (fun S _ hy ↦ (Distribution.exists_forall_isLocallyMemBesovAt φ hp S isCompact_singleton
      (singleton_subset_iff.2 hy)).imp fun _ h ↦ h _ rfl)
    T hK

end Boundaryless

end TauCeti.BundleTest
