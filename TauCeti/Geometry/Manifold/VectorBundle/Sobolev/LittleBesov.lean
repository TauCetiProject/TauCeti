/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Local.Little
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Besov
import Mathlib.Topology.Algebra.Module.Equiv.Submodule
import TauCeti.Algebra.Module.Submodule.Map

/-!
# Little Besov spaces of distributions on bundle tests

Let `V → M` be a smooth real vector bundle with model fibre `F`, and let `A` be a square chart
partition of `V` (`TauCeti.SquareChartPartition`). A real functional `T` on the bundle tests
`TauCeti.BundleTest I F V`, for instance a distributional section of a bundle whose dual density
bundle is `V`, has finitely many localizations `χᵢ Tᵢⱼ`
(`TauCeti.SquareChartPartition.localization`), compactly supported tempered distributions on the
model space `E`. Its Besov regularity `B^s_{p,q}` with respect to `A`
(`TauCeti.SquareChartPartition.MemBesov`) is read off these localizations.

The **little Besov space** `b^s_{p,∞}(E)` is the closure of the Schwartz functions in
`B^s_{p,∞}(E)` (`TemperedDistribution.MemLittleBesov`). For `p < ∞` it consists of the elements of
`B^s_{p,∞}` whose weighted Littlewood–Paley blocks `2^{ks} ‖Δₖ u‖_p` tend to zero; at `p = ∞` it is
the little Hölder–Zygmund space `c^s`. This file builds the corresponding subspace of the bundle
Besov space `B^s_{p,∞}`, for every real `s` and `1 ≤ p ≤ ∞`.

* `T` is **`b^s_{p,∞}` with respect to `A`** (`TauCeti.SquareChartPartition.MemLittleBesov`) when
  all its localizations lie in `b^s_{p,∞}(E, ℂ)`. For `p < ∞` this is the decay
  `2^{ks} ‖Δₖ (χᵢ Tᵢⱼ)‖_p → 0` of the weighted blocks of every localization
  (`TauCeti.SquareChartPartition.memLittleBesov_iff_tendsto`). It implies `B^s_{p,∞}`, follows from
  `B^s_{p,q}` with `q < ∞` when `p < ∞`, and from `H^s` when `p = 2`.
* The **little Besov space** `TauCeti.SquareChartPartition.littleBesovSpace` is the real subspace
  of the Besov space `B^s_{p,∞}` of `A` (`TauCeti.SquareChartPartition.besovSpace`) whose
  components lie in `b^s_{p,∞}(E, ℂ)`, that is, which represent functionals that are `b^s_{p,∞}`
  with respect to `A` (`TauCeti.SquareChartPartition.mem_littleBesovSpace_iff_memLittleBesov`). It
  is closed (`TauCeti.SquareChartPartition.isClosed_littleBesovSpace`), hence a Banach space with
  the norm inherited from `B^s_{p,∞}`, so its inclusion `(A.littleBesovSpace φ s p).subtypeₗᵢ` is
  isometric. It is linearly equivalent to the subspace of `b^s_{p,∞}` functionals
  (`TauCeti.SquareChartPartition.littleBesovSpaceEquiv`).

**Independence of the choices.** Being `b^s_{p,∞}` near a point of `M`
(`TauCeti.BundleTest.IsLocallyMemLittleBesovAt`) is defined in a chart and a frame, and does not
depend on them (`TauCeti.BundleTest.isLocallyMemLittleBesovAt_iff`), since local `b^s_{p,∞}`
regularity on `E` is invariant under smooth multiples and smooth changes of variables
(`Distribution.isInvariantLocalRegularity_isLocallyMemLittleBesovAt`). A functional is `b^s_{p,∞}`
with respect to `A` exactly when it is `b^s_{p,∞}` near every point
(`TauCeti.SquareChartPartition.memLittleBesov_iff_forall_isLocallyMemLittleBesovAt`), so two square
chart partitions have the same `b^s_{p,∞}` functionals. The isomorphism between their Besov spaces
(`TauCeti.SquareChartPartition.besovSpaceCongr`) therefore restricts to an isomorphism of Banach
spaces between their little Besov spaces (`TauCeti.SquareChartPartition.littleBesovSpaceCongr`),
and the pinned norms on them are equivalent. Likewise the change of bump function
(`TauCeti.SquareChartPartition.besovBumpEquiv`) restricts to the little Besov spaces
(`TauCeti.SquareChartPartition.littleBesovBumpEquiv`).

## References

* H. Triebel, *Theory of Function Spaces*, Birkhäuser, 1983, §2.3.2 (the closure of the Schwartz
  functions in `B^s_{p,∞}`) and §3.2.2 (Besov spaces on manifolds, defined chart by chart).
* J. Bergh and J. Löfström, *Interpolation Spaces: An Introduction*, Springer, 1976,
  Theorem 3.4.2 and §6.2.
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace MeasureTheory TemperedDistribution
open scoped Manifold ContDiff Distributions CompactConvergenceCLM ENNReal

/-! ### Local little Besov regularity on bundles -/

namespace TauCeti.BundleTest

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- A real functional `T` on bundle tests is **`b^s_{p,∞}` near `x`**, for the little Besov space
built from the Littlewood–Paley partition of `φ`, if, in some smooth chart `c` at `x` with smooth
inverse and some frame `t` over its source, the component `ψ ↦ T (ψ • v)` of the local
representative of `T` along every `v : F` is `b^s_{p,∞}` near `c x`
(`TauCeti.BundleTest.IsLocallyAt` for `Distribution.IsLocallyMemLittleBesovAt`). The chart and the
frame do not matter (`TauCeti.BundleTest.isLocallyMemLittleBesovAt_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. -/
def IsLocallyMemLittleBesovAt (φ : ContDiffBump (0 : E)) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M) : Prop :=
  IsLocallyAt (fun _ S y ↦ S.IsLocallyMemLittleBesovAt φ s p y) T x

variable {φ : ContDiffBump (0 : E)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M}

/-- Being `b^s_{p,∞}` near `x` is `TauCeti.BundleTest.IsLocallyAt` for
`Distribution.IsLocallyMemLittleBesovAt`. -/
theorem isLocallyMemLittleBesovAt_def :
    IsLocallyMemLittleBesovAt φ s p T x ↔
      IsLocallyAt (fun _ S y ↦ S.IsLocallyMemLittleBesovAt φ s p y) T x :=
  Iff.rfl

/-- **Local little Besov regularity in any chart and frame.** For a smooth chart `c` at `x` with
smooth inverse and a frame `t` over its source, `T` is `b^s_{p,∞}` near `x` exactly when every
component of its local representative in `(t, c)` is `b^s_{p,∞}` near `c x`. -/
theorem isLocallyMemLittleBesovAt_iff (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) (hx : x ∈ c.source) :
    IsLocallyMemLittleBesovAt φ s p T x ↔
      ∀ v, (t.chartComponent c hc hct T v).IsLocallyMemLittleBesovAt φ s p (c x) :=
  isLocallyAt_iff (Distribution.isInvariantLocalRegularity_isLocallyMemLittleBesovAt φ p s) T hc hcs
    hct hx

/-- **Monotonicity.** Being `b^s_{p,∞}` near `x` implies being `b^{s'}_{p,∞}` near `x` for
`s' ≤ s`. -/
theorem IsLocallyMemLittleBesovAt.mono (h : IsLocallyMemLittleBesovAt φ s p T x) {s' : ℝ}
    (hs : s' ≤ s) : IsLocallyMemLittleBesovAt φ s' p T x :=
  IsLocallyAt.mono h fun _ _ _ h ↦ h.mono hs

/-- **Independence of the bump function.** A functional `b^s_{p,∞}` near `x` for the
Littlewood–Paley partition of `φ` is `b^s_{p,∞}` near `x` for that of any other bump function. -/
theorem IsLocallyMemLittleBesovAt.of_bump (h : IsLocallyMemLittleBesovAt φ s p T x)
    (φ' : ContDiffBump (0 : E)) : IsLocallyMemLittleBesovAt φ' s p T x :=
  IsLocallyAt.mono h fun _ _ _ h ↦ h.of_bump φ'

/-- A functional `b^s_{p,∞}` near `x` is `B^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.isLocallyMemBesovAt (h : IsLocallyMemLittleBesovAt φ s p T x) :
    IsLocallyMemBesovAt φ s p ∞ T x :=
  isLocallyMemBesovAt_def.2 <| IsLocallyAt.mono h fun _ _ _ h ↦ h.isLocallyMemBesovAt

/-- For `p < ∞`, a functional `B^s_{p,q}` near `x` with `q < ∞` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemBesovAt.isLocallyMemLittleBesovAt_of_ne_top {q : ℝ≥0∞}
    (h : IsLocallyMemBesovAt φ s p q T x) (hp : p ≠ (∞ : ℝ≥0∞)) (hq : q ≠ (∞ : ℝ≥0∞)) :
    IsLocallyMemLittleBesovAt φ s p T x :=
  IsLocallyAt.mono (isLocallyMemBesovAt_def.1 h) fun _ _ _ h ↦
    h.isLocallyMemLittleBesovAt_of_ne_top hp hq

variable (φ s p T) in
/-- The points near which `T` is `b^s_{p,∞}` form an open set. -/
theorem isOpen_setOf_isLocallyMemLittleBesovAt :
    IsOpen {x : M | IsLocallyMemLittleBesovAt φ s p T x} :=
  isOpen_setOf_isLocallyAt (Distribution.isLocalRegularity_isLocallyMemLittleBesovAt φ p s) T

/-- A real multiple of a functional `b^s_{p,∞}` near `x` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.smul (h : IsLocallyMemLittleBesovAt φ s p T x) (a : ℝ) :
    IsLocallyMemLittleBesovAt φ s p (a • T) x :=
  IsLocallyAt.smul (Distribution.isLocalRegularity_isLocallyMemLittleBesovAt φ p s) h a

/-- The negative of a functional `b^s_{p,∞}` near `x` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.neg (h : IsLocallyMemLittleBesovAt φ s p T x) :
    IsLocallyMemLittleBesovAt φ s p (-T) x :=
  IsLocallyAt.neg (Distribution.isLocalRegularity_isLocallyMemLittleBesovAt φ p s) h

/-- A nonzero real multiple of `T` is `b^s_{p,∞}` near `x` exactly when `T` is. -/
theorem isLocallyMemLittleBesovAt_smul_iff {a : ℝ} (ha : a ≠ 0) :
    IsLocallyMemLittleBesovAt φ s p (a • T) x ↔ IsLocallyMemLittleBesovAt φ s p T x :=
  isLocallyAt_smul_iff (Distribution.isLocalRegularity_isLocallyMemLittleBesovAt φ p s) ha

/-- The negative of `T` is `b^s_{p,∞}` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallyMemLittleBesovAt_neg_iff :
    IsLocallyMemLittleBesovAt φ s p (-T) x ↔ IsLocallyMemLittleBesovAt φ s p T x :=
  isLocallyAt_neg_iff (Distribution.isLocalRegularity_isLocallyMemLittleBesovAt φ p s)

/-- A sum of functionals `b^s_{p,∞}` near `x` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.add (h : IsLocallyMemLittleBesovAt φ s p T x)
    (h' : IsLocallyMemLittleBesovAt φ s p T' x) : IsLocallyMemLittleBesovAt φ s p (T + T') x :=
  IsLocallyAt.add (Distribution.isInvariantLocalRegularity_isLocallyMemLittleBesovAt φ p s) h h'

/-- A difference of functionals `b^s_{p,∞}` near `x` is `b^s_{p,∞}` near `x`. -/
theorem IsLocallyMemLittleBesovAt.sub (h : IsLocallyMemLittleBesovAt φ s p T x)
    (h' : IsLocallyMemLittleBesovAt φ s p T' x) : IsLocallyMemLittleBesovAt φ s p (T - T') x :=
  IsLocallyAt.sub (Distribution.isInvariantLocalRegularity_isLocallyMemLittleBesovAt φ p s) h h'

variable (φ s p) in
/-- On a manifold without boundary, the zero functional is `b^s_{p,∞}` near every point. -/
theorem isLocallyMemLittleBesovAt_zero [I.Boundaryless] (x : M) :
    IsLocallyMemLittleBesovAt φ s p (0 : BundleTest I F V →L_c[ℝ] ℝ) x :=
  isLocallyAt_zero _ (Distribution.isLocalRegularity_isLocallyMemLittleBesovAt φ p s) x

end TauCeti.BundleTest

namespace TauCeti

namespace SquareChartPartition

attribute [local instance] ContMDiffSection.ChartTestData.memTrivializationAtlas

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

variable (A : SquareChartPartition ι I F V) (φ : ContDiffBump (0 : E))

/-! ### Little Besov regularity -/

section MemLittleBesov

variable (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- A real functional `T` on bundle tests of `V`, for instance a distributional section of a bundle
whose dual density bundle is `V`, is **`b^s_{p,∞}` with respect to the square chart partition `A`**
when each of its localizations `χᵢ Tᵢⱼ` (`TauCeti.SquareChartPartition.localization`) lies in the
little Besov space `b^s_{p,∞}(E, ℂ)` built from the Littlewood–Paley partition of `φ`, the closure
of the Schwartz functions in `B^s_{p,∞}(E, ℂ)`. -/
def MemLittleBesov (T : BundleTest I F V →L_c[ℝ] ℝ) : Prop :=
  ∀ i j, (A.localization i j T).MemLittleBesov φ s p

variable {A φ s p} {T : BundleTest I F V →L_c[ℝ] ℝ}

theorem memLittleBesov_iff :
    A.MemLittleBesov φ s p T ↔ ∀ i j, (A.localization i j T).MemLittleBesov φ s p :=
  Iff.rfl

theorem MemLittleBesov.localization (hT : A.MemLittleBesov φ s p T) (i : ι)
    (j : Fin (Module.finrank ℝ F)) : (A.localization i j T).MemLittleBesov φ s p :=
  hT i j

/-- **Decay of the weighted blocks.** For `1 ≤ p < ∞`, a functional is `b^s_{p,∞}` with respect to
`A` exactly when, for each of its localizations `χᵢ Tᵢⱼ`, the Littlewood–Paley blocks
`Δₖ (χᵢ Tᵢⱼ)` are `Lᵖ` functions with `2^{ks} ‖Δₖ (χᵢ Tᵢⱼ)‖_p → 0`. -/
theorem memLittleBesov_iff_tendsto (hp : p ≠ (∞ : ℝ≥0∞)) :
    A.MemLittleBesov φ s p T ↔ ∀ i j, ∃ f : ℕ → Lp ℂ p (volume : Measure E),
      (∀ k, littlewoodPaleyBlock ℂ φ k (A.localization i j T) = f k) ∧
        Tendsto (fun k : ℕ ↦ (2 : ℝ) ^ (s * k) * ‖f k‖) atTop (𝓝 0) :=
  forall₂_congr fun _ _ ↦ TemperedDistribution.memLittleBesov_iff_tendsto hp

/-- **`b^s_{p,∞} ⊆ B^s_{p,∞}`.** A functional which is `b^s_{p,∞}` with respect to `A` is
`B^s_{p,∞}` with respect to `A`. -/
theorem MemLittleBesov.memBesov (hT : A.MemLittleBesov φ s p T) : A.MemBesov φ s p ∞ T :=
  memBesov_iff.2 fun i j ↦ (hT i j).memBesov

/-- **`B^s_{p,q} ⊆ b^s_{p,∞}` for `p, q < ∞`.** -/
theorem MemBesov.memLittleBesov_of_ne_top {q : ℝ≥0∞} (hT : A.MemBesov φ s p q T)
    (hp : p ≠ (∞ : ℝ≥0∞)) (hq : q ≠ (∞ : ℝ≥0∞)) : A.MemLittleBesov φ s p T :=
  fun i j ↦ (hT.localization i j).memLittleBesov_of_ne_top hp hq

/-- **`H^s ⊆ b^s_{2,∞}`.** A functional which is `H^s` with respect to `A` is `b^s_{2,∞}` with
respect to `A`. -/
theorem MemSobolev.memLittleBesov (hT : A.MemSobolev s T) (φ : ContDiffBump (0 : E)) :
    A.MemLittleBesov φ s 2 T :=
  fun i j ↦ (hT.localization i j).memLittleBesov ENNReal.ofNat_ne_top φ

/-- **Monotonicity.** `b^s_{p,∞} ⊆ b^{s'}_{p,∞}` for `s' ≤ s`. -/
theorem MemLittleBesov.mono {s' : ℝ} (hT : A.MemLittleBesov φ s p T) (hs : s' ≤ s) :
    A.MemLittleBesov φ s' p T :=
  fun i j ↦ (hT i j).mono hs

/-- **Independence of the bump function.** Being `b^s_{p,∞}` with respect to `A` does not depend
on the bump function of the Littlewood–Paley partition. -/
theorem MemLittleBesov.of_bump (hT : A.MemLittleBesov φ s p T) (φ' : ContDiffBump (0 : E)) :
    A.MemLittleBesov φ' s p T :=
  fun i j ↦ (hT i j).of_bump φ'

theorem MemLittleBesov.zero : A.MemLittleBesov φ s p 0 := fun i j ↦ by
  rw [map_zero]
  exact TemperedDistribution.MemLittleBesov.zero

theorem MemLittleBesov.add {T' : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemLittleBesov φ s p T)
    (hT' : A.MemLittleBesov φ s p T') : A.MemLittleBesov φ s p (T + T') := fun i j ↦ by
  rw [map_add]
  exact (hT i j).add (hT' i j)

theorem MemLittleBesov.smul (hT : A.MemLittleBesov φ s p T) (a : ℝ) :
    A.MemLittleBesov φ s p (a • T) := fun i j ↦ by
  rw [map_smul, ← smul_one_smul ℂ a]
  exact (hT i j).smul _

variable (A φ s p)

/-- The functionals on bundle tests that are `b^s_{p,∞}` with respect to `A`, as a real
subspace. -/
def memLittleBesovSubmodule : Submodule ℝ (BundleTest I F V →L_c[ℝ] ℝ) where
  carrier := {T | A.MemLittleBesov φ s p T}
  add_mem' := MemLittleBesov.add
  zero_mem' := MemLittleBesov.zero
  smul_mem' a _ hT := hT.smul a

@[simp]
theorem mem_memLittleBesovSubmodule :
    T ∈ A.memLittleBesovSubmodule φ s p ↔ A.MemLittleBesov φ s p T :=
  Iff.rfl

end MemLittleBesov

/-! ### The little Besov spaces -/

section LittleBesovSpace

variable (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The **little Besov space `b^s_{p,∞}` of functionals on bundle tests of `V`** with respect to
the square chart partition `A`: the elements of the Besov space `B^s_{p,∞}` of `A`
(`TauCeti.SquareChartPartition.besovSpace`) all of whose components lie in the little Besov space
`b^s_{p,∞}(E, ℂ)`. These are the elements representing functionals that are `b^s_{p,∞}` with
respect to `A` (`TauCeti.SquareChartPartition.mem_littleBesovSpace_iff_memLittleBesov`). It is a
closed subspace (`TauCeti.SquareChartPartition.isClosed_littleBesovSpace`), hence complete, with
the norm of `B^s_{p,∞}`. -/
def littleBesovSpace : Submodule ℝ (A.besovSpace φ s p ∞) where
  carrier := {u | ∀ k, u.val k ∈ BesovSpace.littleBesov ℂ φ s p}
  add_mem' hu hu' k := (BesovSpace.littleBesov ℂ φ s p).add_mem (hu k) (hu' k)
  zero_mem' _ := (BesovSpace.littleBesov ℂ φ s p).zero_mem
  smul_mem' a _ hu k := by
    rw [Submodule.coe_smul, Pi.smul_apply, ← smul_one_smul ℂ a]
    exact (BesovSpace.littleBesov ℂ φ s p).smul_mem _ (hu k)

variable {s p}

theorem mem_littleBesovSpace {u : A.besovSpace φ s p ∞} :
    u ∈ A.littleBesovSpace φ s p ↔ ∀ k, u.val k ∈ BesovSpace.littleBesov ℂ φ s p :=
  Iff.rfl

/-- An element of the Besov space `B^s_{p,∞}` of `A` lies in the little Besov space exactly when
the functional it represents is `b^s_{p,∞}` with respect to `A`. -/
theorem mem_littleBesovSpace_iff_memLittleBesov {u : A.besovSpace φ s p ∞} :
    u ∈ A.littleBesovSpace φ s p ↔ A.MemLittleBesov φ s p (A.besovToDistribution φ s p ∞ u) := by
  rw [mem_littleBesovSpace, memLittleBesov_iff, Prod.forall]
  refine forall₂_congr fun i j ↦ ?_
  rw [← BesovSpace.memLittleBesov_toDistr_iff, ← A.localization_besovToDistribution φ u (i, j)]

/-- The tuple of localizations of a functional which is `B^s_{p,∞}` with respect to `A` lies in
the little Besov space exactly when the functional is `b^s_{p,∞}` with respect to `A`. -/
@[simp]
theorem ofMemBesov_mem_littleBesovSpace_iff {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemBesov φ s p ∞ T) :
    A.ofMemBesov φ hT ∈ A.littleBesovSpace φ s p ↔ A.MemLittleBesov φ s p T := by
  rw [mem_littleBesovSpace_iff_memLittleBesov, besovToDistribution_ofMemBesov]

/-- The element of the little Besov space representing a functional which is `b^s_{p,∞}` with
respect to `A`: the tuple of its localizations. -/
def ofMemLittleBesov {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemLittleBesov φ s p T) :
    A.littleBesovSpace φ s p :=
  ⟨A.ofMemBesov φ hT.memBesov, (A.ofMemBesov_mem_littleBesovSpace_iff φ hT.memBesov).2 hT⟩

@[simp]
theorem coe_ofMemLittleBesov {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemLittleBesov φ s p T) :
    (A.ofMemLittleBesov φ hT : A.besovSpace φ s p ∞) = A.ofMemBesov φ hT.memBesov :=
  (rfl)

theorem besovToDistribution_ofMemLittleBesov {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemLittleBesov φ s p T) :
    A.besovToDistribution φ s p ∞ (A.ofMemLittleBesov φ hT) = T :=
  A.besovToDistribution_ofMemBesov φ hT.memBesov

/-- The element of the little Besov space representing the functional of `u` is `u`. -/
@[simp]
theorem ofMemLittleBesov_besovToDistribution (u : A.littleBesovSpace φ s p) :
    A.ofMemLittleBesov φ ((A.mem_littleBesovSpace_iff_memLittleBesov φ).1 u.property) = u :=
  Subtype.ext (A.ofMemBesov_besovToDistribution φ _)

variable (s p) in
/-- The functionals represented by the little Besov space are exactly those which are
`b^s_{p,∞}` with respect to `A`. -/
theorem map_besovToDistribution_littleBesovSpace :
    (A.littleBesovSpace φ s p).map (A.besovToDistribution φ s p ∞) =
      A.memLittleBesovSubmodule φ s p :=
  Submodule.ext fun _ ↦
    ⟨by rintro ⟨u, hu, rfl⟩; exact (A.mem_littleBesovSpace_iff_memLittleBesov φ).1 hu,
      fun hT ↦ ⟨_, (A.ofMemLittleBesov φ hT).property, A.besovToDistribution_ofMemLittleBesov φ hT⟩⟩

variable (s p) in
/-- The little Besov space is linearly equivalent to the space of functionals on bundle tests that
are `b^s_{p,∞}` with respect to `A`, through the restriction of
`TauCeti.SquareChartPartition.besovToDistribution`. -/
def littleBesovSpaceEquiv : A.littleBesovSpace φ s p ≃ₗ[ℝ] A.memLittleBesovSubmodule φ s p :=
  (Submodule.equivMapOfInjective _ (A.besovToDistribution_injective φ) _).trans
    (LinearEquiv.ofEq _ _ (A.map_besovToDistribution_littleBesovSpace φ s p))

@[simp]
theorem coe_littleBesovSpaceEquiv_apply (u : A.littleBesovSpace φ s p) :
    (A.littleBesovSpaceEquiv φ s p u : BundleTest I F V →L_c[ℝ] ℝ) =
      A.besovToDistribution φ s p ∞ u :=
  (rfl)

@[simp]
theorem littleBesovSpaceEquiv_symm_apply (T : A.memLittleBesovSubmodule φ s p) :
    (A.littleBesovSpaceEquiv φ s p).symm T =
      A.ofMemLittleBesov φ ((A.mem_memLittleBesovSubmodule φ s p).1 T.property) :=
  (A.littleBesovSpaceEquiv φ s p).symm_apply_eq.2 <|
    Subtype.ext (A.besovToDistribution_ofMemLittleBesov φ _).symm

variable (s p)

/-- The little Besov space is closed in the Besov space `B^s_{p,∞}` of `A`. -/
theorem isClosed_littleBesovSpace :
    IsClosed (A.littleBesovSpace φ s p : Set (A.besovSpace φ s p ∞)) := by
  have h : (A.littleBesovSpace φ s p : Set (A.besovSpace φ s p ∞)) =
      ⋂ k, (fun u : A.besovSpace φ s p ∞ ↦ u.val k) ⁻¹' BesovSpace.littleBesov ℂ φ s p := by
    ext u
    simp [mem_littleBesovSpace]
  rw [h]
  exact isClosed_iInter fun k ↦ BesovSpace.isClosed_littleBesov.preimage
    ((continuous_apply k).comp continuous_subtypeVal)

instance : CompleteSpace (A.littleBesovSpace φ s p) :=
  (A.isClosed_littleBesovSpace φ s p).completeSpace_coe

/-! ### Change of bump function -/

variable {s p}

/-- The change of bump function `TauCeti.SquareChartPartition.besovBumpEquiv` maps the little Besov
space built from `φ` onto the one built from `φ'`. -/
theorem besovBumpEquiv_mem_littleBesovSpace_iff (φ' : ContDiffBump (0 : E))
    {u : A.besovSpace φ s p ∞} :
    A.besovBumpEquiv φ s p ∞ φ' u ∈ A.littleBesovSpace φ' s p ↔ u ∈ A.littleBesovSpace φ s p := by
  rw [mem_littleBesovSpace_iff_memLittleBesov, mem_littleBesovSpace_iff_memLittleBesov,
    besovToDistribution_besovBumpEquiv]
  exact ⟨fun h ↦ h.of_bump φ, fun h ↦ h.of_bump φ'⟩

variable (s p) in
/-- **Independence of the bump function.** The little Besov spaces of `A` built from two bump
functions `φ` and `φ'` are isomorphic Banach spaces, through the restriction of
`TauCeti.SquareChartPartition.besovBumpEquiv`, which does not change the represented
functional. -/
def littleBesovBumpEquiv (φ' : ContDiffBump (0 : E)) :
    A.littleBesovSpace φ s p ≃L[ℝ] A.littleBesovSpace φ' s p :=
  ContinuousLinearEquiv.ofSubmodules (A.besovBumpEquiv φ s p ∞ φ') _ _ <|
    Submodule.map_equiv_eq_iff.2 fun _ ↦ A.besovBumpEquiv_mem_littleBesovSpace_iff φ φ'

@[simp]
theorem coe_littleBesovBumpEquiv_apply (φ' : ContDiffBump (0 : E)) (u : A.littleBesovSpace φ s p) :
    (A.littleBesovBumpEquiv φ s p φ' u : A.besovSpace φ' s p ∞) = A.besovBumpEquiv φ s p ∞ φ' u :=
  ContinuousLinearEquiv.ofSubmodules_apply _ _ u

/-- The change of bump function sends the element representing `T` for `φ` to the one
representing `T` for `φ'`. -/
@[simp]
theorem littleBesovBumpEquiv_ofMemLittleBesov (φ' : ContDiffBump (0 : E))
    {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemLittleBesov φ s p T) :
    A.littleBesovBumpEquiv φ s p φ' (A.ofMemLittleBesov φ hT) =
      A.ofMemLittleBesov φ' (hT.of_bump φ') :=
  Subtype.ext <| by
    rw [coe_littleBesovBumpEquiv_apply, coe_ofMemLittleBesov, coe_ofMemLittleBesov,
      besovBumpEquiv_ofMemBesov]

@[simp]
theorem littleBesovBumpEquiv_symm (φ' : ContDiffBump (0 : E)) :
    (A.littleBesovBumpEquiv φ s p φ').symm = A.littleBesovBumpEquiv φ' s p φ :=
  ContinuousLinearEquiv.ext <| funext fun v ↦ by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [coe_littleBesovBumpEquiv_apply, coe_littleBesovBumpEquiv_apply,
      ← A.besovBumpEquiv_symm φ φ' (s := s) (p := p) (q := ∞),
      ContinuousLinearEquiv.apply_symm_apply]

end LittleBesovSpace

/-! ### Independence of the partition -/

section Independence

variable {κ : Type*} [Fintype κ] {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **`b^s_{p,∞}` with respect to a partition is local `b^s_{p,∞}` regularity.** A real functional
`T` on bundle tests is `b^s_{p,∞}` with respect to the square chart partition `A` exactly when it
is `b^s_{p,∞}` near every point of `M` (`TauCeti.BundleTest.IsLocallyMemLittleBesovAt`). In
particular this does not depend on the partition
(`TauCeti.SquareChartPartition.memLittleBesov_iff_memLittleBesov`). -/
theorem memLittleBesov_iff_forall_isLocallyMemLittleBesovAt {T : BundleTest I F V →L_c[ℝ] ℝ} :
    A.MemLittleBesov φ s p T ↔ ∀ x, BundleTest.IsLocallyMemLittleBesovAt φ s p T x :=
  memLittleBesov_iff.trans <| (A.forall_localization_iff_forall_isLocallyAt
    (Distribution.isInvariantLocalRegularity_isLocallyMemLittleBesovAt φ p s)
    (fun _ _ χ _ hχ hS ↦
      Distribution.isLocallyMemLittleBesovAt_iff_exists_ne_zero_memLittleBesov_cutoffTempered.2
        ⟨χ, hχ, hS⟩)
    fun _ _ _ ↦
      Distribution.memLittleBesov_cutoffTempered_of_forall_isLocallyMemLittleBesovAt).trans <|
    forall_congr' fun _ ↦ BundleTest.isLocallyMemLittleBesovAt_def.symm

/-- **Independence of the partition.** A real functional on bundle tests is `b^s_{p,∞}` with
respect to one square chart partition of `V` exactly when it is `b^s_{p,∞}` with respect to any
other. -/
theorem memLittleBesov_iff_memLittleBesov (B : SquareChartPartition κ I F V)
    {T : BundleTest I F V →L_c[ℝ] ℝ} : A.MemLittleBesov φ s p T ↔ B.MemLittleBesov φ s p T := by
  rw [memLittleBesov_iff_forall_isLocallyMemLittleBesovAt,
    memLittleBesov_iff_forall_isLocallyMemLittleBesovAt]

variable (s p) in
/-- Two square chart partitions of `V` have the same `b^s_{p,∞}` functionals. -/
theorem memLittleBesovSubmodule_eq (B : SquareChartPartition κ I F V) :
    A.memLittleBesovSubmodule φ s p = B.memLittleBesovSubmodule φ s p :=
  Submodule.ext fun _ ↦ A.memLittleBesov_iff_memLittleBesov φ B

/-- The identification `TauCeti.SquareChartPartition.besovSpaceCongr` of the Besov spaces
`B^s_{p,∞}` of two partitions maps the little Besov space of `A` onto that of `B`. -/
theorem besovSpaceCongr_mem_littleBesovSpace_iff (B : SquareChartPartition κ I F V)
    {u : A.besovSpace φ s p ∞} :
    A.besovSpaceCongr φ s p ∞ B u ∈ B.littleBesovSpace φ s p ↔ u ∈ A.littleBesovSpace φ s p := by
  rw [mem_littleBesovSpace_iff_memLittleBesov, mem_littleBesovSpace_iff_memLittleBesov,
    besovToDistribution_besovSpaceCongr_apply, A.memLittleBesov_iff_memLittleBesov φ B]

variable (s p) in
/-- **Equivalence of the little Besov spaces of two partitions.** The little Besov spaces
`b^s_{p,∞}` of two square chart partitions `A` and `B` of `V` are isomorphic Banach spaces, through
the restriction of `TauCeti.SquareChartPartition.besovSpaceCongr`, which sends an element to the
element representing the same functional on bundle tests. So the pinned norms of the two partitions
are equivalent on the `b^s_{p,∞}` functionals. -/
def littleBesovSpaceCongr (B : SquareChartPartition κ I F V) :
    A.littleBesovSpace φ s p ≃L[ℝ] B.littleBesovSpace φ s p :=
  ContinuousLinearEquiv.ofSubmodules (A.besovSpaceCongr φ s p ∞ B) _ _ <|
    Submodule.map_equiv_eq_iff.2 fun _ ↦ A.besovSpaceCongr_mem_littleBesovSpace_iff φ B

@[simp]
theorem coe_littleBesovSpaceCongr_apply (B : SquareChartPartition κ I F V)
    (u : A.littleBesovSpace φ s p) :
    (A.littleBesovSpaceCongr φ s p B u : B.besovSpace φ s p ∞) = A.besovSpaceCongr φ s p ∞ B u :=
  ContinuousLinearEquiv.ofSubmodules_apply _ _ u

/-- The identification sends the element representing `T` with respect to `A` to the one
representing `T` with respect to `B`. -/
@[simp]
theorem littleBesovSpaceCongr_ofMemLittleBesov (B : SquareChartPartition κ I F V)
    {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemLittleBesov φ s p T) :
    A.littleBesovSpaceCongr φ s p B (A.ofMemLittleBesov φ hT) =
      B.ofMemLittleBesov φ ((A.memLittleBesov_iff_memLittleBesov φ B).1 hT) :=
  Subtype.ext <| by
    rw [coe_littleBesovSpaceCongr_apply, coe_ofMemLittleBesov, coe_ofMemLittleBesov,
      besovSpaceCongr_ofMemBesov]

variable (s p) in
/-- The identification of the little Besov spaces of a partition with itself is the identity. -/
@[simp]
theorem littleBesovSpaceCongr_refl :
    A.littleBesovSpaceCongr φ s p A = ContinuousLinearEquiv.refl ℝ (A.littleBesovSpace φ s p) :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ Subtype.ext <| by
    rw [coe_littleBesovSpaceCongr_apply, besovSpaceCongr_refl]
    rfl

/-- The inverse of the identification from `A` to `B` is the identification from `B` to `A`. -/
@[simp]
theorem littleBesovSpaceCongr_symm (B : SquareChartPartition κ I F V) :
    (A.littleBesovSpaceCongr φ s p B).symm = B.littleBesovSpaceCongr φ s p A :=
  ContinuousLinearEquiv.ext <| funext fun v ↦ by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [coe_littleBesovSpaceCongr_apply, coe_littleBesovSpaceCongr_apply,
      ← A.besovSpaceCongr_symm φ s p ∞ B, ContinuousLinearEquiv.apply_symm_apply]

/-- The identifications compose: going from `A` to `B` and then to `C` is going from `A` to
`C`. -/
@[simp]
theorem littleBesovSpaceCongr_trans {ν : Type*} [Fintype ν] (B : SquareChartPartition κ I F V)
    (C : SquareChartPartition ν I F V) :
    (A.littleBesovSpaceCongr φ s p B).trans (B.littleBesovSpaceCongr φ s p C) =
      A.littleBesovSpaceCongr φ s p C :=
  ContinuousLinearEquiv.ext <| funext fun u ↦ Subtype.ext <| by
    rw [ContinuousLinearEquiv.trans_apply, coe_littleBesovSpaceCongr_apply,
      coe_littleBesovSpaceCongr_apply, coe_littleBesovSpaceCongr_apply,
      ← A.besovSpaceCongr_trans φ s p ∞ B C, ContinuousLinearEquiv.trans_apply]

end Independence

end SquareChartPartition

end TauCeti
