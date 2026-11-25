/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.ChangeOfVariables
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Localization

/-!
# The Sobolev wave front set of a functional on bundle tests

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a
finite-dimensional real inner product space `E`, and let `T` be a real continuous linear functional
on the bundle tests `TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, `T` has components along the vectors `v` of the model fibre `F`
(`Bundle.Trivialization.chartComponent`), complex distributions on the chart target. As for the
wave front set (`TauCeti.BundleTest.waveFrontSet`), `T` is **microlocally `H^s`** in the chart at
`(y, η)` when all these components are microlocally `H^s` there
(`Distribution.IsMicrolocallySobolevAt`).

Being microlocally `H^s` is an invariant notion of microlocal regularity
(`Distribution.isInvariantMicrolocalRegularity_isMicrolocallySobolevAt`): it is preserved by smooth
multiples, finite sums and restriction, and pullback along a change of variables transforms it by
the transpose of the derivative
(`Distribution.isMicrolocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`).
So microlocal `H^s` regularity of `T` is `TauCeti.BundleTest.IsMicrolocallyAt` for
`Distribution.IsMicrolocallySobolevAt`, and it does not depend on the chart or the frame
(`Bundle.Trivialization.forall_chartComponent_microlocal_iff`,
`TauCeti.BundleTest.isMicrolocallySobolevAt_iff`). Hence microlocal `H^s` regularity of `T` at a
covector `ξ ∈ T*ₓM` is well defined on a manifold without boundary
(`TauCeti.BundleTest.IsMicrolocallySobolevAt`), and the **`H^s` wave front set** of `T`
(`TauCeti.BundleTest.sobolevWaveFrontSet`) is the set of nonzero covectors of the cotangent bundle
`TauCeti.CotangentBundle I M` at which `T` is not microlocally `H^s`. It is conic, closed in the
complement of the zero section, grows with `s`, lies in the wave front set, and the `H^s` wave front
set of a sum lies in the union.

## Main declarations

* `TauCeti.BundleTest.IsMicrolocallySobolevAt`: microlocal `H^s` regularity of `T` at a covector
  of `M`, with its defining property `TauCeti.BundleTest.isMicrolocallySobolevAt_def`, and
  `TauCeti.BundleTest.isMicrolocallySobolevAt_iff`, its characterization in every chart and frame.
* `TauCeti.BundleTest.IsMicrolocallySmoothAt.isMicrolocallySobolevAt`,
  `TauCeti.BundleTest.IsMicrolocallySobolevAt.mono`,
  `TauCeti.BundleTest.IsMicrolocallySobolevAt.add`,
  `TauCeti.BundleTest.IsMicrolocallySobolevAt.smul`: microlocal smoothness implies microlocal
  `H^s` regularity, which implies `H^r` regularity for `r ≤ s` and is preserved by sums and real
  multiples.
* `TauCeti.BundleTest.sobolevWaveFrontSet`: the `H^s` wave front set of `T`, a subset of the
  cotangent bundle.
* `TauCeti.BundleTest.mk_smul_mem_sobolevWaveFrontSet_iff`: the `H^s` wave front set is conic.
* `TauCeti.BundleTest.isOpen_setOf_isMicrolocallySobolevAt`: microlocal `H^s` regularity is an
  open condition on the cotangent bundle, so the `H^s` wave front set is closed in the complement
  of the zero section (`TauCeti.BundleTest.isOpen_diff_sobolevWaveFrontSet`).
* `TauCeti.BundleTest.sobolevWaveFrontSet_mono`,
  `TauCeti.BundleTest.sobolevWaveFrontSet_subset_waveFrontSet`: it grows with `s` and lies in the
  wave front set.
* `TauCeti.BundleTest.sobolevWaveFrontSet_add_subset`,
  `TauCeti.BundleTest.sobolevWaveFrontSet_smul`: the `H^s` wave front set of a sum lies in the
  union, and nonzero real multiples do not change it.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1
  (the `H^s` wave front set, and its invariance under diffeomorphisms).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (the wave front set on a manifold).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology InnerProduct CompactConvergenceCLM

/-! ### Microlocal Sobolev regularity on the manifold -/

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

/-- A real functional `T` on bundle tests is **microlocally `H^s`** at a covector `ξ` at `x` if,
in some smooth chart `c` at `x` with smooth inverse and some frame `t` over its source, every
component of the local representative of `T` is microlocally `H^s` at `c x` in the direction of
the covector `ξ ∘ D(c⁻¹)(c x)` read in the chart, identified with a vector of `E` through the inner
product. The chart and the frame do not matter
(`TauCeti.BundleTest.isMicrolocallySobolevAt_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` is never
microlocally `H^s` there. -/
def IsMicrolocallySobolevAt (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : Prop :=
  IsMicrolocallyAt (fun _ S y η ↦ S.IsMicrolocallySobolevAt s y η) T x ξ

/-- Microlocal `H^s` regularity is `TauCeti.BundleTest.IsMicrolocallyAt` for
`Distribution.IsMicrolocallySobolevAt`. -/
theorem isMicrolocallySobolevAt_def {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} :
    IsMicrolocallySobolevAt s T x ξ ↔
      IsMicrolocallyAt (fun _ S y η ↦ S.IsMicrolocallySobolevAt s y η) T x ξ :=
  Iff.rfl

/-- **Microlocal Sobolev regularity in any chart and frame.** For a smooth chart `c` at `x` with
smooth inverse and a frame `t` over its source, `T` is microlocally `H^s` at the covector `ξ` at
`x` exactly when every component of its local representative in `(t, c)` is microlocally `H^s`
at `c x` in the direction of `ξ` read in the chart. -/
theorem isMicrolocallySobolevAt_iff {s : ℝ} (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) {x : M} (hx : x ∈ c.source) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    IsMicrolocallySobolevAt s T x ξ ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySobolevAt s (c x)
        ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x))) :=
  isMicrolocallyAt_iff (isInvariantMicrolocalRegularity_isMicrolocallySobolevAt s) T hc hcs hct hx
    ξ

/-- A functional microlocally smooth at a covector is microlocally `H^s` there, for every `s`. -/
theorem IsMicrolocallySmoothAt.isMicrolocallySobolevAt {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (h : IsMicrolocallySmoothAt T x ξ) (s : ℝ) :
    IsMicrolocallySobolevAt s T x ξ :=
  (isMicrolocallySmoothAt_def.1 h).mono fun _ _ _ _ h ↦ h.isMicrolocallySobolevAt s

/-- Being microlocally `H^s` at a covector implies being microlocally `H^r` there for `r ≤ s`. -/
theorem IsMicrolocallySobolevAt.mono {s r : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (h : IsMicrolocallySobolevAt s T x ξ) (hrs : r ≤ s) :
    IsMicrolocallySobolevAt r T x ξ :=
  IsMicrolocallyAt.mono h fun _ _ _ _ h ↦ h.mono hrs

/-- Microlocal `H^s` regularity on the manifold depends only on the ray through the covector. -/
theorem isMicrolocallySobolevAt_smul_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} {r : ℝ} (hr : 0 < r) :
    IsMicrolocallySobolevAt s T x (r • ξ) ↔ IsMicrolocallySobolevAt s T x ξ :=
  isMicrolocallyAt_smul_iff (isInvariantMicrolocalRegularity_isMicrolocallySobolevAt s) hr

/-- The sum of two functionals microlocally `H^s` at a covector is microlocally `H^s` there. -/
theorem IsMicrolocallySobolevAt.add {s : ℝ} {S T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (hS : IsMicrolocallySobolevAt s S x ξ)
    (hT : IsMicrolocallySobolevAt s T x ξ) : IsMicrolocallySobolevAt s (S + T) x ξ :=
  IsMicrolocallyAt.add (isInvariantMicrolocalRegularity_isMicrolocallySobolevAt s) hS hT

/-- A real multiple of a functional microlocally `H^s` at a covector is microlocally `H^s`
there. -/
theorem IsMicrolocallySobolevAt.smul {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (h : IsMicrolocallySobolevAt s T x ξ) (a : ℝ) :
    IsMicrolocallySobolevAt s (a • T) x ξ :=
  IsMicrolocallyAt.smul (isInvariantMicrolocalRegularity_isMicrolocallySobolevAt s) h a

/-- **Microlocal `H^s` regularity is an open condition.** The covectors at which a real functional
on bundle tests is microlocally `H^s` form an open subset of the cotangent bundle. -/
theorem isOpen_setOf_isMicrolocallySobolevAt (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsOpen {p : CotangentBundle I M | IsMicrolocallySobolevAt s T p.proj p.snd} :=
  isOpen_setOf_isMicrolocallyAt (isInvariantMicrolocalRegularity_isMicrolocallySobolevAt s) T

/-! ### The Sobolev wave front set -/

variable (I) in
/-- The **`H^s` wave front set** of a real functional `T` on bundle tests, for instance a
distributional section of a bundle: the nonzero covectors of `M` at which `T` is not microlocally
`H^s`. -/
def sobolevWaveFrontSet (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) : Set (CotangentBundle I M) :=
  {p | p.snd ≠ 0 ∧ ¬ IsMicrolocallySobolevAt s T p.proj p.snd}

@[simp]
theorem mem_sobolevWaveFrontSet_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ}
    {p : CotangentBundle I M} :
    p ∈ sobolevWaveFrontSet I s T ↔ p.snd ≠ 0 ∧ ¬ IsMicrolocallySobolevAt s T p.proj p.snd :=
  Iff.rfl

/-- The `H^s` wave front set is conic: it is invariant under positive scaling of the
covectors. -/
theorem mk_smul_mem_sobolevWaveFrontSet_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} {r : ℝ} (hr : 0 < r) :
    TotalSpace.mk x (r • ξ) ∈ sobolevWaveFrontSet I s T ↔
      TotalSpace.mk x ξ ∈ sobolevWaveFrontSet I s T := by
  simp [isMicrolocallySobolevAt_smul_iff hr, hr.ne']

/-- **The `H^s` wave front set is closed** in the complement of the zero section of the cotangent
bundle. -/
theorem isOpen_diff_sobolevWaveFrontSet (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsOpen (zeroSectionCompl (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) \
      sobolevWaveFrontSet I s T) := by
  have h : zeroSectionCompl (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) \
      sobolevWaveFrontSet I s T =
        zeroSectionCompl (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ∩
          {p | IsMicrolocallySobolevAt s T p.proj p.snd} := by
    ext p
    simp only [Set.mem_sdiff, mem_zeroSectionCompl, mem_sobolevWaveFrontSet_iff, mem_inter_iff,
      mem_ofPred_eq]
    tauto
  rw [h]
  exact (isOpen_zeroSectionCompl _ _).inter (isOpen_setOf_isMicrolocallySobolevAt s T)

/-- The `H^s` wave front set grows with `s`. -/
theorem sobolevWaveFrontSet_mono {s r : ℝ} (hrs : r ≤ s) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I r T ⊆ sobolevWaveFrontSet I s T :=
  fun _ ⟨hp, h⟩ ↦ ⟨hp, fun h' ↦ h (h'.mono hrs)⟩

/-- The `H^s` wave front set lies in the wave front set. -/
theorem sobolevWaveFrontSet_subset_waveFrontSet (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s T ⊆ waveFrontSet I T :=
  fun _ ⟨hp, h⟩ ↦ mem_waveFrontSet_iff.2 ⟨hp, fun h' ↦ h (h'.isMicrolocallySobolevAt s)⟩

/-- The `H^s` wave front set of a sum lies in the union of the `H^s` wave front sets. -/
theorem sobolevWaveFrontSet_add_subset (s : ℝ) (S T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (S + T) ⊆ sobolevWaveFrontSet I s S ∪ sobolevWaveFrontSet I s T := by
  refine fun p ⟨hp, h⟩ ↦ by_contra fun hST ↦ h ?_
  simp only [mem_union, mem_sobolevWaveFrontSet_iff, not_or, not_and, not_not] at hST
  exact (hST.1 hp).add (hST.2 hp)

/-- A real multiple of `T` has `H^s` wave front set contained in that of `T`. -/
theorem sobolevWaveFrontSet_smul_subset (s a : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (a • T) ⊆ sobolevWaveFrontSet I s T :=
  fun _ ⟨hp, h⟩ ↦ ⟨hp, fun hT ↦ h (hT.smul a)⟩

/-- A nonzero real multiple of `T` has the same `H^s` wave front set as `T`. -/
@[simp]
theorem sobolevWaveFrontSet_smul (s : ℝ) {a : ℝ} (ha : a ≠ 0) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (a • T) = sobolevWaveFrontSet I s T := by
  refine (sobolevWaveFrontSet_smul_subset s a T).antisymm ?_
  simpa [smul_smul, inv_mul_cancel₀ ha] using sobolevWaveFrontSet_smul_subset s a⁻¹ (a • T)

/-- The negative of `T` has the same `H^s` wave front set as `T`. -/
@[simp]
theorem sobolevWaveFrontSet_neg (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (-T) = sobolevWaveFrontSet I s T := by
  rw [← neg_one_smul ℝ T, sobolevWaveFrontSet_smul s (neg_ne_zero.2 one_ne_zero)]

/-- The `H^s` wave front set of a difference lies in the union of the `H^s` wave front sets. -/
theorem sobolevWaveFrontSet_sub_subset (s : ℝ) (S T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (S - T) ⊆ sobolevWaveFrontSet I s S ∪ sobolevWaveFrontSet I s T := by
  simpa [sub_eq_add_neg] using sobolevWaveFrontSet_add_subset s S (-T)

/-- On a manifold without boundary, the zero functional has empty `H^s` wave front set. -/
@[simp]
theorem sobolevWaveFrontSet_zero [I.Boundaryless] (s : ℝ) :
    sobolevWaveFrontSet I s (0 : BundleTest I F V →L_c[ℝ] ℝ) = ∅ :=
  subset_empty_iff.1 (waveFrontSet_zero (I := I) (F := F) (V := V) ▸
    sobolevWaveFrontSet_subset_waveFrontSet s 0)

end TauCeti.BundleTest
