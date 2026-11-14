/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Global sections with a prescribed value

Let `V` be a `C^n` real vector bundle, `n ≤ ∞`, over a finite-dimensional Hausdorff `C^n`
manifold. Every vector in `V` is the value of a global `C^n` section. This lets tensorial
operations on globally `C^n` sections define maps on individual fibres. The section
`FiberBundle.contMDiffExtend I F v` cuts off Mathlib's `FiberBundle.extend F v`, which is constant
in the trivialization at the base point of `v` on its base set, with a smooth bump function
supported in that base set; it does not depend on `n`. It agrees with `FiberBundle.extend F v`
near the base point, its closed support is compact and lies in that base set, and in a vector
bundle it is linear in `v`. Equivalently, evaluation of global `C^n` sections at a point is
surjective.

Every fibre vector is moreover the value of a compactly supported `C^n` section supported in any
prescribed neighbourhood of its base point
(`ContMDiffSection.exists_apply_eq_isCompact_tsupport_subset`): a global `C^n` section with that
value, cut off by a smooth bump function.
-/

public section

open Bundle
open scoped ContDiff Manifold Topology

/-- A smooth bump function on a `C^n` manifold, `n ≤ ∞`, is `C^n`; Mathlib's
`SmoothBumpFunction.contMDiff` assumes a smooth manifold. -/
private theorem SmoothBumpFunction.contMDiff_of_isManifold {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I n M] {c : M}
    (ρ : SmoothBumpFunction I c) : CMDiff n ρ := by
  refine contMDiff_of_tsupport fun y hy ↦ ?_
  have hy' := ρ.tsupport_subset_chartAt_source hy
  exact (((ρ.contDiffAt (n := ⊤)).of_le ENat.LEInfty.out).contMDiffAt.comp _
    (contMDiffAt_extChartAt' hy')).congr_of_eventuallyEq
      (ρ.eqOn_source.eventuallyEq_of_mem <| (chartAt H c).open_source.mem_nhds hy')

namespace FiberBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M]
  (F : Type*) {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]

section Construction

variable [TopologicalSpace F] [∀ x, Zero (V x)] [FiberBundle F V]

/-- A global section of `V` through the fibre vector `v : V x`: Mathlib's `FiberBundle.extend F v`,
which is constant in the trivialization at `x` on its base set, cut off by a smooth bump function
supported in that base set. When `ℝ` acts on the fibres by a multiplicative action it takes the
value `v` at `x` (`FiberBundle.contMDiffExtend_apply_self`), and in a `C^n` vector bundle over a
`C^n` manifold, `n ≤ ∞`, it is `C^n` (`FiberBundle.contMDiff_contMDiffExtend`). -/
noncomputable def contMDiffExtend [∀ x, SMul ℝ (V x)] {x : M} (v : V x) : Π y : M, V y :=
  (((SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.1 <|
    (trivializationAt F V x).open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x).choose :
      M → ℝ) • extend F v

/-- `FiberBundle.contMDiffExtend I F v` is `FiberBundle.extend F v` times one smooth bump function,
centred at the base point `x` of `v`, supported in the base set of the trivialization at `x`, and
the same for every `v : V x`. -/
private theorem exists_contMDiffExtend_eq_smul [∀ x, SMul ℝ (V x)] (x : M) :
    ∃ ρ : SmoothBumpFunction I x, tsupport ρ ⊆ (trivializationAt F V x).baseSet ∧
      ∀ v : V x, contMDiffExtend I F v = (ρ : M → ℝ) • extend F v := by
  have hρ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.1 <|
    (trivializationAt F V x).open_baseSet.mem_nhds <| mem_baseSet_trivializationAt F V x
  exact ⟨hρ.choose, hρ.choose_spec.2, fun _ ↦ rfl⟩

/-- `FiberBundle.contMDiffExtend I F v` takes the value `v` at the base point of `v`. -/
@[simp]
theorem contMDiffExtend_apply_self [∀ x, MulAction ℝ (V x)] {x : M} (v : V x) :
    contMDiffExtend I F v x = v := by
  simp [contMDiffExtend]

/-- Near the base point of `v`, `FiberBundle.contMDiffExtend I F v` agrees with Mathlib's
`FiberBundle.extend F v`. -/
theorem eventually_contMDiffExtend_eq_extend [∀ x, MulAction ℝ (V x)] {x : M} (v : V x) :
    ∀ᶠ y in 𝓝 x, contMDiffExtend I F v y = extend F v y := by
  obtain ⟨ρ, -, hρ⟩ := exists_contMDiffExtend_eq_smul I F (V := V) x
  filter_upwards [ρ.eventuallyEq_one] with y hy
  simp [hρ, hy]

variable [∀ x, SMulWithZero ℝ (V x)]

/-- The closed support of `FiberBundle.contMDiffExtend I F v` lies in the base set of the
trivialization at the base point of `v`. -/
theorem closure_setOf_contMDiffExtend_ne_zero_subset_baseSet {x : M} (v : V x) :
    closure {y | contMDiffExtend I F v y ≠ 0} ⊆ (trivializationAt F V x).baseSet := by
  obtain ⟨ρ, hρs, hρ⟩ := exists_contMDiffExtend_eq_smul I F (V := V) x
  refine (closure_mono fun y hy ↦ Function.mem_support.2 fun h ↦ ?_).trans hρs
  simp [hρ, h] at hy

/-- The closed support of `FiberBundle.contMDiffExtend I F v` is compact. -/
theorem isCompact_closure_setOf_contMDiffExtend_ne_zero {x : M} (v : V x) :
    IsCompact (closure {y | contMDiffExtend I F v y ≠ 0}) := by
  obtain ⟨ρ, -, hρ⟩ := exists_contMDiffExtend_eq_smul I F (V := V) x
  refine ρ.hasCompactSupport.isCompact.of_isClosed_subset isClosed_closure
    (closure_mono fun y hy ↦ Function.mem_support.2 fun h ↦ ?_)
  simp [hρ, h] at hy

/-- `FiberBundle.contMDiffExtend I F v` vanishes off the base set of the trivialization at the
base point of `v`. -/
theorem contMDiffExtend_apply_of_notMem_baseSet {x y : M} (v : V x)
    (hy : y ∉ (trivializationAt F V x).baseSet) : contMDiffExtend I F v y = 0 := by
  by_contra h
  exact hy <| closure_setOf_contMDiffExtend_ne_zero_subset_baseSet I F v <| subset_closure h

end Construction

variable [NormedAddCommGroup F] [NormedSpace ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

section Linear

/-- At each point `y`, `FiberBundle.contMDiffExtend I F v y` is `ℝ`-linear in `v`: off the base
set of the trivialization at the base point the cut-off vanishes, and on it `FiberBundle.extend`
is the linear inverse of the trivialization. -/
private theorem exists_linearMap_contMDiffExtend_apply (x y : M) :
    ∃ L : V x →ₗ[ℝ] V y, ∀ v, contMDiffExtend I F v y = L v := by
  obtain ⟨ρ, hρs, hρ⟩ := exists_contMDiffExtend_eq_smul I F (V := V) x
  refine ⟨ρ y • (trivializationAt F V x).symmₗ ℝ y ∘ₗ (trivializationAt F V x).linearMapAt ℝ x,
    fun v ↦ ?_⟩
  by_cases hy : y ∈ (trivializationAt F V x).baseSet
  · simp [hρ, extend, hy, mem_baseSet_trivializationAt F V x]
  · have h0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hy (hρs h)
    simp [hρ, h0]

/-- `FiberBundle.contMDiffExtend I F` sends the zero vector to the zero section. -/
@[simp]
theorem contMDiffExtend_zero {x : M} : contMDiffExtend I F (0 : V x) = 0 := by
  funext y
  obtain ⟨L, hL⟩ := exists_linearMap_contMDiffExtend_apply I F (V := V) x y
  simp [hL]

/-- `FiberBundle.contMDiffExtend I F` is additive in the fibre vector. -/
theorem contMDiffExtend_add {x : M} (v w : V x) :
    contMDiffExtend I F (v + w) = contMDiffExtend I F v + contMDiffExtend I F w := by
  funext y
  obtain ⟨L, hL⟩ := exists_linearMap_contMDiffExtend_apply I F (V := V) x y
  simp [hL]

/-- `FiberBundle.contMDiffExtend I F` commutes with real scalar multiplication. -/
theorem contMDiffExtend_smul {x : M} (c : ℝ) (v : V x) :
    contMDiffExtend I F (c • v) = c • contMDiffExtend I F v := by
  funext y
  obtain ⟨L, hL⟩ := exists_linearMap_contMDiffExtend_apply I F (V := V) x y
  simp [hL]

/-- `FiberBundle.contMDiffExtend I F` commutes with negation. -/
theorem contMDiffExtend_neg {x : M} (v : V x) :
    contMDiffExtend I F (-v) = -contMDiffExtend I F v := by
  funext y
  obtain ⟨L, hL⟩ := exists_linearMap_contMDiffExtend_apply I F (V := V) x y
  simp [hL]

/-- `FiberBundle.contMDiffExtend I F` commutes with subtraction. -/
theorem contMDiffExtend_sub {x : M} (v w : V x) :
    contMDiffExtend I F (v - w) = contMDiffExtend I F v - contMDiffExtend I F w := by
  funext y
  obtain ⟨L, hL⟩ := exists_linearMap_contMDiffExtend_apply I F (V := V) x y
  simp [hL]

end Linear

/-- In a `C^n` vector bundle over a `C^n` manifold, `n ≤ ∞`,
`FiberBundle.contMDiffExtend I F v` is a global `C^n` section. -/
theorem contMDiff_contMDiffExtend {n : ℕ∞ω} [ENat.LEInfty n] [IsManifold I n M]
    [ContMDiffVectorBundle n F V I] {x : M} (v : V x) :
    CMDiff n (T% (contMDiffExtend I F v)) := by
  obtain ⟨ρ, hρs, hρ⟩ := exists_contMDiffExtend_eq_smul I F (V := V) x
  rw [hρ]
  refine (SmoothBumpFunction.contMDiff_of_isManifold ρ).contMDiffOn.smul_section_of_tsupport
    (trivializationAt F V x).open_baseSet hρs ?_
  rw [(trivializationAt F V x).contMDiffOn_section_baseSet_iff]
  exact (contMDiffOn_const (c := (trivializationAt F V x ⟨x, v⟩).2)).congr fun y hy ↦ by
    simp [extend, hy]

/-- In a `C^n` vector bundle over a `C^n` manifold, `n ≤ ∞`, every fibre vector is the value of a
global `C^n` section. The fibre need not be finite-dimensional, and the base need not be compact or
boundaryless. -/
theorem exists_contMDiff_section_eq (n : ℕ∞ω) [ENat.LEInfty n] [IsManifold I n M]
    [ContMDiffVectorBundle n F V I] {x : M} (v : V x) :
    ∃ s : Π y : M, V y, CMDiff n (T% s) ∧ s x = v :=
  ⟨contMDiffExtend I F v, contMDiff_contMDiffExtend I F v, contMDiffExtend_apply_self I F v⟩

end FiberBundle

namespace ContMDiffSection

section Surjective

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- In a `C^n` vector bundle over a `C^n` manifold, `n ≤ ∞`, evaluation of `C^n` sections at a
point is surjective: every fibre vector is the value of a global `C^n` section. -/
theorem evalLinearMap_surjective (n : ℕ∞ω) [ENat.LEInfty n] [IsManifold I n M]
    [ContMDiffVectorBundle n F V I] (x : M) :
    Function.Surjective (evalLinearMap I F n V x) := fun v ↦ by
  obtain ⟨s, hs, hsx⟩ := FiberBundle.exists_contMDiff_section_eq I F n v
  exact ⟨⟨s, hs⟩, by simpa using hsx⟩

end Surjective

section CompactSupport

open Set
open scoped Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞} [IsManifold I n M]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle n F V I]

/-- On a `C^n` manifold, every vector `v` of the fibre over `x₀` is the value at `x₀` of a `C^n`
section (smooth when `n = ∞`) whose closed support is compact and contained in any prescribed
neighbourhood `U` of `x₀`. -/
theorem exists_apply_eq_isCompact_tsupport_subset (x₀ : M) (v : V x₀) {U : Set M}
    (hU : U ∈ 𝓝 x₀) :
    ∃ s : Cₛ^n⟮I; F, V⟯, s x₀ = v ∧ IsCompact s.tsupport ∧ s.tsupport ⊆ U := by
  obtain ⟨t, ht, htv⟩ := FiberBundle.exists_contMDiff_section_eq I F (n : ℕ∞ω) v
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.1 hU
  let s : Cₛ^n⟮I; F, V⟯ :=
    ⟨(ρ : M → ℝ) • t, (SmoothBumpFunction.contMDiff_of_isManifold (n := n) ρ).smul_section ht⟩
  have hsρ : s.tsupport ⊆ _root_.tsupport ρ :=
    (tsupport_subset_iff (_root_.isClosed_tsupport _)).2 fun x hx ↦ by
      simp [s, image_eq_zero_of_notMem_tsupport (f := (ρ : M → ℝ)) hx]
  exact ⟨s, by simp [s, htv],
    ρ.hasCompactSupport.isCompact.of_isClosed_subset s.isClosed_tsupport hsρ, hsρ.trans hρ⟩

end CompactSupport

end ContMDiffSection
