/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.BumpFunction
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Global sections with a prescribed value

Let `V` be a `C^n` real vector bundle, `n ≤ ∞`, over a finite-dimensional Hausdorff smooth
manifold. Every vector in `V` is the value of a global `C^n` section. This lets tensorial
operations on globally `C^n` sections define maps on individual fibres. The construction cuts off
Mathlib's locally `C^n` `FiberBundle.extend` with a smooth bump function. Equivalently,
evaluation of global `C^n` sections at a point is surjective.

For applications requiring a linear family of global sections agreeing with the constant-coordinate
local sections of `FiberBundle.trivializationAt F V x` near `x`, `ContMDiffSection.liftModel`
cuts off `symmL` with a smooth bump function equal to `1` near `x`.

Every fibre vector is moreover the value of a compactly supported `C^n` section supported in any
prescribed neighbourhood of its base point
(`ContMDiffSection.exists_apply_eq_isCompact_tsupport_subset`): a global `C^n` section with that
value, cut off by a smooth bump function.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace FiberBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- In a `C^n` vector bundle with `n ≤ ∞`, every fibre vector is the value of a global `C^n`
section. The fibre need not be finite-dimensional, and the base need not be compact or
boundaryless. -/
theorem exists_contMDiff_section_eq (n : ℕ∞ω) [ENat.LEInfty n] [ContMDiffVectorBundle n F V I]
    {x : M} (v : V x) : ∃ s : Π y : M, V y, CMDiff n (T% s) ∧ s x = v := by
  obtain ⟨u, hu, hs⟩ := exists_contMDiffOn_extend (k := n) I F v
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
    (interior_mem_nhds.2 hu)
  refine ⟨(ρ : M → ℝ) • extend F v, ?_, by simp⟩
  exact (ρ.contMDiff.of_le ENat.LEInfty.out).contMDiffOn.smul_section_of_tsupport
    isOpen_interior hρ (hs.mono interior_subset)

end FiberBundle

namespace ContMDiffSection

section Surjective

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- In a `C^n` vector bundle with `n ≤ ∞`, evaluation of `C^n` sections at a point is surjective:
every fibre vector is the value of a global `C^n` section. -/
theorem evalLinearMap_surjective (n : ℕ∞ω) [ENat.LEInfty n] [ContMDiffVectorBundle n F V I]
    (x : M) : Function.Surjective (evalLinearMap I F n V x) := fun v ↦ by
  obtain ⟨s, hs, hsx⟩ := FiberBundle.exists_contMDiff_section_eq I F n v
  exact ⟨⟨s, hs⟩, by simpa using hsx⟩

section LiftModel

open scoped Topology

variable (I F V) in
/-- Cut off the constant-coordinate local sections of `trivializationAt F V x` by a smooth bump
equal to `1` near `x`, producing an `ℝ`-linear lift from the model fibre `F` to global `C^n`
sections. -/
noncomputable def liftModel (n : ℕ∞ω) [ENat.LEInfty n] [ContMDiffVectorBundle n F V I] (x : M) :
    F →ₗ[ℝ] Cₛ^n⟮I; F, V⟯ :=
  let e := FiberBundle.trivializationAt F V x
  let hx := e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt F V x)
  let hρ := (SmoothBumpFunction.nhds_basis_support (I := I) hx).mem_iff.mp hx
  let ρ := hρ.choose
  { toFun u :=
      ⟨(ρ : M → ℝ) • fun y ↦ e.symmL ℝ y u,
        (ρ.contMDiff.of_le ENat.LEInfty.out).contMDiffOn.smul_section_of_tsupport
          e.open_baseSet hρ.choose_spec.1 <|
          (TauCeti.Manifold.contMDiffOn_symm_baseSet (e := e) u).congr fun y hy ↦ by
            simp [Trivialization.symmL_apply e hy]⟩
    map_add' u₁ u₂ := by ext y; simp [smul_add]
    map_smul' c u := by ext y; simp [smul_comm c] }

/-- Near `x`, `ContMDiffSection.liftModel` agrees with the constant-coordinate local sections of
`trivializationAt F V x`. -/
theorem liftModel_eventuallyEq {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffVectorBundle n F V I]
    (x : M) (u : F) :
    ∀ᶠ y in 𝓝 x, liftModel I F V n x u y = (FiberBundle.trivializationAt F V x).symmL ℝ y u := by
  let hx := (FiberBundle.trivializationAt F V x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt F V x)
  let hρ := (SmoothBumpFunction.nhds_basis_support (I := I) hx).mem_iff.mp hx
  filter_upwards [hρ.choose.eventuallyEq_one] with y hy
  dsimp [liftModel]
  rw [hy, Pi.one_apply, one_smul]

/-- At the base point `x`, `ContMDiffSection.liftModel` evaluates to
`(trivializationAt F V x).symmL`. -/
@[simp]
theorem liftModel_apply_self {n : ℕ∞ω} [ENat.LEInfty n] [ContMDiffVectorBundle n F V I]
    (x : M) (u : F) :
    liftModel I F V n x u x = (FiberBundle.trivializationAt F V x).symmL ℝ x u :=
  (liftModel_eventuallyEq x u).self_of_nhds

end LiftModel

end Surjective

section CompactSupport

open Set
open scoped Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle n F V I]

/-- Every vector `v` of the fibre over `x₀` is the value at `x₀` of a `C^n` section (smooth when
`n = ∞`) whose closed support is compact and contained in any prescribed neighbourhood `U` of
`x₀`. -/
theorem exists_apply_eq_isCompact_tsupport_subset (x₀ : M) (v : V x₀) {U : Set M}
    (hU : U ∈ 𝓝 x₀) :
    ∃ s : Cₛ^n⟮I; F, V⟯, s x₀ = v ∧ IsCompact s.tsupport ∧ s.tsupport ⊆ U := by
  obtain ⟨t, ht, htv⟩ := FiberBundle.exists_contMDiff_section_eq I F (n : ℕ∞ω) v
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.1 hU
  let s : Cₛ^n⟮I; F, V⟯ := ⟨(ρ : M → ℝ) • t, (ρ.contMDiff.of_le (mod_cast le_top)).smul_section ht⟩
  have hsρ : s.tsupport ⊆ _root_.tsupport ρ :=
    (tsupport_subset_iff (_root_.isClosed_tsupport _)).2 fun x hx ↦ by
      simp [s, image_eq_zero_of_notMem_tsupport (f := (ρ : M → ℝ)) hx]
  exact ⟨s, by simp [s, htv],
    ρ.hasCompactSupport.isCompact.of_isClosed_subset s.isClosed_tsupport hsρ, hsρ.trans hρ⟩

end CompactSupport

end ContMDiffSection
