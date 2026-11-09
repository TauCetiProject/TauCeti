/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Global sections with a prescribed value

Let `V` be a `C^n` real vector bundle, `n ≤ ∞`, over a finite-dimensional Hausdorff smooth
manifold. Every vector in `V` is the value of a global `C^n` section. This lets tensorial
operations on globally `C^n` sections define maps on individual fibres. The construction cuts off
Mathlib's locally `C^n` `FiberBundle.extend` with a smooth bump function.

Every fibre vector is moreover the value of a compactly supported smooth section supported in any
prescribed neighbourhood of its base point
(`ContMDiffSection.exists_apply_eq_isCompact_tsupport_subset`): the section is constant in the
preferred trivialization and cut off by a smooth bump function.
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

open Set
open scoped Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞} {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle n F V I]

/-- Every vector `v` of the fibre over `x₀` is the value at `x₀` of a smooth section whose closed
support is compact and contained in any prescribed neighbourhood `U` of `x₀`. -/
theorem exists_apply_eq_isCompact_tsupport_subset (x₀ : M) (v : V x₀) {U : Set M}
    (hU : U ∈ 𝓝 x₀) :
    ∃ s : Cₛ^n⟮I; F, V⟯, s x₀ = v ∧ IsCompact s.tsupport ∧ s.tsupport ⊆ U := by
  let e := trivializationAt F V x₀
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  obtain ⟨ρ, -, hρ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x₀).mem_iff.1
    (Filter.inter_mem hU (e.open_baseSet.mem_nhds hx₀))
  -- The section `x ↦ e.symm x c` is constant, equal to the coordinate `c` of `v`, in `e`.
  obtain ⟨c, hc⟩ : ∃ c, e.symm x₀ c = v := ⟨_, e.symm_apply_apply_mk hx₀ v⟩
  have ht : ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun x ↦ TotalSpace.mk' F x (e.symm x c)) e.baseSet := by
    rw [e.contMDiffOn_section_baseSet_iff]
    exact contMDiffOn_const.congr fun x hx ↦ by rw [e.apply_mk_symm hx]
  let s : Cₛ^n⟮I; F, V⟯ := ⟨fun x ↦ ρ x • e.symm x c,
    (ρ.contMDiff.of_le (mod_cast le_top)).contMDiffOn.smul_section_of_tsupport e.open_baseSet
      (hρ.trans inter_subset_right) ht⟩
  have hs (x : M) : s x = ρ x • e.symm x c := (rfl)
  have hsρ : s.tsupport ⊆ _root_.tsupport ρ :=
    (tsupport_subset_iff (_root_.isClosed_tsupport _)).2 fun x hx ↦ by
      rw [hs, image_eq_zero_of_notMem_tsupport (f := (ρ : M → ℝ)) hx, zero_smul]
  exact ⟨s, by rw [hs, ρ.eq_one, one_smul, hc],
    ρ.hasCompactSupport.isCompact.of_isClosed_subset s.isClosed_tsupport hsρ,
    hsρ.trans (hρ.trans inter_subset_left)⟩

end ContMDiffSection
