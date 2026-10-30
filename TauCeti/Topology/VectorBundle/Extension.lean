/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Tietze
public import Mathlib.Topology.PartitionOfUnity
public import TauCeti.Topology.VectorBundle.Hom

/-!
# Extending sections and bundle maps from closed subsets

Let `E` be a vector bundle over a normal paracompact base `B` whose model fibre has the Tietze
extension property, for instance a finite-dimensional real or complex normed space. A section of
`E` which is continuous on a closed subset `s` of `B` agrees on `s` with a continuous section
defined on all of `B` (`TauCeti.exists_continuous_section_extension`). In each trivialization the
coordinates of the section are extended by the Tietze extension theorem, and these local
extensions are glued with a partition of unity subordinate to the trivializations.

Applied to Mathlib's Hom bundle, this extends a fibrewise continuous linear map between finite-rank
real or complex vector bundles from a closed subset to the whole base. If the given map is
invertible at every point of `s`, the extension is invertible on an open neighbourhood of `s`
(`TauCeti.exists_continuous_clm_bundle_extension_isInvertible`), because invertibility is an open
condition along a continuous Hom-bundle section
(`Continuous.isOpen_setOf_clm_bundle_isInvertible`). This is the classical statement that an
isomorphism of vector bundles over a closed subset extends to an isomorphism over a neighbourhood,
which underlies clutching constructions and relative K-theory.

## References

* M. F. Atiyah, *K-theory*, §1.4, where the compact Hausdorff case is proved by the same
  extend-locally-and-glue argument.
-/

public section

open Bundle Set Function
open scoped Topology

namespace TauCeti

universe u w

section Section

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {B : Type u} [TopologicalSpace B] [NormalSpace B] [ParacompactSpace B]
  {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TietzeExtension.{u, w} F]
  {E : B → Type*} [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]
  [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]

include 𝕜 in
/-- **Tietze extension for sections of a vector bundle.** Over a normal paracompact base, a
section which is continuous on a closed set agrees there with a continuous global section,
provided the model fibre has the Tietze extension property. The scalar field `𝕜` of the
bundle is explicit: it does not occur in the statement. -/
theorem exists_continuous_section_extension {s : Set B} (hs : IsClosed s) {σ : ∀ x, E x}
    (hσ : ContinuousOn (fun x ↦ TotalSpace.mk' F x (σ x)) s) :
    ∃ τ : ∀ x, E x, Continuous (fun x ↦ TotalSpace.mk' F x (τ x)) ∧ ∀ x ∈ s, τ x = σ x := by
  classical
  let e : B → Trivialization F (π F E) := fun i ↦ trivializationAt F E i
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i ↦ (e i).baseSet) (fun i ↦ (e i).open_baseSet)
    fun x _ ↦ mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F E x⟩
  -- In the chart `e i`, extend the coordinates of `σ` from `s ∩ tsupport (ρ i)` to `B`.
  have hext (i : B) : ∃ g : C(B, F), ∀ x ∈ s ∩ tsupport (ρ i), g x = (e i ⟨x, σ x⟩).2 := by
    have hc : ContinuousOn (fun x ↦ (e i ⟨x, σ x⟩).2) (s ∩ tsupport (ρ i)) :=
      continuous_snd.comp_continuousOn <| (e i).continuousOn.comp (hσ.mono inter_subset_left)
        fun x hx ↦ (e i).mem_source.2 (hρ i hx.2)
    obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq (hs.inter (isClosed_tsupport _))
      ⟨_, hc.domRestrict⟩
    exact ⟨g, fun x hx ↦ congr($hg ⟨x, hx⟩)⟩
  choose g hg using hext
  -- Glue the local extensions with the partition of unity.
  let w : B → B → 𝕜 := fun i x ↦ algebraMap ℝ 𝕜 (ρ i x)
  let t : B → ∀ x, E x := fun i x ↦ w i x • (e i).symm x (g i x)
  have ht (x : B) : support (t · x) ⊆ ρ.finsupport x := fun i hi ↦
    (ρ.mem_finsupport x).2 fun h ↦ hi (by simp [t, w, h])
  refine ⟨fun x ↦ ∑ᶠ i, t i x, ?_, fun x hx ↦ ?_⟩
  · refine continuous_iff_continuousAt.2 fun x₀ ↦ (FiberBundle.continuousAt_section F x₀).2 ?_
    -- Near `x₀` only the charts in a finite set `I` contribute, and the coordinates of the
    -- glued section in the chart at `x₀` are a finite sum.
    obtain ⟨I, hI⟩ := ρ.exists_finset_nhds x₀
    let e₀ := trivializationAt F E x₀
    have hx₀ : x₀ ∈ e₀.baseSet := mem_baseSet_trivializationAt F E x₀
    have hcoord : (fun x ↦ ∑ i ∈ I, w i x • (e₀ ⟨x, (e i).symm x (g i x)⟩).2) =ᶠ[𝓝 x₀]
        fun x ↦ (e₀ ⟨x, ∑ᶠ i, t i x⟩).2 := by
      filter_upwards [hI, e₀.open_baseSet.mem_nhds hx₀] with x hx hxe
      rw [finsum_eq_sum_of_support_subset _ fun i hi ↦ hx.2 ((ρ.mem_finsupport x).1 (ht x hi)),
        ← e₀.continuousLinearMapAt_apply_of_mem (R := 𝕜) hxe, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul, e₀.continuousLinearMapAt_apply_of_mem (R := 𝕜) hxe]
    refine ContinuousAt.congr (tendsto_finsetSum I fun i _ ↦ ?_) hcoord
    by_cases hi : x₀ ∈ tsupport (ρ i)
    · -- The chart `e i` is defined near `x₀`, where the local extension is continuous.
      have hsec : ContinuousAt (fun x ↦ TotalSpace.mk' F x ((e i).symm x (g i x))) x₀ :=
        ((e i).continuousOn_symm.continuousAt (prod_mem_nhds
          ((e i).open_baseSet.mem_nhds (hρ i hi)) Filter.univ_mem)).comp_of_eq
            (continuousAt_id.prodMk (g i).continuous.continuousAt) rfl
      have he₀ : ContinuousAt e₀ (TotalSpace.mk' F x₀ ((e i).symm x₀ (g i x₀))) :=
        e₀.continuousOn.continuousAt (e₀.open_source.mem_nhds (e₀.mem_source.2 hx₀))
      exact ((continuous_algebraMap ℝ 𝕜).comp (ρ i).continuous).continuousAt.smul
        (he₀.comp_of_eq hsec rfl).snd
    · -- Away from the support of `ρ i` the corresponding term vanishes.
      refine (continuousAt_const (y := (0 : F))).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hi] with x hx
      simp [w, hx]
  · have hti (i : B) : t i x = w i x • σ x := by
      by_cases h : ρ i x = 0
      · simp [t, w, h]
      · have hxi : x ∈ s ∩ tsupport (ρ i) := ⟨hx, subset_tsupport _ h⟩
        simp only [t, hg i x hxi, (e i).symm_apply_apply_mk (hρ i hxi.2)]
    dsimp only
    rw [finsum_eq_sum_of_support_subset _ (ht x)]
    simp only [hti, ← Finset.sum_smul, w, ← map_sum, ρ.sum_finsupport (mem_univ x), map_one,
      one_smul]

end Section

section Hom

variable {𝕜 : Type*} [RCLike 𝕜]
  {B : Type u} [TopologicalSpace B] [NormalSpace B] [ParacompactSpace B]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₁ E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-- **Extending a bundle isomorphism from a closed subset.** Over a normal paracompact base, let
`ϕ` be a fibrewise continuous linear map between real or complex vector bundles of finite rank,
continuous as a Hom-bundle section on a closed set `s` and invertible at every point of `s`. Then
`ϕ` agrees on `s` with a continuous Hom-bundle section on the whole base which is invertible on an
open neighbourhood of `s`. -/
theorem exists_continuous_clm_bundle_extension_isInvertible {s : Set B} (hs : IsClosed s)
    {ϕ : ∀ x, E₁ x →L[𝕜] E₂ x}
    (hϕ : ContinuousOn (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂)
      (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (ϕ x)) s)
    (hinv : ∀ x ∈ s, (ϕ x).IsInvertible) :
    ∃ ψ : ∀ x, E₁ x →L[𝕜] E₂ x,
      Continuous (fun x ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun y ↦ E₁ y →L[𝕜] E₂ y) x (ψ x)) ∧
      (∀ x ∈ s, ψ x = ϕ x) ∧ ∃ U, IsOpen U ∧ s ⊆ U ∧ ∀ x ∈ U, (ψ x).IsInvertible := by
  have := FiniteDimensional.complete 𝕜 F₁
  obtain ⟨ψ, hψ, hψϕ⟩ := exists_continuous_section_extension 𝕜 hs hϕ
  exact ⟨ψ, hψ, hψϕ, _, hψ.isOpen_setOf_clm_bundle_isInvertible,
    fun x hx ↦ by simpa [hψϕ x hx] using hinv x hx, fun _ hx ↦ hx⟩

end Hom

end TauCeti
