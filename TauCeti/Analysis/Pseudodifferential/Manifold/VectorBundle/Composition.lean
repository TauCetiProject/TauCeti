/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Basic
import TauCeti.Analysis.Pseudodifferential.Manifold.Composition

/-!
# Composition of classical pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F`, `G` smooth complex vector bundles over `M`,
with `F` of finite rank. This file shows that the classical pseudodifferential operators between
bundles (`TauCeti.sectionClassicalPseudodifferentialOperators`) are closed under composition: if
`P : Γ(E) → Γ(F)` has order `m` and `R : Γ(F) → Γ(G)` has order `m'`, then `R ∘ P` has order
`m' + m` (`TauCeti.comp_mem_sectionClassicalPseudodifferentialOperators`). In particular the
operators of order `0` on the sections of a bundle are closed under composition, and an elliptic
operator between bundles can be checked against a candidate parametrix through `P ∘ Q` and
`Q ∘ P`.

The matrix entries of `R ∘ P` are sums of compositions of matrix entries of `R` and of `P`, as for
products of matrices; the sum runs over a frame of the intermediate bundle `F`. Fix the entry
`f ↦ χ ℓ(t'' (R (P (f ψ t⁻¹ v))))` and a compact set `K`. As `R` is properly supported, its
values on `K` only see its input near a compact set `K'`. Over a compact neighbourhood `L` of
`K'`, finitely many trivializations `tᵢ` of `F`, a partition of unity `ρᵢ` and cutoffs `ψᵢ`
write every section `h` of `F` as `∑ᵢ ∑ⱼ (ρᵢ bⱼ*(tᵢ h)) ψᵢ tᵢ⁻¹ bⱼ` for a basis `(bⱼ)` of the
model fibre (`IsCompact.exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply`). Applying
this to `h = P (f ψ t⁻¹ v)` shows that on `K` the entry of `R ∘ P` agrees with

`∑ᵢ ∑ⱼ (f ↦ χ ℓ(t'' (R (f ψᵢ tᵢ⁻¹ bⱼ)))) ∘ (f ↦ ρᵢ bⱼ*(tᵢ (P (f ψ t⁻¹ v)))),`

a finite sum of compositions of entries of `R` and of `P`. These are classical pseudodifferential
operators of order `m' + m` on `M` (`TauCeti.comp_mem_classicalPseudodifferentialOperators`), and
an operator which agrees on every compact set with one of order `m' + m` has that order
(`TauCeti.mem_classicalPseudodifferentialOperators_of_forall_isCompact`).

## Main results

* `TauCeti.comp_mem_sectionClassicalPseudodifferentialOperators`: the composition of classical
  pseudodifferential operators between bundles of orders `m'` and `m` has order `m' + m`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators between sections of vector bundles and their composition).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

open Bundle Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
  {G : M → Type*} [TopologicalSpace (TotalSpace U G)] [∀ x, AddCommGroup (G x)]
  [∀ x, Module ℝ (G x)] [∀ x, Module ℂ (G x)] [∀ x, TopologicalSpace (G x)] [FiberBundle U G]
  [VectorBundle ℝ U G] [VectorBundle ℂ U G] [ContMDiffVectorBundle ∞ U G 𝓘(ℝ, CoordinateSpace n)]

/-- **Composition of classical pseudodifferential operators between bundles.** Let `E`, `F`, `G`
be smooth complex vector bundles over a manifold modelled on `ℝⁿ`, with `F` of finite rank. If
`P : Γ(E) → Γ(F)` is a classical pseudodifferential operator of order `m` and `R : Γ(F) → Γ(G)`
one of order `m'`, then `R ∘ P` is a classical pseudodifferential operator of order `m' + m`. -/
theorem comp_mem_sectionClassicalPseudodifferentialOperators [FiniteDimensional ℂ W] {m m' : ℝ}
    {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    {R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); U, G⟯}
    (hR : R ∈ sectionClassicalPseudodifferentialOperators m')
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) :
    R ∘ₗ P ∈ sectionClassicalPseudodifferentialOperators (m' + m) := by
  have := ChartedSpace.locallyCompactSpace (CoordinateSpace n) M
  rw [mem_sectionClassicalPseudodifferentialOperators_iff] at hR hP ⊢
  have hRP := hR.1.comp hP.1
  refine ⟨hRP, fun t _ ψ hψ v t'' _ χ hχ ℓ ↦
    mem_classicalPseudodifferentialOperators_of_forall_isCompact (hRP.sectionEntry ..)
      fun K hK ↦ ?_⟩
  -- On `K`, `R` only sees its input near `K'`, inside the interior of a compact set `L` over which
  -- the sections of `F` split in finitely many cut-off frames.
  obtain ⟨K', hK', -, hR₂⟩ := isSectionProperlySupported_iff.1 hR.1 K hK
  obtain ⟨L, hL, hK'L⟩ := exists_compact_superset hK'
  set b := Module.finBasis ℂ W
  obtain ⟨ι, _, c, ρ, ψ', hρ, hψ', hsum⟩ :=
    hL.exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply (I := 𝓘(ℝ, CoordinateSpace n))
      (F := F) b
  refine ⟨∑ i, ∑ j, sectionEntry (trivializationAt W F (c i)) (ψ' i) (hψ' i) (b j) t'' χ hχ ℓ R ∘ₗ
      sectionEntry t ψ hψ v (trivializationAt W F (c i)) (ρ i) (hρ i)
        (b.coord j).toContinuousLinearMap P,
    sum_mem fun i _ ↦ sum_mem fun j _ ↦ comp_mem_classicalPseudodifferentialOperators
      (hR.2 _ _ _ _ _ _ _ _) (hP.2 _ _ _ _ _ _ _ _), fun f x hx ↦ ?_⟩
  set h := P (f • t.cutoffFrameSection ψ hψ v)
  set s := ∑ i, ∑ j, (trivializationAt W F (c i)).cutoffFrameCoeff (ρ i) (hρ i)
    (b.coord j).toContinuousLinearMap h •
      (trivializationAt W F (c i)).cutoffFrameSection (ψ' i) (hψ' i) (b j)
  -- `R h` agrees on `K` with `R s`, for the frame decomposition `s` of `h` over `L`.
  have hRh : R h x = R s x := by
    have h0 := hR₂ (h - s) (Filter.mem_of_superset (isOpen_interior.mem_nhdsSet.2 hK'L)
      fun y hy ↦ by rw [mem_ofPred_eq, ContMDiffSection.coe_sub, Pi.sub_apply,
        hsum h y (interior_subset hy), sub_self]) x hx
    rwa [map_sub, ContMDiffSection.coe_sub, Pi.sub_apply, sub_eq_zero] at h0
  have hentry (i : ι) (j) : sectionEntry t ψ hψ v (trivializationAt W F (c i)) (ρ i) (hρ i)
      (b.coord j).toContinuousLinearMap P f = (trivializationAt W F (c i)).cutoffFrameCoeff (ρ i)
        (hρ i) (b.coord j).toContinuousLinearMap h := by
    ext y
    simp [h]
  rw [sectionEntry_apply, LinearMap.comp_apply, hRh]
  simp [hentry, s, Finset.mul_sum]

end TauCeti
