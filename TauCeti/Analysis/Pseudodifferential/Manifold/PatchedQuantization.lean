/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol

/-!
# Patched quantization on a manifold

Locally finite sums of chart quantizations are how pseudodifferential operators on a manifold are
built from local symbols (Hörmander III, §18.1; Melrose, §5.3): with a locally finite atlas, a
partition of unity `φᵢ` and cutoffs `ψᵢ` equal to `1` near the supports of the `φᵢ`, the operator
`∑ᵢ φᵢ Op(aᵢ) ψᵢ` is the patched quantization of the local symbols `aᵢ`. Each summand is a
classical pseudodifferential operator
(`OpenPartialHomeomorph.chartQuantization_mem_classicalPseudodifferentialOperators`), and a
locally finite sum of such operators is one too
(`TauCeti.locallyFiniteSum_mem_classicalPseudodifferentialOperators`); this file shows that the
patched quantization is one.

## Main results

* `TauCeti.patchedQuantization`: the **patched quantization** `∑ᵢ φᵢ Op(aᵢ) ψᵢ` of classical
  symbols `aᵢ` in charts `eᵢ`, for cutoffs whose supports form a locally finite family on `M`.
* `TauCeti.patchedQuantization_mem_classicalPseudodifferentialOperators`: the patched quantization
  of classical symbols of order `m` is a classical pseudodifferential operator of order `m`.
* `TauCeti.classicalPrincipalSymbol_patchedQuantization`: its principal symbol is the locally
  finite sum of the principal symbols of the chart quantizations, which
  `OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization` computes.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem
  18.1.17 and Definition 18.1.20.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Filter Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {m : ℝ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {ι : Type*}

/-! ### Patched quantization -/

variable {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (φ ψ : (i : ι) → 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)) (a : ι → ClassicalSymbol n ℂ ℂ m)

/-- The **patched quantization** `f ↦ ∑ᵢ (φᵢ · Op(aᵢ) (ψᵢ · (f ∘ eᵢ⁻¹))) ∘ eᵢ` of classical symbols
`aᵢ` in charts `eᵢ` of the maximal atlas, with cutoffs `φᵢ`, `ψᵢ` with compact supports in the
chart targets whose chart preimages `eᵢ⁻¹(supp φᵢ ∪ supp ψᵢ)` form a locally finite family: the
locally finite sum of the chart quantizations (`OpenPartialHomeomorph.chartQuantization`). -/
def patchedQuantization
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i))) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ContMDiffMap.locallyFiniteSum (fun i ↦ (e i).chartQuantization (he i) (φ i) (ψ i) (a i)) fun f ↦
    hS.subset fun i ↦ (subset_tsupport _).trans
      (((e i).tsupport_chartQuantization_subset (he i) _ _ _ f).trans
        (image_mono subset_union_left))

/-- The patched quantization is evaluated pointwise as the locally finite sum of the chart
quantizations. -/
@[simp]
theorem patchedQuantization_apply
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i)))
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    patchedQuantization he φ ψ a hS f x =
      ∑ᶠ i, (e i).chartQuantization (he i) (φ i) (ψ i) (a i) f x :=
  ContMDiffMap.locallyFiniteSum_apply f x

/-- **Patched quantization.** For charts `eᵢ` of the maximal atlas, classical symbols `aᵢ` of order
`m` and cutoffs `φᵢ`, `ψᵢ` with compact supports in the chart targets, such that the chart preimages
`eᵢ⁻¹(supp φᵢ ∪ supp ψᵢ)` form a locally finite family, the patched quantization
`f ↦ ∑ᵢ (φᵢ · Op(aᵢ) (ψᵢ · (f ∘ eᵢ⁻¹))) ∘ eᵢ` is a classical pseudodifferential operator of order
`m` on `M`. -/
theorem patchedQuantization_mem_classicalPseudodifferentialOperators
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i))) :
    patchedQuantization he φ ψ a hS ∈ classicalPseudodifferentialOperators m :=
  locallyFiniteSum_mem_classicalPseudodifferentialOperators hS
    (fun i ↦ image_union (e i).symm _ _ ▸
      ((e i).isCompact_symm_image_tsupport (φ i)).union ((e i).isCompact_symm_image_tsupport (ψ i)))
    (fun i ↦
      (e i).chartQuantization_mem_classicalPseudodifferentialOperators (he i) (φ i) (ψ i) (a i))
    (fun i f ↦ ((e i).tsupport_chartQuantization_subset (he i) _ _ _ f).trans
      (image_mono subset_union_left))
    fun i _ hf ↦ (e i).chartQuantization_eq_zero (he i) _ _ _ fun p hp ↦
      hf.self_of_nhdsSet p (image_mono subset_union_right hp)

/-- **The principal symbol of a patched quantization** is the locally finite sum of the principal
symbols of its chart quantizations `φᵢ Op(aᵢ) ψᵢ`. -/
theorem classicalPrincipalSymbol_patchedQuantization [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i))) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (patchedQuantization he φ ψ a hS) x ξ =
      ∑ᶠ i, classicalPrincipalSymbol m ((e i).chartQuantization (he i) (φ i) (ψ i) (a i)) x ξ :=
  classicalPrincipalSymbol_locallyFiniteSum hS
    (fun i f ↦ ((e i).tsupport_chartQuantization_subset (he i) _ _ _ f).trans
      (image_mono subset_union_left))
    (fun i ↦
      (e i).chartQuantization_mem_classicalPseudodifferentialOperators (he i) (φ i) (ψ i) (a i))
    (patchedQuantization_mem_classicalPseudodifferentialOperators he φ ψ a hS) x ξ

end TauCeti
