/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.IsManifold.MaximalAtlas

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

Conversely, on a compact manifold of positive dimension every classical pseudodifferential
operator is a finite sum of chart quantizations, exactly and not only modulo an operator of order
`-∞` as in `TauCeti.exists_sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`. For
a partition of unity `ρₓ` subordinate to charts and, for each `x`, a partition of unity `σₓᵢ` of
`M`, every operator is `P = ∑ₓ ∑ᵢ ρₓ P σₓᵢ`. The supports of `ρₓ` and `σₓᵢ` may be far apart, but
the maximal atlas contains a chart whose source contains both, with disjoint images in `ℝⁿ`
(`IsCompact.exists_smoothPartition_mem_maximalAtlas_eqOn_symm`). In that chart `ρₓ P σₓᵢ` is the
chart quantization of the symbol of a chart compression of `P`
(`OpenPartialHomeomorph.chartQuantization_eq_mulLeft_comp_comp_mulLeft`). So the classical
pseudodifferential operators of order `m` on a compact manifold are the span of the chart
quantizations of classical symbols of order `m`, and a property of operators that is preserved
by finite sums holds for all of them once it holds for chart quantizations. This fails in
dimension `0`, where a chart sees a single point.

## Main results

* `TauCeti.patchedQuantization`: the **patched quantization** `∑ᵢ φᵢ Op(aᵢ) ψᵢ` of classical
  symbols `aᵢ` in charts `eᵢ`, for cutoffs whose supports form a locally finite family on `M`.
* `TauCeti.patchedQuantization_mem_classicalPseudodifferentialOperators`: the patched quantization
  of classical symbols of order `m` is a classical pseudodifferential operator of order `m`.
* `TauCeti.exists_forall_eq_sum_mulLeft_comp_comp_mulLeft`: on a compact manifold of positive
  dimension, finitely many pairs of cutoffs `φᵢ`, `ψᵢ`, each pair in one chart, split every
  operator as `P = ∑ᵢ φᵢ P ψᵢ`.
* `TauCeti.exists_eq_sum_chartQuantization`: on a compact manifold of positive dimension, every
  classical pseudodifferential operator of order `m` is a finite sum of chart quantizations of
  classical symbols of order `m`.
* `TauCeti.classicalPseudodifferentialOperators_eq_span_chartQuantization`: there, the classical
  pseudodifferential operators of order `m` are the span of the chart quantizations.

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

/-! ### Operators on a compact manifold are finite sums of chart quantizations -/

section Compact

variable [CompactSpace M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [NeZero n]

/-- **Splitting `ρ P` along cutoffs in common charts.** Let `ρ` be a cutoff in a chart `e` of a
compact manifold modelled on `ℝⁿ`, `n ≠ 0`. There are finitely many charts `Eᵢ` of the maximal atlas
and cutoffs `φᵢ`, `ψᵢ` in their targets such that every complex-linear operator `P` on the
complex-valued smooth functions on `M` satisfies `ρ P = ∑ᵢ φᵢ P ψᵢ`, with the cutoffs read on `M`
through the charts. -/
private theorem exists_forall_mulLeft_comp_eq_sum_mulLeft_comp_comp_mulLeft
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (ρ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ (k : ℕ) (E : Fin k → OpenPartialHomeomorph M (CoordinateSpace n))
      (hE : ∀ i, E i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (φ ψ : ∀ i, 𝓓(⟨(E i).target, (E i).open_target⟩, ℝ)),
      ∀ P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
          C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        LinearMap.mulLeft ℂ (e.complexCutoffPullback he ρ 1) ∘ₗ P =
          ∑ i, LinearMap.mulLeft ℂ ((E i).complexCutoffPullback (hE i) (φ i) 1) ∘ₗ P ∘ₗ
            LinearMap.mulLeft ℂ ((E i).complexCutoffPullback (hE i) (ψ i) 1) := by
  -- A partition of unity `σᵢ` of `M` whose pieces lie in charts `Eᵢ` agreeing with `e` over the
  -- support of `ρ`; each `σᵢ` is the pullback of a cutoff `τᵢ` in `Eᵢ`.
  obtain ⟨ι, _, σ, E, hσ, hE⟩ := isCompact_univ.exists_smoothPartition_mem_maximalAtlas_eqOn_symm
    he ρ.hasCompactSupport.isCompact ρ.tsupport_subset
  choose hEa hσc hσE hρE hEq using hE
  choose τ hτ using fun i ↦ OpenPartialHomeomorph.exists_cutoffPullback_one_eq (hEa i) (hσc i)
    (hσE i)
  let eqv := Fintype.equivFin ι
  -- The cutoff `ρ`, read in the chart `Eᵢ`, has the same pullback to `M` as in `e`.
  let ρ' (i : ι) : 𝓓(⟨(E i).target, (E i).open_target⟩, ℝ) :=
    ⟨ρ, ρ.contDiff, ρ.hasCompactSupport, hρE i⟩
  refine ⟨Fintype.card ι, fun j ↦ E (eqv.symm j), fun j ↦ hEa (eqv.symm j),
    fun j ↦ ρ' (eqv.symm j), fun j ↦ τ (eqv.symm j), fun P ↦ ?_⟩
  rw [Fintype.sum_equiv eqv.symm _
    (fun i ↦ LinearMap.mulLeft ℂ ((E i).complexCutoffPullback (hEa i) (ρ' i) 1) ∘ₗ P ∘ₗ
      LinearMap.mulLeft ℂ ((E i).complexCutoffPullback (hEa i) (τ i) 1)) fun _ ↦ rfl]
  have hρ' (i : ι) : (E i).complexCutoffPullback (hEa i) (ρ' i) = e.complexCutoffPullback he ρ :=
    (e.complexCutoffPullback_congr he (hEa i) (ψ' := ρ' i) rfl (hEq i).symm).symm
  -- `ρ P u = ∑ᵢ ρ P (σᵢ u)`, since `∑ᵢ σᵢ = 1`.
  ext u p
  have hσ1 : ∑ i, (E i).complexCutoffPullback (hEa i) (τ i) 1 * u = u := by
    ext q
    simp [← Finset.sum_mul, OpenPartialHomeomorph.complexCutoffPullback_one_apply, hτ,
      ← Complex.ofReal_sum, hσ q (mem_univ q)]
  simp only [hρ', LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.sum_apply,
    ← Finset.mul_sum, ← map_sum, hσ1]

/-- **Splitting operators along pairs of cutoffs in common charts.** On a compact manifold modelled
on `ℝⁿ` with `n ≠ 0`, there are finitely many charts `eᵢ` of the maximal atlas and cutoffs `φᵢ`,
`ψᵢ` with compact supports in their targets such that every complex-linear operator `P` on the
complex-valued smooth functions on `M` is `∑ᵢ φᵢ P ψᵢ`, with the cutoffs read on `M` through the
charts. The supports of `φᵢ` and `ψᵢ` may be far apart on `M`: the maximal atlas contains charts
whose source has two components with disjoint images in `ℝⁿ`. -/
theorem exists_forall_eq_sum_mulLeft_comp_comp_mulLeft :
    ∃ (k : ℕ) (e : Fin k → OpenPartialHomeomorph M (CoordinateSpace n))
      (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (φ ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)),
      ∀ P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
          C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯,
        P = ∑ i, LinearMap.mulLeft ℂ ((e i).complexCutoffPullback (he i) (φ i) 1) ∘ₗ P ∘ₗ
          LinearMap.mulLeft ℂ ((e i).complexCutoffPullback (he i) (ψ i) 1) := by
  -- A smooth partition of unity `fₓ` subordinate to the chart sources; on the compact space `M`
  -- only the finitely many `x ∈ s` have `fₓ ≠ 0`. Each `fₓ` is the pullback of a cutoff `ρₓ` in
  -- the chart at `x`, and `ρₓ P` splits along cutoffs in common charts.
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, CoordinateSpace n) M
  have hs := f.locallyFinite.finite_nonempty_of_compact
  choose ρ hρ using fun x ↦ OpenPartialHomeomorph.exists_cutoffPullback_one_eq
    (IsManifold.chart_mem_maximalAtlas x) (isCompact_univ.of_isClosed_subset (isClosed_tsupport _)
      (subset_univ _)) (hf x)
  choose k E hE φ ψ hP using fun x ↦ exists_forall_mulLeft_comp_eq_sum_mulLeft_comp_comp_mulLeft
    (IsManifold.chart_mem_maximalAtlas x) (ρ x)
  -- The pairs `(x, i)` with `x ∈ s`, enumerated by `Fin k`.
  let eqv := Fintype.equivFin (Σ x : hs.toFinset, Fin (k x))
  refine ⟨_, fun j ↦ E _ (eqv.symm j).2, fun j ↦ hE _ (eqv.symm j).2, fun j ↦ φ _ (eqv.symm j).2,
    fun j ↦ ψ _ (eqv.symm j).2, fun P ↦ ?_⟩
  rw [Fintype.sum_equiv eqv.symm _
    (fun p ↦ LinearMap.mulLeft ℂ ((E p.1.val p.2).complexCutoffPullback (hE p.1.val p.2)
      (φ p.1.val p.2) 1) ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ ((E p.1.val p.2).complexCutoffPullback
        (hE p.1.val p.2) (ψ p.1.val p.2) 1)) fun _ ↦ rfl, Fintype.sum_sigma]
  simp only [← hP, Finset.sum_coe_sort hs.toFinset fun x ↦
    LinearMap.mulLeft ℂ ((chartAt (CoordinateSpace n) x).complexCutoffPullback
      (IsManifold.chart_mem_maximalAtlas x) (ρ x) 1) ∘ₗ P]
  -- `P u = ∑ₓ fₓ P u`, since `∑ₓ fₓ = 1`.
  ext u p
  have hf1 : ∑ x ∈ hs.toFinset, f x p = 1 :=
    f.sum_finsupport' p (mem_univ p) fun x hx ↦ hs.mem_toFinset.2 ⟨p, (f.mem_finsupport p).1 hx⟩
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
    ContMDiffMap.coe_sum, ContMDiffMap.coe_mul, Finset.sum_apply, Pi.mul_apply,
    OpenPartialHomeomorph.complexCutoffPullback_one_apply, hρ]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hf1, Complex.ofReal_one, one_mul]

variable {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
  C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-- **On a compact manifold, a classical pseudodifferential operator is a finite sum of chart
quantizations.** If `M` is compact and modelled on `ℝⁿ` with `n ≠ 0`, every classical
pseudodifferential operator `P` of order `m` is exactly `∑ᵢ Op_{eᵢ}(aᵢ)` for finitely many charts
`eᵢ` of the maximal atlas, cutoffs `φᵢ`, `ψᵢ` in their targets and classical symbols `aᵢ` of order
`m`, with no remainder of order `-∞`. -/
theorem exists_eq_sum_chartQuantization (hP : P ∈ classicalPseudodifferentialOperators m) :
    ∃ (k : ℕ) (e : Fin k → OpenPartialHomeomorph M (CoordinateSpace n))
      (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (φ ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)) (a : Fin k → ClassicalSymbol n ℂ ℂ m),
      P = ∑ i, (e i).chartQuantization (he i) (φ i) (ψ i) (a i) := by
  obtain ⟨k, e, he, φ, ψ, hP'⟩ := exists_forall_eq_sum_mulLeft_comp_comp_mulLeft (n := n) (M := M)
  -- Each piece `φᵢ P ψᵢ` is the chart quantization of the symbol of the compression of `P` by `φᵢ`
  -- and `ψᵢ`, localized by cutoffs equal to `1` on their supports.
  choose a ha using fun i ↦ (mem_classicalPseudodifferentialOperators_iff.1 hP).2 (e i) (he i)
    (φ i) (ψ i)
  choose φ₁ hφ₁ using fun i ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (φ i).hasCompactSupport.isCompact (φ i).tsupport_subset
  choose ψ₁ hψ₁ using fun i ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (ψ i).hasCompactSupport.isCompact (ψ i).tsupport_subset
  refine ⟨k, e, he, φ₁, ψ₁, a, ?_⟩
  rw [Finset.sum_congr rfl fun i _ ↦ (e i).chartQuantization_eq_mulLeft_comp_comp_mulLeft (he i)
    (ha i) (fun y hy ↦ (hφ₁ i).1.self_of_nhdsSet y hy)
    (fun y hy ↦ (hψ₁ i).1.self_of_nhdsSet y hy)]
  exact hP' P

variable (n M m) in
/-- **The classical pseudodifferential operators on a compact manifold are spanned by chart
quantizations.** If `M` is compact and modelled on `ℝⁿ` with `n ≠ 0`, the classical
pseudodifferential operators of order `m` are the complex span of the chart quantizations
`Op_e(a)` of classical symbols `a` of order `m`, over all charts `e` of the maximal atlas and all
cutoffs in their targets.

In dimension `0` this fails as soon as `M` has two points: a chart then has a single point in its
source, so chart quantizations only multiply each value of a function by a constant, while every
operator, such as the exchange of the two values, is a classical pseudodifferential operator
(`TauCeti.mem_classicalPseudodifferentialOperators_of_dim_eq_zero`). -/
theorem classicalPseudodifferentialOperators_eq_span_chartQuantization :
    classicalPseudodifferentialOperators (M := M) m = Submodule.span ℂ
      {Q | ∃ (e : OpenPartialHomeomorph M (CoordinateSpace n))
        (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
        (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m),
        e.chartQuantization he φ ψ a = Q} := by
  refine le_antisymm (fun P hP ↦ ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨k, e, he, φ, ψ, a, rfl⟩ := exists_eq_sum_chartQuantization hP
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span ⟨e i, he i, φ i, ψ i, a i, rfl⟩
  · rintro _ ⟨e, he, φ, ψ, a, rfl⟩
    exact e.chartQuantization_mem_classicalPseudodifferentialOperators he φ ψ a

end Compact

end TauCeti
