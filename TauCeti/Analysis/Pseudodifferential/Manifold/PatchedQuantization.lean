/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Splitting
public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing

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
`-∞` as in `TauCeti.exists_sub_patchedQuantization_mem_smoothingPseudodifferentialOperators`.
Every operator splits as `P = ∑ᵢ φᵢ P ψᵢ` for finitely many pairs of cutoffs `φᵢ`, `ψᵢ`, each pair
in one chart of the maximal atlas (`TauCeti.exists_forall_eq_sum_mulLeft_comp_comp_mulLeft`). In
that chart `φᵢ P ψᵢ` is the chart quantization of the symbol of a chart compression of `P`
(`OpenPartialHomeomorph.chartQuantization_eq_mulLeft_comp_comp_mulLeft`). So the classical
pseudodifferential operators of order `m` on a compact manifold are the span of the chart
quantizations of classical symbols of order `m`, and a property of operators that is preserved
by finite sums holds for all of them once it holds for chart quantizations. This fails in
dimension `0` as soon as `M` has two points, since a chart then sees a single point.

On any manifold, a classical pseudodifferential operator `P` is the patched quantization of its
chart symbols modulo an operator of order `-∞`
(`TauCeti.sub_patchedQuantization_mem_smoothingPseudodifferentialOperators`): for a locally finite
partition of unity `ρᵢ` in charts and cutoffs `χᵢ` equal to `1` near the supports of the `ρᵢ`, the
difference `P - ∑ᵢ ρᵢ P χᵢ` is the locally finite sum of the operators `ρᵢ P (1 - χᵢ)`, which have
order `-∞` by pseudolocality. That sum is properly supported, being the difference of two properly
supported operators, so it has order `-∞`
(`TauCeti.locallyFiniteSum_mem_classicalPseudodifferentialOperators_of_isProperlySupported`). On a
σ-compact manifold, compact or not, such charts and cutoffs exist, chosen once for all operators
(`TauCeti.exists_sub_patchedQuantization_mem_smoothingPseudodifferentialOperators`). Constructions
with symbols, such as asymptotic sums, are thereby carried out chart by chart on a noncompact
manifold, using that the patched quantization is additive in the symbols
(`TauCeti.patchedQuantization_eq_add`).

## Main results

* `TauCeti.patchedQuantization`: the **patched quantization** `∑ᵢ φᵢ Op(aᵢ) ψᵢ` of classical
  symbols `aᵢ` in charts `eᵢ`, for cutoffs whose supports form a locally finite family on `M`.
* `TauCeti.patchedQuantization_mem_classicalPseudodifferentialOperators`: the patched quantization
  of classical symbols of order `m` is a classical pseudodifferential operator of order `m`.
* `TauCeti.classicalPrincipalSymbol_patchedQuantization`: its principal symbol is the locally
  finite sum of the principal symbols of the chart quantizations, which
  `OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization` computes.
* `TauCeti.patchedQuantization_congr`, `TauCeti.patchedQuantization_eq_add`: the patched
  quantization only depends on the full symbols, additively, also across orders.
* `TauCeti.sub_patchedQuantization_mem_smoothingPseudodifferentialOperators`: a classical
  pseudodifferential operator differs from the patched quantization of its chart symbols, for a
  locally finite partition of unity in charts, by an operator of order `-∞`.
* `TauCeti.exists_sub_patchedQuantization_mem_smoothingPseudodifferentialOperators`: on a
  σ-compact manifold, every classical pseudodifferential operator of order `m` is a patched
  quantization of classical symbols of order `m` modulo an operator of order `-∞`, for charts and
  cutoffs that do not depend on the operator.
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

universe u

variable {n : ℕ} {m : ℝ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
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

/-- At each point only finitely many chart quantizations of a patched quantization are nonzero. -/
private theorem finite_support_chartQuantization_apply {m' : ℝ} (b : ι → ClassicalSymbol n ℂ ℂ m')
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i)))
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    (Function.support fun i ↦ (e i).chartQuantization (he i) (φ i) (ψ i) (b i) f x).Finite :=
  (hS.point_finite x).subset fun i hi ↦ image_mono subset_union_left
    ((e i).tsupport_chartQuantization_subset (he i) _ _ _ f (subset_tsupport _ hi))

/-- The patched quantization only depends on the full symbols, also for classical symbols of
different orders. -/
theorem patchedQuantization_congr {m' : ℝ} {b : ι → ClassicalSymbol n ℂ ℂ m'}
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i)))
    (h : ∀ i, (a i).toSymbol.coefficient = (b i).toSymbol.coefficient) :
    patchedQuantization he φ ψ a hS = patchedQuantization he φ ψ b hS := by
  ext f x
  simp only [patchedQuantization_apply, (e _).chartQuantization_congr (he _) _ _ (h _)]

/-- The patched quantization is additive in the full symbols, also for classical symbols of
different orders: if the full symbols of `aᵢ` are the sums of those of `bᵢ` and `cᵢ`, then
`∑ᵢ Op_{eᵢ}(aᵢ) = ∑ᵢ Op_{eᵢ}(bᵢ) + ∑ᵢ Op_{eᵢ}(cᵢ)`. -/
theorem patchedQuantization_eq_add {m₁ m₂ : ℝ} {b : ι → ClassicalSymbol n ℂ ℂ m₁}
    {c : ι → ClassicalSymbol n ℂ ℂ m₂}
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i)))
    (h : ∀ i,
      (a i).toSymbol.coefficient = (b i).toSymbol.coefficient + (c i).toSymbol.coefficient) :
    patchedQuantization he φ ψ a hS =
      patchedQuantization he φ ψ b hS + patchedQuantization he φ ψ c hS := by
  ext f x
  rw [LinearMap.add_apply, ContMDiffMap.coe_add, Pi.add_apply, patchedQuantization_apply,
    patchedQuantization_apply, patchedQuantization_apply,
    ← finsum_add_distrib (finite_support_chartQuantization_apply he φ ψ b hS f x)
      (finite_support_chartQuantization_apply he φ ψ c hS f x)]
  simp only [(e _).chartQuantization_eq_add (he _) _ _ (h _), LinearMap.add_apply,
    ContMDiffMap.coe_add, Pi.add_apply]

/-! ### Operators on a compact manifold are finite sums of chart quantizations -/

section Compact

variable [CompactSpace M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [NeZero n]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
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
  obtain ⟨ι, _, e, he, φ, ψ, hP'⟩ :=
    exists_forall_eq_sum_mulLeft_comp_comp_mulLeft (E := CoordinateSpace n) (M := M)
  -- Each piece `φᵢ P ψᵢ` is the chart quantization of the symbol of the compression of `P` by `φᵢ`
  -- and `ψᵢ`, localized by cutoffs equal to `1` on their supports.
  choose a ha using fun i ↦ (mem_classicalPseudodifferentialOperators_iff.1 hP).2 (e i) (he i)
    (φ i) (ψ i)
  choose φ₁ hφ₁ using fun i ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (φ i).hasCompactSupport.isCompact (φ i).tsupport_subset
  choose ψ₁ hψ₁ using fun i ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (ψ i).hasCompactSupport.isCompact (ψ i).tsupport_subset
  -- Enumerate the pieces by `Fin k`.
  let eqv := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun j ↦ e (eqv j), fun j ↦ he (eqv j), fun j ↦ φ₁ (eqv j),
    fun j ↦ ψ₁ (eqv j), fun j ↦ a (eqv j), ?_⟩
  rw [eqv.sum_comp fun i ↦ (e i).chartQuantization (he i) (φ₁ i) (ψ₁ i) (a i),
    Finset.sum_congr rfl fun i _ ↦ (e i).chartQuantization_eq_mulLeft_comp_comp_mulLeft (he i)
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

/-! ### Operators are patched quantizations modulo order `-∞` -/

section ModuloSmoothing

variable {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {ρ χ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)}

/-- **A classical pseudodifferential operator is a patched quantization modulo order `-∞`.** Let
`P` be a classical pseudodifferential operator of order `m`. Let `ρᵢ` be cutoffs in charts `eᵢ`
whose pullbacks add up to `1`, `χᵢ` cutoffs equal to `1` near the supports of the `ρᵢ`, and `aᵢ`
the symbol of the chart compression of `P` by `ρᵢ` and `χᵢ`. If `φᵢ` and `ψᵢ` are cutoffs equal to
`1` on the supports of `ρᵢ` and `χᵢ`, with locally finite chart preimages, then `P` and the patched
quantization `∑ᵢ Op_{eᵢ}(aᵢ)` differ by an operator of order `-∞`. This is the locally finite
counterpart of `TauCeti.sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`.

The difference is the locally finite sum of the operators `ρᵢ P (1 - χᵢ)`, which have order `-∞`
by pseudolocality; it is properly supported as the difference of two properly supported
operators. -/
theorem sub_patchedQuantization_mem_smoothingPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hρ : ∀ x, ∑ᶠ i, (e i).complexCutoffPullback (he i) (ρ i) 1 x = 1)
    (hχ : ∀ i, ∀ᶠ y in 𝓝ˢ (tsupport (ρ i)), χ i y = 1)
    (ha : ∀ i (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue (a i).toSymbol.coefficient u x =
        (e i).complexChartCompression (he i) (ρ i) (χ i) P
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x)
    (hφ : ∀ i, EqOn (φ i) 1 (tsupport (ρ i))) (hψ : ∀ i, EqOn (ψ i) 1 (tsupport (χ i)))
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i))) :
    P - patchedQuantization he φ ψ a hS ∈ smoothingPseudodifferentialOperators := by
  -- The operators `Tᵢ = ρᵢ P (1 - χᵢ)` have outputs supported where `φᵢ = 1`.
  set ρ' := fun i ↦ (e i).complexCutoffPullback (he i) (ρ i) 1
  set T := fun i ↦ LinearMap.mulLeft ℂ (ρ' i) ∘ₗ P ∘ₗ
    LinearMap.mulLeft ℂ (1 - (e i).complexCutoffPullback (he i) (χ i) 1)
  have hρS (i : ι) : tsupport (ρ' i) ⊆ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i)) :=
    ((e i).tsupport_complexCutoffPullback_subset (he i) _ _).trans (image_mono fun y hy ↦
      Or.inl (subset_tsupport _ (by simp [hφ i hy])))
  have hTsupp (i : ι) (f) : tsupport (T i f) ⊆ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i)) := by
    simp only [T, LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul]
    exact tsupport_mul_subset_left.trans (hρS i)
  have hT (f) : LocallyFinite fun i ↦ Function.support (T i f) :=
    hS.subset fun i ↦ (subset_tsupport _).trans (hTsupp i f)
  -- Since `∑ᵢ ρᵢ = 1` and `Op_{eᵢ}(aᵢ) = ρᵢ P χᵢ`, the difference is `∑ᵢ Tᵢ`.
  have key : P - patchedQuantization he φ ψ a hS = ContMDiffMap.locallyFiniteSum T hT := by
    ext f x
    have hfin : (Function.support fun i ↦ ρ' i x).Finite :=
      (hS.point_finite x).subset fun i hi ↦ hρS i (subset_tsupport _ hi)
    rw [LinearMap.sub_apply, ContMDiffMap.coe_sub, Pi.sub_apply, patchedQuantization_apply,
      ContMDiffMap.locallyFiniteSum_apply]
    simp only [(e _).chartQuantization_eq_mulLeft_comp_comp_mulLeft (he _) (ha _) (hφ _) (hψ _), T,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, map_sub, sub_mul, one_mul,
      ContMDiffMap.coe_mul, ContMDiffMap.coe_sub, Pi.mul_apply, Pi.sub_apply]
    rw [finsum_sub_distrib (hfin.subset (Function.support_mul_subset_left _ _))
      (hfin.subset (Function.support_mul_subset_left _ _)), ← finsum_mul, hρ x, one_mul]
  have hprop : IsProperlySupported (ContMDiffMap.locallyFiniteSum T hT) :=
    key ▸ (mem_classicalPseudodifferentialOperators_iff.1 (sub_mem hP
      (patchedQuantization_mem_classicalPseudodifferentialOperators he φ ψ a hS))).1
  rw [key]
  exact mem_smoothingPseudodifferentialOperators_iff.2 fun m' ↦
    locallyFiniteSum_mem_classicalPseudodifferentialOperators_of_isProperlySupported hS
      (fun i ↦ mem_smoothingPseudodifferentialOperators_iff.1
        (mulLeft_comp_comp_mulLeft_mem_smoothingPseudodifferentialOperators hP
          ((e i).disjoint_tsupport_complexCutoffPullback_one_sub (he i) (hχ i))) m')
      hTsupp hprop

end ModuloSmoothing

/-- **On a σ-compact manifold, classical pseudodifferential operators are patched quantizations
modulo order `-∞`.** There are points `cᵢ` and cutoffs `φᵢ`, `ψᵢ` in the preferred charts at the
`cᵢ`, whose chart preimages form a locally finite family, such that every classical
pseudodifferential operator `P` of any order `m` differs from the patched quantization
`∑ᵢ Op_{eᵢ}(aᵢ)` of classical symbols `aᵢ` of order `m` (`TauCeti.patchedQuantization`) by an
operator of order `-∞`. The charts and cutoffs do not depend on `P`. -/
theorem exists_sub_patchedQuantization_mem_smoothingPseudodifferentialOperators
    [SigmaCompactSpace M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] :
    ∃ (ι : Type u) (c : ι → M)
      (φ ψ : ∀ i, 𝓓(⟨(chartAt (CoordinateSpace n) (c i)).target,
        (chartAt (CoordinateSpace n) (c i)).open_target⟩, ℝ))
      (hS : LocallyFinite fun i ↦
        (chartAt (CoordinateSpace n) (c i)).symm '' (tsupport (φ i) ∪ tsupport (ψ i))),
      ∀ (m : ℝ) (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯),
        P ∈ classicalPseudodifferentialOperators m → ∃ a : ι → ClassicalSymbol n ℂ ℂ m,
          P - patchedQuantization (fun i ↦ IsManifold.chart_mem_maximalAtlas (c i)) φ ψ a hS ∈
            smoothingPseudodifferentialOperators := by
  -- A partition of unity `ρᵢ` in charts, inside open sets `Wᵢ` with locally finite preimages.
  obtain ⟨ι, c, ρ, W, hW, hWf, hρ⟩ :=
    exists_locallyFinite_finsum_cutoffPullback_eq_one (E := CoordinateSpace n) (M := M)
  set e := fun i ↦ chartAt (CoordinateSpace n) (c i)
  have he (i : ι) : e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (c i)
  -- Cutoffs `χᵢ = 1` near `supp ρᵢ` and `ψᵢ = 1` near `supp χᵢ`, all supported in `Wᵢ`.
  choose χ _ hχ hχW using fun i ↦ TestFunction.exists_cutoff_tsupport_subset (n := ⊤)
    (Ω := ⟨(e i).target, (e i).open_target⟩) (ρ i).hasCompactSupport.isCompact (hW i).1
    (hW i).2.1 (hW i).2.2
  choose ψ _ hψ hψW using fun i ↦ TestFunction.exists_cutoff_tsupport_subset (n := ⊤)
    (Ω := ⟨(e i).target, (e i).open_target⟩) (χ i).hasCompactSupport.isCompact (hW i).1
    (hχW i) (hW i).2.2
  have hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (χ i) ∪ tsupport (ψ i)) :=
    hWf.subset fun i ↦ image_mono (union_subset (hχW i) (hψW i))
  -- The pullbacks of the `ρᵢ`, read as complex functions, add up to `1`.
  have hρ' (x : M) : ∑ᶠ i, (e i).complexCutoffPullback (he i) (ρ i) 1 x = 1 := by
    have hfin : (Function.support fun i ↦ (e i).cutoffPullback (he i) (ρ i) 1 x).Finite :=
      (hWf.point_finite x).subset fun i hi ↦ image_mono (hW i).2.1
        ((e i).tsupport_cutoffPullback_subset (he i) _ _ (subset_tsupport _ hi))
    simp only [OpenPartialHomeomorph.complexCutoffPullback_one_apply]
    rw [← Complex.ofReal_one, ← hρ x]
    exact (map_finsum Complex.ofRealHom hfin).symm
  refine ⟨ι, c, χ, ψ, hS, fun m P hP ↦ ?_⟩
  choose a ha using fun i ↦
    (mem_classicalPseudodifferentialOperators_iff.1 hP).2 (e i) (he i) (ρ i) (χ i)
  exact ⟨a, sub_patchedQuantization_mem_smoothingPseudodifferentialOperators he χ ψ a hP hρ' hχ ha
    (fun i y hy ↦ (hχ i).self_of_nhdsSet y hy) (fun i y hy ↦ (hψ i).self_of_nhdsSet y hy) hS⟩

end TauCeti
