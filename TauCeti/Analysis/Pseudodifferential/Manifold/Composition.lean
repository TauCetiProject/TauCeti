/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Basic
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Pseudodifferential.Composition.Classical
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Geometry.Manifold.IsManifold.MaximalAtlas
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Composition of classical pseudodifferential operators on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. This file shows that the classical pseudodifferential
operators on `M` (`TauCeti.classicalPseudodifferentialOperators`) are closed under composition: if
`P` has order `m'` and `Q` has order `m`, then `P ∘ Q` has order `m' + m`
(`TauCeti.comp_mem_classicalPseudodifferentialOperators`). In particular the operators of order
`0` are closed under composition. Composition is what parametrices on a manifold need: a
parametrix `Q` of an elliptic `P` is checked through the compositions `P ∘ Q` and `Q ∘ P`.

## The argument

Fix a chart `e` and cutoffs `φ`, `ψ` in its target. The operator `Q` is properly supported, so it
sends the functions supported in `e⁻¹(supp ψ)` to functions supported in a compact set `K'`, which
need not lie in the source of `e`. A partition of unity `ρᵢ` on `K'` splits the compression of
`P ∘ Q` into the compressions of `P ∘ (ρᵢ Q)`. Each `ρᵢ` is supported in the source of a chart `Eᵢ`
that agrees with `e` over the supports of `φ` and `ψ`: either `e` itself, or, when the support of
`ρᵢ` leaves the source of `e`, a chart made of a neighbourhood of `e⁻¹(supp φ ∪ supp ψ)` read
through `e` and a neighbourhood of the support of `ρᵢ`, with disjoint images in `ℝⁿ`
(`OpenPartialHomeomorph.exists_mem_maximalAtlas_eqOn_symm`). Such a chart exists in
positive dimension because the maximal atlas contains every chart, not only those of a fixed
atlas.

In the chart `Eᵢ`, with a cutoff `χᵢ` equal to `1` on the image of the support of `ρᵢ`, the
compression of `P ∘ (ρᵢ Q)` is the compression of `P` by `φ` and `χᵢ` after that of `ρᵢ Q` by `χᵢ`
and `ψ` (`OpenPartialHomeomorph.complexChartCompression_comp_apply`). These are `Op(aᵢ)` and
`Op(bᵢ)` for classical symbols of orders `m'` and `m`, and `bᵢ` vanishes at positions outside the
support of `χᵢ`. So their composition is `Op(aᵢ # bᵢ)`, with `aᵢ # bᵢ` classical of order `m' + m`
(`TauCeti.ClassicalSymbol.sharp`), and the compression of `P ∘ Q` is the quantization of
`∑ᵢ aᵢ # bᵢ`. No smoothing remainder has to be estimated separately: the parts of `P ∘ Q` between
distant points are part of the compressions in the charts `Eᵢ`.

In dimension `0` every properly supported operator has every order
(`TauCeti.mem_classicalPseudodifferentialOperators_of_eq_zero`), so only proper support has to be
checked (`TauCeti.IsProperlySupported.comp`).

## Main results

* `TauCeti.comp_mem_classicalPseudodifferentialOperators`: the composition of classical
  pseudodifferential operators of orders `m'` and `m` is classical of order `m' + m`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.8
  and the discussion after Definition 18.1.20.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Filter Set
open scoped ContDiff Manifold Distributions SchwartzMap Topology

universe u

namespace TauCeti

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **Charts for a partition of unity.** Let `e` be a chart, `C` a compact subset of its target and
`K` a compact subset of `M`. In positive dimension there are finitely many smooth functions `ρᵢ`
adding up to `1` on `K`, with compact supports, and charts `Eᵢ` containing the support of `ρᵢ` in
their sources and `C` in their targets, with the same inverse as `e` on `C`. Where the support of
`ρᵢ` leaves the source of `e`, the chart `Eᵢ` is made of a neighbourhood of `e⁻¹(C)` read through
`e` and a neighbourhood of the support of `ρᵢ`, with disjoint images. -/
private theorem exists_chart_partition [NeZero n] {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) {C : Set (CoordinateSpace n)}
    (hC : IsCompact C) (hCe : C ⊆ e.target) {K : Set M} (hK : IsCompact K) :
    ∃ (ι : Type u) (_ : Fintype ι) (ρ : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
      (E : ι → OpenPartialHomeomorph M (CoordinateSpace n)), (∀ x ∈ K, ∑ i, ρ i x = 1) ∧
      ∀ i, E i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M ∧
        IsCompact (tsupport (ρ i)) ∧ tsupport (ρ i) ⊆ (E i).source ∧ C ⊆ (E i).target ∧
          EqOn (E i).symm e.symm C := by
  classical
  -- A bounded open neighbourhood `W` of `C` and the compact set `L = e⁻¹(closure W)`.
  obtain ⟨W, hWo, hCW, hWe, hWc⟩ := exists_open_between_and_isCompact_closure hC e.open_target hCe
  set L := e.symm '' closure W
  have hLc : IsCompact L := hWc.image_of_continuousOn (e.continuousOn_symm.mono hWe)
  have hLe : L ⊆ e.source := image_subset_iff.2 fun y hy ↦ e.map_target (hWe hy)
  -- A finite smooth bump covering of `K` whose bumps lie in `e.source`, or away from `L`.
  obtain ⟨ι, _, f, hf⟩ := hK.exists_smoothBumpCovering_isSubordinate 𝓘(ℝ, CoordinateSpace n)
    (U := fun x ↦ if x ∈ e.source then e.source else Lᶜ) fun x _ ↦ by
      split_ifs with hx
      · exact e.open_source.mem_nhds hx
      · exact hLc.isClosed.isOpen_compl.mem_nhds fun hxL ↦ hx (hLe hxL)
  have hchart : ∀ i, ∃ E ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M,
      tsupport (f i) ⊆ E.source ∧ C ⊆ E.target ∧ EqOn E.symm e.symm C := by
    intro i
    by_cases hc : f.c i ∈ e.source
    · exact ⟨e, he, by simpa [hc] using hf i, hCe, eqOn_refl _ _⟩
    obtain ⟨E, hE, hfE, hWE, hEe⟩ := OpenPartialHomeomorph.exists_mem_maximalAtlas_eqOn_symm he
      (IsManifold.chart_mem_maximalAtlas (f.c i)) hWo hWe hWc (f i).hasCompactSupport.isCompact
      (f i).tsupport_subset_chartAt_source
      (subset_compl_iff_disjoint_right.1 (by simpa [hc] using hf i))
    exact ⟨E, hE, hfE, hCW.trans hWE, hEe.mono hCW⟩
  choose E hE hfE hCE hEe using hchart
  have hρ (i) : tsupport (f.toSmoothPartitionOfUnity i) ⊆ tsupport (f i) :=
    closure_mono (f.support_toSmoothPartitionOfUnity_subset i)
  refine ⟨ι, inferInstance, fun i ↦ f.toSmoothPartitionOfUnity i, E, fun x hx ↦ ?_, fun i ↦
    ⟨hE i, (f i).hasCompactSupport.isCompact.of_isClosed_subset (isClosed_tsupport _) (hρ i),
      (hρ i).trans (hfE i), hCE i, hEe i⟩⟩
  rw [← finsum_eq_sum_of_fintype]
  exact f.toSmoothPartitionOfUnity.sum_eq_one hx

variable {P Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
  C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m m' : ℝ}

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **One piece of the composition.** Let `ρ` be a smooth function with compact support in the
source of a chart `E` that agrees with the chart `e` over the supports of the cutoffs `φ` and `ψ`.
Then the compression of `P ∘ (ρ Q)` by `φ` and `ψ` in `e` is `Op(a # b)`, where `a` and `b` are the
symbols of the compressions of `P` and of `ρ Q` in `E`, through a cutoff `χ` equal to `1` on the
image of the support of `ρ`. -/
private theorem exists_quantizeSchwartzValue_eq_complexChartCompression_comp_mulLeft
    (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m)
    {e E : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (hE : E ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) {ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯}
    (hρc : IsCompact (tsupport ρ)) (hρE : tsupport ρ ⊆ E.source)
    (hCE : tsupport φ ∪ tsupport ψ ⊆ E.target)
    (hEe : EqOn E.symm e.symm (tsupport φ ∪ tsupport ψ)) :
    ∃ c : ClassicalSymbol n ℂ ℂ (m' + m), ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
      quantizeSchwartzValue c.toSymbol.coefficient u x =
        e.complexChartCompression he φ ψ
          (P ∘ₗ LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ρ) ∘ₗ Q)
          (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  set Qρ := LinearMap.mulLeft ℂ (ContMDiffMap.ofReal ρ) ∘ₗ Q with hQρ
  -- The cutoffs `φ` and `ψ` read in the chart `E`, and a cutoff `χ` equal to `1` on the image of
  -- the support of `ρ`.
  let φ' : 𝓓(⟨E.target, E.open_target⟩, ℝ) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, subset_union_left.trans hCE⟩
  let ψ' : 𝓓(⟨E.target, E.open_target⟩, ℝ) :=
    ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_union_right.trans hCE⟩
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    (Ω := ⟨E.target, E.open_target⟩) (hρc.image_of_continuousOn (E.continuousOn.mono hρE))
    (image_subset_iff.2 fun x hx ↦ E.map_source (hρE hx))
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 E hE φ' χ
  obtain ⟨b, hb⟩ := (mem_classicalPseudodifferentialOperators_iff.1
    (mulLeft_comp_mem_classicalPseudodifferentialOperators hQ (ContMDiffMap.ofReal ρ))).2 E hE χ ψ'
  -- The symbol of the compression of `ρ Q` vanishes off the support of `χ`.
  have hbs : b.toSymbol.HasCompactSpatialSupport :=
    Symbol.hasCompactSpatialSupport_iff_exists_tsupport_quantizeSchwartzValue_subset.2
      ⟨tsupport χ, χ.hasCompactSupport.isCompact, fun u _ ↦ closure_mono <|
        Function.support_subset_iff'.2 fun y hy ↦ by
          rw [hb u y, OpenPartialHomeomorph.complexChartCompression_apply,
            Function.notMem_support.1 hy, zero_smul]⟩
  refine ⟨a.sharp b hbs, fun u x ↦ ?_⟩
  set U := ContMDiffMap.ofContDiff u (u.smooth ⊤)
  -- The outputs of `ρ Q` lie in the source of `E`, at points where `χ ∘ E = 1`.
  have hfactor : ∀ y, Qρ (E.complexCutoffPullback hE ψ' U) y ≠ 0 →
      y ∈ E.source ∧ χ (E y) = 1 := fun y hy ↦ by
    have hρy : ρ y ≠ 0 := fun h ↦ hy (by simp [hQρ, h])
    exact ⟨hρE (subset_tsupport _ hρy),
      hχ.self_of_nhdsSet _ (mem_image_of_mem _ (subset_tsupport _ hρy))⟩
  set w := (hbs.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
    (b.toSymbol.contDiff_quantizeSchwartzValue u)
  have hw : ContMDiffMap.ofContDiff w (w.smooth ⊤) = E.complexChartCompression hE χ ψ' Qρ U := by
    ext y
    rw [ContMDiffMap.coe_ofContDiff, HasCompactSupport.toSchwartzMap_toFun, hb u y]
  rw [ClassicalSymbol.toSymbol_sharp, Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue,
    ha, hw, ← OpenPartialHomeomorph.complexChartCompression_comp_apply _ _ _ _ _ _ hfactor,
    ← OpenPartialHomeomorph.complexChartCompression_congr he hE rfl rfl hEe.symm]

/-- **Composition of classical pseudodifferential operators.** If `P` is a classical
pseudodifferential operator of order `m'` and `Q` one of order `m` on a manifold modelled on `ℝⁿ`,
then `P ∘ Q` is a classical pseudodifferential operator of order `m' + m`. -/
theorem comp_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m')
    (hQ : Q ∈ classicalPseudodifferentialOperators m) :
    P ∘ₗ Q ∈ classicalPseudodifferentialOperators (m' + m) := by
  have hPQ := (mem_classicalPseudodifferentialOperators_iff.1 hP).1.comp
    (mem_classicalPseudodifferentialOperators_iff.1 hQ).1
  rcases eq_or_ne n 0 with hn | hn
  · exact mem_classicalPseudodifferentialOperators_of_eq_zero hn hPQ _
  have : NeZero n := ⟨hn⟩
  refine mem_classicalPseudodifferentialOperators_iff.2 ⟨hPQ, fun e he φ ψ ↦ ?_⟩
  -- `Q` sends the functions supported in `e⁻¹(supp ψ)` to functions supported in `K'`, and a
  -- partition of unity `ρᵢ` on `K'` splits `Q` there into pieces `ρᵢ Q`, each seen in a chart `Eᵢ`
  -- that agrees with `e` over the supports of `φ` and `ψ`.
  obtain ⟨K', hK', hQK', -⟩ :=
    isProperlySupported_iff.1 (mem_classicalPseudodifferentialOperators_iff.1 hQ).1 _
    (ψ.hasCompactSupport.isCompact.image_of_continuousOn
    (e.continuousOn_symm.mono ψ.tsupport_subset))
  obtain ⟨ι, _, ρ, E, hρ1, hE⟩ := exists_chart_partition he
    (φ.hasCompactSupport.isCompact.union ψ.hasCompactSupport.isCompact)
    (union_subset φ.tsupport_subset ψ.tsupport_subset) hK'
  choose hEa hρc hρE hCE hEe using hE
  choose c hc using fun i ↦ exists_quantizeSchwartzValue_eq_complexChartCompression_comp_mulLeft
    hP hQ he (hEa i) φ ψ (hρc i) (hρE i) (hCE i) (hEe i)
  refine ⟨∑ i, c i, fun u x ↦ ?_⟩
  set F := e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff u (u.smooth ⊤))
  -- The pieces `ρᵢ Q F` add up to `Q F`, which is supported in `K'`.
  have hsplit : Q F = ∑ i, LinearMap.mulLeft ℂ (ContMDiffMap.ofReal (ρ i)) (Q F) := by
    ext y
    simp only [ContMDiffMap.coe_sum, Finset.sum_apply, LinearMap.mulLeft_apply,
      ContMDiffMap.coe_mul, Pi.mul_apply, ContMDiffMap.ofReal_apply, ← Finset.sum_mul]
    by_cases hy : y ∈ K'
    · rw [← Complex.ofReal_sum, hρ1 y hy, Complex.ofReal_one, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hy
        (hQK' F (OpenPartialHomeomorph.tsupport_complexCutoffPullback_subset he ψ _) h), mul_zero]
  simp only [ClassicalSymbol.toSymbol_sum, Symbol.quantizeSchwartzValue_sum_left, hc,
    OpenPartialHomeomorph.complexChartCompression_apply, LinearMap.comp_apply]
  rw [← Finset.smul_sum]
  conv_rhs => rw [hsplit, map_sum, ContMDiffMap.coe_sum, Finset.sum_apply]

end TauCeti
