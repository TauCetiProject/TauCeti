/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.LocalSymbol.Elliptic
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.PrincipalSymbol
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Operator.Banach
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Elliptic pseudodifferential operators between vector bundles in charts

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F` smooth complex vector bundles over `M` with
finite-dimensional model fibres `V` and `W`. A classical pseudodifferential operator
`P : Γ(E) → Γ(F)` of order `m` (`TauCeti.sectionClassicalPseudodifferentialOperators`) has a
principal symbol `σ_m(P)(x, ξ) : E_x → F_x` (`TauCeti.sectionClassicalPrincipalSymbol`), and it is
elliptic at `x` (`TauCeti.IsSectionClassicalEllipticAt`) when `σ_m(P)(x, ξ)` is bijective at every
nonzero covector `ξ`. This file reads the principal symbol and ellipticity off the local
description of `P`.

In a chart `e` whose source lies in the base sets of trivializations `t` of `E` and `t'` of `F`,
the compression `u ↦ φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹` of `P` by cutoffs `φ`, `ψ` is the
quantization of a classical symbol `a` with values in `V →L[ℂ] W`
(`TauCeti.exists_quantizeSchwartzValue_eq_apply_chartCutoffSection`). Its principal symbol is the
principal symbol of `P` read in the frames, multiplied by the cutoffs: for `x` in the chart source
and every frequency `η`,

`a_m(e x, η) v = φ(e x) ψ(e x) t'ₓ (σ_m(P)(x, ⟪η, ·⟫ ∘ de_x) (t⁻¹ₓ v))`

(`TauCeti.coefficient_principal_apply_eq_sectionClassicalPrincipalSymbol`). This is the
transformation law of the principal symbol under changes of charts and frames
(Hörmander III, §18.1; Taylor, Lecture I, §8): the chart principal symbols of `P` are the
readings in charts and frames of one function on the cotangent bundle with values in
`Hom(E, F)`. The proof reads `a` entry by entry. Its scalar entry `ℓ ∘ a ∘ v` is the symbol of
the scalar chart compression of the matrix entry `f ↦ ρ ℓ(t' (P (f ρ t⁻¹ v)))` of `P`, for a
cutoff `ρ` equal to `1` over the supports of `φ` and `ψ`
(`Bundle.Trivialization.chartCutoffSection_postcompCLM_toSpanSingleton`). So the scalar
description `TauCeti.coefficient_principal_eq_classicalPrincipalSymbol` of chart principal
symbols and the transformation law `TauCeti.classicalPrincipalSymbol_sectionEntry` of the entries
apply.

Consequently, where `φ ψ` does not vanish, `P` is elliptic at `x` exactly when the matrix
`a_m(e x, η)` is invertible at every nonzero frequency
(`TauCeti.isSectionClassicalEllipticAt_iff_forall_isInvertible`), and on an open set `U` where
`φ ψ ≠ 0` the restriction of `a` to `U` is an elliptic classical symbol exactly when `P` is
elliptic over `U` (`TauCeti.isElliptic_restrict_iff_forall_isSectionClassicalEllipticAt`).
Ellipticity is an open condition (`TauCeti.IsSectionClassicalEllipticAt.eventually`). On a compact
set over which `P` is elliptic and `φ ψ ≠ 0`, the chart symbol is elliptic at large frequencies
with the inverse bound of order `-m`, and a symbol of order `-m` with values in `W →L[ℂ] V`
inverts it on both sides at large frequencies near that set
(`TauCeti.exists_isEllipticOn_of_forall_isSectionClassicalEllipticAt`,
`TauCeti.exists_comp_eq_id_of_forall_isSectionClassicalEllipticAt`). These are the local inverse
symbols from which a parametrix of an elliptic operator between bundles is assembled chart by
chart, and through which the Euclidean elliptic theory of matrix-valued symbols applies to `P`.
The scalar forms of these statements are in
`TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic`.

## Main results

* `TauCeti.coefficient_principal_apply_eq_sectionClassicalPrincipalSymbol`: the principal symbol
  of a chart symbol of `P` is the principal symbol of `P` read in the chart and the frames.
* `TauCeti.isSectionClassicalEllipticAt_iff_forall_isInvertible`: ellipticity in a chart.
* `TauCeti.isElliptic_restrict_iff_forall_isSectionClassicalEllipticAt`: the chart symbol is
  elliptic over an open set exactly when `P` is.
* `TauCeti.IsSectionClassicalEllipticAt.eventually`,
  `TauCeti.isOpen_setOf_isSectionClassicalEllipticAt`: ellipticity is an open condition.
* `TauCeti.exists_isEllipticOn_of_forall_isSectionClassicalEllipticAt`,
  `TauCeti.exists_comp_eq_id_of_forall_isSectionClassicalEllipticAt`: local inverse symbols.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators between sections of vector bundles and their principal symbols).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §4 and §8.
-/

public section

noncomputable section

open Bundle Filter Set TauCeti Module
open scoped ContDiff Distributions Manifold SchwartzMap Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {m : ℝ}
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

namespace TauCeti

/-! ### The principal symbol in a chart -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {t : Trivialization V (π V E)} [MemTrivializationAtlas t] {hE : e.source ⊆ t.baseSet}
  {t' : Trivialization W (π W F)} [MemTrivializationAtlas t']
  {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {a : ClassicalSymbol n V W m}

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- The scalar entry `ℓ ∘ a ∘ v` of the chart symbol `a` of `P` is the symbol of the scalar chart
compression of the matrix entry `f ↦ ρ ℓ(t' (P (f ρ t⁻¹ v)))` of `P`, for a cutoff `ρ` equal to
`1` over the supports of `φ` and `ψ`. -/
private theorem quantizeSchwartzValue_map_entryMap_eq_complexChartCompression
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    (ρ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hρE : tsupport ρ ⊆ t.baseSet)
    (hρF : tsupport ρ ⊆ t'.baseSet) (hρ : ∀ y ∈ tsupport φ ∪ tsupport ψ, ρ (e.symm y) = 1)
    (ℓ : W →L[ℂ] ℂ) (v : V) (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n) :
    quantizeSchwartzValue (a.map (Symbol.entryMap ℓ v)).toSymbol.coefficient u y =
      e.complexChartCompression he φ ψ (sectionEntry t ρ hρE v t' ρ hρF ℓ P)
        (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y := by
  rw [ClassicalSymbol.toSymbol_map, Symbol.quantizeSchwartzValue_map_entryMap, ha,
    OpenPartialHomeomorph.complexChartCompression_apply, sectionEntry_apply,
    t.chartCutoffSection_postcompCLM_toSpanSingleton he hE ψ u v ρ hρE
      fun y hy ↦ hρ y (Or.inr hy)]
  by_cases hφ : φ y = 0
  · simp [hφ]
  rw [hρ y (Or.inl (subset_tsupport _ hφ)), one_smul, ContinuousLinearMap.map_smul_of_tower]

/-- **The principal symbol in a chart.** Let `a` be the symbol of the compression
`u ↦ φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹` of a classical pseudodifferential operator `P` of order
`m` between bundles, in a chart `e` whose source lies in the base sets of the trivializations `t`
and `t'`. At a point `x` of the chart source, the principal symbol of `a` at the frequency `η` is
the principal symbol of `P` at the covector `⟪η, ·⟫ ∘ de_x`, read in the frames `t` and `t'`, times
`φ(e x) ψ(e x)`. -/
theorem coefficient_principal_apply_eq_sectionClassicalPrincipalSymbol
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hF : e.source ⊆ t'.baseSet)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {x : M} (hx : x ∈ e.source) (η : CoordinateSpace n) (v : V) :
    a.principal.coefficient (e x, η) v =
      ((φ (e x) * ψ (e x) : ℝ) : ℂ) • t'.continuousLinearMapAt ℂ x
        (sectionClassicalPrincipalSymbol m P x
          ((innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x)) (t.symm x v)) := by
  -- A function `ρ` on `M`, supported in the chart source, equal to `1` over the supports of `φ`
  -- and `ψ`, cuts off the frames of `E` and `F`.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhdsSet_tsupport_union φ ψ
  obtain ⟨ρ, hρs, hρχ⟩ := e.exists_tsupport_subset_eq_one he χ e.open_source
    (image_subset_iff.2 fun y hy ↦ e.map_target (χ.tsupport_subset hy))
  have hρ (y : CoordinateSpace n) (hy : y ∈ tsupport φ ∪ tsupport ψ) : ρ (e.symm y) = 1 :=
    hρχ y (subset_tsupport _ (by simp [hχ.self_of_nhdsSet y hy]))
  set ξ := (innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x)
  -- It suffices to compare the scalar entries `ℓ ∘ a_m ∘ v`.
  suffices h : ∀ ℓ : W →L[ℂ] ℂ, ℓ (a.principal.coefficient (e x, η) v) =
      ℓ (((φ (e x) * ψ (e x) : ℝ) : ℂ) •
        t'.continuousLinearMapAt ℂ x (sectionClassicalPrincipalSymbol m P x ξ (t.symm x v))) by
    refine (finBasis ℂ W).ext_elem fun j ↦ ?_
    simpa using h ((finBasis ℂ W).coord j).toContinuousLinearMap
  intro ℓ
  have hA := (mem_sectionClassicalPseudodifferentialOperators_iff.1 hP).2 t ρ (hρs.trans hE) v
    t' ρ (hρs.trans hF) ℓ
  have hentry := coefficient_principal_eq_classicalPrincipalSymbol hA he φ ψ
    (quantizeSchwartzValue_map_entryMap_eq_complexChartCompression ha ρ (hρs.trans hE)
      (hρs.trans hF) hρ ℓ v) hx η
  rw [ClassicalSymbol.principal_map] at hentry
  have hℓ := DFunLike.congr_fun hentry 1
  simp only [HomogeneousSymbol.coefficient_map, Symbol.entryMap_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] at hℓ
  rw [hℓ, classicalPrincipalSymbol_sectionEntry hP, map_smul, smul_eq_mul]
  by_cases hφψ : φ (e x) * ψ (e x) = 0
  · simp [hφψ]
  have hρx : ρ x = 1 := by
    simpa [e.left_inv hx] using hρ (e x) (Or.inl (subset_tsupport _ (left_ne_zero_of_mul hφψ)))
  rw [hρx, mul_one, Complex.ofReal_one, one_mul]

/-- **Ellipticity in a chart.** Let `a` be the symbol of the chart compression
`u ↦ φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹` of a classical pseudodifferential operator `P` of order
`m` between bundles. At a point `x` of the chart source where `φ ψ` does not vanish, `P` is elliptic
exactly when the principal symbol of `a` is invertible at `e x` at every nonzero frequency. -/
theorem isSectionClassicalEllipticAt_iff_forall_isInvertible
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hF : e.source ⊆ t'.baseSet)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {x : M} (hx : x ∈ e.source) (hφψ : φ (e x) * ψ (e x) ≠ 0) :
    IsSectionClassicalEllipticAt m P x ↔
      ∀ η : CoordinateSpace n, η ≠ 0 → (a.principal.coefficient (e x, η)).IsInvertible := by
  have he₁ : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by simp) he
  have hc : ((φ (e x) * ψ (e x) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hφψ
  set T := t'.continuousLinearEquivAt ℂ x (hF hx)
  set S := (t.continuousLinearEquivAt ℂ x (hE hx)).symm
  have hcb : Function.Bijective fun w : W ↦ ((φ (e x) * ψ (e x) : ℝ) : ℂ) • w :=
    ⟨smul_right_injective W hc, fun w ↦ ⟨_, smul_inv_smul₀ hc w⟩⟩
  -- The principal symbol of `a` at `(e x, η)` is `σ_m(P)(x, ξ)` between the frame isomorphisms.
  have key (η : CoordinateSpace n) : (a.principal.coefficient (e x, η) : V → W) =
      (fun w ↦ ((φ (e x) * ψ (e x) : ℝ) : ℂ) • w) ∘ T ∘ sectionClassicalPrincipalSymbol m P x
        ((innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x)) ∘ S := by
    rw [t'.coe_continuousLinearEquivAt_eq, t.symm_continuousLinearEquivAt_eq]
    funext v
    rw [coefficient_principal_apply_eq_sectionClassicalPrincipalSymbol hP hF ha hx]
    simp [t.symmL_apply (hE hx)]
  have hbij (η : CoordinateSpace n) : (a.principal.coefficient (e x, η)).IsInvertible ↔
      Function.Bijective (sectionClassicalPrincipalSymbol m P x
        ((innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x))) := by
    rw [ContinuousLinearMap.isInvertible_iff_bijective, key, hcb.of_comp_iff',
      T.bijective.of_comp_iff', Function.Bijective.of_comp_iff _ S.bijective]
  rw [isSectionClassicalEllipticAt_iff]
  simp_rw [hbij]
  refine ⟨fun h η hη ↦ h _ ((innerSL_comp_mvfderiv_eq_zero_iff he₁ hx).not.2 hη),
    fun h ξ hξ ↦ ?_⟩
  -- The covector `ξ` is `⟪η, ·⟫ ∘ de_x` for the frequency `η` dual to `ξ ∘ (de_x)⁻¹`.
  have hηξ := innerSL_toDual_symm_comp_inverse_mvfderiv he₁ hx ξ
  exact hηξ ▸ h _ (toDual_symm_comp_inverse_mvfderiv_ne_zero he₁ hx hξ)

/-- **The chart symbol of an elliptic operator.** Let `a` be the symbol of the chart compression of
`P` by `φ`, `ψ` in a chart `e` and frames `t`, `t'`, and let `U` be an open set on which `φ ψ` does
not vanish (so `U` lies in the chart target). The restriction of `a` to `U` is an elliptic
classical symbol on `U` exactly when `P` is elliptic at `e⁻¹ y` for every `y ∈ U`. -/
theorem isElliptic_restrict_iff_forall_isSectionClassicalEllipticAt
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hF : e.source ⊆ t'.baseSet)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {U : TopologicalSpace.Opens (CoordinateSpace n)} (hφψ : ∀ y ∈ U, φ y * ψ y ≠ 0) :
    (ClassicalSymbol.restrict U a).IsElliptic ↔
      ∀ y ∈ U, IsSectionClassicalEllipticAt m P (e.symm y) := by
  rw [ClassicalSymbol.isElliptic_restrict_iff]
  refine forall₂_congr fun y hy ↦ ?_
  have hU := OpenPartialHomeomorph.mem_target_of_mul_ne_zero (hφψ y hy)
  have hy' := e.right_inv hU
  rw [isSectionClassicalEllipticAt_iff_forall_isInvertible hP hF ha (e.map_target hU)
    (hy'.symm ▸ hφψ y hy), hy']

end Chart

/-! ### Openness -/

/-- **Ellipticity is an open condition.** An operator between bundles elliptic at `x` is elliptic
at every point near `x`. -/
theorem IsSectionClassicalEllipticAt.eventually {x : M}
    (hPx : IsSectionClassicalEllipticAt m P x) :
    ∀ᶠ y in 𝓝 x, IsSectionClassicalEllipticAt m P y := by
  -- In dimension zero, or between trivial fibres, all operators are elliptic; else `P` has
  -- order `m`.
  rcases subsingleton_or_nontrivial (CoordinateSpace n) with hn | hn
  · exact .of_forall isSectionClassicalEllipticAt_of_subsingleton
  refine hPx.mem_or_subsingleton.elim (fun hP ↦ ?_)
    fun ⟨_, _⟩ ↦ .of_forall isSectionClassicalEllipticAt_of_subsingleton_fiber
  -- A chart `e` of the maximal atlas at `x` over which both bundles are trivial.
  obtain ⟨e, he, hx, hE, hF⟩ :=
    exists_mem_maximalAtlas_source_subset_baseSet 𝓘(ℝ, CoordinateSpace n) ∞ V E W F x
  -- A cutoff `χ` equal to `1` near `e x`, and the symbol `a` of the compression by `χ`, `χ`.
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩)
    isCompact_singleton (singleton_subset_iff.2 (e.map_source hx))
  rw [nhdsSet_singleton] at hχ
  obtain ⟨a, ha⟩ := exists_quantizeSchwartzValue_eq_apply_chartCutoffSection he _ hE hP _ hF χ χ
  have hinv := (isSectionClassicalEllipticAt_iff_forall_isInvertible hP hF ha hx
    (by simp [hχ.self_of_nhds])).1 hPx
  -- The principal symbol of `a` is invertible near `e x` at every nonzero frequency.
  have hall := hχ.and (a.principal.eventually_forall_isInvertible_coefficient hinv)
  filter_upwards [e.open_source.mem_nhds hx, (e.continuousAt hx).eventually hall] with y hy hy'
  exact (isSectionClassicalEllipticAt_iff_forall_isInvertible hP hF ha hy (by simp [hy'.1])).2
    hy'.2

variable (m P) in
/-- **Ellipticity is an open condition.** The points at which an operator between bundles is
elliptic form an open set. -/
theorem isOpen_setOf_isSectionClassicalEllipticAt :
    IsOpen {x : M | IsSectionClassicalEllipticAt m P x} :=
  isOpen_iff_mem_nhds.2 fun _ hx ↦ hx.eventually

/-! ### Local inverse symbols -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {t : Trivialization V (π V E)} [MemTrivializationAtlas t] {hE : e.source ⊆ t.baseSet}
  {t' : Trivialization W (π W F)} [MemTrivializationAtlas t']
  {φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {a : ClassicalSymbol n V W m}

/-- The chart symbol of `P` is elliptic on an open set containing a set `K` at whose points `φ ψ`
does not vanish and over which `P` is elliptic. -/
private theorem exists_isElliptic_restrict_of_forall_isSectionClassicalEllipticAt
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hF : e.source ⊆ t'.baseSet)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {K : Set (CoordinateSpace n)} (hKφψ : ∀ y ∈ K, φ y * ψ y ≠ 0)
    (hKP : ∀ y ∈ K, IsSectionClassicalEllipticAt m P (e.symm y)) :
    ∃ U : TopologicalSpace.Opens (CoordinateSpace n), K ⊆ U ∧
      (ClassicalSymbol.restrict U a).IsElliptic := by
  set U : TopologicalSpace.Opens (CoordinateSpace n) :=
    ⟨{y | φ y * ψ y ≠ 0 ∧ IsSectionClassicalEllipticAt m P (e.symm y)},
      e.isOpen_setOf_mul_ne_zero_and_symm_mem φ ψ (isOpen_setOf_isSectionClassicalEllipticAt m P)⟩
  exact ⟨U, fun y hy ↦ ⟨hKφψ y hy, hKP y hy⟩,
    (isElliptic_restrict_iff_forall_isSectionClassicalEllipticAt (U := U) hP hF ha
      fun _ hy ↦ hy.1).2 fun _ hy ↦ hy.2⟩

/-- **Ellipticity of a chart symbol over a compact set.** Let `a` be the symbol of the chart
compression of `P` by `φ`, `ψ` in a chart `e` and frames `t`, `t'`, and `K` a compact set at whose
points `φ ψ` does not vanish (so `K` lies in the chart target) and over which `P` is elliptic. Then
`a` is elliptic over `K` at all frequencies of norm at least some radius `R`: its value is
invertible there, with `‖a(y, ξ)⁻¹‖ ≤ C ⟨ξ⟩^(-m)`. -/
theorem exists_isEllipticOn_of_forall_isSectionClassicalEllipticAt
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hF : e.source ⊆ t'.baseSet)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hKφψ : ∀ y ∈ K, φ y * ψ y ≠ 0) (hKP : ∀ y ∈ K, IsSectionClassicalEllipticAt m P (e.symm y)) :
    ∃ R, a.toSymbol.IsEllipticOn {p | p.1 ∈ K ∧ R ≤ ‖p.2‖} := by
  obtain ⟨U, hKU, hUa⟩ :=
    exists_isElliptic_restrict_of_forall_isSectionClassicalEllipticAt hP hF ha hKφψ hKP
  exact ClassicalSymbol.exists_isEllipticOn_of_isElliptic_restrict hUa hKU hK

/-- **Local inverse symbols of an elliptic operator between bundles.** Let `a` be the symbol of
the chart compression of `P` by `φ`, `ψ` in a chart `e` and frames `t`, `t'`, and `K` a compact set
at whose points `φ ψ` does not vanish (so `K` lies in the chart target) and over which `P` is
elliptic. Then a symbol `b` of order `-m` with values in `W →L[ℂ] V` inverts `a` on both sides at
all large frequencies and all positions near `K`. -/
theorem exists_comp_eq_id_of_forall_isSectionClassicalEllipticAt
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m) (hF : e.source ⊆ t'.baseSet)
    (ha : ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)))
    {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (hKφψ : ∀ y ∈ K, φ y * ψ y ≠ 0) (hKP : ∀ y ∈ K, IsSectionClassicalEllipticAt m P (e.symm y)) :
    ∃ (b : Symbol n W V (-m)) (R : ℝ), ∀ᶠ y in 𝓝ˢ K, ∀ ξ, R ≤ ‖ξ‖ →
      b.coefficient (y, ξ) ∘L a.toSymbol.coefficient (y, ξ) = .id ℂ V ∧
        a.toSymbol.coefficient (y, ξ) ∘L b.coefficient (y, ξ) = .id ℂ W := by
  obtain ⟨U, hKU, hUa⟩ :=
    exists_isElliptic_restrict_of_forall_isSectionClassicalEllipticAt hP hF ha hKφψ hKP
  exact ClassicalSymbol.exists_comp_eq_id_of_isElliptic_restrict hUa hKU hK

end Chart

end TauCeti
