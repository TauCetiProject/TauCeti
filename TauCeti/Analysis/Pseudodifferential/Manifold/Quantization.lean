/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Basic
import TauCeti.Analysis.Pseudodifferential.CoordinateChange.Chart
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Quantization in a chart and patching on a manifold

Let `M` be a manifold modelled on `ℝⁿ`, `e` a chart of its maximal smooth atlas, `φ`, `ψ` cutoffs
with compact supports in the chart target and `a` a symbol on `ℝⁿ`. The **chart quantization**

`f ↦ (φ · Op(a) (ψ · (f ∘ e⁻¹))) ∘ e`,

extended by zero off the chart source, is a complex-linear operator on the complex-valued smooth
functions on `M` (`OpenPartialHomeomorph.chartQuantization`). Locally finite sums of chart
quantizations are how pseudodifferential operators on a manifold are built from local symbols
(Hörmander III, §18.1; Melrose, §5.3): with a locally finite atlas, a partition of unity `φᵢ` and
cutoffs `ψᵢ` equal to `1` near the supports of the `φᵢ`, the operator `∑ᵢ φᵢ Op(aᵢ) ψᵢ` is the
patched quantization of the local symbols `aᵢ`.

This file shows that these operators are classical pseudodifferential operators in the sense of
`TauCeti.classicalPseudodifferentialOperators`, whose definition reads an operator in every chart
of the maximal atlas, not only in the chart used to build it.

* `OpenPartialHomeomorph.exists_quantizeSchwartzValue_eq_complexChartCompression_chartQuantization`:
  read in another chart `e'` through cutoffs `φ'`, `ψ'`, the chart quantization of a classical
  symbol `a` of order `m` is the quantization of a classical symbol `b` of order `m`, whose
  principal symbol is `φ'(x) ψ'(x) φ(κ x) ψ(κ x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)` on the source of the
  transition map `κ = e ∘ e'⁻¹` and vanishes elsewhere. The compression is the change of
  coordinates by `κ` of `Op(a)` with the cutoffs `φ' · (φ ∘ κ)` and `ψ' · (ψ ∘ κ)`, both supported
  in the source of `κ`, so `TauCeti.ClassicalSymbol.exists_smul_quantizeSchwartzValue_comp_eq`
  applies.
* `OpenPartialHomeomorph.chartQuantization_mem_classicalPseudodifferentialOperators`: the chart
  quantization of a classical symbol of order `m` is a classical pseudodifferential operator of
  order `m`. Its outputs are supported in `e⁻¹(supp φ)`, and it only sees its input on
  `e⁻¹(supp ψ)`, so it is properly supported.
* `TauCeti.exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum`: a locally finite sum
  `∑ᵢ Pᵢ` of classical pseudodifferential operators of order `m` is one, provided each `Pᵢ` has
  outputs supported in a compact set `Sᵢ` and only sees its input near `Sᵢ`, with `(Sᵢ)` locally
  finite. Near a compact set only finitely many `Pᵢ` matter.
* `TauCeti.exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum_chartQuantization`:
  the **patched quantization** `∑ᵢ φᵢ Op(aᵢ) ψᵢ` of classical symbols of order `m` in charts `eᵢ`,
  for cutoffs whose supports form a locally finite family on `M`, is a classical
  pseudodifferential operator of order `m`.

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

namespace OpenPartialHomeomorph

/-! ### Chart quantization -/

section Schwartz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)

/-- **Pushing a complex-valued function on the manifold forward to a Schwartz function.** For a
cutoff `ψ` with compact support in the target of the chart `e`, the function `ψ · (h ∘ e⁻¹)` on
`E` is smooth with compact support, hence a Schwartz function, linear in `h`
(`OpenPartialHomeomorph.complexCutoffPushforward` as a Schwartz function). -/
def schwartzCutoffPushforward (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ] 𝓢(E, ℂ) where
  toFun h := (e.hasCompactSupport_complexCutoffPushforward he ψ h).toSchwartzMap
    (contMDiff_iff_contDiff.1 (e.complexCutoffPushforward he ψ h).contMDiff)
  map_add' g h := by
    ext y
    simp
  map_smul' c h := by
    ext y
    simp

@[simp]
theorem schwartzCutoffPushforward_apply (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (h : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, ℂ), ℂ⟯) (y : E) :
    e.schwartzCutoffPushforward he ψ h y = ψ y • h (e.symm y) := by
  simp [schwartzCutoffPushforward]

end Schwartz

variable {n : ℕ} {m : ℝ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

/-- The **chart quantization** of a symbol `a` on `ℝⁿ` in the chart `e`, with cutoffs `φ` and
`ψ` with compact supports in the chart target: the operator

`f ↦ (φ · Op(a) (ψ · (f ∘ e⁻¹))) ∘ e`

on the complex-valued smooth functions on `M`, extended by zero off the chart source. -/
def chartQuantization (a : Symbol n ℂ ℂ m) (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun f := e.complexCutoffPullback he φ <| ContMDiffMap.ofContDiff
    (quantizeSchwartzValue a.coefficient (e.schwartzCutoffPushforward he ψ f))
    (a.contDiff_quantizeSchwartzValue _)
  map_add' f g := by
    rw [← map_add]
    congr 1
    ext x
    obtain ⟨C, -, hC⟩ := a.exists_bound_coefficient_slice x
    simp [map_add, quantizeSchwartzValue_add_right
      (a.continuous_coefficient_slice x).aestronglyMeasurable hC]
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1
    ext x
    simp

theorem chartQuantization_apply_of_mem (a : Symbol n ℂ ℂ m)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    {p : M} (hp : p ∈ e.source) :
    e.chartQuantization he a φ ψ f p =
      φ (e p) • quantizeSchwartzValue a.coefficient (e.schwartzCutoffPushforward he ψ f) (e p) := by
  simp [chartQuantization, complexCutoffPullback_apply_of_mem he _ _ hp]

theorem chartQuantization_apply_of_notMem (a : Symbol n ℂ ℂ m)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯)
    {p : M} (hp : p ∉ e.source) : e.chartQuantization he a φ ψ f p = 0 := by
  simp [chartQuantization, complexCutoffPullback_apply_of_notMem he _ _ hp]

/-- The chart quantization is supported in the chart preimage of the support of `φ`. -/
theorem tsupport_chartQuantization_subset (a : Symbol n ℂ ℂ m)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    tsupport (e.chartQuantization he a φ ψ f) ⊆ e.symm '' tsupport φ := by
  rw [chartQuantization, LinearMap.coe_mk, AddHom.coe_mk]
  exact e.tsupport_complexCutoffPullback_subset he φ _

/-- The chart quantization only sees its input on the chart preimage of the support of `ψ`. -/
theorem chartQuantization_eq_zero (a : Symbol n ℂ ℂ m) (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hf : ∀ p ∈ e.symm '' tsupport ψ, f p = 0) :
    e.chartQuantization he a φ ψ f = 0 := by
  have hv : e.schwartzCutoffPushforward he ψ f = 0 := by
    ext y
    rw [schwartzCutoffPushforward_apply, FunLike.coe_zero, Pi.zero_apply]
    by_cases hy : ψ y = 0
    · rw [hy, zero_smul]
    · rw [hf _ ⟨y, subset_tsupport _ hy, rfl⟩, smul_zero]
  ext p
  by_cases hp : p ∈ e.source
  · simp [chartQuantization_apply_of_mem he _ _ _ _ hp, hv]
  · simp [chartQuantization_apply_of_notMem he _ _ _ _ hp]

/-! ### Reading a chart quantization in another chart -/

omit [ChartedSpace (CoordinateSpace n) M] [T2Space M] in
/-- A point lies in the source of the transition map `e ∘ e'⁻¹` iff it lies in the target of `e'`
and `e'⁻¹` sends it into the source of `e`. -/
private theorem mem_symm_trans_source_iff {e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    {x : CoordinateSpace n} :
    x ∈ (e'.symm.trans e).source ↔ x ∈ e'.target ∧ e'.symm x ∈ e.source := by
  rw [trans_source, symm_source, mem_inter_iff, mem_preimage]

include he in
/-- The cutoff `φ' · (φ ∘ e ∘ e'⁻¹)` for two charts: it is smooth with compact support in the source
of the transition map `κ = e ∘ e'⁻¹`, where it is `φ'(x) φ(κ x)`. -/
private theorem exists_transitionCutoff {e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ Φ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      tsupport Φ ⊆ (e'.symm.trans e).source ∧
        ∀ x ∈ (e'.symm.trans e).source, Φ x = φ' x * φ ((e'.symm.trans e) x) := by
  set h := e'.cutoffPushforward he' φ' (e.cutoffPullback he φ 1)
  refine ⟨h, contMDiff_iff_contDiff.1 h.contMDiff,
    e'.hasCompactSupport_cutoffPushforward he' φ' _,
    e.tsupport_cutoffPushforward_cutoffPullback_subset he he' φ' φ 1, fun x hx ↦ ?_⟩
  simp [h, cutoffPullback_apply_of_mem he _ _ (mem_symm_trans_source_iff.1 hx).2]

/-- **A chart quantization read in another chart.** Let `a` be a classical symbol of order `m`,
`φ`, `ψ` cutoffs in the target of the chart `e`, and `φ'`, `ψ'` cutoffs in the target of another
chart `e'` of the maximal atlas. The compression of the chart quantization
`f ↦ (φ · Op(a) (ψ · (f ∘ e⁻¹))) ∘ e` by `φ'` and `ψ'` in the chart `e'` is `Op(b)` for a classical
symbol `b` of order `m`. On the source of the transition map `κ = e ∘ e'⁻¹` its principal symbol
is the principal symbol of `a` transported by the cotangent map of `κ`,

`σ(b)(x, ξ) = φ'(x) ψ'(x) φ(κ x) ψ(κ x) σ(a)(κ x, (Dκ(x)*)⁻¹ ξ)`,

and off this source it vanishes. -/
theorem exists_quantizeSchwartzValue_eq_complexChartCompression_chartQuantization
    (a : ClassicalSymbol n ℂ ℂ m) (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {e' : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ' ψ' : 𝓓(⟨e'.target, e'.open_target⟩, ℝ)) :
    ∃ b : ClassicalSymbol n ℂ ℂ m,
      (∀ x ∈ (e'.symm.trans e).source, ∀ ξ, b.principal.coefficient (x, ξ) =
        (φ' x * ψ' x * (φ ((e'.symm.trans e) x) * ψ ((e'.symm.trans e) x))) •
          a.principal.coefficient ((e'.symm.trans e) x,
            ContinuousLinearMap.adjoint (Ring.inverse (fderiv ℝ (e'.symm.trans e) x)) ξ)) ∧
      (∀ x ∉ (e'.symm.trans e).source, ∀ ξ, b.principal.coefficient (x, ξ) = 0) ∧
      ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (x : CoordinateSpace n),
        quantizeSchwartzValue b.toSymbol.coefficient u x =
          e'.complexChartCompression he' φ' ψ' (e.chartQuantization he a.toSymbol φ ψ)
            (ContMDiffMap.ofContDiff u (u.smooth ⊤)) x := by
  obtain ⟨Φ, hΦ, hΦc, hΦs, hΦv⟩ := exists_transitionCutoff he he' φ' φ
  obtain ⟨Ψ, hΨ, hΨc, hΨs, hΨv⟩ := exists_transitionCutoff he he' ψ' ψ
  set κ := e'.symm.trans e with hκ
  have hΦ0 : ∀ x ∉ κ.source, Φ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hΦs h)
  obtain ⟨b, hb, hop⟩ := a.exists_smul_quantizeSchwartzValue_comp_eq κ
    (contDiffOn_symm_trans_of_mem_maximalAtlas he' he)
    (fun _ hz ↦ (contDiffAt_symm_trans_symm_of_mem_maximalAtlas he' he hz).contDiffWithinAt)
    hΦ hΦc hΦs hΨ hΨc hΨs
  refine ⟨b, fun x hx ξ ↦ ?_, fun x hx ξ ↦ ?_, fun u x ↦ ?_⟩
  · rw [hb, hΦv x hx, hΨv x hx]
    ring_nf
  · rw [hb, hΦ0 x hx, zero_mul, zero_smul]
  -- The input of `Op(a)` is `v = ψ · (g ∘ e⁻¹)` for the pullback `g = (ψ' u) ∘ e'`: on the source
  -- of `κ` it is `v (κ y) = ψ(κ y) ψ'(y) u(y)`, and it vanishes off the target of `κ`.
  set g := e'.complexCutoffPullback he' ψ' (ContMDiffMap.ofContDiff u (u.smooth ⊤))
  set v := e.schwartzCutoffPushforward he ψ g
  have hv : ∀ y ∈ κ.source, v (κ y) = Ψ y • u y := by
    intro y hy
    have hy' := mem_symm_trans_source_iff.1 hy
    -- `κ y = e (e'⁻¹ y)`, sent back to `e'⁻¹ y` by `e⁻¹` and on to `y` by `e'`.
    simp [v, g, hΨv y hy, hκ, e.left_inv hy'.2,
      complexCutoffPullback_apply_of_mem he' _ _ (e'.map_target hy'.1), e'.right_inv hy'.1]
    ring
  have hv0 : ∀ z ∉ κ.target, v z = 0 := by
    intro z hz
    rw [schwartzCutoffPushforward_apply]
    rw [hκ, trans_target, symm_target, mem_inter_iff, not_and_or] at hz
    rcases hz with hz | hz
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hz (ψ.tsupport_subset h), zero_smul]
    · rw [complexCutoffPullback_apply_of_notMem he' _ _ hz, smul_zero]
  rw [← hop u v hv hv0 x, complexChartCompression_apply]
  by_cases hx : x ∈ κ.source
  · have hx' := mem_symm_trans_source_iff.1 hx
    rw [chartQuantization_apply_of_mem he _ _ _ _ hx'.2, hΦv x hx, smul_smul, hκ, coe_trans,
      Function.comp_apply]
  · rw [hΦ0 x hx, zero_smul]
    by_cases hx' : x ∈ e'.target
    · have hxs : e'.symm x ∉ e.source := fun h ↦ hx (mem_symm_trans_source_iff.2 ⟨hx', h⟩)
      rw [chartQuantization_apply_of_notMem he _ _ _ _ hxs, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hx' (φ'.tsupport_subset h), zero_smul]

/-- **Chart quantizations are classical pseudodifferential operators.** For a classical symbol `a`
of order `m` on `ℝⁿ`, a chart `e` of the maximal atlas and cutoffs `φ`, `ψ` with compact supports in
the chart target, the operator `f ↦ (φ · Op(a) (ψ · (f ∘ e⁻¹))) ∘ e` is a classical
pseudodifferential operator of order `m` on `M`. -/
theorem chartQuantization_mem_classicalPseudodifferentialOperators (a : ClassicalSymbol n ℂ ℂ m)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    e.chartQuantization he a.toSymbol φ ψ ∈ classicalPseudodifferentialOperators m := by
  refine mem_classicalPseudodifferentialOperators_iff.2
    ⟨isProperlySupported_iff.2 fun K _ ↦ ?_, fun e' he' φ' ψ' ↦ ?_⟩
  · refine ⟨_, (e.isCompact_symm_image_tsupport φ).union (e.isCompact_symm_image_tsupport ψ),
      fun f _ ↦ (tsupport_chartQuantization_subset he _ _ _ f).trans subset_union_left,
      fun f hf x _ ↦ ?_⟩
    rw [chartQuantization_eq_zero he _ _ _ fun p hp ↦
      (hf.filter_mono (nhdsSet_mono subset_union_right)).self_of_nhdsSet p hp,
      ContMDiffMap.coe_zero, Pi.zero_apply]
  · obtain ⟨b, -, -, hb⟩ :=
      exists_quantizeSchwartzValue_eq_complexChartCompression_chartQuantization he a φ ψ he' φ' ψ'
    exact ⟨b, hb⟩

end OpenPartialHomeomorph

/-! ### Locally finite sums -/

namespace TauCeti

variable {n : ℕ} {m : ℝ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] {ι : Type*}
  {P : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {S : ι → Set M}

omit [T2Space M] in
/-- At a point of a compact set `K`, a locally finite sum of operators with outputs supported in
the sets `Sᵢ` is the finite sum over the indices with `Sᵢ` meeting `K`. -/
private theorem finsum_apply_eq_sum (hS : LocallyFinite S)
    (hsupp : ∀ i f, tsupport (P i f) ⊆ S i) {K : Set M} (hK : IsCompact K)
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) {x : M} (hx : x ∈ K) :
    ∑ᶠ i, P i f x = ∑ i ∈ (hS.finite_nonempty_inter_compact hK).toFinset, P i f x :=
  finsum_eq_sum_of_support_subset _ fun i hi ↦
    (hS.finite_nonempty_inter_compact hK).mem_toFinset.2 ⟨x, hsupp i f (subset_tsupport _ hi), hx⟩

/-- A locally finite sum of operators `Pᵢ` with outputs supported in compact sets `Sᵢ`, each only
seeing its input near `Sᵢ`, is properly supported. -/
private theorem isProperlySupported_of_apply_eq_finsum (hS : LocallyFinite S)
    (hSc : ∀ i, IsCompact (S i)) (hsupp : ∀ i f, tsupport (P i f) ⊆ S i)
    (hloc : ∀ i f, (∀ᶠ y in 𝓝ˢ (S i), f y = 0) → P i f = 0)
    {Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} (hQ : ∀ f x, Q f x = ∑ᶠ i, P i f x) :
    IsProperlySupported Q := by
  refine isProperlySupported_iff.2 fun K hK ↦ ?_
  -- Only the finitely many `Pᵢ` with `Sᵢ` meeting `K` see functions supported in `K` or act at
  -- points of `K`, so `K'` is the union of their sets `Sᵢ`.
  set I := (hS.finite_nonempty_inter_compact hK).toFinset
  refine ⟨⋃ i ∈ I, S i, I.isCompact_biUnion fun i _ ↦ hSc i, fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · refine closure_minimal (fun x hx ↦ ?_)
      (I.finite_toSet.isClosed_biUnion fun i _ ↦ (hSc i).isClosed)
    obtain ⟨i, hi⟩ : ∃ i, P i f x ≠ 0 := by
      by_contra! h
      exact hx (by rw [hQ, finsum_eq_zero_of_forall_eq_zero h])
    -- `f` vanishes off `K`, so `Pᵢ f = 0` unless `Sᵢ` meets `K`.
    have hiI : i ∈ I := by
      by_contra hiI
      refine hi ?_
      rw [hloc i f ?_, ContMDiffMap.coe_zero, Pi.zero_apply]
      refine Filter.mem_of_superset (hK.isClosed.isOpen_compl.mem_nhdsSet.2 fun y hy hyK ↦
        hiI ((hS.finite_nonempty_inter_compact hK).mem_toFinset.2 ⟨y, hy, hyK⟩)) fun y hy ↦ ?_
      exact image_eq_zero_of_notMem_tsupport fun h ↦ hy (hf h)
    exact mem_biUnion hiI (hsupp i f (subset_tsupport _ hi))
  · rw [hQ, finsum_apply_eq_sum hS hsupp hK f hx]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    rw [hloc i f (hf.filter_mono (nhdsSet_mono (subset_biUnion_of_mem hi))),
      ContMDiffMap.coe_zero, Pi.zero_apply]

/-- **Locally finite sums of pseudodifferential operators.** Let `Pᵢ` be classical
pseudodifferential operators of order `m` on `M`, and `Sᵢ` compact sets forming a locally finite
family, such that the outputs of `Pᵢ` are supported in `Sᵢ` and `Pᵢ f = 0` whenever `f` vanishes
near `Sᵢ`. Then the locally finite sum `f ↦ ∑ᵢ Pᵢ f` is a classical pseudodifferential operator of
order `m`. -/
theorem exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum (hS : LocallyFinite S)
    (hSc : ∀ i, IsCompact (S i)) (hP : ∀ i, P i ∈ classicalPseudodifferentialOperators m)
    (hsupp : ∀ i f, tsupport (P i f) ⊆ S i)
    (hloc : ∀ i f, (∀ᶠ y in 𝓝ˢ (S i), f y = 0) → P i f = 0) :
    ∃ Q ∈ classicalPseudodifferentialOperators m, ∀ f x, Q f x = ∑ᶠ i, P i f x := by
  classical
  have hpt (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
      (Function.support fun i ↦ P i f x).Finite :=
    (hS.point_finite x).subset fun i hi ↦ hsupp i f (subset_tsupport _ hi)
  -- The sum of the outputs, a smooth function since the supports are locally finite.
  let F (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ :=
    ⟨fun x ↦ ∑ᶠ i, P i f x, contMDiff_finsum (fun i ↦ (P i f).contMDiff)
      (hS.subset fun i ↦ (subset_tsupport _).trans (hsupp i f))⟩
  have hF (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
      F f x = ∑ᶠ i, P i f x :=
    congrFun (ContMDiffMap.coeFn_mk _ _) x
  let Q : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ :=
    { toFun := F
      map_add' f g := by
        ext x
        simp only [hF, map_add, ContMDiffMap.coe_add, Pi.add_apply]
        exact finsum_add_distrib (hpt f x) (hpt g x)
      map_smul' c f := by
        ext x
        simp only [hF, map_smul, ContMDiffMap.complex_smul_apply, RingHom.id_apply, ← smul_eq_mul]
        exact (smul_finsum' c (hpt f x)).symm }
  have hQ (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
      Q f x = ∑ᶠ i, P i f x :=
    hF f x
  refine ⟨Q, mem_classicalPseudodifferentialOperators_iff.2
    ⟨isProperlySupported_of_apply_eq_finsum hS hSc hsupp hloc hQ, fun e he φ ψ ↦ ?_⟩, hQ⟩
  · -- In a chart, only the finitely many `Pᵢ` with `Sᵢ` meeting `e⁻¹(supp φ)` contribute.
    have hK := e.isCompact_symm_image_tsupport φ
    set I := (hS.finite_nonempty_inter_compact hK).toFinset
    choose a ha using fun i ↦ (mem_classicalPseudodifferentialOperators_iff.1 (hP i)).2 e he φ ψ
    refine ⟨∑ i ∈ I, a i, fun u x ↦ ?_⟩
    rw [ClassicalSymbol.toSymbol_sum, Symbol.quantizeSchwartzValue_sum_left]
    simp only [ha, OpenPartialHomeomorph.complexChartCompression_apply, ← Finset.smul_sum, hQ]
    by_cases hx : φ x = 0
    · simp [hx]
    rw [finsum_apply_eq_sum hS hsupp hK _ ⟨x, subset_tsupport _ hx, rfl⟩]

/-- **Patched quantization.** For charts `eᵢ` of the maximal atlas, classical symbols `aᵢ` of order
`m` and cutoffs `φᵢ`, `ψᵢ` with compact supports in the chart targets, such that the chart preimages
`eᵢ⁻¹(supp φᵢ ∪ supp ψᵢ)` form a locally finite family, the operator
`f ↦ ∑ᵢ (φᵢ · Op(aᵢ) (ψᵢ · (f ∘ eᵢ⁻¹))) ∘ eᵢ` is a classical pseudodifferential operator of order
`m` on `M`. -/
theorem exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum_chartQuantization
    {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (a : ι → ClassicalSymbol n ℂ ℂ m) (φ ψ : (i : ι) → 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ))
    (hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (φ i) ∪ tsupport (ψ i))) :
    ∃ Q ∈ classicalPseudodifferentialOperators m, ∀ f x,
      Q f x = ∑ᶠ i, (e i).chartQuantization (he i) (a i).toSymbol (φ i) (ψ i) f x :=
  exists_mem_classicalPseudodifferentialOperators_apply_eq_finsum hS
    (fun i ↦ image_union (e i).symm _ _ ▸
      ((e i).isCompact_symm_image_tsupport (φ i)).union ((e i).isCompact_symm_image_tsupport (ψ i)))
    (fun i ↦
      (e i).chartQuantization_mem_classicalPseudodifferentialOperators (he i) (a i) (φ i) (ψ i))
    (fun i f ↦ ((e i).tsupport_chartQuantization_subset (he i) _ _ _ f).trans
      (image_mono subset_union_left))
    fun i _ hf ↦ (e i).chartQuantization_eq_zero (he i) _ _ _ fun p hp ↦
      hf.self_of_nhdsSet p (image_mono subset_union_right hp)

end TauCeti
