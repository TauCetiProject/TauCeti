/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.AdaptedChart.Parametric
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.AdaptedChart

/-!
# Adapted charts along a totally real embedding, depending on a parameter

Let `J s` be `C^ℓ` almost complex structures on a boundaryless manifold `M`, depending on a
parameter `s` in an open set `S` of a normed space `P`, jointly `C^ℓ` in `s` and the point when
read in the extended chart `χ` at `ι x₀`. Let `ι : N → M` be a `C^k` totally real embedding for
`J s₀`, with `1 ≤ ℓ` and `ℓ + 1 ≤ k`. This file chooses, for every `s` near `s₀`, an adapted
chart `ψ s` of `M` for `ι (N)` and `J s` (`TauCeti.IsAdaptedChart`), such that

* the sources of the `ψ s` contain one open neighbourhood `O` of `ι x₀`;
* the charts depend `C^ℓ` on the parameter: `ψ s x` and `(ψ s)⁻¹ p` are read off from one
  partial homeomorphism `e` of `(P × F) × F` onto an open subset of `P × E` that is `C^ℓ` with
  `C^ℓ` inverse, the parametric adapted extension
  `TauCeti.parametricAdaptedNormalExtension` of `ι` and `J` read in the extended charts.

This is McDuff–Salamon Exercise B.4.10 with parameters
(`TauCeti.IsTotallyRealEmbedding.exists_adaptedChart_parametric`). Only `J s₀` needs `ι` to be
totally real: total reality is an open condition, and the inverse function theorem for the
parametric extension (`TauCeti.exists_parametricAdaptedChart`) gives it for `s` near `s₀`. The
chart `ψ s` is the slice of `e` at `s`, restricted by the shrinking step of
`TauCeti.exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension`; the open set cutting the
sources is chosen once for all parameters near `s₀`, using that `ι` is an embedding.

The consumer in view is the boundary regularity of pseudoholomorphic maps for a structure
depending on the domain point, with the parameter the boundary coordinate.

## Main declarations

* `TauCeti.IsTotallyRealEmbedding.exists_adaptedChart_parametric`: the family of adapted charts.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace TauCeti

variable {E H M F H' N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [I'.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {ℓ : ℕ∞} {k : ℕ∞ω} {ι : N → M}

section Slice

variable {V W : Type*} [TopologicalSpace V] [TopologicalSpace W]

/-- The slice at `s` of a partial homeomorphism of `(P × V) × V` onto a subset of `P × W` which
preserves the parameter in both directions. -/
private noncomputable def slice (e : OpenPartialHomeomorph ((P × V) × V) (P × W))
    (he : ∀ p, (e p).1 = p.1.1) (hes : ∀ q ∈ e.target, (e.symm q).1.1 = q.1) (s : P) :
    OpenPartialHomeomorph (V × V) W where
  toFun p := (e ((s, p.1), p.2)).2
  invFun w := ((e.symm (s, w)).1.2, (e.symm (s, w)).2)
  source := {p | ((s, p.1), p.2) ∈ e.source}
  target := {w | (s, w) ∈ e.target}
  map_source' p hp := by
    have h := e.map_source hp
    rwa [← Prod.mk.eta (p := e ((s, p.1), p.2)), he] at h
  map_target' w hw := by
    have h := e.map_target hw
    rwa [← Prod.mk.eta (p := e.symm (s, w)), ← Prod.mk.eta (p := (e.symm (s, w)).1),
      hes _ hw] at h
  left_inv' p hp := by
    have h := e.left_inv hp
    -- `e` maps `((s, p.1), p.2)` to `(s, w)`, so the inverse at `(s, w)` returns it.
    rw [← Prod.mk.eta (p := e ((s, p.1), p.2)), he] at h
    simp [h]
  right_inv' w hw := by
    have h := e.right_inv hw
    rw [← Prod.mk.eta (p := e.symm (s, w)), ← Prod.mk.eta (p := (e.symm (s, w)).1),
      hes _ hw] at h
    simp [h]
  open_source := e.open_source.preimage (by fun_prop)
  open_target := e.open_target.preimage (by fun_prop)
  continuousOn_toFun := continuous_snd.comp_continuousOn
    (e.continuousOn.comp (by fun_prop : Continuous fun p : V × V ↦ ((s, p.1), p.2)).continuousOn
      fun _ hp ↦ hp)
  continuousOn_invFun := by
    have hc : ContinuousOn (fun w : W ↦ e.symm (s, w)) {w | (s, w) ∈ e.target} :=
      e.continuousOn_symm.comp (Continuous.prodMk_right s).continuousOn fun _ hw ↦ hw
    exact ((continuous_snd.comp continuous_fst).comp_continuousOn hc).prodMk
      (continuous_snd.comp_continuousOn hc)

end Slice

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **One slice.** For a partial homeomorphism `e` whose underlying map is the parametric adapted
extension of `ι` and `J` read in the extended charts `φ` at `x₀` and `χ` at `ι x₀`, with `C^ℓ`
inverse and source over the domain of `ι` read in `φ`, and an open `O ∋ ι x₀` such that the
points `z` with `ι z ∈ O` have `((s, φ z), 0)` in the source of `e`, the slice of `e` at `s`
gives an adapted chart for `ι (N)` and `J s`. -/
private theorem exists_isAdaptedChart_slice [IsManifold I' k N]
    {J : P → ContMDiffAlmostComplexStructure I ℓ M} {x₀ : N} {s : P}
    (hι : ContMDiff I' I k ι) (hℓ : 1 ≤ ℓ) (hk : (ℓ : ℕ∞ω) + 1 ≤ k)
    {e : OpenPartialHomeomorph ((P × F) × F) (P × E)}
    (he : ⇑e = parametricAdaptedNormalExtension (writtenInExtChartAt I' I x₀ ι)
      (fun q ↦ (J q.1).inChart (ι x₀) q.2))
    (hesc : ContDiffOn ℝ ℓ e.symm e.target)
    (heU : ∀ p ∈ e.source, p.1.2 ∈ (extChartAt I' x₀).target ∩
      (extChartAt I' x₀).symm ⁻¹' (ι ⁻¹' (extChartAt I (ι x₀)).source))
    {O : Set M} (hO : IsOpen O) (hx₀O : ι x₀ ∈ O)
    (hOe : ∀ z, ι z ∈ O → z ∈ (extChartAt I' x₀).source ∧
      ((s, extChartAt I' x₀ z), 0) ∈ e.source) :
    ∃ ψ : OpenPartialHomeomorph M (F × F), IsAdaptedChart (J s) (range ι) ψ ∧
      (∀ x, ψ x = ((e.symm (s, extChartAt I (ι x₀) x)).1.2,
        (e.symm (s, extChartAt I (ι x₀) x)).2)) ∧
      (∀ x, x ∈ ψ.source ↔ x ∈ (extChartAt I (ι x₀)).source ∧
        (s, extChartAt I (ι x₀) x) ∈ e.target ∧ x ∈ O) ∧
      ∀ p ∈ ψ.target, ((s, p.1), p.2) ∈ e.source ∧
        ψ.symm p = (extChartAt I (ι x₀)).symm (e ((s, p.1), p.2)).2 := by
  have hfst (p : (P × F) × F) : (e p).1 = p.1.1 := by
    rw [he, parametricAdaptedNormalExtension_apply]
  set es := slice e hfst (fun q hq ↦ e.fst_fst_symm_of_coe_eq_parametricAdaptedNormalExtension
    he hq) s
  -- The slice, its inverse, source and target, by the defining formulas of `slice`.
  have hes (p : F × F) : es p = (e ((s, p.1), p.2)).2 := rfl
  have hess (w : E) : es.symm w = ((e.symm (s, w)).1.2, (e.symm (s, w)).2) := rfl
  have hessrc (p : F × F) : p ∈ es.source ↔ ((s, p.1), p.2) ∈ e.source := Iff.rfl
  have hestgt (w : E) : w ∈ es.target ↔ (s, w) ∈ e.target := Iff.rfl
  have hesΦ : ⇑es = adaptedNormalExtension (writtenInExtChartAt I' I x₀ ι)
      ((J s).inChart (ι x₀)) := by
    funext p
    rw [hes, he, parametricAdaptedNormalExtension_apply]
  have hessc : ContDiffOn ℝ ℓ es.symm es.target := by
    have hc := hesc.comp (contDiffOn_const.prodMk contDiffOn_id) fun w hw ↦ (hestgt w).1 hw
    exact (((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).comp_contDiffOn hc).congr
      fun w _ ↦ hess w
  obtain ⟨ψ, hψcoe, hψsymm, hψsrc, hψtgt, -, -, hψ⟩ :=
    exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension hι hℓ hk hesΦ hessc
      (fun p hp ↦ ⟨heU _ ((hessrc p).1 hp), mem_univ _⟩) hO hx₀O fun z hz ↦
        ⟨(hOe z hz).1, (hessrc _).2 (hOe z hz).2⟩
  exact ⟨ψ, hψ, fun x ↦ by rw [hψcoe, hess], fun x ↦ by rw [hψsrc, hestgt],
    fun p hp ↦ ⟨((hψtgt p).1 hp).1, by rw [hψsymm, hes]⟩⟩

/-- **Adapted charts depending on a parameter.** Let `J s`, for `s` in an open set `S` of a
complete normed space `P`, be `C^ℓ` almost complex structures on `M` which, read in the extended
chart `χ` at `ι x₀`, are jointly `C^ℓ` in `(s, v)`, and let `ι` be a `C^k` totally real embedding
for `J s₀`, `s₀ ∈ S`, with `1 ≤ ℓ` and `ℓ + 1 ≤ k`. Then there are an open `S' ∋ s₀` inside `S`,
an open `O ∋ ι x₀` of `M`, a partial homeomorphism `e` of `(P × F) × F` into `P × E` which is the
parametric adapted extension of `ι` and `J` read in the extended charts at `x₀` and `ι x₀`, `C^ℓ`
with `C^ℓ` inverse, and for every `s ∈ S'` an adapted chart `ψ s` for `ι (N)` and `J s`
(`TauCeti.IsAdaptedChart`) whose source contains `O`, given by the slice of `e⁻¹` at `s` read
after `χ`, with inverse `χ⁻¹` after the slice of `e`. -/
theorem IsTotallyRealEmbedding.exists_adaptedChart_parametric [CompleteSpace P]
    [IsManifold I' k N] {J : P → ContMDiffAlmostComplexStructure I ℓ M} {S : Set P} {s₀ : P}
    {x₀ : N} (h : IsTotallyRealEmbedding I' I k (J s₀).almostComplexStructureAt ι)
    (hℓ : 1 ≤ ℓ) (hk : (ℓ : ℕ∞ω) + 1 ≤ k) (hS : IsOpen S) (hs₀ : s₀ ∈ S)
    (hJ : ContDiffOn ℝ ℓ (fun q : P × E ↦ (J q.1).inChart (ι x₀) q.2)
      (S ×ˢ (extChartAt I (ι x₀)).target)) :
    ∃ (S' : Set P) (O : Set M) (e : OpenPartialHomeomorph ((P × F) × F) (P × E))
      (ψ : P → OpenPartialHomeomorph M (F × F)),
      IsOpen S' ∧ s₀ ∈ S' ∧ S' ⊆ S ∧ IsOpen O ∧ ι x₀ ∈ O ∧
      ⇑e = parametricAdaptedNormalExtension (writtenInExtChartAt I' I x₀ ι)
        (fun q ↦ (J q.1).inChart (ι x₀) q.2) ∧
      ContDiffOn ℝ ℓ e e.source ∧ ContDiffOn ℝ ℓ e.symm e.target ∧
      ∀ s ∈ S', IsAdaptedChart (J s) (range ι) (ψ s) ∧ O ⊆ (ψ s).source ∧
        (∀ x, ψ s x = ((e.symm (s, extChartAt I (ι x₀) x)).1.2,
          (e.symm (s, extChartAt I (ι x₀) x)).2)) ∧
        ∀ p ∈ (ψ s).target, ((s, p.1), p.2) ∈ e.source ∧
          (ψ s).symm p = (extChartAt I (ι x₀)).symm (e ((s, p.1), p.2)).2 := by
  have : IsManifold I' ((ℓ : ℕ∞ω) + 1) N := IsManifold.of_le hk
  have : IsManifold I ((ℓ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hℓ' : (1 : ℕ∞ω) ≤ ℓ := by exact_mod_cast hℓ
  have hι : ContMDiff I' I ((ℓ : ℕ∞ω) + 1) ι := h.isSmoothEmbedding.contMDiff.of_le hk
  have hιd : MDifferentiableAt I' I ι x₀ := (hι x₀).mdifferentiableAt (by simp)
  set χ := extChartAt I (ι x₀)
  set φ := extChartAt I' x₀
  set γ := writtenInExtChartAt I' I x₀ ι
  obtain ⟨hU, hx₀U, hγ, hγΩ⟩ := isOpen_mem_contDiffOn_mapsTo_writtenInExtChartAt hι x₀
  -- The parametric adapted extension inverts near `((s₀, φ x₀), 0)`.
  obtain ⟨e, he, he₀, heU, -, hec, hesc⟩ :=
    exists_parametricAdaptedChart hS hU (hS.prod (isOpen_extChartAt_target (ι x₀))) hs₀ hx₀U hℓ'
      hγ hJ (fun s hs x hx ↦ ⟨hs, hγΩ hx⟩)
      ((J s₀).inChart_inChart (ι x₀) (hγΩ hx₀U))
      (h.isMaximalTotallyRealMap.fderiv_writtenInExtChartAt_injective h.two_mul_finrank hιd)
      (h.isMaximalTotallyRealMap.isMaximalTotallyReal_range_fderiv_writtenInExtChartAt hιd)
  have he₀t : e ((s₀, φ x₀), 0) = (s₀, χ (ι x₀)) := by
    rw [he, parametricAdaptedNormalExtension_apply, adaptedNormalExtension_zero]
    exact Prod.ext rfl (writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x₀))
  -- Product neighbourhoods of `(s₀, (φ x₀, 0))` in the source and `(s₀, χ (ι x₀))` in the target.
  obtain ⟨S₁, V₁, hS₁, hV₁, hs₀S₁, h₀V₁, hSV₁⟩ := isOpen_prod_iff.1
    (e.open_source.preimage (by fun_prop : Continuous fun q : P × (F × F) ↦ ((q.1, q.2.1), q.2.2)))
    s₀ (φ x₀, 0) he₀
  obtain ⟨S₂, T, hS₂, hT, hs₀S₂, hT₀, hST⟩ := isOpen_prod_iff.1 e.open_target s₀ (χ (ι x₀))
    (he₀t ▸ e.map_source he₀)
  -- The open `O₁` cutting the sources, chosen once for all parameters.
  obtain ⟨O₁, hO₁, hx₀O₁, hO₁e⟩ :=
    h.isSmoothEmbedding.isEmbedding.isInducing.exists_isOpen_extChartAt_zero_mem hV₁ h₀V₁
  set S' := S ∩ S₁ ∩ S₂
  -- For each parameter in `S'`, the slice of `e` gives an adapted chart.
  have key := fun s (hs : s ∈ S') ↦ exists_isAdaptedChart_slice (J := J)
    h.isSmoothEmbedding.contMDiff hℓ hk he hesc (fun p hp ↦ (heU hp).1.2) hO₁ hx₀O₁ fun z hz ↦
      ⟨(hO₁e z hz).1, hSV₁ (mk_mem_prod hs.1.2 (hO₁e z hz).2)⟩
  have hs₀S' : s₀ ∈ S' := ⟨⟨hs₀, hs₀S₁⟩, hs₀S₂⟩
  have : Nonempty (OpenPartialHomeomorph M (F × F)) := ⟨(key s₀ hs₀S').choose⟩
  choose! ψ hψ hψcoe hψsrc hψtgt using key
  -- The common part of the sources.
  set O := χ.source ∩ χ ⁻¹' T ∩ O₁
  have hO : IsOpen O :=
    ((continuousOn_extChartAt (ι x₀)).isOpen_inter_preimage (isOpen_extChartAt_source _) hT).inter
      hO₁
  refine ⟨S', O, e, ψ, (hS.inter hS₁).inter hS₂, hs₀S', fun s hs ↦ hs.1.1, hO,
    ⟨⟨mem_extChartAt_source _, hT₀⟩, hx₀O₁⟩, he, hec, hesc, fun s hs ↦
      ⟨hψ s hs, fun x hx ↦ (hψsrc s hs x).2 ⟨hx.1.1, hST ⟨hs.2, hx.1.2⟩, hx.2⟩, hψcoe s hs,
        hψtgt s hs⟩⟩

end TauCeti
