/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.AdaptedChart.Family
public import TauCeti.Geometry.Manifold.Complex.TotallyReal.AdaptedChart

/-!
# Converging families of adapted charts along a totally real embedding

Let `ι : N → M` be a totally real embedding for a `C^ℓ` almost complex structure `J₀` on a
boundaryless manifold `M`, with `1 ≤ ℓ`, and let `J i` be `C^ℓ` almost complex structures with
`J i → J₀` in `C^ℓ` along the image of `ι` near `ι x₀`, read in the extended chart `χ` at
`ι x₀`. This file chooses the adapted charts of `TauCeti.IsTotallyRealEmbedding.exists_adaptedChart`
for `J₀` and, eventually along the filter, for every `J i` (`TauCeti.IsAdaptedChart`: flattening
`ι (N)`, intertwining the structure with the standard one along `ι (N)`, standard pushforward on
the zero section) so that they converge in `C^ℓ`:

* the targets of the charts `ψ i` all contain one open neighbourhood `T` of `ψ₀ (ι x₀)`, and on
  `T` the inverse charts, read in `χ`, converge to that of `ψ₀` in `C^ℓ`;
* the sources of the charts all contain the image under `χ⁻¹` of one open neighbourhood `S` of
  `χ (ι x₀)`, and on `S` the charts, read in `χ`, converge to `ψ₀` in `C^ℓ`.

This is the last clause of McDuff–Salamon Exercise B.4.10. The charts are those of the model
construction `TauCeti.exists_adaptedChart_family` in the extended charts at `x₀` and `ι x₀`. Its
adapted extensions share one source, so the shrinking of the chart sources that makes them meet
`ι (N)` only near `ι x₀` can be done once for the whole family
(`TauCeti.exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension`).
Convergence is `TauCeti.TendstoContDiffAt`: continuous convergence of the derivatives of order at
most `ℓ`, which on open sets is locally uniform convergence of these derivatives.

## Main declarations

* `TauCeti.IsTotallyRealEmbedding.exists_adaptedChart_family`: adapted charts converging in
  `C^ℓ`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Exercise B.4.10.
-/

public section

open Set Filter Manifold
open scoped Topology Manifold ContDiff

namespace TauCeti

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ F H'} [I'.Boundaryless] [TopologicalSpace N] [ChartedSpace H' N]
  {ℓ : ℕ} {k : ℕ∞ω} {ι : N → M} {α : Type*} {l : Filter α}
  {J₀ : ContMDiffAlmostComplexStructure I ℓ M} {J : α → ContMDiffAlmostComplexStructure I ℓ M}

/-- **Adapted charts converging in `C^ℓ`.** Let `ι` be a `C^k` totally real embedding for a
`C^ℓ` almost complex structure `J₀`, with `1 ≤ ℓ` and `ℓ + 1 ≤ k`, and let `J i` be `C^ℓ`
almost complex structures converging to `J₀` in `C^ℓ` at every point of `ι (N)` near `ι x₀`, read
in the extended chart `χ` at `ι x₀`. Then there are an adapted chart `ψ₀` for `J₀` and,
eventually along `l`, adapted charts `ψ i` for `J i`, all defined at `ι x₀` with the same value
there and with sources inside that of `χ`, such that

* the targets of all of them contain one open neighbourhood `T` of `ψ₀ (ι x₀)`, on which
  `χ ∘ (ψ i)⁻¹ → χ ∘ ψ₀⁻¹` in `C^ℓ`;
* their sources all contain `χ⁻¹ (S)` for one open neighbourhood `S ⊆ χ.target` of `χ (ι x₀)`,
  on which `ψ i ∘ χ⁻¹ → ψ₀ ∘ χ⁻¹` in `C^ℓ`. -/
theorem IsTotallyRealEmbedding.exists_adaptedChart_family [IsManifold I' k N]
    (h : IsTotallyRealEmbedding I' I k J₀.almostComplexStructureAt ι) (hℓ : 1 ≤ ℓ)
    (hk : (ℓ : ℕ∞ω) + 1 ≤ k) (x₀ : N)
    (hconv : ∀ᶠ z in 𝓝 x₀,
      TendstoContDiffAt ℝ ℓ (fun i ↦ (J i).inChart (ι x₀)) (J₀.inChart (ι x₀)) l
        (extChartAt I (ι x₀) (ι z))) :
    ∃ (ψ₀ : OpenPartialHomeomorph M (F × F)) (ψ : α → OpenPartialHomeomorph M (F × F))
      (T : Set (F × F)) (S : Set E),
      ι x₀ ∈ ψ₀.source ∧ ψ₀.source ⊆ (extChartAt I (ι x₀)).source ∧
      IsAdaptedChart J₀ (range ι) ψ₀ ∧
      (∀ᶠ i in l, ι x₀ ∈ (ψ i).source ∧ (ψ i).source ⊆ (extChartAt I (ι x₀)).source ∧
        IsAdaptedChart (J i) (range ι) (ψ i) ∧ ψ i (ι x₀) = ψ₀ (ι x₀) ∧ T ⊆ (ψ i).target ∧
        MapsTo (extChartAt I (ι x₀)).symm S (ψ i).source) ∧
      IsOpen T ∧ ψ₀ (ι x₀) ∈ T ∧ T ⊆ ψ₀.target ∧
      (∀ p ∈ T, TendstoContDiffAt ℝ ℓ (fun i ↦ extChartAt I (ι x₀) ∘ (ψ i).symm)
        (extChartAt I (ι x₀) ∘ ψ₀.symm) l p) ∧
      IsOpen S ∧ extChartAt I (ι x₀) (ι x₀) ∈ S ∧ S ⊆ (extChartAt I (ι x₀)).target ∧
      MapsTo (extChartAt I (ι x₀)).symm S ψ₀.source ∧
      ∀ z ∈ S, TendstoContDiffAt ℝ ℓ (fun i ↦ ψ i ∘ (extChartAt I (ι x₀)).symm)
        (ψ₀ ∘ (extChartAt I (ι x₀)).symm) l z := by
  -- Regularity bookkeeping, as for a single adapted chart.
  have hk' : (((ℓ : ℕ∞) : ℕ∞ω)) + 1 ≤ k := by exact_mod_cast hk
  have hℓ' : (1 : ℕ∞) ≤ ℓ := by exact_mod_cast hℓ
  have : IsManifold I' ((ℓ : ℕ∞ω) + 1) N := IsManifold.of_le hk
  have : IsManifold I ((ℓ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hι : ContMDiff I' I ((ℓ : ℕ∞ω) + 1) ι := h.isSmoothEmbedding.contMDiff.of_le hk
  have hιd : MDifferentiableAt I' I ι x₀ := (hι x₀).mdifferentiableAt (by simp)
  set y := ι x₀
  set χ := extChartAt I y
  set φ := extChartAt I' x₀
  set γ := writtenInExtChartAt I' I x₀ ι
  obtain ⟨hU₁, hx₀U₁, hγ₁, hγΩ₁⟩ := isOpen_mem_contDiffOn_mapsTo_writtenInExtChartAt hι x₀
  -- The parameter domain, shrunk to where the structures converge.
  obtain ⟨N₀, hN₀conv, hN₀, hx₀N₀⟩ := eventually_nhds_iff.1 hconv
  set U := (φ.target ∩ φ.symm ⁻¹' (ι ⁻¹' χ.source)) ∩ φ.symm ⁻¹' N₀
  have hU : IsOpen U :=
    ((continuousOn_extChartAt_symm x₀).mono inter_subset_left).isOpen_inter_preimage hU₁ hN₀
  have hx₀U : φ x₀ ∈ U := ⟨hx₀U₁, by
    rw [mem_preimage, φ.left_inv (mem_extChartAt_source x₀)]
    exact hx₀N₀⟩
  have hγ : ContDiffOn ℝ ((ℓ : ℕ∞ω) + 1) γ U := hγ₁.mono inter_subset_left
  have hγΩ : MapsTo γ U χ.target := hγΩ₁.mono_left inter_subset_left
  have hΩ : IsOpen χ.target := isOpen_extChartAt_target y
  have hγx₀ : γ (φ x₀) = χ y := writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x₀)
  have hJ (i : α) : ContDiffOn ℝ ℓ ((J i).inChart y) χ.target := (J i).contDiffOn_inChart y
  have hJ₀ : ContDiffOn ℝ ℓ (J₀.inChart y) χ.target := J₀.contDiffOn_inChart y
  have hconv' (q : F) (hq : q ∈ U) :
      TendstoContDiffAt ℝ ℓ (fun i ↦ (J i).inChart y) (J₀.inChart y) l (γ q) :=
    hN₀conv (φ.symm q) hq.2
  -- The model family of adapted charts.
  obtain ⟨e₀, e, T₀, hT₀, hγT₀, hT₀Ω, he₀, hp₀, hs, hT₀e₀, hc₀, hev, hlim⟩ :=
    TauCeti.exists_adaptedChart_family (J := fun i ↦ (J i).inChart y) hU hΩ hx₀U hℓ hγ hγΩ
      (Eventually.of_forall hJ) hJ₀ hconv' (J₀.inChart_inChart y (hγΩ hx₀U))
      (h.isMaximalTotallyRealMap.fderiv_writtenInExtChartAt_injective h.two_mul_finrank hιd)
      (h.isMaximalTotallyRealMap.isMaximalTotallyReal_range_fderiv_writtenInExtChartAt hιd)
  rw [hγx₀] at hγT₀
  have hs₁ : e₀.source ⊆ (φ.target ∩ φ.symm ⁻¹' (ι ⁻¹' χ.source)) ×ˢ univ :=
    hs.trans (prod_mono inter_subset_left subset_rfl)
  -- One open set `O` cuts the sources of all the charts down near `ι x₀`.
  obtain ⟨O, hO, hx₀O, hOe⟩ :=
    h.isSmoothEmbedding.isEmbedding.isInducing.exists_isOpen_extChartAt_zero_mem e₀.open_source hp₀
  -- The limit chart.
  obtain ⟨ψ₀, hψ₀, hψ₀symm, hψ₀src, hψ₀tgt, hx₀ψ₀, hψ₀x₀, hψ₀A⟩ :=
    exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension h.isSmoothEmbedding.contMDiff hℓ' hk'
      he₀ hc₀ hs₁ hO hx₀O hOe
  -- The charts of the family, chosen wherever the model extension is available. At the other
  -- indices `ψ₀` is a placeholder: the conclusions only concern indices eventually along `l`,
  -- where `hev` makes the model extension available.
  have hex (i : α) : ∃ ψ' : OpenPartialHomeomorph M (F × F),
      (⇑(e i) = adaptedNormalExtension γ ((J i).inChart y) ∧ (e i).source = e₀.source ∧
        ContDiffOn ℝ ℓ (e i).symm (e i).target) →
      (∀ x, ψ' x = (e i).symm (χ x)) ∧ (∀ p, ψ'.symm p = χ.symm (e i p)) ∧
      (∀ x, x ∈ ψ'.source ↔ x ∈ χ.source ∧ χ x ∈ (e i).target ∧ x ∈ O) ∧
      (∀ p, p ∈ ψ'.target ↔ p ∈ (e i).source ∧ e i p ∈ χ.target ∧ χ.symm (e i p) ∈ O) ∧
      y ∈ ψ'.source ∧ ψ' y = (φ x₀, 0) ∧ IsAdaptedChart (J i) (range ι) ψ' := by
    by_cases hi : ⇑(e i) = adaptedNormalExtension γ ((J i).inChart y) ∧
      (e i).source = e₀.source ∧ ContDiffOn ℝ ℓ (e i).symm (e i).target
    · obtain ⟨hei, hsi, hci⟩ := hi
      obtain ⟨ψ', hψ'⟩ := exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension
        h.isSmoothEmbedding.contMDiff hℓ' hk' hei hci (hsi ▸ hs₁) hO hx₀O
        (fun z hz ↦ hsi ▸ hOe z hz)
      exact ⟨ψ', fun _ ↦ hψ'⟩
    · exact ⟨ψ₀, fun h' ↦ (hi h').elim⟩
  choose ψ hψ using hex
  -- Eventually along `l` the charts come from the model extensions.
  have hψev := hev.mono fun i hi ↦ And.intro hi (hψ i ⟨hi.1, hi.2.1, hi.2.2.2⟩)
  -- The common target `T`: near `(φ x₀, 0)` the extensions eventually land in `χ (O)`.
  have hV : IsOpen (χ.target ∩ χ.symm ⁻¹' O) :=
    (continuousOn_extChartAt_symm y).isOpen_inter_preimage hΩ hO
  have hmem : χ y ∈ χ.target ∩ χ.symm ⁻¹' O :=
    ⟨mem_extChartAt_target y, by
      rw [mem_preimage, χ.left_inv (mem_extChartAt_source y)]
      exact hx₀O⟩
  obtain ⟨W, hW, hp₀W, hWV⟩ :=
    (tendstoContDiffAt_adaptedNormalExtension (p := (φ x₀, 0)) hU hΩ hγ hγΩ
      (Eventually.of_forall hJ) hJ₀ hx₀U (hconv' (φ x₀) hx₀U)).exists_isOpen_eventually_mapsTo
      (by rw [adaptedNormalExtension_zero, hγx₀]; exact hV.mem_nhds hmem)
  set T := W ∩ ψ₀.target
  have hT : IsOpen T := hW.inter ψ₀.open_target
  have hTψ₀ : T ⊆ ψ₀.target := inter_subset_right
  have hTe₀ : T ⊆ e₀.source := fun p hp ↦ ((hψ₀tgt p).1 hp.2).1
  -- The common forward domain `S`.
  set S := T₀ ∩ (χ.target ∩ χ.symm ⁻¹' O)
  have hS : IsOpen S := hT₀.inter hV
  have hSΩ : S ⊆ χ.target := fun z hz ↦ hz.2.1
  have hψT : ∀ᶠ i in l, T ⊆ (ψ i).target := by
    filter_upwards [hψev, hWV] with i hi hWi p hp
    obtain ⟨⟨hei, hsi, -, -⟩, -, -, -, hψtgt, -⟩ := hi
    have hq : e i p ∈ χ.target ∩ χ.symm ⁻¹' O := by
      rw [hei]
      exact hWi hp.1
    exact (hψtgt p).2 ⟨hsi ▸ hTe₀ hp, hq.1, hq.2⟩
  have hSψ : ∀ x ∈ χ.symm '' S, ∀ (e' : OpenPartialHomeomorph (F × F) E), T₀ ⊆ e'.target →
      x ∈ χ.source ∧ χ x ∈ e'.target ∧ x ∈ O := by
    rintro _ ⟨z, hz, rfl⟩ e' he'
    refine ⟨χ.map_target hz.2.1, ?_, hz.2.2⟩
    rw [χ.right_inv hz.2.1]
    exact he' hz.1
  refine ⟨ψ₀, ψ, T, S, hx₀ψ₀, fun x hx ↦ ((hψ₀src x).1 hx).1, hψ₀A, ?_, hT,
    ⟨by rw [hψ₀x₀]; exact hp₀W, ψ₀.map_source hx₀ψ₀⟩, hTψ₀, ?_, hS, ⟨hγT₀, hmem⟩, hSΩ,
    fun z hz ↦ (hψ₀src _).2 (hSψ _ (mem_image_of_mem _ hz) e₀ hT₀e₀), ?_⟩
  · filter_upwards [hψev, hψT] with i hi hTψi
    obtain ⟨⟨-, -, hTi, -⟩, -, -, hψsrc, -, hx₀ψ, hψx₀, hψA⟩ := hi
    exact ⟨hx₀ψ, fun x hx ↦ ((hψsrc x).1 hx).1, hψA, hψx₀.trans hψ₀x₀.symm, hTψi,
      fun z hz ↦ (hψsrc _).2 (hSψ _ (mem_image_of_mem _ hz) (e i) hTi)⟩
  · -- The inverse charts read in `χ` are the extensions on `T`.
    intro p hp
    have hpU : p.1 ∈ U := (hs (hTe₀ hp)).1
    have hlimp := (tendstoContDiffAt_adaptedNormalExtension (p := p) hU hΩ hγ hγΩ
      (Eventually.of_forall hJ) hJ₀ hpU (hconv' p.1 hpU)).congr
      (hev.mono fun i hi ↦ hi.1.symm)
    rw [← he₀] at hlimp
    refine hlimp.congr_of_eqOn (hT.mem_nhds hp) ?_ fun q hq ↦ ?_
    · filter_upwards [hψev, hψT] with i hi hTψi q hq
      obtain ⟨-, -, hψsymm, -, hψtgt, -⟩ := hi
      rw [Function.comp_apply, hψsymm, χ.right_inv ((hψtgt q).1 (hTψi hq)).2.1]
    · rw [Function.comp_apply, hψ₀symm, χ.right_inv ((hψ₀tgt q).1 (hTψ₀ hq)).2.1]
  · -- The charts read in `χ` are the inverse extensions on the chart target.
    intro z hz
    refine (hlim z hz.1).congr_of_eqOn (hΩ.mem_nhds (hSΩ hz)) ?_ fun w hw ↦ ?_
    · filter_upwards [hψev] with i hi w hw
      obtain ⟨-, hψi, -⟩ := hi
      rw [Function.comp_apply, hψi, χ.right_inv hw]
    · rw [Function.comp_apply, hψ₀, χ.right_inv hw]

end TauCeti
