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

The regularity is `ℓ : ℕ∞`, and for `ℓ = ∞` the convergence, in hypothesis and conclusion, is at
every finite order. In particular, for smooth structures `J i → J₀` in `C^∞`,
the adapted charts can be chosen to converge in `C^∞`.

## Main declarations

* `TauCeti.IsTotallyRealEmbedding.exists_adaptedChart_family`: adapted charts converging in
  `C^ℓ`, for `ℓ : ℕ∞`.

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
  {ℓ : ℕ∞} {k : ℕ∞ω} {ι : N → M} {α : Type*} {l : Filter α}
  {J₀ : ContMDiffAlmostComplexStructure I ℓ M} {J : α → ContMDiffAlmostComplexStructure I ℓ M}

/-- **The model family in the extended charts.** Write `φ` and `χ` for the extended charts at `x₀`
and `ι x₀`, and `γ` for `ι` read in them. Under the hypotheses of
`TauCeti.IsTotallyRealEmbedding.exists_adaptedChart_family`, the adapted extensions of `J₀` and,
eventually, of the `J i`, read in `χ`, restrict to partial homeomorphisms `e₀` and `e i` with one
source inside the domain of `γ`, whose inverses converge in `C^ℓ` on a neighbourhood `T₀` of
`χ (ι x₀)` and which themselves converge in `C^ℓ` on the source. There
are also an open `O ∋ ι x₀` whose points of `ι (N)` have their zero-section point in the source,
and an open `W ∋ (φ x₀, 0)` that the `e i` eventually map into `χ (O)`. -/
private theorem exists_adaptedChart_family_model [IsManifold I' k N]
    (h : IsTotallyRealEmbedding I' I k J₀.almostComplexStructureAt ι) (hℓ : 1 ≤ ℓ)
    (hk : (ℓ : ℕ∞ω) + 1 ≤ k) (x₀ : N)
    (hconv : ∀ᶠ z in 𝓝 x₀,
      TendstoContDiffAt ℝ ℓ (fun i ↦ (J i).inChart (ι x₀)) (J₀.inChart (ι x₀)) l
        (extChartAt I (ι x₀) (ι z))) :
    ∃ (e₀ : OpenPartialHomeomorph (F × F) E) (e : α → OpenPartialHomeomorph (F × F) E)
      (T₀ : Set E) (O : Set M) (W : Set (F × F)),
      ⇑e₀ = adaptedNormalExtension (writtenInExtChartAt I' I x₀ ι) (J₀.inChart (ι x₀)) ∧
      ContDiffOn ℝ ℓ e₀.symm e₀.target ∧
      (∀ᶠ i in l, ⇑(e i) =
          adaptedNormalExtension (writtenInExtChartAt I' I x₀ ι) ((J i).inChart (ι x₀)) ∧
        (e i).source = e₀.source ∧ T₀ ⊆ (e i).target ∧ ContDiffOn ℝ ℓ (e i).symm (e i).target) ∧
      e₀.source ⊆ ((extChartAt I' x₀).target ∩
        (extChartAt I' x₀).symm ⁻¹' (ι ⁻¹' (extChartAt I (ι x₀)).source)) ×ˢ univ ∧
      IsOpen T₀ ∧ extChartAt I (ι x₀) (ι x₀) ∈ T₀ ∧ T₀ ⊆ e₀.target ∧
      (∀ z ∈ T₀, TendstoContDiffAt ℝ ℓ (fun i ↦ ⇑(e i).symm) e₀.symm l z) ∧
      (∀ p ∈ e₀.source, TendstoContDiffAt ℝ ℓ (fun i ↦ ⇑(e i)) e₀ l p) ∧
      IsOpen O ∧ ι x₀ ∈ O ∧
      (∀ z, ι z ∈ O → z ∈ (extChartAt I' x₀).source ∧ (extChartAt I' x₀ z, 0) ∈ e₀.source) ∧
      IsOpen W ∧ (extChartAt I' x₀ x₀, 0) ∈ W ∧
      ∀ᶠ i in l, MapsTo (e i) W
        ((extChartAt I (ι x₀)).target ∩ (extChartAt I (ι x₀)).symm ⁻¹' O) := by
  have : IsManifold I' ((ℓ : ℕ∞ω) + 1) N := IsManifold.of_le hk
  have : IsManifold I ((ℓ : ℕ∞ω) + 1) M := IsManifold.of_le (n := ∞) (by exact_mod_cast le_top)
  have hι : ContMDiff I' I ((ℓ : ℕ∞ω) + 1) ι := h.isSmoothEmbedding.contMDiff.of_le hk
  have hιd : MDifferentiableAt I' I ι x₀ := (hι x₀).mdifferentiableAt (by simp)
  set χ := extChartAt I (ι x₀)
  set φ := extChartAt I' x₀
  set γ := writtenInExtChartAt I' I x₀ ι
  obtain ⟨hU₁, hx₀U₁, hγ₁, hγΩ₁⟩ := isOpen_mem_contDiffOn_mapsTo_writtenInExtChartAt hι x₀
  -- The parameter domain `U`, shrunk to where the structures converge.
  obtain ⟨N₀, hN₀conv, hN₀, hx₀N₀⟩ := eventually_nhds_iff.1 hconv
  set U := (φ.target ∩ φ.symm ⁻¹' (ι ⁻¹' χ.source)) ∩ φ.symm ⁻¹' N₀
  have hU : IsOpen U :=
    ((continuousOn_extChartAt_symm x₀).mono inter_subset_left).isOpen_inter_preimage hU₁ hN₀
  have hx₀U : φ x₀ ∈ U := ⟨hx₀U₁, by
    rw [mem_preimage, φ.left_inv (mem_extChartAt_source x₀)]
    exact hx₀N₀⟩
  have hγ : ContDiffOn ℝ ((ℓ : ℕ∞ω) + 1) γ U := hγ₁.mono inter_subset_left
  have hγΩ : MapsTo γ U χ.target := hγΩ₁.mono_left inter_subset_left
  have hΩ : IsOpen χ.target := isOpen_extChartAt_target (ι x₀)
  have hγx₀ : γ (φ x₀) = χ (ι x₀) :=
    writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x₀)
  have hJ := Eventually.of_forall (f := l) fun i ↦ (J i).contDiffOn_inChart (ι x₀)
  have hJ₀ := J₀.contDiffOn_inChart (ι x₀)
  -- The extensions converge at every point of `U × F`.
  have hext (p : F × F) (hp : p.1 ∈ U) :=
    tendstoContDiffAt_adaptedNormalExtension hU hΩ hγ hγΩ hJ hJ₀ hp (hN₀conv (φ.symm p.1) hp.2)
  obtain ⟨e₀, e, T₀, hT₀, hγT₀, -, he₀, hp₀, hs, hT₀e₀, hc₀, hev, hlim⟩ :=
    exists_adaptedChart_family hU hΩ hx₀U hℓ hγ hγΩ hJ hJ₀
      (fun q hq ↦ hN₀conv (φ.symm q) hq.2) (J₀.inChart_inChart _ (hγΩ hx₀U))
      (h.isMaximalTotallyRealMap.fderiv_writtenInExtChartAt_injective h.two_mul_finrank hιd)
      (h.isMaximalTotallyRealMap.isMaximalTotallyReal_range_fderiv_writtenInExtChartAt hιd)
  rw [hγx₀] at hγT₀
  -- One open set `O` cuts the chart sources down near `ι x₀`.
  obtain ⟨O, hO, hx₀O, hOe⟩ :=
    h.isSmoothEmbedding.isEmbedding.isInducing.exists_isOpen_extChartAt_zero_mem e₀.open_source hp₀
  have hV : IsOpen (χ.target ∩ χ.symm ⁻¹' O) :=
    (continuousOn_extChartAt_symm (ι x₀)).isOpen_inter_preimage hΩ hO
  obtain ⟨W, hW, hp₀W, hWV⟩ := (hext (φ x₀, 0) hx₀U).exists_isOpen_eventually_mapsTo
    (by
      rw [adaptedNormalExtension_zero, hγx₀]
      refine hV.mem_nhds ⟨mem_extChartAt_target _, ?_⟩
      rw [mem_preimage, χ.left_inv (mem_extChartAt_source _)]
      exact hx₀O)
  refine ⟨e₀, e, T₀, O, W, he₀, hc₀, hev, hs.trans (prod_mono inter_subset_left subset_rfl), hT₀,
    hγT₀, hT₀e₀, hlim, fun p hp ↦ ?_, hO, hx₀O, hOe, hW, hp₀W, ?_⟩
  · rw [he₀]
    exact (hext p (hs hp).1).congr (hev.mono fun i hi ↦ hi.1.symm)
  · filter_upwards [hev, hWV] with i ⟨hei, _⟩ hWi
    rwa [hei]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- **Adapted charts from a family of adapted extensions.** For partial homeomorphisms `e i` that
are adapted extensions for the `J i`, read in the extended chart `χ` at `ι x₀`, with the common
source of `e₀`, inside the domain of `ι` read in the charts, and with `C^ℓ` inverses, there are
adapted charts `ψ i` for the `J i` built from them by
`TauCeti.exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension` with one cut-off set `O`. The
chart `ψ₀` is the value at the other indices. -/
private theorem exists_isAdaptedChart_family_of_adaptedNormalExtension [IsManifold I' k N]
    (hι : ContMDiff I' I k ι) (hℓ : 1 ≤ ℓ) (hk : (ℓ : ℕ∞ω) + 1 ≤ k) {x₀ : N}
    {e₀ : OpenPartialHomeomorph (F × F) E} (e : α → OpenPartialHomeomorph (F × F) E)
    (hs : e₀.source ⊆ ((extChartAt I' x₀).target ∩
      (extChartAt I' x₀).symm ⁻¹' (ι ⁻¹' (extChartAt I (ι x₀)).source)) ×ˢ univ)
    {O : Set M} (hO : IsOpen O) (hx₀O : ι x₀ ∈ O)
    (hOe : ∀ z, ι z ∈ O → z ∈ (extChartAt I' x₀).source ∧ (extChartAt I' x₀ z, 0) ∈ e₀.source)
    (ψ₀ : OpenPartialHomeomorph M (F × F)) :
    ∀ i, ∃ ψ : OpenPartialHomeomorph M (F × F),
      ⇑(e i) = adaptedNormalExtension (writtenInExtChartAt I' I x₀ ι) ((J i).inChart (ι x₀)) →
      (e i).source = e₀.source → ContDiffOn ℝ ℓ (e i).symm (e i).target →
      (∀ x, ψ x = (e i).symm (extChartAt I (ι x₀) x)) ∧
      (∀ p, ψ.symm p = (extChartAt I (ι x₀)).symm (e i p)) ∧
      (∀ x, x ∈ ψ.source ↔
        x ∈ (extChartAt I (ι x₀)).source ∧ extChartAt I (ι x₀) x ∈ (e i).target ∧ x ∈ O) ∧
      (∀ p, p ∈ ψ.target ↔ p ∈ (e i).source ∧ e i p ∈ (extChartAt I (ι x₀)).target ∧
        (extChartAt I (ι x₀)).symm (e i p) ∈ O) ∧
      ι x₀ ∈ ψ.source ∧ ψ (ι x₀) = (extChartAt I' x₀ x₀, 0) ∧
      IsAdaptedChart (J i) (range ι) ψ := by
  intro i
  by_cases hi : ⇑(e i) = adaptedNormalExtension (writtenInExtChartAt I' I x₀ ι)
      ((J i).inChart (ι x₀)) ∧ (e i).source = e₀.source ∧ ContDiffOn ℝ ℓ (e i).symm (e i).target
  · obtain ⟨hei, hsi, hci⟩ := hi
    obtain ⟨ψ', hψ'⟩ := exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension hι hℓ hk hei hci
      (hsi ▸ hs) hO hx₀O fun z hz ↦ hsi ▸ hOe z hz
    exact ⟨ψ', fun _ _ _ ↦ hψ'⟩
  · exact ⟨ψ₀, fun hei hsi hci ↦ (hi ⟨hei, hsi, hci⟩).elim⟩

/-- **Adapted charts converging in `C^ℓ`.** Let `ι` be a `C^k` totally real embedding for a
`C^ℓ` almost complex structure `J₀`, with `ℓ : ℕ∞` (possibly `∞`), `1 ≤ ℓ` and `ℓ + 1 ≤ k`, and
let `J i` be `C^ℓ` almost complex structures converging to `J₀` in `C^ℓ` at every point of
`ι (N)` near `ι x₀`, read in the extended chart `χ` at `ι x₀`. Then
there are an adapted chart `ψ₀` for `J₀` and, eventually along `l`, adapted charts `ψ i` for
`J i`, all defined at `ι x₀` with the same value there and with sources inside that of `χ`, such
that

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
  set χ := extChartAt I (ι x₀)
  obtain ⟨e₀, e, T₀, O, W, he₀, hc₀, hev, hs, hT₀, hγT₀, hT₀e₀, hlim, hlimΦ, hO, hx₀O, hOe, hW,
    hp₀W, hWV⟩ := exists_adaptedChart_family_model h hℓ hk x₀ hconv
  have hιc := h.isSmoothEmbedding.contMDiff
  obtain ⟨ψ₀, hψ₀, hψ₀symm, hψ₀src, hψ₀tgt, hx₀ψ₀, hψ₀x₀, hψ₀A⟩ :=
    exists_isAdaptedChart_of_coe_eq_adaptedNormalExtension hιc hℓ hk he₀ hc₀ hs hO hx₀O hOe
  choose ψ hψ using exists_isAdaptedChart_family_of_adaptedNormalExtension (J := J) hιc hℓ hk e
    hs hO hx₀O hOe ψ₀
  -- Eventually along `l` the charts come from the model extensions.
  have hψev := (hev.and hWV).mono fun i hi ↦ by
    obtain ⟨⟨hei, hes, -, hic⟩, -⟩ := id hi
    exact And.intro hi (hψ i hei hes hic)
  -- The common target `T` and forward domain `S`.
  set T := W ∩ ψ₀.target
  have hT : IsOpen T := hW.inter ψ₀.open_target
  have hTe₀ : T ⊆ e₀.source := fun p hp ↦ ((hψ₀tgt p).1 hp.2).1
  set S := T₀ ∩ (χ.target ∩ χ.symm ⁻¹' O)
  have hSΩ : S ⊆ χ.target := fun z hz ↦ hz.2.1
  have hS : IsOpen S := hT₀.inter
    ((continuousOn_extChartAt_symm _).isOpen_inter_preimage (isOpen_extChartAt_target _) hO)
  have hx₀S : χ (ι x₀) ∈ S := by
    refine ⟨hγT₀, mem_extChartAt_target _, ?_⟩
    rw [mem_preimage, χ.left_inv (mem_extChartAt_source _)]
    exact hx₀O
  have hSψ (e' : OpenPartialHomeomorph (F × F) E) (he' : T₀ ⊆ e'.target) (z : E) (hz : z ∈ S) :
      χ.symm z ∈ χ.source ∧ χ (χ.symm z) ∈ e'.target ∧ χ.symm z ∈ O :=
    ⟨χ.map_target hz.2.1, (χ.right_inv hz.2.1).symm ▸ he' hz.1, hz.2.2⟩
  refine ⟨ψ₀, ψ, T, S, hx₀ψ₀, fun x hx ↦ ((hψ₀src x).1 hx).1, hψ₀A, ?_, hT,
    ⟨by rw [hψ₀x₀]; exact hp₀W, ψ₀.map_source hx₀ψ₀⟩, inter_subset_right, ?_, hS, hx₀S, hSΩ,
    fun z hz ↦ (hψ₀src _).2 (hSψ e₀ hT₀e₀ z hz), ?_⟩
  · filter_upwards [hψev] with i ⟨⟨⟨_, hsi, hTi, _⟩, hWi⟩, _, _, hψsrc, hψtgt, hx₀ψ, hψx₀, hψA⟩
    refine ⟨hx₀ψ, fun x hx ↦ ((hψsrc x).1 hx).1, hψA, hψx₀.trans hψ₀x₀.symm, fun p hp ↦ ?_,
      fun z hz ↦ (hψsrc _).2 (hSψ (e i) hTi z hz)⟩
    have hq := hWi hp.1
    exact (hψtgt p).2 ⟨hsi ▸ hTe₀ hp, hq.1, hq.2⟩
  · -- The inverse charts read in `χ` are the extensions on `T`.
    intro p hp
    refine (hlimΦ p (hTe₀ hp)).congr_of_eqOn (hT.mem_nhds hp) ?_ fun q hq ↦ ?_
    · filter_upwards [hψev] with i ⟨⟨_, hWi⟩, _, hψsymm, _⟩ q hq
      rw [Function.comp_apply, hψsymm, χ.right_inv (hWi hq.1).1]
    · rw [Function.comp_apply, hψ₀symm, χ.right_inv ((hψ₀tgt q).1 hq.2).2.1]
  · -- The charts read in `χ` are the inverse extensions on the chart target.
    intro z hz
    refine (hlim z hz.1).congr_of_eqOn ((isOpen_extChartAt_target _).mem_nhds (hSΩ hz)) ?_
      fun w hw ↦ by rw [Function.comp_apply, hψ₀, χ.right_inv hw]
    filter_upwards [hψev] with i ⟨_, hψi, _⟩ w hw
    rw [Function.comp_apply, hψi, χ.right_inv hw]

end TauCeti
