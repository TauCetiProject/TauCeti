/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Analysis.Sobolev.Wkp.FiniteCover
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Wkp
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Smooth sections are dense in `W^{k,p}(V)`

Let `M` be a Hausdorff smooth manifold without boundary modelled on a finite-dimensional real inner
product space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre
`F`, and let `A` be a finite bundle atlas (so `M` is compact). This file shows that for
`1 ≤ p < ∞` and every order `k` the `C^∞` sections of `V` are dense in the Sobolev space
`W^{k,p}(V)` of `TauCeti.SobolevSection A μ p k`
(`TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff`,
`TauCeti.SobolevSection.denseRange_ofContMDiffSection_comp_ofLE`), and hence so are the `Cᵏ`
sections (`TauCeti.SobolevSection.denseRange_ofContMDiffSection`). The exponent must be finite:
smooth functions are not dense in `W^{1,∞}`, as `|x|` on an interval shows.

Both arguments localize with a smooth partition of unity `χ` subordinate to the chart domains of
`A`: every `w` is the finite sum of the products `χ i • w`
(`TauCeti.SobolevSection.sum_contMDiffSMulL_eq_self_of_sum_eq_one`), and it suffices to approximate
an element supported in the domain of one chart `i`. Its chart-`i` components are approximated by
functions smooth on the chart image (Meyers–Serrin), and these, multiplied by a smooth cutoff `ψ`
supported in the chart domain, are the chart readings of `C^∞` sections
(`TauCeti.FiniteBundleAtlas.contMDiff_smul_chartSection`). What remains is to control the error in
all charts at once by its chart-`i` components.

The unconditional argument does this with the estimate
`TauCeti.SobolevSection.exists_norm_contMDiffSMulL_le`: for a smooth `χ` whose support has closure
in the domain of chart `i`, the norm of `χ • w` in `W^{k,p}(V)` is at most a constant times the norm
of the chart-`i` components of `w`. In chart `j`, the image of chart `j` is covered by a piece on
which the chart-`j` data of `χ • w` are transferred from chart `i` by the continuous map
`TauCeti.FiniteBundleAtlas.transferL`, and an open set on which they vanish
(`TauCeti.FiniteBundleAtlas.exists_transfer_piece`); the norm on chart `j` is bounded by the norms
on the two pieces (`TauCeti.Wkp.norm_le_norm_restrictL_add_norm_restrictL`).

Alternatively, an element `u` vanishing off a closed subset `L` of the domain of chart `i` is the
extension by zero `TauCeti.SobolevSection.extendByZeroL` of its chart-`i` components, whenever
`W^{k,p}(V)` admits extension by zero from a single chart
(`TauCeti.SobolevSection.HasExtensionByZero`), and extension by zero is continuous. Over surfaces
(`E = ℂ`, with Lebesgue measure) extension by zero holds for `Cⁿ` bundles at every order `k ≤ n`
(`TauCeti.SobolevSection.hasExtensionByZero`), by the invariance of the local Sobolev classes under
changes of chart and trivialization
(`TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm`).

## Main results

* `TauCeti.SobolevSection.mem_range_ofContMDiffSection_comp_ofLE_iff`: the elements of
  `W^{k,p}(V)` given by `C^∞` sections are those whose chart data are the coordinates of a `C^∞`
  section.
* `TauCeti.SobolevSection.denseRange_ofContMDiffSection_comp_ofLE_of_hasExtensionByZero`,
  `TauCeti.SobolevSection.denseRange_ofContMDiffSection_of_hasExtensionByZero`: under extension by
  zero, `C^∞` sections, and hence `Cᵏ` sections, are dense in `W^{k,p}(V)` for `1 ≤ p < ∞`.
* `TauCeti.SobolevSection.exists_norm_contMDiffSMulL_le`: sections cut off inside one chart are
  controlled in `W^{k,p}(V)` by their components in that chart.
* `TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff`,
  `TauCeti.SobolevSection.denseRange_ofContMDiffSection_comp_ofLE`: the `C^∞` sections are dense in
  `W^{k,p}(V)` for every `k` and `1 ≤ p < ∞`.
* `TauCeti.SobolevSection.denseRange_ofContMDiffSection`: the `Cᵏ` sections are dense.
* `TauCeti.SobolevSection.denseRange_ofExponentLEL`: lowering the exponent has dense range.
* `TauCeti.SobolevSection.hasExtensionByZero`: over surfaces, extension by zero holds for `Cⁿ`
  bundles at orders `k ≤ n`; `hasExtensionByZero_of_le_one` is the case
  `k ≤ 1` for `C¹` bundles.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces of sections).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* N. G. Meyers and J. Serrin, *H = W*, Proc. Nat. Acad. Sci. USA **51** (1964), 1055–1056.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace TauCeti

open FiniteBundleAtlas

namespace SobolevSection

section General

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {k : ℕ} [IsManifold 𝓘(ℝ, E) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

/-- The elements of `W^{k,p}(V)` given by `C^∞` sections are those whose chart data are the
coordinates of a `C^∞` section. -/
theorem mem_range_ofContMDiffSection_comp_ofLE_iff {w : SobolevSection A μ p k} :
    w ∈ LinearMap.range ((ofContMDiffSection A μ p k).comp
      (ContMDiffSection.ofLE (I := 𝓘(ℝ, E)) (F := F) (V := V) ENat.LEInfty.out)) ↔
      ∃ s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯, ∀ i,
        A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s := by
  have h (s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯) (i : Fin A.n) := chartValueL_ofContMDiffSection_ae A μ p k
    (ContMDiffSection.ofLE ENat.LEInfty.out s) i
  simp only [ContMDiffSection.coe_ofLE] at h
  refine ⟨?_, fun ⟨s, hs⟩ ↦ ⟨s, eq_of_ae_eq_coord (h s) hs⟩⟩
  rintro ⟨s, rfl⟩
  exact ⟨s, h s⟩

/-- **A `C^∞` section built in one chart.** Let `ψ` be smooth with `tsupport ψ` inside the domain
of chart `i`, and let `v j` be chart-`i` Sobolev functions represented by functions `f j` smooth on
the chart image. Then `ψ` times the section with chart-`i` coordinates `∑ j, f j • finBasis ℝ F j`
is a `C^∞` section; its element of `W^{k,p}(V)` vanishes off `tsupport ψ`, and its chart-`i`
components are the products of the `v j` with `ψ` read in chart `i`. -/
private theorem exists_mem_range_value_ae {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) (hψi : tsupport ψ ⊆ A.dom i)
    {v : Fin (finrank ℝ F) → Wkp μ (A.image i) p k} {f : Fin (finrank ℝ F) → E → ℝ}
    (hf : ∀ j, ContDiffOn ℝ ∞ (f j) (A.image i))
    (hvf : ∀ j, (Wkp.value k (v j) : E → ℝ) =ᵐ[μ.restrict (A.image i)] f j) :
    ∃ a ∈ LinearMap.range ((ofContMDiffSection A μ p k).comp
      (ContMDiffSection.ofLE (I := 𝓘(ℝ, E)) (F := F) (V := V) ENat.LEInfty.out)),
      a ∈ aeZeroOff A μ p k (tsupport ψ) ∧ ∀ j,
        (Wkp.value k ((a : A.sectionChartData.SobolevData μ p k) i j) : E → ℝ)
          =ᵐ[μ.restrict (A.image i)] fun y ↦ ψ ((A.chart i).symm y) * Wkp.value k (v j) y := by
  obtain ⟨G, hG⟩ : ∃ G : E → F, ∀ y, G y = ∑ j, f j y • finBasis ℝ F j := ⟨_, fun _ ↦ rfl⟩
  have hGs : ContDiffOn ℝ ∞ G (A.image i) := by
    rw [funext hG]
    exact ContDiffOn.sum fun j _ ↦ (hf j).smul contDiffOn_const
  obtain ⟨s, hs⟩ : ∃ s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯, ⇑s = fun x ↦ ψ x • A.chartSection i G x :=
    ⟨⟨_, contMDiff_smul_chartSection hψ (A.image i).isOpen
      (hψi.trans (A.dom_subset_dom_inter_preimage_image i)) hGs⟩, rfl⟩
  have has (i' : Fin A.n) := chartValueL_ofContMDiffSection_ae A μ p k
    (ContMDiffSection.ofLE ENat.LEInfty.out s) i'
  simp only [ContMDiffSection.coe_ofLE, hs] at has
  refine ⟨_, ⟨s, rfl⟩, mem_aeZeroOff_of_ae_eq_coord has fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul], fun j ↦ ?_⟩
  filter_upwards [value_ae_eq_repr_coord (has i) j, hvf j,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h1 h2 hy
  rw [LinearMap.comp_apply, h1, A.coord_fun_smul i ψ _ hy, coord_chartSection G hy, hG, map_smul,
    Finsupp.smul_apply, (finBasis ℝ F).repr_sum_self, smul_eq_mul, h2]

/-- **The localized density step.** An element vanishing off a closed subset `L` of the domain of
chart `i` is a limit of elements given by `C^∞` sections. Take a smooth cutoff `ψ` equal to one on
`L` with support in the chart domain, approximate the chart-`i` components by functions smooth on
the chart image (Meyers–Serrin), and multiply them by `ψ`: these are the chart readings of smooth
sections vanishing off `tsupport ψ`, and extension by zero is continuous. -/
private theorem mem_closure_range_of_mem_aeZeroOff [T2Space M] (hp : p ≠ ⊤)
    (h : HasExtensionByZero A μ p k) {i : Fin A.n} {L : Set M} (hL : IsClosed L)
    (hLi : L ⊆ A.dom i) {u : SobolevSection A μ p k} (hu : u ∈ aeZeroOff A μ p k L) :
    u ∈ Submodule.topologicalClosure (LinearMap.range ((ofContMDiffSection A μ p k).comp
      (ContMDiffSection.ofLE (I := 𝓘(ℝ, E)) (F := F) (V := V) ENat.LEInfty.out))) := by
  have := A.compactSpace
  -- A smooth cutoff `ψ`, equal to one on `L`, with support in the domain of chart `i`.
  obtain ⟨O, hO, hLO, hOi⟩ := normal_exists_closure_subset hL (A.isOpen_dom i) hLi
  obtain ⟨ψ, hψ, -, hψO, hψL⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, E) (n := ⊤) hO hL hLO
  have hψi : tsupport ψ ⊆ A.dom i := by rw [tsupport, hψO]; exact hOi
  have hLψ : L ⊆ tsupport ψ := fun x hx ↦ subset_tsupport ψ (by
    rw [Function.mem_support, (hψL x).1 hx]; exact one_ne_zero)
  have hu' := aeZeroOff_mono hLψ hu
  -- Multiplication by `ψ`, read in chart `i`, on the chart-`i` Sobolev functions.
  let T : Wkp μ (A.image i) p k →L[ℝ] Wkp μ (A.image i) p k :=
    Wkp.contDiffOnSMulL (A.chart i).open_target.uniqueDiffOn (A.isCompact_closure_image i)
      (A.closure_image_subset_target i) k (A.contDiffOn_comp_chart_symm hψ i)
  have hT (v : Wkp μ (A.image i) p k) : (Wkp.value k (T v) : E → ℝ)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ ψ ((A.chart i).symm y) * Wkp.value k v y :=
    Wkp.value_contDiffOnSMulL_ae _ _ _ k _ v
  -- `T` fixes the chart-`i` components of `u`, since `ψ = 1` on `L`.
  set ui : Fin (finrank ℝ F) → Wkp μ (A.image i) p k :=
    ((u : SobolevSection A μ p k) : A.sectionChartData.SobolevData μ p k) i
  have hTu (j : Fin (finrank ℝ F)) : T (ui j) = ui j := Wkp.ext k <| Lp.ext <| by
    filter_upwards [hT (ui j), mem_chartAeZeroOff.1 (mem_chartAeZeroOff_of_mem_aeZeroOff hu i) j]
      with y h1 h2
    rw [h1]
    by_cases hy : (A.chart i).symm y ∈ L
    · rw [(hψL _).1 hy, one_mul]
    · rw [h2 hy, mul_zero]
  -- Meyers–Serrin approximations of the chart-`i` components, multiplied by `ψ`.
  choose v f hf hvf hlim using fun j ↦ Wkp.exists_contDiffOn_approximation hp k (ui j)
  choose a ha haψ hav using fun m ↦
    exists_mem_range_value_ae hψ hψi (v := fun j ↦ v j m) (fun j ↦ hf j m) fun j ↦ hvf j m
  -- Convergence of the chart-`i` components, then of the extensions by zero.
  have hconv : Tendsto (fun m ↦ chartRestrictL A μ p k i (tsupport ψ) ⟨a m, haψ m⟩) atTop
      (𝓝 (chartRestrictL A μ p k i (tsupport ψ) ⟨u, hu'⟩)) := by
    refine tendsto_subtype_rng.2 (tendsto_pi_nhds.2 fun j ↦ ?_)
    have hcomp (m : ℕ) : ((a m : SobolevSection A μ p k) :
        A.sectionChartData.SobolevData μ p k) i j = T (v j m) :=
      Wkp.ext k (Lp.ext ((hav m j).trans (hT (v j m)).symm))
    simp only [coe_chartRestrictL_apply, hcomp]
    have hT' := (T.continuous.tendsto _).comp (hlim j)
    rw [hTu j] at hT'
    exact hT'
  have hE := tendsto_subtype_rng.1 (tendsto_of_tendsto_chartRestrictL h (isClosed_tsupport ψ) hψi
    hconv)
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hE
    (Eventually.of_forall fun m ↦ Submodule.le_topologicalClosure _ (ha m))

/-- **Density of `C^∞` sections, assuming extension by zero.** For `1 ≤ p < ∞`, the elements of
`W^{k,p}(V)` given by `C^∞` sections are dense, provided `W^{k,p}(V)` admits extension by zero
from a single chart (`TauCeti.SobolevSection.HasExtensionByZero`). -/
theorem denseRange_ofContMDiffSection_comp_ofLE_of_hasExtensionByZero [T2Space M] (hp : p ≠ ⊤)
    (h : HasExtensionByZero A μ p k) :
    DenseRange ((ofContMDiffSection A μ p k).comp
      (ContMDiffSection.ofLE (I := 𝓘(ℝ, E)) (F := F) (V := V) ENat.LEInfty.out)) := by
  have := A.compactSpace
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ A.dom
    A.isOpen_dom (by rw [A.iUnion_dom])
  intro w
  rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe, SetLike.mem_coe,
    ← sum_contMDiffSMulL_eq_self_of_sum_eq_one (fun i ↦ (χ i).contMDiff)
      (fun x ↦ by simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)) w]
  exact Submodule.sum_mem _ fun i _ ↦ mem_closure_range_of_mem_aeZeroOff hp h
    (isClosed_tsupport _) (hχ i) (contMDiffSMulL_mem_aeZeroOff _ w)

/-- **Density of `Cᵏ` sections, assuming extension by zero.** For `1 ≤ p < ∞`, the elements of
`W^{k,p}(V)` given by `Cᵏ` sections are dense, provided `W^{k,p}(V)` admits extension by zero from
a single chart. -/
theorem denseRange_ofContMDiffSection_of_hasExtensionByZero [T2Space M] (hp : p ≠ ⊤)
    (h : HasExtensionByZero A μ p k) : DenseRange (ofContMDiffSection A μ p k) :=
  (denseRange_ofContMDiffSection_comp_ofLE_of_hasExtensionByZero hp h).mono <| by
    rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩

end General

section Unconditional

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {k : ℕ} [IsManifold 𝓘(ℝ, E) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

variable [T2Space M]

/-- **Sections supported in one chart are controlled by that chart.** Let `1 ≤ p ≤ ∞` and let `χ`
be a smooth function whose support has closure inside the domain of chart `i`. Then the norm of
`χ • w` in `W^{k,p}(V)` is bounded by a constant multiple of the norm of the chart-`i` components
of `w`, the constant depending on `χ` but not on `w`. -/
theorem exists_norm_contMDiffSMulL_le {i : Fin A.n} {χ : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ χ) (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C, ∀ w : SobolevSection A μ p k,
      ‖contMDiffSMulL A μ p k hχ w‖ ≤ C * ‖(w : A.sectionChartData.SobolevData μ p k) i‖ := by
  have := A.compactSpace
  have := ChartedSpace.locallyCompactSpace E M
  have hK : IsCompact (tsupport χ) := (isClosed_tsupport χ).isCompact
  obtain ⟨U, hU, hKU, hUi, -⟩ :=
    exists_open_between_and_isCompact_closure hK (A.isOpen_dom i) hχi
  choose P R hP hPc hPD hPQ hR hcov hRK using fun j ↦ A.exists_transfer_piece hKU hU hUi hK j
  -- Multiplication by `χ` read in chart `i`, and the transfers from chart `i` to the charts `j`.
  set L := Wkp.contDiffOnSMulL (mu := μ) (p := p) (A.chart i).open_target.uniqueDiffOn
    (A.isCompact_closure_image i) (A.closure_image_subset_target i) k
    (A.contDiffOn_comp_chart_symm hχ i)
  refine ⟨∑ j, ∑ _m : Fin (finrank ℝ F),
    ‖A.transferL μ p k i j (hPc j) (hPD j) (hPQ j)‖ * ‖L‖, fun w ↦ ?_⟩
  set v := contMDiffSMulL A μ p k hχ w
  have hvi : ‖(v : A.sectionChartData.SobolevData μ p k) i‖ ≤
      ‖L‖ * ‖(w : A.sectionChartData.SobolevData μ p k) i‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun l ↦ ?_
    rw [contMDiffSMulL_apply]
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm _ l) (norm_nonneg _))
  simp only [Finset.sum_mul]
  refine A.sectionChartData.norm_le_sum_of_norm_le μ p k fun (j : Fin A.n) m ↦ ?_
  have hPj : P j ≤ A.image j := SetLike.coe_subset_coe.1 ((hP j).trans (A.overlap_subset_image i j))
  refine (Wkp.norm_le_norm_restrictL_add_norm_restrictL hPj (hR j) (hcov j) k _).trans ?_
  -- Away from the image of the support of `χ`, the components of `χ • w` vanish.
  have hzero : Wkp.restrictL (hR j) k ((v : A.sectionChartData.SobolevData μ p k) j m) = 0 := by
    refine Wkp.ext k (Lp.ext ?_)
    filter_upwards [Wkp.value_restrictL_ae (hR j) k
        ((v : A.sectionChartData.SobolevData μ p k) j m),
      ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (hR j))
        (value_contMDiffSMulL_ae hχ w j m),
      ae_restrict_mem (R j).isOpen.measurableSet,
      (Lp.coeFn_zero ℝ p (μ.restrict (R j : Set E)))] with y h₁ h₂ hy h₃
    rw [h₁, ← Wkp.valueL_apply k (0 : Wkp μ (R j) p k), map_zero, h₃, Pi.zero_apply]
    exact h₂.trans (by rw [image_eq_zero_of_notMem_tsupport (hRK j y hy), zero_mul])
  -- On the transfer piece, they are the transfer of the chart-`i` components of `χ • w`.
  rw [hzero, norm_zero, add_zero,
    A.restrictL_eq_transferL μ p k v.property (hP j) (hPc j) (hPD j) le_rfl (hPQ j) m]
  calc _ ≤ ‖A.transferL μ p k i j (hPc j) (hPD j) (hPQ j)‖ *
        ‖fun l ↦ Wkp.restrictL (le_rfl : A.image i ≤ A.image i) k
          ((v : A.sectionChartData.SobolevData μ p k) i l)‖ :=
        (norm_le_pi_norm _ m).trans (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ ‖A.transferL μ p k i j (hPc j) (hPD j) (hPQ j)‖ *
        (‖L‖ * ‖(w : A.sectionChartData.SobolevData μ p k) i‖) := by
        refine mul_le_mul_of_nonneg_left (le_trans ?_ hvi) (norm_nonneg _)
        exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l ↦
          (Wkp.norm_restrictL_le _ k _).trans (norm_le_pi_norm _ l)
    _ = _ := (mul_assoc _ _ _).symm

variable (A μ p k) in
/-- The Sobolev sections of the `C^∞` sections of `V`. -/
private def smoothSubmodule : Submodule ℝ (SobolevSection A μ p k) where
  carrier := {w | ∃ s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯,
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) ∧
      ofContMDiffSection A μ p k s = w}
  add_mem' := by
    rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact ⟨s + t, hs.add_section ht, map_add _ s t⟩
  zero_mem' := ⟨0, contMDiff_zeroSection ℝ V, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨s, hs, rfl⟩
    exact ⟨c • s, hs.const_smul_section, map_smul _ c s⟩

omit [T2Space M] in
/-- A multiplier equal to `1` wherever the `Cᵏ` section `s` is nonzero fixes its Sobolev
section. -/
private theorem contMDiffSMulL_ofContMDiffSection_of_smul_eq {χ : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ χ) {s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯} (h : ∀ x, χ x • s x = s x) :
    contMDiffSMulL A μ p k hχ (ofContMDiffSection A μ p k s) = ofContMDiffSection A μ p k s := by
  rw [contMDiffSMulL_ofContMDiffSection]
  congr
  exact funext h

omit [T2Space M] in
/-- The chart-`i` components of the Sobolev section of the section
`x ↦ ψ x • A.chartSection i f x` are the products by `ψ` of any
`u l ∈ W^{k,p}(A.image i)` whose values are the components of `f` in the basis
`Module.finBasis ℝ F`. -/
private theorem coe_ofContMDiffSection_smul_chartSection {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) {f : E → F} {u : Fin (finrank ℝ F) → Wkp μ (A.image i) p k}
    (hu : ∀ l, (Wkp.value k (u l) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ (finBasis ℝ F).repr (f y) l)
    {s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯} (hs : ⇑s = fun x ↦ ψ x • A.chartSection i f x)
    (l : Fin (finrank ℝ F)) :
    (ofContMDiffSection A μ p k s : A.sectionChartData.SobolevData μ p k) i l =
      Wkp.contDiffOnSMulL (A.chart i).open_target.uniqueDiffOn (A.isCompact_closure_image i)
        (A.closure_image_subset_target i) k (A.contDiffOn_comp_chart_symm hψ i) (u l) := by
  refine Wkp.ext k (Lp.ext ?_)
  have hc := chartValueL_ofContMDiffSection_ae A μ p k s i
  filter_upwards [SectionChartData.value_ae_eq_repr_coord
      (hc.trans (A.sectionChartData_coord_ae_eq μ i s).symm) l,
    A.sectionChartData_coord_ae_eq μ i s, hu l, Wkp.value_contDiffOnSMulL_ae _ _ _ k _ (u l),
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h₁ h₂ h₃ h₄ hy
  refine (h₁.trans ?_).trans h₄.symm
  rw [h₂, h₃, hs, A.coord_fun_smul i ψ _ hy, coord_chartSection f hy, map_smul, Finsupp.smul_apply,
    smul_eq_mul]

omit [T2Space M] in
/-- If `ψ • z = z`, the chart-`i` components of the difference between `z` and the Sobolev section
of `x ↦ ψ x • A.chartSection i f x` are bounded by the errors between the
chart-`i` components of `z` and any `u l` whose values are the components of `f`. -/
private theorem norm_coe_ofContMDiffSection_sub_le {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) {f : E → F} {u : Fin (finrank ℝ F) → Wkp μ (A.image i) p k}
    (hu : ∀ l, (Wkp.value k (u l) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ (finBasis ℝ F).repr (f y) l)
    {s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯} (hs : ⇑s = fun x ↦ ψ x • A.chartSection i f x)
    {z : SobolevSection A μ p k} (hz : contMDiffSMulL A μ p k hψ z = z) (l : Fin (finrank ℝ F)) :
    ‖((ofContMDiffSection A μ p k s - z : SobolevSection A μ p k) :
        A.sectionChartData.SobolevData μ p k) i l‖ ≤
      ‖Wkp.contDiffOnSMulL (mu := μ) (p := p) (A.chart i).open_target.uniqueDiffOn
        (A.isCompact_closure_image i) (A.closure_image_subset_target i) k
        (A.contDiffOn_comp_chart_symm hψ i)‖ *
        dist ((z : A.sectionChartData.SobolevData μ p k) i l) (u l) := by
  rw [Submodule.coe_sub,
    Pi.sub_apply (ofContMDiffSection A μ p k s : A.sectionChartData.SobolevData μ p k) z i,
    Pi.sub_apply, coe_ofContMDiffSection_smul_chartSection hψ hu hs l]
  conv_lhs => rw [← hz, contMDiffSMulL_apply]
  exact (congrArg norm (ContinuousLinearMap.map_sub _ _ _).symm).trans_le
    ((ContinuousLinearMap.le_opNorm _ _).trans_eq (congrArg (_ * ·) (dist_eq_norm' _ _).symm))

/-- **Local approximation.** Let `ψ` and `χ` be smooth cutoffs with `χ = 1` on the support of `ψ`
and the support of `χ` having closure in the domain of chart `i`. Every `z ∈ W^{k,p}(V)` with
`ψ • z = z` is a limit of Sobolev sections of `C^∞` sections: approximate its chart-`i` components
by functions smooth on the chart image (Meyers–Serrin), cut them off by `ψ`, and control the error
by its chart-`i` components (`TauCeti.SobolevSection.exists_norm_contMDiffSMulL_le`). -/
private theorem mem_closure_smoothSubmodule_of_contMDiffSMulL_eq (hp : p ≠ ⊤) {i : Fin A.n}
    {ψ χ : M → ℝ} (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) (hχ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ χ)
    (hχi : tsupport χ ⊆ A.dom i) (hψχ : EqOn χ 1 (tsupport ψ)) {z : SobolevSection A μ p k}
    (hz : contMDiffSMulL A μ p k hψ z = z) :
    z ∈ closure (smoothSubmodule A μ p k : Set (SobolevSection A μ p k)) := by
  have hψi : tsupport ψ ⊆ A.dom i := fun x hx ↦ hχi (subset_closure fun h ↦ by
    simp [hψχ hx] at h)
  obtain ⟨C₀, hC⟩ := exists_norm_contMDiffSMulL_le (k := k) (μ := μ) (p := p) hχ hχi
  set C := max C₀ 0
  set L := Wkp.contDiffOnSMulL (mu := μ) (p := p) (A.chart i).open_target.uniqueDiffOn
    (A.isCompact_closure_image i) (A.closure_image_subset_target i) k
    (A.contDiffOn_comp_chart_symm hψ i)
  rw [Metric.mem_closure_iff]
  intro ε hε
  set δ := ε / ((C + 1) * (‖L‖ + 1))
  have hδ : 0 < δ := by positivity
  -- Approximate the chart-`i` components of `z` by functions smooth on the chart image, and cut
  -- the resulting chart expression off by `ψ`.
  choose u hu hdist using fun l ↦ Metric.mem_closure_iff.1
    (Wkp.dense_contDiffOn_representatives (mu := μ) (Omega := A.image i) hp k
      ((z : A.sectionChartData.SobolevData μ p k) i l)) δ hδ
  choose g hg hgu using hu
  set f : E → F := fun y ↦ ∑ l, g l y • finBasis ℝ F l
  have hf : ContDiffOn ℝ ∞ f (A.image i) :=
    ContDiffOn.sum (s := Finset.univ) fun l _ ↦ (hg l).smul contDiffOn_const
  have hfu (l : Fin (finrank ℝ F)) : (Wkp.value k (u l) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ (finBasis ℝ F).repr (f y) l :=
    (hgu l).trans (Eventually.of_forall fun y ↦ by simp only [f]; rw [Basis.repr_sum_self])
  have ht := contMDiff_smul_chartSection hψ (A.image i).isOpen
    (hψi.trans (A.dom_subset_dom_inter_preimage_image i)) hf
  set s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯ := ⟨_, ht.of_le (by exact_mod_cast le_top)⟩
  refine ⟨ofContMDiffSection A μ p k s, ⟨s, ht, rfl⟩, ?_⟩
  -- `χ` fixes the difference between the approximation and `z`, so the difference is controlled
  -- by its chart-`i` components, which are `ψ • (u l - z i l)`.
  have hfix : contMDiffSMulL A μ p k hχ (ofContMDiffSection A μ p k s - z) =
      ofContMDiffSection A μ p k s - z := by
    rw [map_sub, contMDiffSMulL_ofContMDiffSection_of_smul_eq hχ fun x ↦ ?_]
    · conv_lhs => rw [← hz]
      rw [contMDiffSMulL_contMDiffSMulL_of_eqOn hψ hχ hψχ, hz]
    · by_cases hx : x ∈ tsupport ψ
      · simp [s, hψχ hx]
      · simp [s, image_eq_zero_of_notMem_tsupport hx]
  have hcomp (l : Fin (finrank ℝ F)) :
      ‖((ofContMDiffSection A μ p k s - z : SobolevSection A μ p k) :
        A.sectionChartData.SobolevData μ p k) i l‖ ≤ ‖L‖ * δ :=
    (norm_coe_ofContMDiffSection_sub_le hψ hfu rfl hz l).trans
      (mul_le_mul_of_nonneg_left (hdist l).le (norm_nonneg _))
  calc dist z (ofContMDiffSection A μ p k s)
      = ‖contMDiffSMulL A μ p k hχ (ofContMDiffSection A μ p k s - z)‖ := by
        rw [hfix, dist_comm, dist_eq_norm]
    _ ≤ C * (‖L‖ * δ) := (hC _).trans (mul_le_mul (le_max_left _ _)
        ((pi_norm_le_iff_of_nonneg (by positivity)).2 hcomp) (norm_nonneg _) (le_max_right _ _))
    _ < (C + 1) * (‖L‖ + 1) * δ := by
        nlinarith [mul_nonneg (le_max_right C₀ 0) hδ.le, mul_nonneg (norm_nonneg L) hδ.le]
    _ = ε := mul_div_cancel₀ _ (by positivity)

variable (A μ p k) in
/-- **Smooth sections are dense in `W^{k,p}(V)`** for `1 ≤ p < ∞`. On a compact manifold without
boundary, given by a finite bundle atlas of a Hausdorff manifold, the Sobolev sections of the
`C^∞` sections of `V` are dense in the Sobolev space `W^{k,p}(V)` of sections, for every order
`k`. -/
theorem dense_ofContMDiffSection_contMDiff (hp : p ≠ ⊤) :
    Dense {w : SobolevSection A μ p k | ∃ s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) ∧
        ofContMDiffSection A μ p k s = w} := by
  have := A.compactSpace
  refine (Submodule.dense_iff_topologicalClosure_eq_top (s := smoothSubmodule A μ p k)).2
    (eq_top_iff.2 fun w _ ↦ ?_)
  -- Decompose `w` by a smooth partition of unity subordinate to the chart domains.
  obtain ⟨φ, hφ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ A.dom
    A.isOpen_dom (by simp [A.iUnion_dom])
  have h1 (x : M) : ∑ i, φ i x = 1 := by
    rw [← finsum_eq_sum_of_fintype]
    exact φ.sum_eq_one (mem_univ x)
  rw [← sum_contMDiffSMulL_eq_self_of_sum_eq_one (fun i ↦ (φ i).contMDiff) h1 w]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  -- Each piece `φ i • w` is fixed by cutoffs supported in chart `i`.
  obtain ⟨ψ, hψ, -, hψi, hψ1⟩ :=
    (isClosed_tsupport (φ i)).exists_contMDiff_tsupport_subset_eq_one_iff (I := 𝓘(ℝ, E))
      (A.isOpen_dom i) (hφ i)
  obtain ⟨χ, hχ, -, hχi, hχ1⟩ :=
    (isClosed_tsupport ψ).exists_contMDiff_tsupport_subset_eq_one_iff (I := 𝓘(ℝ, E))
      (A.isOpen_dom i) hψi
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  exact mem_closure_smoothSubmodule_of_contMDiffSMulL_eq hp hψ hχ hχi (fun x hx ↦ (hχ1 x).1 hx)
    (contMDiffSMulL_contMDiffSMulL_of_eqOn _ hψ (fun x hx ↦ (hψ1 x).1 hx) w)

variable (A μ p k) in
/-- **`C^∞` sections are dense in `W^{k,p}(V)`** for every order `k` and `1 ≤ p < ∞`, stated for
the inclusion of `C^∞` sections; see `TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff`. -/
theorem denseRange_ofContMDiffSection_comp_ofLE (hp : p ≠ ⊤) :
    DenseRange ((ofContMDiffSection A μ p k).comp
      (ContMDiffSection.ofLE (I := 𝓘(ℝ, E)) (F := F) (V := V) ENat.LEInfty.out)) :=
  (dense_ofContMDiffSection_contMDiff A μ p k hp).mono <| by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [LinearMap.comp_apply]
    exact congrArg _ (ContMDiffSection.ext fun x ↦ congrFun (ContMDiffSection.coe_ofLE _ ⟨s, hs⟩) x)

variable (A μ p k) in
/-- **`Cᵏ` sections are dense in `W^{k,p}(V)`** for `1 ≤ p < ∞`; see
`TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff` for density of `C^∞` sections. -/
theorem denseRange_ofContMDiffSection (hp : p ≠ ⊤) : DenseRange (ofContMDiffSection A μ p k) :=
  (dense_ofContMDiffSection_contMDiff A μ p k hp).mono (by rintro _ ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)

variable (A μ k) in
/-- **Lowering the exponent has dense range.** For `1 ≤ p ≤ q`, the inclusion
`W^{k,q}(V) → W^{k,p}(V)` (`TauCeti.SectionChartData.ofExponentLEL`) has dense range. For `p < ∞`
its range contains the `Cᵏ` sections, which are dense; for `p = ∞` it is the identity. -/
theorem denseRange_ofExponentLEL {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q) :
    DenseRange (A.sectionChartData.ofExponentLEL μ k hpq) := by
  rcases eq_or_ne p ⊤ with rfl | hp
  · obtain rfl := top_le_iff.1 hpq
    exact Function.Surjective.denseRange fun w ↦ ⟨w, SectionChartData.ofExponentLEL_self w⟩
  refine (denseRange_ofContMDiffSection A μ p k hp).mono ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨ofContMDiffSection A μ q k s, ofExponentLEL_ofContMDiffSection hpq s⟩

end Unconditional

section Planar

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ℂ M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Extension by zero over surfaces.** For a `Cⁿ` bundle over a `Cⁿ` surface, `n ≠ 0`, and an
order `k ≤ n`: let `L` be a closed subset of the domain of chart `i`, and
`g` a tuple of chart-`i` Sobolev functions vanishing off `L`. The section equal to the function `g`
defines on the chart, and zero off it, has locally `W^{k,p}` readings in chart `i` and in every
chart away from `L`, so it defines an element of `W^{k,p}(V)`
(`TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm`). -/
theorem hasExtensionByZero {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, ℂ) n M]
    [ContMDiffVectorBundle n F V 𝓘(ℝ, ℂ)] (hn : n ≠ 0)
    (hkn : (k : WithTop ℕ∞) ≤ n) : HasExtensionByZero A volume p k := by
  refine hasExtensionByZero_iff.2 fun i L hL hLi g ↦ ?_
  classical
  obtain ⟨G, hG⟩ : ∃ G : ℂ → F, ∀ y, G y = if (A.chart i).symm y ∈ L then
      ∑ j, Wkp.value k ((g : Fin (finrank ℝ F) → Wkp volume (A.image i) p k) j) y • finBasis ℝ F j
      else 0 := ⟨_, fun _ ↦ rfl⟩
  -- The components of `g` are the coordinates of `G` in the basis `finBasis ℝ F`.
  have hGj (j : Fin (finrank ℝ F)) :
      (Wkp.value k ((g : Fin (finrank ℝ F) → Wkp volume (A.image i) p k) j) : ℂ → ℝ)
        =ᵐ[volume.restrict (A.image i)] fun y ↦ (finBasis ℝ F).repr (G y) j := by
    filter_upwards [mem_chartAeZeroOff.1 g.property j] with y hy
    rw [hG]
    split_ifs with hL'
    · rw [(finBasis ℝ F).repr_sum_self]
    · rw [hy hL', map_zero, Finsupp.coe_zero, Pi.zero_apply]
  -- The section `A.chartSection i G` vanishes off `L`.
  have ht : ∀ x ∉ L, A.chartSection i G x = 0 := fun x hx ↦ chartSection_eq_zero fun hxi ↦ by
    rw [hG, ite_eq_right (by rwa [(A.chart i).left_inv (A.dom_subset_chart_source i hxi)])]
  -- Chart `i` near `L`, and every chart away from `L`.
  have hopen : ∀ i', IsOpen ((A.image i' : Set ℂ) ∩ (A.chart i').symm ⁻¹' Lᶜ) := fun i' ↦
    ((A.chart i').continuousOn_symm.mono ((A.image_subset_chart_image_closure_dom i').trans
      ((A.chart_image_closure_dom_subset i').trans inter_subset_left))).isOpen_inter_preimage
        (A.image i').isOpen hL.isOpen_compl
  let U : Fin A.n → Set ℂ := fun i' ↦
    if i' = i then A.image i else A.image i' ∩ (A.chart i').symm ⁻¹' Lᶜ
  have hU : ∀ i', IsOpen (U i') := fun i' ↦ by
    simp only [U]
    split_ifs
    · exact (A.image i).isOpen
    · exact hopen i'
  have hcover : ∀ x, ∃ i', x ∈ A.dom i' ∧ A.chart i' x ∈ U i' := fun x ↦ by
    by_cases hx : x ∈ L
    · refine ⟨i, hLi hx, ?_⟩
      simp only [U, ↓reduceIte]
      exact A.mem_image.2 ⟨x, hLi hx, rfl⟩
    · obtain ⟨i', hi'⟩ := A.exists_mem_dom x
      refine ⟨i', hi', ?_⟩
      simp only [U]
      split_ifs with hii
      · exact hii ▸ A.mem_image.2 ⟨x, hi', rfl⟩
      · exact ⟨A.mem_image.2 ⟨x, hi', rfl⟩, by
          rwa [mem_preimage, (A.chart i').left_inv (A.dom_subset_chart_source i' hi')]⟩
  have hmem : ∀ i', MemWkpLoc p (U i') k (A.coord i' (A.chartSection i G)) := fun i' ↦ by
    simp only [U]
    split_ifs with hii
    · rw [hii]
      refine MemWkpLoc.congr ?_ (fun y hy ↦ coord_chartSection G hy)
      exact (finBasis ℝ F).memWkpLoc_iff.2 fun j ↦
        (Wkp.memWkpLoc_value_of_ae_le (Opens.ext (A.image i).isOpen.interior_eq)
          (ae_subset.2 (by simp)) ((g : Fin (finrank ℝ F) → Wkp volume (A.image i) p k) j)).congr_ae
          (hGj j)
    · exact memWkpLoc_zero_fun.congr fun y hy ↦ A.coord_eq_zero hy.1 (ht _ hy.2)
  obtain ⟨w, hw⟩ := exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm
    (A := A) A.chart (fun _ ↦ IsManifold.chart_mem_maximalAtlas _) A.triv U hU
    (fun x ↦ let ⟨i', hi', hi'U⟩ := hcover x
      ⟨i', A.dom_subset_chart_source i' hi', A.dom_subset_baseSet i' hi', hi'U⟩)
    (fun i' ↦ by simpa only [funext (A.coord_def i' _)] using hmem i') hn hkn
  refine ⟨⟨w, mem_aeZeroOff_of_ae_eq_coord hw ht⟩,
    Subtype.ext <| funext fun j ↦ Wkp.ext k <| Lp.ext ?_⟩
  rw [coe_chartRestrictL_apply]
  filter_upwards [value_ae_eq_repr_coord (hw i) j, hGj j,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h1 h2 hy
  refine h1.trans ?_
  rw [coord_chartSection G hy, h2]

/-- **Extension by zero over surfaces at orders `k ≤ 1`**, for a `C¹` bundle over a `C¹` surface
and every `1 ≤ p ≤ ∞`. -/
theorem hasExtensionByZero_of_le_one [IsManifold 𝓘(ℝ, ℂ) 1 M]
    [ContMDiffVectorBundle 1 F V 𝓘(ℝ, ℂ)] (hk : k ≤ 1) : HasExtensionByZero A volume p k :=
  hasExtensionByZero one_ne_zero (by exact_mod_cast hk)

end Planar

end SobolevSection

end TauCeti
