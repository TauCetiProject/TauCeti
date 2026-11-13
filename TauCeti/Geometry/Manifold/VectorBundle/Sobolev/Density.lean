/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.AEZeroOff
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Chart
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Wkp
import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin

/-!
# Smooth sections are dense in `W^{k,p}(V)`

Let `M` be a Hausdorff smooth manifold without boundary modelled on a finite-dimensional real inner
product space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre
`F`, and let `A` be a finite bundle atlas (so `M` is compact). This file shows that for
`1 ≤ p < ∞` the `C^∞` sections of `V` are dense in the Sobolev space `W^{k,p}(V)` of
`TauCeti.SobolevSection A μ p k` as soon as `W^{k,p}(V)` admits extension by zero from a single
chart (`TauCeti.SobolevSection.HasExtensionByZero`). Over surfaces (`E = ℂ`, with Lebesgue
measure) extension by zero holds for `k ≤ 1`
(`TauCeti.SobolevSection.hasExtensionByZero_of_le_one`), so there the `C^∞` sections are dense
(`TauCeti.SobolevSection.denseRange_ofContMDiffSection_comp_ofLE`), and hence so are the `Cᵏ`
sections (`TauCeti.SobolevSection.denseRange_ofContMDiffSection`).

The proof localizes with a smooth partition of unity `χ` subordinate to the chart domains of `A`:
every `w` is the finite sum of the products `χ i • w`
(`TauCeti.SobolevSection.sum_contMDiffSMulL_eq_self_of_sum_eq_one`), and `χ i • w` vanishes off
the closed set `tsupport (χ i) ⊆ A.dom i` (`TauCeti.SobolevSection.contMDiffSMulL_mem_aeZeroOff`).
An element `u` vanishing off a closed subset `L` of the domain of chart `i` is the extension by
zero `TauCeti.SobolevSection.extendLocalL` of its chart-`i` components, and extension by zero is
continuous. To approximate `u`, take a smooth cutoff `ψ` equal to one on `L` with support in the
chart domain, approximate the chart-`i` components of `u` by functions smooth on the chart image
(Meyers–Serrin, `TauCeti.Wkp.exists_contDiffOn_approximation`), and multiply them by `ψ`. The
products are the chart readings of `C^∞` sections vanishing off `tsupport ψ`, whose chart-`i`
components converge to those of `u`; continuity of `extendLocalL` gives convergence in
`W^{k,p}(V)`.

Extension by zero is the only step that depends on the order `k`. Over surfaces it follows from
the invariance of the local Sobolev classes of order at most one under changes of chart
(`TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm`): the
section equal to the given functions on the chart and zero off it has locally `W^{k,p}` readings
in chart `i` near `L` and in every chart away from `L`.

## Main results

* `TauCeti.SobolevSection.mem_range_ofContMDiffSection_comp_ofLE_iff`: the elements of
  `W^{k,p}(V)` given by `C^∞` sections are those whose chart data are the coordinates of a `C^∞`
  section.
* `TauCeti.SobolevSection.denseRange_ofContMDiffSection_comp_ofLE_of_hasExtensionByZero`,
  `TauCeti.SobolevSection.denseRange_ofContMDiffSection_of_hasExtensionByZero`: under extension by
  zero, `C^∞` sections, and hence `Cᵏ` sections, are dense in `W^{k,p}(V)` for `1 ≤ p < ∞`.
* `TauCeti.SobolevSection.hasExtensionByZero_of_le_one`: over surfaces, extension by zero holds
  for `k ≤ 1`.
* `TauCeti.SobolevSection.denseRange_ofContMDiffSection_comp_ofLE`: over surfaces, `C^∞` sections
  are dense in `W^{k,p}(V)` for `1 ≤ p < ∞` and `k ≤ 1`.
* `TauCeti.SobolevSection.denseRange_ofContMDiffSection`: over surfaces, `Cᵏ` sections are dense
  in `W^{k,p}(V)` for `1 ≤ p < ∞` and `k ≤ 1`.

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
    ⟨⟨_, contMDiff_smul_chartSection hψ hψi hGs⟩, rfl⟩
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
  have hE := ((extendLocalL h (isClosed_tsupport ψ) hψi).continuous.tendsto _).comp hconv
  simp only [Function.comp_def, extendLocalL_chartRestrictL] at hE
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

section Planar

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ℂ M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- **Extension by zero over surfaces at orders `k ≤ 1`.** Let `L` be a closed subset of the
domain of chart `i`, and `g` a tuple of chart-`i` Sobolev functions vanishing off `L`. The section
equal to the function `g` defines on the chart, and zero off it, has locally `W^{k,p}` readings in
chart `i` and in every chart away from `L`, so it defines an element of `W^{k,p}(V)`
(`TauCeti.SobolevSection.exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm`). -/
theorem hasExtensionByZero_of_le_one [IsManifold 𝓘(ℝ, ℂ) 1 M]
    [ContMDiffVectorBundle 1 F V 𝓘(ℝ, ℂ)] (hk : k ≤ 1) : HasExtensionByZero A volume p k := by
  refine hasExtensionByZero_iff.2 fun i L hL hLi g ↦ ?_
  classical
  obtain ⟨G, hG⟩ : ∃ G : ℂ → F, ∀ y, G y = if (A.chart i).symm y ∈ L then
      ∑ j, Wkp.value k ((g : Fin (finrank ℝ F) → Wkp volume (A.image i) p k) j) y • finBasis ℝ F j
      else 0 := ⟨_, fun _ ↦ rfl⟩
  -- The components of `g` are the coordinates of `G` in the basis `finBasis ℝ F`.
  have hGj (j : Fin (finrank ℝ F)) :
      (Wkp.value k ((g : Fin (finrank ℝ F) → Wkp volume (A.image i) p k) j) : ℂ → ℝ)
        =ᵐ[volume.restrict (A.image i)] fun y ↦ (finBasis ℝ F).repr (G y) j := by
    filter_upwards [mem_chartAeZeroOff.1 g.2 j] with y hy
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
      refine MemWkpLoc.congr_fun ?_ (fun y hy ↦ (coord_chartSection G hy).symm)
        (A.image i).isOpen.measurableSet
      exact (finBasis ℝ F).memWkpLoc_iff.2 fun j ↦
        (Wkp.memWkpLoc_value_of_ae_le (Opens.ext (A.image i).isOpen.interior_eq)
          (ae_subset.2 (by simp)) ((g : Fin (finrank ℝ F) → Wkp volume (A.image i) p k) j)).congr_ae
          (hGj j)
    · exact memWkpLoc_zero_fun.congr_fun (fun y hy ↦ (A.coord_eq_zero hy.1 (ht _ hy.2)).symm)
        (hopen i').measurableSet
  obtain ⟨w, hw⟩ := exists_ae_eq_coord_of_memWkpLoc_trivialization_comp_chart_symm
    (A := A) hk A.chart (fun _ ↦ IsManifold.chart_mem_maximalAtlas _) A.triv U hU
    (fun x ↦ let ⟨i', hi', hi'U⟩ := hcover x
      ⟨i', A.dom_subset_chart_source i' hi', A.dom_subset_baseSet i' hi', hi'U⟩)
    fun i' ↦ by simpa only [funext (A.coord_def i' _)] using hmem i'
  refine ⟨⟨w, mem_aeZeroOff_of_ae_eq_coord hw ht⟩,
    Subtype.ext <| funext fun j ↦ Wkp.ext k <| Lp.ext ?_⟩
  rw [coe_chartRestrictL_apply]
  filter_upwards [value_ae_eq_repr_coord (hw i) j, hGj j,
    ae_restrict_mem (A.image i).isOpen.measurableSet] with y h1 h2 hy
  refine h1.trans ?_
  rw [coord_chartSection G hy, h2]

variable [IsManifold 𝓘(ℝ, ℂ) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)]

/-- **`C^∞` sections are dense in `W^{k,p}(V)`** over a compact Hausdorff surface, for
`1 ≤ p < ∞` and `k ≤ 1`. -/
theorem denseRange_ofContMDiffSection_comp_ofLE [T2Space M] (hp : p ≠ ⊤) (hk : k ≤ 1) :
    DenseRange ((ofContMDiffSection A volume p k).comp
      (ContMDiffSection.ofLE (I := 𝓘(ℝ, ℂ)) (F := F) (V := V) ENat.LEInfty.out)) :=
  denseRange_ofContMDiffSection_comp_ofLE_of_hasExtensionByZero hp (hasExtensionByZero_of_le_one hk)

/-- **`Cᵏ` sections are dense in `W^{k,p}(V)`** over a compact Hausdorff surface, for
`1 ≤ p < ∞` and `k ≤ 1`. In fact the `C^∞` sections are dense
(`TauCeti.SobolevSection.denseRange_ofContMDiffSection_comp_ofLE`). -/
theorem denseRange_ofContMDiffSection [T2Space M] (hp : p ≠ ⊤) (hk : k ≤ 1) :
    DenseRange (ofContMDiffSection A volume p k) :=
  denseRange_ofContMDiffSection_of_hasExtensionByZero hp (hasExtensionByZero_of_le_one hk)

end Planar

end SobolevSection

end TauCeti
