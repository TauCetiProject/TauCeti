/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.FiniteCover
public import TauCeti.Analysis.Sobolev.Wkp.MeyersSerrin
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Transfer
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Smooth sections are dense in `W^{k,p}(V)`

Let `M` be a smooth Hausdorff manifold without boundary modelled on a finite-dimensional real inner
product space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre
`F`, and let `A` be a finite bundle atlas, so that `M` is compact. For `1 ≤ p < ∞` and every order
`k`, the `C^∞` sections of `V` are dense in the Sobolev space `W^{k,p}(V)` of
`TauCeti.SobolevSection` (`TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff`); in
particular the map `TauCeti.SobolevSection.ofContMDiffSection` from `Cᵏ` sections has dense range.
This is the smooth density of the bundle Sobolev spaces used to extend identities from smooth
sections to all of `W^{k,p}(V)` by continuity. The exponent must be finite: smooth functions are
not dense in `W^{1,∞}`, as `|x|` on an interval shows.

## The argument

A smooth partition of unity `φ i` subordinate to the chart domains splits `w ∈ W^{k,p}(V)` as
`w = ∑ i, φ i • w` (`TauCeti.SobolevSection.sum_contMDiffSMulL_apply_eq_self`), so it suffices to
approximate a section `z` fixed by a cutoff `ψ` supported in the domain of one chart `i`. Its
chart-`i` components are approximated in `W^{k,p}` of the chart image by functions smooth there
(the Meyers–Serrin theorem `TauCeti.Wkp.dense_contDiffOn_representatives`); cut off by `ψ`, these
are the coordinates of smooth sections of `V` supported in chart `i`
(`TauCeti.FiniteBundleAtlas.contMDiff_smul_triv_symm`).

The error is measured in all charts at once by the following estimate, which is the main
technical input (`TauCeti.SobolevSection.exists_norm_contMDiffSMulL_le`): for a smooth `χ` whose
support has closure in the domain of chart `i`, the norm of `χ • w` in `W^{k,p}(V)` is at most a
constant times the norm of the chart-`i` components of `w`. In chart `j`, the image of chart `j` is
covered by a piece on which the chart-`j` data of `χ • w` are transferred from chart `i` by the
continuous map `TauCeti.FiniteBundleAtlas.transferL`, and an open set on which they vanish
(`TauCeti.FiniteBundleAtlas.exists_transfer_piece`); the norm on chart `j` is bounded by the norms
on the two pieces (`TauCeti.Wkp.norm_le_norm_restrictL_add_norm_restrictL`).

## Main results

* `TauCeti.SobolevSection.exists_norm_contMDiffSMulL_le`: sections cut off inside one chart are
  controlled in `W^{k,p}(V)` by their components in that chart.
* `TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff`: the `C^∞` sections are dense in
  `W^{k,p}(V)` for `1 ≤ p < ∞`.
* `TauCeti.SobolevSection.denseRange_ofContMDiffSection`: the `Cᵏ` sections are dense.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* N. G. Meyers and J. Serrin, *H = W*, Proc. Nat. Acad. Sci. U.S.A. 51 (1964), 1055–1056.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace TauCeti

open FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {k : ℕ}

namespace SobolevSection

variable [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

/-- **Sections supported in one chart are controlled by that chart.** Let `1 ≤ p < ∞` and let `χ`
be a smooth function whose support has closure inside the domain of chart `i`. Then the norm of
`χ • w` in `W^{k,p}(V)` is bounded by a constant multiple of the norm of the chart-`i` components
of `w`, the constant depending on `χ` but not on `w`. -/
theorem exists_norm_contMDiffSMulL_le (hp : p ≠ ⊤) {i : Fin A.n} {χ : M → ℝ}
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
    ‖A.transferL μ p k hp i j (hPc j) (hPD j) (hPQ j)‖ * ‖L‖, fun w ↦ ?_⟩
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
    A.restrictL_eq_transferL μ p k hp v.2 (hP j) (hPc j) (hPD j) le_rfl (hPQ j) m]
  calc _ ≤ ‖A.transferL μ p k hp i j (hPc j) (hPD j) (hPQ j)‖ *
        ‖fun l ↦ Wkp.restrictL (le_rfl : A.image i ≤ A.image i) k
          ((v : A.sectionChartData.SobolevData μ p k) i l)‖ :=
        (norm_le_pi_norm _ m).trans (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ ‖A.transferL μ p k hp i j (hPc j) (hPD j) (hPQ j)‖ *
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
`x ↦ ψ x • (A.triv i).symm x (f (A.chart i x))` are the products by `ψ` of any
`u l ∈ W^{k,p}(A.image i)` whose values are the components of `f` in the basis
`Module.finBasis ℝ F`. -/
private theorem coe_ofContMDiffSection_smul_triv_symm {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) {f : E → F} {u : Fin (finrank ℝ F) → Wkp μ (A.image i) p k}
    (hu : ∀ l, (Wkp.value k (u l) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ (finBasis ℝ F).repr (f y) l)
    {s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯} (hs : ⇑s = fun x ↦ ψ x • (A.triv i).symm x (f (A.chart i x)))
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
  rw [h₂, h₃, hs, A.coord_smul_triv_symm ψ f hy, map_smul, Finsupp.smul_apply, smul_eq_mul]

omit [T2Space M] in
/-- If `ψ • z = z`, the chart-`i` components of the difference between `z` and the Sobolev section
of `x ↦ ψ x • (A.triv i).symm x (f (A.chart i x))` are bounded by the errors between the
chart-`i` components of `z` and any `u l` whose values are the components of `f`. -/
private theorem norm_coe_ofContMDiffSection_sub_le {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ ψ) {f : E → F} {u : Fin (finrank ℝ F) → Wkp μ (A.image i) p k}
    (hu : ∀ l, (Wkp.value k (u l) : E → ℝ) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ (finBasis ℝ F).repr (f y) l)
    {s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯} (hs : ⇑s = fun x ↦ ψ x • (A.triv i).symm x (f (A.chart i x)))
    {z : SobolevSection A μ p k} (hz : contMDiffSMulL A μ p k hψ z = z) (l : Fin (finrank ℝ F)) :
    ‖((ofContMDiffSection A μ p k s - z : SobolevSection A μ p k) :
        A.sectionChartData.SobolevData μ p k) i l‖ ≤
      ‖Wkp.contDiffOnSMulL (mu := μ) (p := p) (A.chart i).open_target.uniqueDiffOn
        (A.isCompact_closure_image i) (A.closure_image_subset_target i) k
        (A.contDiffOn_comp_chart_symm hψ i)‖ *
        dist ((z : A.sectionChartData.SobolevData μ p k) i l) (u l) := by
  rw [Submodule.coe_sub,
    Pi.sub_apply (ofContMDiffSection A μ p k s : A.sectionChartData.SobolevData μ p k) z i,
    Pi.sub_apply, coe_ofContMDiffSection_smul_triv_symm hψ hu hs l]
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
  obtain ⟨C₀, hC⟩ := exists_norm_contMDiffSMulL_le (k := k) (μ := μ) hp hχ hχi
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
  have ht := A.contMDiff_smul_triv_symm hψ hψi hf
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
  rw [← sum_contMDiffSMulL_apply_eq_self (fun i ↦ (φ i).contMDiff) h1 w]
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
/-- **`Cᵏ` sections are dense in `W^{k,p}(V)`** for `1 ≤ p < ∞`; see
`TauCeti.SobolevSection.dense_ofContMDiffSection_contMDiff` for density of `C^∞` sections. -/
theorem denseRange_ofContMDiffSection (hp : p ≠ ⊤) : DenseRange (ofContMDiffSection A μ p k) :=
  (dense_ofContMDiffSection_contMDiff A μ p k hp).mono (by rintro _ ⟨s, -, rfl⟩; exact ⟨s, rfl⟩)

end SobolevSection

end TauCeti
