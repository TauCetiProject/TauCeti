/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.HigherOrder
public import TauCeti.Analysis.Sobolev.Local.Norm
import TauCeti.Analysis.Complex.Wirtinger.Regularity
import TauCeti.Analysis.Sobolev.Local.Norm.ContDiff
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# The higher-order elliptic estimate for smooth real Cauchy–Riemann operators

Let `M` be a complex curve without boundary and `V → M` a complex vector bundle with
finite-dimensional model fibre, smooth as a real vector bundle, with a finite bundle atlas `A` (so
`M` is compact). Let `D` be a smooth real Cauchy–Riemann operator on `V` and `1 < p < ∞`. This
file proves the elliptic estimate at every order `k`:

`‖ξ‖_{W^{k+1,p}} ≤ C (‖D ξ‖_{W^{k,p}} + ‖ξ‖_{Lᵖ})`

for every `ξ ∈ W^{k+1,p}(Σ, V)`, where `D ξ` is the bounded realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL : W^{k+1,p}(Σ, V) → W^{k,p}(Σ, Λ^{0,1} ⊗ V)`
(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm`). This is the
elliptic estimate of the roadmap's PH6.2 for smooth operators on closed surfaces, at every order;
the case `k = 0` is `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevL_add_norm`.

## The argument

The estimate one order up, `‖ξ‖_{W^{k+1,p}} ≤ C (‖D ξ‖_{W^{k,p}} + ‖ξ‖_{W^{k,p}})`
(`TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL`),
follows the order-one proof. A partition of unity `χᵢ` subordinate to the chart domains splits a
smooth section `s`, and `χᵢ s` is controlled by its chart-`i` components. In chart `i` the reading
`u` of `s` satisfies `\bar∂u = (D s)ᵢ - Zᵢ u` for the zeroth-order term `Zᵢ`, and the interior
`W^{k+1,p}` estimate for `\bar∂` (`TauCeti.exists_eLpNormWkp_le_of_hasWeakConjWirtingerDerivOn`)
bounds `u` near the support of the cutoff by `(D s)ᵢ - Zᵢ u` in `W^{k,p}` and `u` in `Lᵖ`
(`TauCeti.exists_eLpNormWkp_le_of_eqOn_complexAntilinearPartL_add`,
`TauCeti.IsRealCauchyRiemannOperator.exists_eLpNormWkp_coord_smul_le`). The Leibniz bound
`TauCeti.eLpNormWkp_bilin_le` handles the cutoff and the zeroth-order term. For smooth readings the
`W^{k,p}` norms of functions and the norms of chart components are comparable
(`TauCeti.SectionChartData.exists_eLpNormWkp_le_of_chartValueL_ae_eq`,
`TauCeti.SectionChartData.exists_ofReal_norm_le_eLpNormWkp_of_chartValueL_ae_eq`). Smooth
sections are dense, and both sides are continuous, so the estimate extends to all of
`W^{k+1,p}(Σ, V)`. Induction on `k`, with the compatibility of the realizations with forgetting
derivatives (`TauCeti.IsRealCauchyRiemannOperator.zeroOneLowerOrdersL_sobolevSuccL`), lowers the
`W^{k,p}` norm of `ξ` on the right to its `Lᵖ` norm.

## Main results

* `TauCeti.exists_eLpNormWkp_le_of_eqOn_complexAntilinearPartL_add`: the interior `W^{k+1,p}`
  estimate for `\bar∂` plus a zeroth-order term on a planar domain, with values in a
  finite-dimensional complex normed space.
* `TauCeti.IsRealCauchyRiemannOperator.exists_eLpNormWkp_coord_smul_le`: the estimate in one chart,
  for smooth sections cut off inside the chart domain.
* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL`: the
  estimate one order up.
* `TauCeti.IsRealCauchyRiemannOperator.exists_norm_le_norm_sobolevSuccL_add_norm`: the elliptic
  estimate on `W^{k+1,p}(Σ, V)` at every order.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.2 (the elliptic estimate for real
  Cauchy–Riemann operators) and Appendix B.4 (the interior estimates for `\bar∂`).
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal NNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

/-! ### Chart data of `Cᵏ` readings -/

namespace SectionChartData

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData ℂ F S)
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

/-- The `j`th coordinate of `Module.finBasis ℝ F`, as a continuous linear map. -/
private abbrev coordL (j : Fin (finrank ℝ F)) : F →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)

/-- The components of a tuple whose chart data in chart `i` agree with `f` are the coordinates of
`f`. -/
private theorem value_ae_eq_coordL {w : C.SobolevData volume p k} {i : Fin C.n} {f : ℂ → F}
    (hw : C.chartValueL volume p k i w =ᵐ[volume.restrict (C.image i)] f)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k (w i j) : ℂ → ℝ) =ᵐ[volume.restrict (C.image i)] fun y ↦ coordL j (f y) := by
  filter_upwards [C.chartValueL_apply_ae volume p k i w, hw] with y hy hy'
  rw [← hy', hy]
  simp only [coordL, LinearMap.coe_toContinuousLinearMap', Basis.coord_apply,
    Basis.repr_sum_self]

/-- **`W^{k,p}` size of a `Cᵏ` reading.** If the chart data in chart `i` of a tuple agree almost
everywhere with a function `f` that is `Cᵏ` on the image of the chart, the `W^{k,p}` norm of `f`
on the image is bounded by a constant multiple of the norm of the chart-`i` components. -/
theorem exists_eLpNormWkp_le_of_chartValueL_ae_eq (k : ℕ) :
    ∃ c : ℝ≥0, ∀ {w : C.SobolevData volume p k} {i : Fin C.n} {f : ℂ → F},
      ContDiffOn ℝ k f (C.image i) →
      C.chartValueL volume p k i w =ᵐ[volume.restrict (C.image i)] f →
      eLpNormWkp p (C.image i) k f ≤ c * ENNReal.ofReal ‖w i‖ := by
  refine ⟨(k + 1) * ∑ j, ‖finBasis ℝ F j‖₊, fun {w i f} hf hw ↦ ?_⟩
  set U := C.image i
  set L : Fin (finrank ℝ F) → ℝ →L[ℝ] F :=
    fun j ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)
  have hsum : f = ∑ j, fun y ↦ L j (coordL j (f y)) := by
    funext y
    simp [L, Finset.sum_apply, Basis.coord_apply, (finBasis ℝ F).sum_repr]
  have hj (j : Fin (finrank ℝ F)) :
      eLpNormWkp p U k (fun y ↦ coordL j (f y)) ≤ (k + 1 : ℝ≥0∞) * ENNReal.ofReal ‖w i‖ := by
    have hg : ContDiffOn ℝ k (fun y ↦ coordL j (f y)) U :=
      (coordL j).contDiff.comp_contDiffOn hf
    have hv := C.value_ae_eq_coordL hw j
    rw [eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv U.isOpen k hg]
    calc ∑ l ∈ Finset.range (k + 1), eLpNorm (iteratedFDeriv ℝ l fun y ↦ coordL j (f y)) p
          (volume.restrict U)
        ≤ ∑ _l ∈ Finset.range (k + 1), ENNReal.ofReal ‖w i‖ := by
          refine Finset.sum_le_sum fun l hl ↦ ?_
          have hl : l ≤ k := Finset.mem_range_succ_iff.1 hl
          rw [← ENNReal.ofReal_toReal
            (Wkp.memLp_iteratedFDeriv_of_contDiffOn k (w i j) hg hv l hl).eLpNorm_ne_top]
          exact ENNReal.ofReal_le_ofReal
            ((Wkp.lpNorm_iteratedFDeriv_le_of_contDiffOn k (w i j) hg hv l hl).trans
              (norm_le_pi_norm (w i) j))
      _ = (k + 1 : ℝ≥0∞) * ENNReal.ofReal ‖w i‖ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          rfl
  calc eLpNormWkp p U k f = eLpNormWkp p U k (∑ j, fun y ↦ L j (coordL j (f y))) := by
        rw [← hsum]
    _ ≤ ∑ j, eLpNormWkp p U k (fun y ↦ L j (coordL j (f y))) :=
        eLpNormWkp_sum_le (Fact.out : 1 ≤ p)
    _ ≤ ∑ j, ‖L j‖ₑ * ((k + 1 : ℝ≥0∞) * ENNReal.ofReal ‖w i‖) :=
        Finset.sum_le_sum fun j _ ↦ (eLpNormWkp_clm_comp_le (L j)).trans (by gcongr; exact hj j)
    _ ≤ ∑ j, (‖finBasis ℝ F j‖₊ : ℝ≥0∞) * ((k + 1 : ℝ≥0∞) * ENNReal.ofReal ‖w i‖) := by
        gcongr with j
        rw [eNorm_eq_nnNorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
        simp [L, ContinuousLinearMap.norm_smulRight_apply]
    _ = ((k + 1 : ℝ≥0) * ∑ j, ‖finBasis ℝ F j‖₊ : ℝ≥0) * ENNReal.ofReal ‖w i‖ := by
        rw [← Finset.sum_mul]
        push_cast
        ring

/-- **Components from a `Cᵏ` reading.** If the chart data in chart `i` of a tuple agree almost
everywhere with a function `f` that is `Cᵏ` on the image of the chart, the norm of the chart-`i`
components is bounded by a constant multiple of the `W^{k,p}` norm of `f` on the image. -/
theorem exists_ofReal_norm_le_eLpNormWkp_of_chartValueL_ae_eq (k : ℕ) :
    ∃ c : ℝ≥0, ∀ {w : C.SobolevData volume p k} {i : Fin C.n} {f : ℂ → F},
      ContDiffOn ℝ k f (C.image i) →
      C.chartValueL volume p k i w =ᵐ[volume.restrict (C.image i)] f →
      ENNReal.ofReal ‖w i‖ ≤ c * eLpNormWkp p (C.image i) k f := by
  refine ⟨∑ j, ‖coordL (F := F) j‖₊, fun {w i f} hf hw ↦ ?_⟩
  set U := C.image i
  have hj (j : Fin (finrank ℝ F)) :
      ENNReal.ofReal ‖w i j‖ ≤ ‖coordL (F := F) j‖ₑ * eLpNormWkp p U k f := by
    have hg : ContDiffOn ℝ k (fun y ↦ coordL j (f y)) U :=
      (coordL j).contDiff.comp_contDiffOn hf
    have hv := C.value_ae_eq_coordL hw j
    refine le_trans ?_ (eLpNormWkp_clm_comp_le (coordL j))
    rw [eLpNormWkp_eq_sum_eLpNorm_iteratedFDeriv U.isOpen k hg]
    refine (ENNReal.ofReal_le_ofReal
      (Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k (w i j) hg hv)).trans ?_
    simp only [← toReal_eLpNorm]
    rw [ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ ENNReal.toReal_nonneg]
    exact Finset.sum_le_sum fun l _ ↦ ENNReal.ofReal_toReal_le
  have hpi : ‖w i‖ ≤ ∑ j, ‖w i j‖ :=
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).2 fun j ↦
      Finset.single_le_sum (f := fun j ↦ ‖w i j‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ j)
  calc ENNReal.ofReal ‖w i‖ ≤ ENNReal.ofReal (∑ j, ‖w i j‖) := ENNReal.ofReal_le_ofReal hpi
    _ = ∑ j, ENNReal.ofReal ‖w i j‖ :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ ∑ j, ‖coordL (F := F) j‖ₑ * eLpNormWkp p U k f := Finset.sum_le_sum fun j _ ↦ hj j
    _ = _ := by
        rw [← Finset.sum_mul]
        simp [eNorm_eq_nnNorm]
        rfl

/-- Forgetting the highest derivative does not increase the norm. -/
theorem norm_lowerOrderL_le (w : C.sobolevSections volume p (k + 1)) :
    ‖C.lowerOrderL volume p k w‖ ≤ ‖w‖ := by
  have h : ‖(C.lowerOrderL volume p k w : C.SobolevData volume p k)‖ ≤
      ‖(w : C.SobolevData volume p (k + 1))‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j ↦ by
        rw [lowerOrderL_apply]
        exact (Wkp.norm_lowerOrder_le k _).trans ((norm_le_pi_norm _ j).trans
          (norm_le_pi_norm (w : C.SobolevData volume p (k + 1)) i))
  exact h

end SectionChartData

/-! ### The interior estimate for `∂bar` plus a zeroth-order term -/

section Planar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- The interior estimate `TauCeti.exists_eLpNormWkp_le_of_hasWeakConjWirtingerDerivOn` for `Cᵏ⁺¹`
maps into `F`, with any real structure compatible with the complex one, transported along a complex
linear isomorphism with a Euclidean space. -/
private theorem exists_eLpNormWkp_le_of_contDiffOn (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    {U O K : Set ℂ} (hU : IsOpen U) (hO : IsOpen O) (hUO : closure U ⊆ O) (hK : IsCompact K)
    (hKU : K ⊆ U) :
    ∃ W Ω' : Opens ℂ, K ⊆ W ∧ (W : Set ℂ) ⊆ Ω' ∧ (Ω' : Set ℂ) ⊆ U ∧ ∃ C : ℝ≥0, ∀ u : ℂ → F,
      ContDiffOn ℝ (k + 1 : ℕ) u O →
      eLpNormWkp p W (k + 1) u ≤ C * (eLpNormWkp p Ω' k
        (fun z ↦ complexAntilinearPartL (fderiv ℝ u z) 1) + eLpNorm u p (volume.restrict Ω')) := by
  have : FiniteDimensional ℂ F := Module.Finite.of_restrictScalars_finite ℝ ℂ F
  let Eu := EuclideanSpace ℂ (Fin (finrank ℂ F))
  let e : F ≃L[ℂ] Eu := .ofFinrankEq (by simp [Eu])
  set eℝ : F →L[ℝ] Eu := (e : F →L[ℂ] Eu).restrictScalars ℝ
  set sℝ : Eu →L[ℝ] F := (e.symm : Eu →L[ℂ] F).restrictScalars ℝ
  obtain ⟨W, Ω', hKW, hWΩ', -, hΩ'U, C₀, hC₀⟩ :=
    exists_eLpNormWkp_le_of_hasWeakConjWirtingerDerivOn (F := Eu) hp hp_top k hK
      (Ω := ⟨U, hU⟩) hKU
  have hΩ'U' : (Ω' : Set ℂ) ⊆ U := subset_closure.trans hΩ'U
  refine ⟨W, Ω', hKW, hWΩ', hΩ'U', ‖sℝ‖₊ * C₀ * ‖eℝ‖₊, fun u hu ↦ ?_⟩
  set ue : ℂ → Eu := fun z ↦ eℝ (u z)
  have hue : ContDiffOn ℝ (k + 1 : ℕ) ue O := eℝ.contDiff.comp_contDiffOn hu
  set dbu : ℂ → Eu := fun z ↦ conjWirtingerDeriv ue z 1
  have hdbu' (z : ℂ) : dbu z = complexAntilinearPartL (fderiv ℝ ue z) 1 :=
    conjWirtingerDeriv_apply_eq_complexAntilinearPartL ue z 1
  -- `∂bar (e ∘ u) = e (∂bar u)` on `U`.
  have hdbu : ∀ z ∈ U, dbu z = eℝ (complexAntilinearPartL (fderiv ℝ u z) 1) := fun z hz ↦ by
    have hd : DifferentiableAt ℝ u z := ((hu.mono (subset_closure.trans hUO)).differentiableOn
      (by simp)).differentiableAt (hU.mem_nhds hz)
    have hf : fderiv ℝ ue z = eℝ.comp (fderiv ℝ u z) :=
      (eℝ.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
    rw [hdbu', hf, ContinuousLinearMap.complexAntilinearPartL_restrictScalars_comp]
    rfl
  have hdbuO : ContDiffOn ℝ k dbu O := by
    have hf : ContDiffOn ℝ k (fun z ↦ complexAntilinearPartL (fderiv ℝ ue z) 1) O :=
      (ContinuousLinearMap.apply ℝ Eu (1 : ℂ)).contDiff.comp_contDiffOn
        (complexAntilinearPartL.contDiff.comp_contDiffOn
          (hue.fderiv_of_isOpen hO (by push_cast; exact le_rfl)))
    exact hf.congr fun z _ ↦ hdbu' z
  have h₁ := hC₀ ue dbu (hue.continuousOn.mono (subset_closure.trans hUO)).memLpLoc
    (hdbuO.memWkpLoc (Ω := ⟨O, hO⟩) (subset_closure.trans hUO))
    (hasWeakConjWirtingerDerivOn_of_contDiffOn
      ((hue.mono (subset_closure.trans hUO)).of_le (by exact_mod_cast Nat.le_add_left 1 k)))
  rw [eLpNormWkp_congr_ae (show dbu =ᵐ[volume.restrict Ω'] _ from
    (ae_restrict_mem Ω'.isOpen.measurableSet).mono fun z hz ↦ hdbu z (hΩ'U' hz))] at h₁
  have h₂ := eLpNormWkp_clm_comp_le (p := p) (U := Ω') (k := 0) (f := u) eℝ
  rw [eLpNormWkp_zero, eLpNormWkp_zero] at h₂
  have hu' : eLpNormWkp p W (k + 1) u = eLpNormWkp p W (k + 1) (fun z ↦ sℝ (ue z)) := by
    congr 1
    funext z
    simp [sℝ, ue, eℝ]
  refine hu'.trans_le ((eLpNormWkp_clm_comp_le sℝ).trans ?_)
  calc ‖sℝ‖ₑ * eLpNormWkp p W (k + 1) ue
      ≤ ‖sℝ‖ₑ * (C₀ * (‖eℝ‖ₑ * eLpNormWkp p Ω' k (fun z ↦ complexAntilinearPartL
          (fderiv ℝ u z) 1) + ‖eℝ‖ₑ * eLpNorm u p (volume.restrict Ω'))) := by
        gcongr
        exact h₁.trans (by gcongr; exact eLpNormWkp_clm_comp_le eℝ)
    _ = _ := by
        simp only [eNorm_eq_nnNorm]
        push_cast
        ring

/-- **Interior `W^{k+1,p}` estimate for `∂bar` plus a zeroth-order term.** Let `U` be open with
compact closure inside an open set `O`, let `K ⊆ U` be compact and let `Z` be a field of real-linear
maps that is `Cᵏ` on `O`. For `1 < p < ∞` there are an open neighbourhood `W ⊆ U` of `K` and a
constant `C` such that every `u` that is `C^{k+1}` on `O`, with `g = ∂bar u + Z u` on `U`, satisfies
`‖u‖_{W^{k+1,p}(W)} ≤ C (‖g‖_{W^{k,p}(U)} + ‖u‖_{W^{k,p}(U)})`. The real structure of the values is
any one compatible with the complex structure. -/
theorem exists_eLpNormWkp_le_of_eqOn_complexAntilinearPartL_add (hp : 1 < p) (hp_top : p ≠ ⊤)
    (k : ℕ) {U O K : Set ℂ} (hU : IsOpen U) (hO : IsOpen O) (hUc : IsCompact (closure U))
    (hUO : closure U ⊆ O) (hK : IsCompact K) (hKU : K ⊆ U) {Z : ℂ → F →L[ℝ] ℂ →L[ℝ] F}
    (hZ : ContDiffOn ℝ k Z O) :
    ∃ W : Opens ℂ, K ⊆ W ∧ (W : Set ℂ) ⊆ U ∧ ∃ C : ℝ≥0, ∀ (u : ℂ → F) (g : ℂ → ℂ →L[ℝ] F),
      ContDiffOn ℝ (k + 1 : ℕ) u O →
      (∀ z ∈ U, g z = complexAntilinearPartL (fderiv ℝ u z) + Z z (u z)) →
      eLpNormWkp p W (k + 1) u ≤ C * (eLpNormWkp p U k g + eLpNormWkp p U k u) := by
  obtain ⟨W, Ω', hKW, hWΩ', hΩ'U, C₀, hC₀⟩ :=
    exists_eLpNormWkp_le_of_contDiffOn (F := F) hp hp_top k hU hO hUO hK hKU
  obtain ⟨c, hc⟩ := hUc.exists_bound_iteratedFDeriv hO hUO hZ
  set e₁ : (ℂ →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (1 : ℂ)
  obtain ⟨L, hL⟩ := exists_eLpNormWkp_clm_apply_le (G₂ := F) (G₃ := ℂ →L[ℝ] F)
    (Fact.out : 1 ≤ p) k c
  refine ⟨W, hKW, hWΩ'.trans hΩ'U, C₀ * ‖e₁‖₊ * (1 + L) + C₀, fun u g hu hg ↦ ?_⟩
  have huU : ContDiffOn ℝ (k + 1 : ℕ) u U := hu.mono (subset_closure.trans hUO)
  set X := eLpNormWkp p U k g
  set Y := eLpNormWkp p U k u
  -- `∂bar u = g - Z u` on `U`.
  have h₁ : eLpNormWkp p Ω' k (fun z ↦ complexAntilinearPartL (fderiv ℝ u z) 1) ≤
      ‖e₁‖ₑ * (X + L * Y) := by
    rw [eLpNormWkp_congr_ae (show (fun z ↦ complexAntilinearPartL (fderiv ℝ u z) 1)
      =ᵐ[volume.restrict Ω'] fun z ↦ e₁ (g z + (-Z z) (u z)) from
        (ae_restrict_mem Ω'.isOpen.measurableSet).mono fun z hz ↦ by
          simp [e₁, hg z (hΩ'U hz)])]
    refine (eLpNormWkp_clm_comp_le e₁).trans ?_
    gcongr
    refine (eLpNormWkp_add_le (Fact.out : 1 ≤ p) (f := g) (g := fun z ↦ (-Z z) (u z))).trans
      (add_le_add (eLpNormWkp_mono_set hΩ'U) ?_)
    refine (hL Ω'.isOpen Ω'.isOpen subset_rfl
      (hZ.neg.mono (hΩ'U.trans (subset_closure.trans hUO)))
      ((huU.of_le (by exact_mod_cast Nat.le_succ k)).mono hΩ'U)
      (fun x hx l hl ↦ by
        rw [show (fun y ↦ -Z y) = -Z from rfl, iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
        exact hc x (subset_closure (hΩ'U hx)) l hl)
      fun x hx ↦ absurd hx.1 hx.2).trans ?_
    gcongr
    exact eLpNormWkp_mono_set hΩ'U
  have h₂ : eLpNorm u p (volume.restrict Ω') ≤ Y :=
    (eLpNorm_mono_measure _ (Measure.restrict_mono hΩ'U le_rfl)).trans eLpNorm_le_eLpNormWkp
  calc eLpNormWkp p W (k + 1) u ≤ C₀ * (‖e₁‖ₑ * (X + L * Y) + Y) :=
        (hC₀ u hu).trans (by gcongr)
    _ ≤ C₀ * (‖e₁‖ₑ * (X + L * Y) + Y + (‖e₁‖ₑ * Y + ‖e₁‖ₑ * L * X + X)) := by
        gcongr _ * ?_
        exact le_self_add
    _ = ((C₀ * ‖e₁‖₊ * (1 + L) + C₀ : ℝ≥0) : ℝ≥0∞) * (X + Y) := by
        simp only [eNorm_eq_nnNorm]
        push_cast
        ring

end Planar

/-! ### The estimate in one chart -/

section Global

open SmoothAlmostComplexStructure FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealCauchyRiemannHigherOrderEstimate : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] (A : FiniteBundleAtlas ℂ M F V)
  {D : (Π x : M, V x) → Π x : M, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
  (hD : IsRealCauchyRiemannOperator F (ofComplexManifold ℂ M) D)
  (hDs : ContMDiffCovariantDerivativeOn F ∞ D univ)
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace IsRealCauchyRiemannOperator

include hD hDs in
/-- **The higher-order elliptic estimate in a chart.** Let `χ` be a smooth function whose support
has closure in the domain of chart `i`. For `1 < p < ∞` and every `k` there is a constant `C` such
that, for every smooth section `s`, the reading of `χ s` in chart `i` satisfies
`‖(χ s)ᵢ‖_{W^{k+1,p}} ≤ C (‖(D s)ᵢ‖_{W^{k,p}} + ‖sᵢ‖_{W^{k,p}})` on the image of the chart. -/
theorem exists_eLpNormWkp_coord_smul_le (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) {i : Fin A.n}
    {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C : ℝ≥0, ∀ s : Π x, V x,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      eLpNormWkp p (A.image i) (k + 1) (A.coord i fun x ↦ χ x • s x) ≤
        C * (eLpNormWkp p (A.image i) k (A.tangentHom.coord i (D s)) +
          eLpNormWkp p (A.image i) k (A.coord i s)) := by
  have := A.compactSpace
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  have htop (m : ℕ) : ((m : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := ENat.LEInfty.out
  set U : Set ℂ := (A.image i : Set ℂ)
  have hU : IsOpen U := (A.image i).isOpen
  set O : Set ℂ := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet
  have hUO : closure U ⊆ O :=
    (A.closure_image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i)
  have hcl : closure U ⊆ (A.chart i).target := A.closure_image_subset_target i
  set K : Set ℂ := A.chart i '' tsupport χ
  have hK : IsCompact K := (isClosed_tsupport χ).isCompact.image_of_continuousOn
    ((A.chart i).continuousOn.mono (hχi.trans (A.dom_subset_chart_source i)))
  set χ' : ℂ → ℝ := fun y ↦ χ ((A.chart i).symm y)
  have hχ' : ContDiffOn ℝ ∞ χ' (A.chart i).target := A.contDiffOn_comp_chart_symm hχ i
  have hχK : ∀ z ∈ U, z ∉ K → χ' z = 0 := fun z hz hzK ↦ by
    by_contra h
    exact hzK ⟨_, subset_tsupport _ h, (A.chart i).right_inv (hcl (subset_closure hz))⟩
  obtain ⟨W, hKW, hWU, C₀, hC₀⟩ := exists_eLpNormWkp_le_of_eqOn_complexAntilinearPartL_add
    (F := F) hp hp_top k hU ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet)
    (A.isCompact_closure_image i) hUO hK (fun y hy ↦ A.mem_image.2 (image_mono hχi hy))
    ((by simpa only [inter_univ] using A.contDiffOn_chartZeroOrder hD hDs isOpen_univ i :
      ContDiffOn ℝ ∞ (A.chartZeroOrder D i) O).of_le (htop _))
  obtain ⟨c, hc⟩ := (A.isCompact_closure_image i).exists_bound_iteratedFDeriv
    (A.chart i).open_target hcl (m := k + 1) (hχ'.of_le (htop _))
  set B : ℝ →L[ℝ] F →L[ℝ] F := ContinuousLinearMap.lsmul ℝ ℝ
  refine ⟨((k + 1 : ℕ) + 1 : ℝ≥0) * (‖B‖₊ * c * 2 ^ (k + 1)) * C₀, fun s hs ↦ ?_⟩
  have hu : ContDiffOn ℝ (k + 1 : ℕ) (A.coord i s) O := A.contDiffOn_coord (hs.of_le (htop _)) i
  have hW := hC₀ _ _ hu fun z hz ↦
    A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hz
      ((hs _).mdifferentiableAt (by simp))
  -- Localize the reading of `χ s` to `W`, where the interior estimate applies.
  rw [eLpNormWkp_congr_ae (show (A.coord i fun x ↦ χ x • s x) =ᵐ[volume.restrict U]
      fun y ↦ B (χ' y) (A.coord i s y) from (ae_restrict_mem hU.measurableSet).mono
        fun y hy ↦ A.coord_fun_smul i χ s hy), ENNReal.coe_mul, mul_assoc]
  refine (eLpNormWkp_bilin_le (Fact.out : 1 ≤ p) B hU W.isOpen hWU
    ((hχ'.of_le (htop _)).mono (subset_closure.trans hcl)) (hu.mono (subset_closure.trans hUO))
    (fun x hx l hl ↦ hc x (subset_closure (hWU hx)) l hl) fun x hx l _ ↦ ?_).trans
    (by gcongr)
  -- Off `K` the product vanishes near `x`.
  have hev : (fun y ↦ B (χ' y) (A.coord i s y)) =ᶠ[nhds x] 0 := by
    filter_upwards [(hU.sdiff hK.isClosed).mem_nhds ⟨hx.1, fun h ↦ hx.2 (hKW h)⟩] with y hy
    simp [B, hχK y hy.1 hy.2]
  rw [(hev.iteratedFDeriv ℝ l).eq_of_nhds, iteratedFDeriv_zero]
  rfl

include hD hDs in
/-- For a smooth section `s` with Sobolev section `w`, the `W^{k,p}` norms of the readings of `D s`
and of `s` in chart `i` are bounded by a multiple of `‖D w‖_{W^{k,p}} + ‖w‖_{W^{k,p}}`. -/
private theorem exists_eLpNormWkp_coord_le (k : ℕ) (i : Fin A.n) :
    ∃ c : ℝ≥0, ∀ s : Cₛ^((k + 1 : ℕ) : ℕ∞ω)⟮𝓘(ℝ, ℂ); F, V⟯,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      eLpNormWkp p (A.image i) k (A.tangentHom.coord i (D s)) +
          eLpNormWkp p (A.image i) k (A.coord i s) ≤
        c * (ENNReal.ofReal ‖hD.sobolevSuccL A hDs volume p k
            (SobolevSection.ofContMDiffSection A volume p (k + 1) s)‖ +
          ENNReal.ofReal ‖A.sectionChartData.lowerOrderL volume p k
            (SobolevSection.ofContMDiffSection A volume p (k + 1) s)‖) := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  have htop (m : ℕ) : ((m : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := ENat.LEInfty.out
  obtain ⟨c₂, hc₂⟩ :=
    A.tangentHom.sectionChartData.exists_eLpNormWkp_le_of_chartValueL_ae_eq (p := p) k
  obtain ⟨c₃, hc₃⟩ := A.sectionChartData.exists_eLpNormWkp_le_of_chartValueL_ae_eq (p := p) k
  refine ⟨c₂ + c₃, fun s hs ↦ ?_⟩
  set O : Set ℂ := (A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.triv i).baseSet
  have hUO : (A.image i : Set ℂ) ⊆ O :=
    (A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i)
  set w := SobolevSection.ofContMDiffSection A volume p (k + 1) s
  set u := A.coord i s
  have hu : ContDiffOn ℝ (k + 1 : ℕ) u O := A.contDiffOn_coord (hs.of_le (htop _)) i
  -- The reading of `D s` is `∂bar u + Z u`, of class `Cᵏ`.
  have hg : ContDiffOn ℝ k (A.tangentHom.coord i (D s)) (A.image i) := by
    have hf : ContDiffOn ℝ k (fun z ↦ complexAntilinearPartL (fderiv ℝ u z) +
        A.chartZeroOrder D i z (u z)) O :=
      (complexAntilinearPartL.contDiff.comp_contDiffOn
        (hu.fderiv_of_isOpen ((A.chart i).isOpen_inter_preimage_symm (A.triv i).open_baseSet)
          (by push_cast; exact le_rfl))).add
        (((by simpa only [inter_univ] using A.contDiffOn_chartZeroOrder hD hDs isOpen_univ i :
          ContDiffOn ℝ ∞ (A.chartZeroOrder D i) O).of_le (htop _)).clm_apply
          (hu.of_le (by exact_mod_cast Nat.le_succ k)))
    exact (hf.mono hUO).congr fun z hz ↦
      A.coord_tangentHom_eq_complexAntilinearPartL_fderiv_add_chartZeroOrder hD hz
        ((hs _).mdifferentiableAt (by simp))
  set Dw : A.tangentHom.sectionChartData.SobolevData volume p k :=
    ((hD.sobolevSuccL A hDs volume p k w : SobolevSection A.tangentHom volume p k) :
      A.tangentHom.sectionChartData.SobolevData volume p k)
  set w₀ : A.sectionChartData.SobolevData volume p k :=
    ((A.sectionChartData.lowerOrderL volume p k w : SobolevSection A volume p k) :
      A.sectionChartData.SobolevData volume p k)
  have h₂ := hc₂ (i := i) (w := Dw) (by rw [sectionChartData_image_tangentHom]; exact hg)
    ((ae_image_tangentHom_iff A volume i).2
      (chartValueL_sobolevSuccL_ofContMDiffSection_ae A hD hDs volume p k s i))
  rw [sectionChartData_image_tangentHom] at h₂
  have h₃ := hc₃ (i := i) (w := w₀) ((hu.of_le (by exact_mod_cast Nat.le_succ k)).mono hUO)
    ((A.sectionChartData.chartValueL_coe_lowerOrderL volume p k w i).symm ▸
      SobolevSection.chartValueL_ofContMDiffSection_ae A volume p (k + 1) s i)
  calc _ ≤ c₂ * ENNReal.ofReal ‖hD.sobolevSuccL A hDs volume p k w‖ +
        c₃ * ENNReal.ofReal ‖A.sectionChartData.lowerOrderL volume p k w‖ :=
        add_le_add (h₂.trans (by gcongr; exact (norm_le_pi_norm Dw i).trans (le_of_eq rfl)))
          (h₃.trans (by gcongr; exact (norm_le_pi_norm w₀ i).trans (le_of_eq rfl)))
    _ ≤ c₂ * ENNReal.ofReal ‖hD.sobolevSuccL A hDs volume p k w‖ +
        c₃ * ENNReal.ofReal ‖A.sectionChartData.lowerOrderL volume p k w‖ +
        (c₂ * ENNReal.ofReal ‖A.sectionChartData.lowerOrderL volume p k w‖ +
          c₃ * ENNReal.ofReal ‖hD.sobolevSuccL A hDs volume p k w‖) := le_self_add
    _ = _ := by
        push_cast
        ring

include hD hDs in
/-- **The chart estimate in Sobolev norms, for smooth sections.** For a smooth `χ` whose support
has closure in the domain of chart `i`, the chart-`i` components of `χ w`, for the Sobolev section
`w` of a smooth section, are bounded in `W^{k+1,p}` by a multiple of
`‖D w‖_{W^{k,p}} + ‖w‖_{W^{k,p}}`. -/
private theorem exists_norm_contMDiffSMulL_component_le (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    {i : Fin A.n} {χ : M → ℝ} (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (hχi : tsupport χ ⊆ A.dom i) :
    ∃ C : ℝ, ∀ s : Cₛ^((k + 1 : ℕ) : ℕ∞ω)⟮𝓘(ℝ, ℂ); F, V⟯,
      ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, F)) ∞ (fun x ↦ TotalSpace.mk' F x (s x)) →
      ‖(SobolevSection.contMDiffSMulL A volume p (k + 1) hχ
          (SobolevSection.ofContMDiffSection A volume p (k + 1) s) :
            A.sectionChartData.SobolevData volume p (k + 1)) i‖ ≤
        C * (‖hD.sobolevSuccL A hDs volume p k
            (SobolevSection.ofContMDiffSection A volume p (k + 1) s)‖ +
          ‖A.sectionChartData.lowerOrderL volume p k
            (SobolevSection.ofContMDiffSection A volume p (k + 1) s)‖) := by
  have htop (m : ℕ) : ((m : ℕ) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := ENat.LEInfty.out
  obtain ⟨Cc, hCc⟩ := exists_eLpNormWkp_coord_smul_le A hD hDs hp hp_top k hχ hχi
  obtain ⟨c₁, hc₁⟩ :=
    A.sectionChartData.exists_ofReal_norm_le_eLpNormWkp_of_chartValueL_ae_eq (p := p) (k + 1)
  obtain ⟨c, hc⟩ := exists_eLpNormWkp_coord_le A hD hDs (p := p) k i
  refine ⟨c₁ * Cc * c, fun s hs ↦ ?_⟩
  set w := SobolevSection.ofContMDiffSection A volume p (k + 1) s
  set a := ‖hD.sobolevSuccL A hDs volume p k w‖
  set b := ‖A.sectionChartData.lowerOrderL volume p k w‖
  have ha0 : 0 ≤ a := (norm_nonneg (hD.sobolevSuccL A hDs volume p k w :
    SobolevSection A.tangentHom volume p k)).trans (le_of_eq rfl)
  have hb0 : 0 ≤ b := norm_nonneg _
  have hcχ : ContDiffOn ℝ (k + 1 : ℕ) (A.coord i fun x ↦ χ x • s x) (A.image i) :=
    (A.contDiffOn_coord ((hχ.of_le (htop _)).smul_section s.contMDiff) i).mono
      ((A.image_subset_chart_image_closure_dom i).trans (A.chart_image_closure_dom_subset i))
  have h₁ := hc₁ hcχ (SobolevSection.chartValueL_contMDiffSMulL_ae_coord hχ
    (SobolevSection.chartValueL_ofContMDiffSection_ae A volume p (k + 1) s) i)
  refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (h₁.trans ?_)
  calc (c₁ : ℝ≥0∞) * eLpNormWkp p (A.image i) (k + 1) (A.coord i fun x ↦ χ x • s x)
      ≤ c₁ * (Cc * (c * (ENNReal.ofReal a + ENNReal.ofReal b))) := by
        gcongr
        exact (hCc s hs).trans (by gcongr; exact hc s hs)
    _ = ENNReal.ofReal (c₁ * Cc * c * (a + b)) := by
        rw [← ENNReal.ofReal_add ha0 hb0, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.ofReal_coe_nnreal, mul_assoc]

include hD hDs in
/-- **The elliptic estimate one order up.** Let `D` be a smooth real Cauchy–Riemann operator on a
complex vector bundle `V` over a compact boundaryless complex curve, with a finite bundle atlas `A`,
and let `1 < p < ∞`. For every `k` there is a constant `C` such that every
`ξ ∈ W^{k+1,p}(Σ, V)` satisfies `‖ξ‖_{W^{k+1,p}} ≤ C (‖D ξ‖_{W^{k,p}} + ‖ξ‖_{W^{k,p}})`, where `D ξ`
is the realization `TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL`. -/
theorem exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL (hp : 1 < p) (hp_top : p ≠ ⊤)
    (k : ℕ) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume p (k + 1),
      ‖w‖ ≤ C * (‖hD.sobolevSuccL A hDs volume p k w‖ +
        ‖A.sectionChartData.lowerOrderL volume p k w‖) := by
  have := A.compactSpace
  -- A partition of unity subordinate to the chart domains, and cutoffs equal to one on its
  -- supports.
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ A.dom
    A.isOpen_dom (by rw [A.iUnion_dom])
  have hχ1 (x : M) : ∑ i, χ i x = 1 := by
    simpa [finsum_eq_sum_of_fintype] using χ.sum_eq_one (mem_univ x)
  choose ψ hψ _ hψi hψ1 using fun i ↦
    (isClosed_tsupport (χ i)).exists_contMDiff_tsupport_subset_eq_one_iff (I := 𝓘(ℝ, ℂ))
      (A.isOpen_dom i) (hχ i)
  choose Cψ hCψ using fun i ↦
    SobolevSection.exists_norm_contMDiffSMulL_le (μ := volume) (p := p) (k := k + 1) (hψ i)
      (hψi i)
  choose Cc hCc using fun i ↦
    exists_norm_contMDiffSMulL_component_le A hD hDs hp hp_top k (χ i).contMDiff (hχ i)
  set C := ∑ i, max (Cψ i) 0 * max (Cc i) 0
  refine ⟨C, fun w ↦ ?_⟩
  -- The estimate is a closed condition, so it suffices to prove it on the dense set of smooth
  -- sections.
  have hP : IsClosed {w : SobolevSection A volume p (k + 1) | ‖w‖ ≤ C *
      (‖hD.sobolevSuccL A hDs volume p k w‖ + ‖A.sectionChartData.lowerOrderL volume p k w‖)} :=
    isClosed_le continuous_norm (continuous_const.mul
      (((continuous_norm (E := zeroOneSobolevSections A volume p k)).comp
        (hD.sobolevSuccL A hDs volume p k).continuous).add
      (continuous_norm.comp (A.sectionChartData.lowerOrderL volume p k).continuous)))
  have hdense := SobolevSection.dense_ofContMDiffSection_contMDiff (A := A) (μ := volume)
    (p := p) (k := k + 1) hp_top
  refine hP.closure_subset_iff.2 ?_ (hdense.closure_eq ▸ mem_univ w)
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_ofPred_eq]
  set w := SobolevSection.ofContMDiffSection A volume p (k + 1) s
  set X := ‖hD.sobolevSuccL A hDs volume p k w‖ + ‖A.sectionChartData.lowerOrderL volume p k w‖
  calc ‖w‖ = ‖∑ i, SobolevSection.contMDiffSMulL A volume p (k + 1) (χ i).contMDiff w‖ := by
        rw [SobolevSection.sum_contMDiffSMulL_eq_self_of_sum_eq_one _ hχ1]
    _ ≤ ∑ i, ‖SobolevSection.contMDiffSMulL A volume p (k + 1) (χ i).contMDiff w‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, max (Cψ i) 0 * max (Cc i) 0 * X := Finset.sum_le_sum fun i _ ↦ ?_
    _ = C * X := by rw [Finset.sum_mul]
  set v := SobolevSection.contMDiffSMulL A volume p (k + 1) (χ i).contMDiff w
  have hvi := hCc i s hs
  calc ‖v‖ = ‖SobolevSection.contMDiffSMulL A volume p (k + 1) (hψ i) v‖ := by
        rw [SobolevSection.contMDiffSMulL_contMDiffSMulL_of_eqOn _ (hψ i) fun _ h ↦ (hψ1 i _).1 h]
    _ ≤ Cψ i * ‖(v : A.sectionChartData.SobolevData volume p (k + 1)) i‖ := hCψ i v
    _ ≤ max (Cψ i) 0 * ‖(v : A.sectionChartData.SobolevData volume p (k + 1)) i‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    _ ≤ max (Cψ i) 0 * (max (Cc i) 0 * X) := by
        gcongr
        exact hvi.trans (by gcongr; exact le_max_left _ _)
    _ = max (Cψ i) 0 * max (Cc i) 0 * X := by ring

omit [IsManifold 𝓘(ℂ) ∞ M] [T2Space M] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- Forgetting all derivatives does not change the chart data. -/
private theorem chartValuesL_lowerOrdersL_zero (k : ℕ) (w : SobolevSection A volume p (k + 1)) :
    A.sectionChartData.chartValuesL volume p 0
        (A.sectionChartData.lowerOrdersL volume p 0 (k + 1) ((zero_add (k + 1)).symm ▸ w)) =
      A.sectionChartData.chartValuesL volume p (k + 1) w := by
  rw [SectionChartData.chartValuesL_lowerOrdersL, SectionChartData.chartValuesL_eqRec]

omit [IsManifold 𝓘(ℂ) ∞ M] [T2Space M] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℂ)] in
/-- Forgetting all derivatives of a section of order `k + 2` is forgetting all derivatives of the
section after forgetting the highest one. -/
private theorem lowerOrdersL_zero_lowerOrderL (k : ℕ) (w : SobolevSection A volume p (k + 1 + 1)) :
    A.sectionChartData.lowerOrdersL volume p 0 (k + 1)
        ((zero_add (k + 1)).symm ▸ A.sectionChartData.lowerOrderL volume p (k + 1) w) =
      A.sectionChartData.lowerOrdersL volume p 0 (k + 1 + 1) ((zero_add (k + 1 + 1)).symm ▸ w) := by
  apply A.sectionChartData.chartValuesL_injective volume p 0
  rw [SectionChartData.chartValuesL_lowerOrdersL, SectionChartData.chartValuesL_lowerOrdersL,
    SectionChartData.chartValuesL_eqRec, SectionChartData.chartValuesL_eqRec,
    SectionChartData.chartValuesL_lowerOrderL]

include hD hDs in
/-- **The higher-order elliptic estimate for a smooth real Cauchy–Riemann operator on a closed
surface.** Let `D` be a smooth real Cauchy–Riemann operator on a complex vector bundle `V` over a
compact boundaryless complex curve, with a finite bundle atlas `A`, and let `1 < p < ∞`. For every
`k` there is a constant `C` such that every `ξ ∈ W^{k+1,p}(Σ, V)` satisfies
`‖ξ‖_{W^{k+1,p}} ≤ C (‖D ξ‖_{W^{k,p}} + ‖ξ‖_{Lᵖ})`, where `D ξ` is the realization
`TauCeti.IsRealCauchyRiemannOperator.sobolevSuccL` and `‖ξ‖_{Lᵖ}` is the norm of `ξ` in
`W^{0,p}(Σ, V)`, all `k + 1` derivatives forgotten. -/
theorem exists_norm_le_norm_sobolevSuccL_add_norm (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ) :
    ∃ C : ℝ, ∀ w : SobolevSection A volume p (k + 1),
      ‖w‖ ≤ C * (‖hD.sobolevSuccL A hDs volume p k w‖ +
        ‖A.sectionChartData.lowerOrdersL volume p 0 (k + 1) ((zero_add (k + 1)).symm ▸ w)‖) := by
  induction k with
  | zero =>
    obtain ⟨C, hC⟩ := exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL A hD hDs hp hp_top 0
    refine ⟨C, fun w ↦ (hC w).trans_eq ?_⟩
    congr 3
    apply A.sectionChartData.chartValuesL_injective volume p 0
    rw [SectionChartData.chartValuesL_lowerOrderL, chartValuesL_lowerOrdersL_zero A 0 w]
  | succ k ih =>
    obtain ⟨C₁, hC₁⟩ :=
      exists_norm_le_norm_sobolevSuccL_add_norm_lowerOrderL A hD hDs hp hp_top (k + 1)
    obtain ⟨C₂, hC₂⟩ := ih
    refine ⟨max C₁ 0 * (1 + max C₂ 0 * 2), fun w ↦ ?_⟩
    set w' := A.sectionChartData.lowerOrderL volume p (k + 1) w
    set S := ‖hD.sobolevSuccL A hDs volume p (k + 1) w‖
    set L := ‖A.sectionChartData.lowerOrdersL volume p 0 (k + 1 + 1)
      ((zero_add (k + 1 + 1)).symm ▸ w)‖
    have hS0 : 0 ≤ S := (norm_nonneg (hD.sobolevSuccL A hDs volume p (k + 1) w :
      SobolevSection A.tangentHom volume p (k + 1))).trans (le_of_eq rfl)
    have hL0 : 0 ≤ L := norm_nonneg _
    have hw0 : 0 ≤ ‖w'‖ := norm_nonneg _
    -- The realization on `w'` is the lowered realization on `w`.
    have hS' : ‖hD.sobolevSuccL A hDs volume p k w'‖ ≤ S := by
      rw [← zeroOneLowerOrdersL_sobolevSuccL A hD hDs volume p k w]
      calc ‖zeroOneLowerOrdersL A volume p k 1 (hD.sobolevSuccL A hDs volume p (k + 1) w)‖
          = ‖A.tangentHom.sectionChartData.lowerOrderL volume p k
              (hD.sobolevSuccL A hDs volume p (k + 1) w :
                SobolevSection A.tangentHom volume p (k + 1))‖ := by
            rw [← SectionChartData.lowerOrdersL_one, ← coe_zeroOneLowerOrdersL]
            rfl
        _ ≤ S := (A.tangentHom.sectionChartData.norm_lowerOrderL_le _).trans (le_of_eq rfl)
    have hw' : ‖w'‖ ≤ max C₂ 0 * (S + L) := by
      refine (hC₂ w').trans ?_
      rw [lowerOrdersL_zero_lowerOrderL A k w]
      refine mul_le_mul (le_max_left _ _) (add_le_add hS' le_rfl) ?_ (le_max_right _ _)
      exact add_nonneg ((norm_nonneg (hD.sobolevSuccL A hDs volume p k w' :
        SobolevSection A.tangentHom volume p k)).trans (le_of_eq rfl)) (norm_nonneg _)
    have h₁ : 0 ≤ max C₁ 0 := le_max_right _ _
    have h₂ : 0 ≤ max C₂ 0 := le_max_right _ _
    calc ‖w‖ ≤ max C₁ 0 * (S + ‖w'‖) :=
          (hC₁ w).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hS0 hw0))
      _ ≤ max C₁ 0 * (S + max C₂ 0 * (S + L)) := by gcongr
      _ ≤ max C₁ 0 * (1 + max C₂ 0 * 2) * (S + L) := by
          nlinarith [mul_nonneg h₁ (mul_nonneg h₂ hL0), mul_nonneg h₁ (mul_nonneg h₂ hS0),
            mul_nonneg h₁ hL0]

end IsRealCauchyRiemannOperator

end Global

end TauCeti
