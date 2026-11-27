/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Regularity
public import TauCeti.Analysis.Normed.Operator.ComplexLinearPart
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Sobolev.Local.Multiplication.Bound.ContDiff
import TauCeti.Analysis.Sobolev.Local.SmoothCoefficients
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Interior estimates and regularity for `∂bar` plus a zeroth-order term

Let `U` be an open planar set whose closure is compact and contained in an open set `O`, and let
`F` be a finite-dimensional complex normed space. For `1 < p < ∞` and every `k`, a map `u` that is
`C^{k+1}` on `U` is bounded in `W^{k+1,p}` near any compact `K ⊆ U` by the `W^{k,p}(U)` norm of
`g = ∂bar u + Z u` and the `W^{k,p}(U)` norm of `u`, for any field `Z` of real-linear maps that is
`Cᵏ` on `O` (`TauCeti.exists_eLpNormWkp_le_of_eqOn_complexAntilinearPartL_add`).

The case `Z = 0` (`TauCeti.exists_eLpNormWkp_succ_le_of_contDiffOn`) is the interior estimate
`TauCeti.exists_eLpNormWkp_le_of_hasWeakConjWirtingerDerivOn`, for `C^{k+1}` maps and transported
from a Euclidean space to `F` along a complex linear isomorphism. The zeroth-order term is then
handled by the Leibniz bound `TauCeti.eLpNormWkp_clm_apply_le`.

The matching regularity statement needs no smoothness of `u`: a locally `Lᵖ` map `u` with a weak
derivative, whose `∂bar u + Z u` agrees almost everywhere with a map in `W^{k,p}_loc`, lies in
`W^{k+1,p}_loc` (`TauCeti.memWkpLoc_succ_of_complexAntilinearPartL_add_ae_eq`), for `Z` of class
`Cᵏ`. It follows from the regularity of `∂bar`,
`TauCeti.HasWeakConjWirtingerDerivOn.memWkpLoc_succ`, by raising the order one step at a time.

## Main results

* `TauCeti.exists_eLpNormWkp_succ_le_of_contDiffOn`: the interior estimate for `∂bar` of `C^{k+1}`
  maps with values in `F`.
* `TauCeti.exists_eLpNormWkp_le_of_eqOn_complexAntilinearPartL_add`: the interior estimate for
  `∂bar` plus a zeroth-order term.
* `TauCeti.memWkpLoc_succ_of_hasWeakFDerivOn_of_memWkpLoc_complexAntilinearPartL`: interior
  regularity for `∂bar` of a weakly differentiable map with values in `F`.
* `TauCeti.memWkpLoc_succ_of_complexAntilinearPartL_add_ae_eq`: interior regularity for `∂bar` plus
  a zeroth-order term.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.4.
-/

public section

noncomputable section

open MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL)
open scoped ENNReal NNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F] {p : ℝ≥0∞}

/-- **Interior `W^{k+1,p}` estimate for `∂bar` of `Cᵏ⁺¹` maps.** The interior estimate
`TauCeti.exists_eLpNormWkp_le_of_hasWeakConjWirtingerDerivOn` for maps that are `C^{k+1}` on the
open set `U`, with values in a finite-dimensional complex normed space `F` whose real structure is
any one compatible with the complex one. -/
theorem exists_eLpNormWkp_succ_le_of_contDiffOn (hp : 1 < p) (hp_top : p ≠ ⊤) (k : ℕ)
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ W Ω' : Opens ℂ, K ⊆ W ∧ (W : Set ℂ) ⊆ Ω' ∧ (Ω' : Set ℂ) ⊆ U ∧ ∃ C : ℝ≥0, ∀ u : ℂ → F,
      ContDiffOn ℝ (k + 1 : ℕ) u U →
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
  have hue : ContDiffOn ℝ (k + 1 : ℕ) ue U := eℝ.contDiff.comp_contDiffOn hu
  set dbu : ℂ → Eu := fun z ↦ conjWirtingerDeriv ue z 1
  -- `∂bar (e ∘ u) = e (∂bar u)`.
  have hdbu : dbu = fun z ↦ eℝ (complexAntilinearPartL (fderiv ℝ u z) 1) :=
    funext fun z ↦ e.conjWirtingerDeriv_comp_left_apply u z 1
  have hdbuU : ContDiffOn ℝ k dbu U := hdbu ▸
    eℝ.contDiff.comp_contDiffOn ((ContinuousLinearMap.apply ℝ F (1 : ℂ)).contDiff.comp_contDiffOn
      (complexAntilinearPartL.contDiff.comp_contDiffOn
        (hu.fderiv_of_isOpen hU (by push_cast; exact le_rfl))))
  have h₁ := hC₀ ue dbu hue.continuousOn.memLpLoc (hdbuU.memWkpLoc (Ω := ⟨U, hU⟩) subset_rfl)
    (hasWeakConjWirtingerDerivOn_of_contDiffOn
      (hue.of_le (by exact_mod_cast Nat.le_add_left 1 k)))
  rw [hdbu] at h₁
  have h₂ := eℝ.eLpNormWkp_comp_le (p := p) (U := Ω') (k := 0) (f := u)
  rw [eLpNormWkp_zero, eLpNormWkp_zero] at h₂
  have hu' : eLpNormWkp p W (k + 1) u = eLpNormWkp p W (k + 1) (fun z ↦ sℝ (ue z)) :=
    congrArg _ (funext fun z ↦ by simp [sℝ, ue, eℝ])
  refine hu'.trans_le (sℝ.eLpNormWkp_comp_le.trans ?_)
  calc ‖sℝ‖ₑ * eLpNormWkp p W (k + 1) ue
      ≤ ‖sℝ‖ₑ * (C₀ * (‖eℝ‖ₑ * eLpNormWkp p Ω' k (fun z ↦ complexAntilinearPartL
          (fderiv ℝ u z) 1) + ‖eℝ‖ₑ * eLpNorm u p (volume.restrict Ω'))) := by
        gcongr
        exact h₁.trans (by gcongr _ * ?_; exact add_le_add eℝ.eLpNormWkp_comp_le h₂)
    _ = _ := by
        simp only [eNorm_eq_nnNorm]
        push_cast
        ring

/-- **Interior `W^{k+1,p}` estimate for `∂bar` plus a zeroth-order term.** Let `U` be open with
compact closure inside an open set `O`, let `K ⊆ U` be compact and let `Z` be a field of real-linear
maps that is `Cᵏ` on `O`. For `1 < p < ∞` there are an open neighbourhood `W ⊆ U` of `K` and a
constant `C` such that every `u` that is `C^{k+1}` on `U`, with `g = ∂bar u + Z u` on `U`, satisfies
`‖u‖_{W^{k+1,p}(W)} ≤ C (‖g‖_{W^{k,p}(U)} + ‖u‖_{W^{k,p}(U)})`. The real structure of the values is
any one compatible with the complex structure. -/
theorem exists_eLpNormWkp_le_of_eqOn_complexAntilinearPartL_add (hp : 1 < p) (hp_top : p ≠ ⊤)
    (k : ℕ) {U O K : Set ℂ} (hU : IsOpen U) (hO : IsOpen O) (hUc : IsCompact (closure U))
    (hUO : closure U ⊆ O) (hK : IsCompact K) (hKU : K ⊆ U) {Z : ℂ → F →L[ℝ] ℂ →L[ℝ] F}
    (hZ : ContDiffOn ℝ k Z O) :
    ∃ W : Opens ℂ, K ⊆ W ∧ (W : Set ℂ) ⊆ U ∧ ∃ C : ℝ≥0, ∀ (u : ℂ → F) (g : ℂ → ℂ →L[ℝ] F),
      ContDiffOn ℝ (k + 1 : ℕ) u U →
      (∀ z ∈ U, g z = complexAntilinearPartL (fderiv ℝ u z) + Z z (u z)) →
      eLpNormWkp p W (k + 1) u ≤ C * (eLpNormWkp p U k g + eLpNormWkp p U k u) := by
  obtain ⟨W, Ω', hKW, hWΩ', hΩ'U, C₀, hC₀⟩ :=
    exists_eLpNormWkp_succ_le_of_contDiffOn (F := F) hp hp_top k hU hK hKU
  obtain ⟨c, hc0, hc⟩ := hZ.exists_nonneg_bound_iteratedFDeriv_of_isOpen hO hUc hUO
  set e₁ : (ℂ →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F (1 : ℂ)
  set L : ℝ≥0 := (k + 1) * (⟨c, hc0⟩ * 2 ^ k)
  refine ⟨W, hKW, hWΩ'.trans hΩ'U, C₀ * ‖e₁‖₊ * (1 + L) + C₀, fun u g hu hg ↦ ?_⟩
  set X := eLpNormWkp p U k g
  set Y := eLpNormWkp p U k u
  -- `∂bar u = g - Z u` on `U`.
  have h₁ : eLpNormWkp p Ω' k (fun z ↦ complexAntilinearPartL (fderiv ℝ u z) 1) ≤
      ‖e₁‖ₑ * (X + L * Y) := by
    rw [eLpNormWkp_congr_ae (show (fun z ↦ complexAntilinearPartL (fderiv ℝ u z) 1)
      =ᵐ[volume.restrict Ω'] fun z ↦ e₁ (g z + (-Z z) (u z)) from
        (ae_restrict_mem Ω'.isOpen.measurableSet).mono fun z hz ↦ by
          simp [e₁, hg z (hΩ'U hz)])]
    refine e₁.eLpNormWkp_comp_le.trans ?_
    gcongr
    refine (eLpNormWkp_add_le hp.le (f := g) (g := fun z ↦ (-Z z) (u z))).trans
      (add_le_add (eLpNormWkp_mono_set hΩ'U) ?_)
    refine (eLpNormWkp_clm_apply_le hp.le (a := -Z) (c := ⟨c, hc0⟩) Ω'.isOpen Ω'.isOpen subset_rfl
      (hZ.neg.mono (hΩ'U.trans (subset_closure.trans hUO)))
      ((hu.of_le (by exact_mod_cast Nat.le_succ k)).mono hΩ'U)
      (fun x hx l hl ↦ by
        rw [iteratedFDeriv_neg_apply, norm_neg]
        exact hc l hl x (subset_closure (hΩ'U hx)))
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

/-- **Interior regularity for `∂bar` of a weakly differentiable map.** Let `1 < p < ∞` and let `u`
be locally `Lᵖ` on an open set `Ω`, with weak derivative `Du`. If `∂bar u`, the value on `1` of the
complex antilinear part of `Du`, lies in `W^{k,p}_loc(Ω)`, then `u` lies in `W^{k+1,p}_loc(Ω)`.
The real structure of the values is any one compatible with the complex structure. -/
theorem memWkpLoc_succ_of_hasWeakFDerivOn_of_memWkpLoc_complexAntilinearPartL (hp : 1 < p)
    (hp_top : p ≠ ⊤) {Ω : Opens ℂ} {k : ℕ} {u : ℂ → F} {Du : ℂ → ℂ →L[ℝ] F}
    (hu : MemLpLoc p Ω u) (hDu : HasWeakFDerivOn volume Ω u Du)
    (hf : MemWkpLoc p Ω k fun z ↦ complexAntilinearPartL (Du z) 1) :
    MemWkpLoc p Ω (k + 1) u := by
  have : FiniteDimensional ℂ F := Module.Finite.of_restrictScalars_finite ℝ ℂ F
  let Eu := EuclideanSpace ℂ (Fin (finrank ℂ F))
  let e : F ≃L[ℂ] Eu := .ofFinrankEq (by simp [Eu])
  set eℝ : F →L[ℝ] Eu := (e : F →L[ℂ] Eu).restrictScalars ℝ
  set sℝ : Eu →L[ℝ] F := (e.symm : Eu →L[ℂ] F).restrictScalars ℝ
  have h := (hDu.clm_comp eℝ).hasWeakConjWirtingerDerivOn
  have hfe : (fun z ↦ (2 : ℂ)⁻¹ • ((eℝ.comp (Du z)) 1 + Complex.I • (eℝ.comp (Du z)) Complex.I)) =
      fun z ↦ eℝ (complexAntilinearPartL (Du z) 1) := by
    funext z
    rw [← ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.complexAntilinearPartL_restrictScalars_comp (e : F →L[ℂ] Eu) (Du z),
      ContinuousLinearMap.complexAntilinearPartL_apply_one]
    simp [eℝ, ← Complex.coe_smul]
  rw [hfe] at h
  have hue := h.memWkpLoc_succ hp hp_top (hu.clm_comp eℝ) (hf.clm_comp eℝ)
  simpa [eℝ, sℝ] using hue.clm_comp sℝ

/-- One step of the regularity for `∂bar` plus a zeroth-order term: if `u` is already in
`W^{k,p}_loc(Ω)`, then so is `∂bar u = g - Z u`, and `u` is in `W^{k+1,p}_loc(Ω)`. -/
private theorem memWkpLoc_succ_of_memWkpLoc_of_complexAntilinearPartL_add_ae_eq (hp : 1 < p)
    (hp_top : p ≠ ⊤) {Ω : Opens ℂ} {k : ℕ} {Z : ℂ → F →L[ℝ] ℂ →L[ℝ] F}
    (hZ : ContDiffOn ℝ k Z Ω) {u : ℂ → F} {Du g : ℂ → ℂ →L[ℝ] F} (hu : MemWkpLoc p Ω k u)
    (hDu : HasWeakFDerivOn volume Ω u Du) (hg : MemWkpLoc p Ω k g)
    (heq : ∀ᵐ z ∂volume.restrict Ω, complexAntilinearPartL (Du z) + Z z (u z) = g z) :
    MemWkpLoc p Ω (k + 1) u := by
  refine memWkpLoc_succ_of_hasWeakFDerivOn_of_memWkpLoc_complexAntilinearPartL hp hp_top
    hu.memLpLoc hDu (((hg.sub (hu.contDiffOn_clm_apply hZ le_rfl subset_rfl)).clm_comp
      (ContinuousLinearMap.apply ℝ F (1 : ℂ))).congr_ae ?_)
  filter_upwards [heq] with z hz
  simp [← hz]

/-- **Interior regularity for `∂bar` plus a zeroth-order term.** Let `1 < p < ∞`, let `Z` be a
field of real-linear maps that is `Cᵏ` on an open set `Ω`, and let `u` be locally `Lᵖ` on `Ω` with
weak derivative `Du`. If `∂bar u + Z u`, with `∂bar u` the complex antilinear part of `Du`, agrees
almost everywhere with a map `g` in `W^{k,p}_loc(Ω)`, then `u` lies in `W^{k+1,p}_loc(Ω)`. -/
theorem memWkpLoc_succ_of_complexAntilinearPartL_add_ae_eq (hp : 1 < p) (hp_top : p ≠ ⊤)
    {Ω : Opens ℂ} {k : ℕ} {Z : ℂ → F →L[ℝ] ℂ →L[ℝ] F} (hZ : ContDiffOn ℝ k Z Ω) {u : ℂ → F}
    {Du g : ℂ → ℂ →L[ℝ] F} (hu : MemLpLoc p Ω u) (hDu : HasWeakFDerivOn volume Ω u Du)
    (hg : MemWkpLoc p Ω k g)
    (heq : ∀ᵐ z ∂volume.restrict Ω, complexAntilinearPartL (Du z) + Z z (u z) = g z) :
    MemWkpLoc p Ω (k + 1) u := by
  induction k with
  | zero =>
    exact memWkpLoc_succ_of_memWkpLoc_of_complexAntilinearPartL_add_ae_eq hp hp_top hZ
      (memWkpLoc_zero_iff.2 hu) hDu hg heq
  | succ k ih =>
    exact memWkpLoc_succ_of_memWkpLoc_of_complexAntilinearPartL_add_ae_eq hp hp_top hZ
      (ih (hZ.of_le (by exact_mod_cast Nat.le_succ k)) hg.of_succ) hDu hg heq

end TauCeti
