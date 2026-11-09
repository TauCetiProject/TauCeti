/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Smooth multiplication on `W^{k,p}(Ω)`

Let `Ω` be an open set whose closure is compact and contained in an open set `U`, and let `ψ` be
smooth on `U`. Multiplication by `ψ` is a continuous linear endomorphism of `W^{k,p}(Ω)` for every
order `k` and every `1 ≤ p ≤ ∞` (`TauCeti.Wkp.contDiffOnSMulL`). No boundary regularity of `Ω`
and no bound on `ψ` outside `closure Ω` is assumed.

The product exists by `TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn` and is unique because an
element of `W^{k,p}(Ω)` is determined by its value (`TauCeti.Wkp.ext`), so the map is linear.
It is continuous by the closed graph theorem: its value is the `Lᵖ` product `ψ u`, which is
continuous in `u` because `ψ` is bounded on `Ω`.

This is the global companion of zero-boundary smooth multiplication
`TauCeti.Wkp0.contDiffSMulL`: no compact support of `ψ` in `Ω` is required, but `ψ` must be smooth
on a neighbourhood of the compact set `closure Ω`.

## Main declarations

* `TauCeti.Wkp.contDiffOnSMulL`: multiplication by `ψ` as an element of
  `W^{k,p}(Ω) →L[ℝ] W^{k,p}(Ω)`.
* `TauCeti.Wkp.value_contDiffOnSMulL_ae`: its value is `ψ u` almost everywhere on `Ω`.
* `TauCeti.Wkp.eq_contDiffOnSMulL_iff`: it is the unique element of `W^{k,p}(Ω)` with that value.
* `TauCeti.Wkp.lowerOrder_contDiffOnSMulL`: it commutes with forgetting the highest derivative.

## References

L. C. Evans, *Partial Differential Equations*, §5.2.3, Theorem 1(iv).
-/

public section

noncomputable section

namespace TauCeti

namespace Wkp

open Filter MeasureTheory TopologicalSpace
open scoped ContDiff Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ENNReal} [Fact (1 ≤ p)] {U : Set E} {psi : E → ℝ}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] [Fact (1 ≤ p)] in
/-- If `|ψ| ≤ C` on `Ω` and `g = ψ f` almost everywhere on `Ω`, then `‖g‖_p ≤ C ‖f‖_p`. -/
private theorem norm_lp_le_of_ae_eq_mul {C : ℝ} (hC : ∀ x ∈ (Omega : Set E), ‖psi x‖ ≤ C)
    {f g : Lp ℝ p (mu.restrict Omega)}
    (hg : (g : E → ℝ) =ᵐ[mu.restrict Omega] fun x => psi x * f x) :
    ‖g‖ ≤ C * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [hg, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x hxΩ) (norm_nonneg _)

/-- A chosen product `ψ u` in `W^{k,p}(Ω)`; see `TauCeti.Wkp.contDiffOnSMulL`. -/
private def contDiffOnSMulAux (hU : IsOpen U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (hpsi : ContDiffOn ℝ ∞ psi U)
    (u : Wkp mu Omega p k) : Wkp mu Omega p k :=
  (exists_value_ae_eq_mul_of_contDiffOn hU hΩ hΩU k hpsi u).choose

private theorem value_contDiffOnSMulAux (hU : IsOpen U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (hpsi : ContDiffOn ℝ ∞ psi U) (u : Wkp mu Omega p k) :
    (value k (contDiffOnSMulAux hU hΩ hΩU k hpsi u) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => psi x * value k u x :=
  (exists_value_ae_eq_mul_of_contDiffOn hU hΩ hΩU k hpsi u).choose_spec

/-- An element of `W^{k,p}(Ω)` is determined by having value `ψ u` almost everywhere. -/
private theorem eq_of_value_ae_eq_mul {k : ℕ} {u w w' : Wkp mu Omega p k}
    (hw : (value k w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => psi x * value k u x)
    (hw' : (value k w' : E → ℝ) =ᵐ[mu.restrict Omega] fun x => psi x * value k u x) :
    w = w' :=
  ext k (Lp.ext (hw.trans hw'.symm))

/-- Multiplication by `ψ` as a linear endomorphism of `W^{k,p}(Ω)`. -/
private def contDiffOnSMulₗ (hU : IsOpen U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (hpsi : ContDiffOn ℝ ∞ psi U) :
    Wkp mu Omega p k →ₗ[ℝ] Wkp mu Omega p k where
  toFun := contDiffOnSMulAux hU hΩ hΩU k hpsi
  map_add' u v := by
    refine eq_of_value_ae_eq_mul (u := u + v) (value_contDiffOnSMulAux hU hΩ hΩU k hpsi _) ?_
    rw [value_add, value_add]
    filter_upwards [Lp.coeFn_add (value k (contDiffOnSMulAux hU hΩ hΩU k hpsi u))
        (value k (contDiffOnSMulAux hU hΩ hΩU k hpsi v)), Lp.coeFn_add (value k u) (value k v),
      value_contDiffOnSMulAux hU hΩ hΩU k hpsi u, value_contDiffOnSMulAux hU hΩ hΩU k hpsi v]
      with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, Pi.add_apply, Pi.add_apply, h₃, h₄, mul_add]
  map_smul' c u := by
    refine eq_of_value_ae_eq_mul (u := c • u) (value_contDiffOnSMulAux hU hΩ hΩU k hpsi _) ?_
    rw [RingHom.id_apply, value_smul, value_smul]
    filter_upwards [Lp.coeFn_smul c (value k (contDiffOnSMulAux hU hΩ hΩU k hpsi u)),
      Lp.coeFn_smul c (value k u), value_contDiffOnSMulAux hU hΩ hΩU k hpsi u]
      with x h₁ h₂ h₃
    rw [h₁, h₂, Pi.smul_apply, Pi.smul_apply, h₃, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- **Smooth multiplication on `W^{k,p}(Ω)`.** If `Ω` has compact closure inside an open set
`U` and `ψ` is smooth on `U`, multiplication by `ψ` is a continuous linear endomorphism of
`W^{k,p}(Ω)`, for every order `k` and every `1 ≤ p ≤ ∞`. Its value is the pointwise product
(`TauCeti.Wkp.value_contDiffOnSMulL_ae`). -/
def contDiffOnSMulL (hU : IsOpen U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (hpsi : ContDiffOn ℝ ∞ psi U) :
    Wkp mu Omega p k →L[ℝ] Wkp mu Omega p k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := contDiffOnSMulₗ hU hΩ hΩU k hpsi) fun u x y hu hy => by
    -- `ψ` is bounded on `Ω`, so the value of the product depends continuously on the value.
    obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn
      (hpsi.continuousOn.mono hΩU)
    have hC' : ∀ z ∈ (Omega : Set E), ‖psi z‖ ≤ max C 0 :=
      fun z hz => (hC z (subset_closure hz)).trans (le_max_left _ _)
    set L := contDiffOnSMulₗ (mu := mu) (p := p) hU hΩ hΩU k hpsi
    have hval : Tendsto (fun n => value k (L (u n))) atTop (𝓝 (value k (L x))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n => max C 0 * ‖u n - x‖) atTop (𝓝 (max C 0 * 0)) :=
        (tendsto_iff_norm_sub_tendsto_zero.1 hu).const_mul _
      rw [mul_zero] at hlim
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
      have hsub : value k (L (u n)) - value k (L x) = value k (L (u n - x)) := by
        simp only [← valueL_apply, map_sub]
      rw [hsub]
      exact (norm_lp_le_of_ae_eq_mul hC'
        (value_contDiffOnSMulAux hU hΩ hΩU k hpsi (u n - x))).trans
        (mul_le_mul_of_nonneg_left (norm_value_le k _) (le_max_right _ _))
    have hy' : Tendsto (fun n => value k (L (u n))) atTop (𝓝 (value k y)) := by
      simpa only [Function.comp_def, valueL_apply] using
        ((valueL (mu := mu) (Omega := Omega) (p := p) k).continuous.tendsto y).comp hy
    exact ext k (tendsto_nhds_unique hy' hval)

/-- The value of smooth multiplication is the pointwise product almost everywhere on `Ω`. -/
theorem value_contDiffOnSMulL_ae (hU : IsOpen U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (hpsi : ContDiffOn ℝ ∞ psi U)
    (u : Wkp mu Omega p k) :
    (value k (contDiffOnSMulL hU hΩ hΩU k hpsi u) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => psi x * value k u x :=
  value_contDiffOnSMulAux hU hΩ hΩU k hpsi u

/-- Smooth multiplication is characterized by its value: an element of `W^{k,p}(Ω)` equals `ψ u`
exactly when its value is `ψ u` almost everywhere on `Ω`. -/
theorem eq_contDiffOnSMulL_iff (hU : IsOpen U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (hpsi : ContDiffOn ℝ ∞ psi U)
    {u w : Wkp mu Omega p k} :
    w = contDiffOnSMulL hU hΩ hΩU k hpsi u ↔
      (value k w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => psi x * value k u x := by
  refine ⟨fun h => h ▸ value_contDiffOnSMulL_ae hU hΩ hΩU k hpsi u, fun h => ?_⟩
  exact eq_of_value_ae_eq_mul h (value_contDiffOnSMulL_ae hU hΩ hΩU k hpsi u)

/-- Smooth multiplication commutes with forgetting the highest weak derivative. -/
theorem lowerOrder_contDiffOnSMulL (hU : IsOpen U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (hpsi : ContDiffOn ℝ ∞ psi U)
    (u : Wkp mu Omega p (k + 1)) :
    lowerOrder k (contDiffOnSMulL hU hΩ hΩU (k + 1) hpsi u) =
      contDiffOnSMulL hU hΩ hΩU k hpsi (lowerOrder k u) := by
  rw [eq_contDiffOnSMulL_iff, ← value_succ, ← value_succ]
  exact value_contDiffOnSMulL_ae hU hΩ hΩU (k + 1) hpsi u

/-- Multiplication by a constant function is scalar multiplication. -/
theorem contDiffOnSMulL_const (hU : IsOpen U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (c : ℝ) (u : Wkp mu Omega p k) :
    contDiffOnSMulL hU hΩ hΩU k (psi := fun _ => c) contDiffOn_const u = c • u := by
  symm
  rw [eq_contDiffOnSMulL_iff, value_smul]
  filter_upwards [Lp.coeFn_smul c (value k u)] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul]

/-- If `|ψ| ≤ C` on `Ω`, the value of `ψ u` has `Lᵖ` norm at most `C` times that of `u`. -/
theorem norm_value_contDiffOnSMulL_le (hU : IsOpen U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (hpsi : ContDiffOn ℝ ∞ psi U) {C : ℝ} (hC : ∀ x ∈ (Omega : Set E), ‖psi x‖ ≤ C)
    (u : Wkp mu Omega p k) :
    ‖value k (contDiffOnSMulL hU hΩ hΩU k hpsi u)‖ ≤ C * ‖value k u‖ :=
  norm_lp_le_of_ae_eq_mul hC (value_contDiffOnSMulL_ae hU hΩ hΩU k hpsi u)

end Wkp

end TauCeti
