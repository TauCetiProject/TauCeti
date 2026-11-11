/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Leibniz
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn

/-!
# Multiplication on `W^{k,p}(Ω)` by functions smooth up to the boundary

Let `Ω` be an open set whose closure is compact and contained in a set `U` of unique
differentiability, and let `ψ` be smooth on `U`. Multiplication by `ψ` is a continuous linear
endomorphism of `W^{k,p}(Ω)` for every order `k` and every `1 ≤ p ≤ ∞`
(`TauCeti.Wkp.uniqueDiffOnSMulL`).

The set `U` need not be open. The motivating case is the closure of the interior `Ω` of a chart
image of a surface with boundary: there `U` is a relatively open subset of the closed upper
half-plane, and the chart reading of a smooth function on the surface is smooth on `U` up to the
real axis, but in general not on any open neighbourhood of `closure Ω`. For open `U` this is
`TauCeti.Wkp.contDiffOnSMulL`.

Only the restriction of `ψ` to `Ω` enters the product. Its derivatives on `Ω` are the derivatives
of `ψ` within `U`, which are continuous on `U` because `U` is a set of unique differentiability,
hence bounded on the compact set `closure Ω`. So the induction on `k` of
`TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn` goes through with `fderivWithin ℝ ψ U` in place
of `fderiv ℝ ψ` (`TauCeti.Wkp.exists_value_ae_eq_mul_of_uniqueDiffOn`), and the operator is
assembled from these products by the closed graph theorem.

## Main declarations

* `TauCeti.Wkp.exists_value_ae_eq_mul_of_uniqueDiffOn`: `ψ u ∈ W^{k,p}(Ω)` for `u ∈ W^{k,p}(Ω)`.
* `TauCeti.Wkp.uniqueDiffOnSMulL`: multiplication by `ψ` as an element of
  `W^{k,p}(Ω) →L[ℝ] W^{k,p}(Ω)`.
* `TauCeti.Wkp.value_uniqueDiffOnSMulL_ae`, `TauCeti.Wkp.eq_uniqueDiffOnSMulL_iff`: its value is
  `ψ u` almost everywhere on `Ω`, and this characterizes it.
* `TauCeti.Wkp.lowerOrder_uniqueDiffOnSMulL`: it commutes with forgetting the highest derivative.
* `TauCeti.Wkp.uniqueDiffOnSMulL_const`, `TauCeti.Wkp.uniqueDiffOnSMulL_add`,
  `TauCeti.Wkp.uniqueDiffOnSMulL_mul`: constants, additivity and multiplicativity in `ψ`.

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

/-- **Multiplication by a function smooth up to the boundary in `W^{k,p}`.** Let `Ω` have compact
closure inside a set `U` of unique differentiability. If `ψ` is smooth on `U` and
`u ∈ W^{k,p}(Ω)`, then `ψ u` lies in `W^{k,p}(Ω)`: some element of `W^{k,p}(Ω)` has value `ψ u`
almost everywhere on `Ω`. -/
theorem exists_value_ae_eq_mul_of_uniqueDiffOn (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (hpsi : ContDiffOn ℝ ∞ psi U) (u : Wkp mu Omega p k) :
    ∃ w : Wkp mu Omega p k, (value k w : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => psi x * value k u x := by
  -- A function continuous on `U` is bounded on `Ω`, so multiplying by it preserves `Lᵖ(Ω)`.
  have hLp : ∀ {phi : E → ℝ}, ContinuousOn phi U → ∀ f : Lp ℝ p (mu.restrict Omega),
      ∃ g : Lp ℝ p (mu.restrict Omega), (g : E → ℝ) =ᵐ[mu.restrict Omega]
        fun x => phi x * f x := fun {phi} hphi f => by
    have h : MemLp (fun x => phi x * f x) p (mu.restrict Omega) :=
      ((hphi.mono hΩU).memLp_top_restrict_of_subset_isCompact hΩ Omega.isOpen.measurableSet
        subset_closure).fun_mul (Lp.memLp f)
    exact ⟨h.toLp _, h.coeFn_toLp⟩
  induction k generalizing psi with
  | zero => simpa only [value_zero] using hLp hpsi.continuousOn (value 0 u)
  | succ k ih =>
    obtain ⟨g, hg⟩ := hLp hpsi.continuousOn (value (k + 1) u)
    set b := stdOrthonormalBasis ℝ E
    refine (exists_value_eq_of_forall_hasWeakLineDerivOn b g k fun i => ?_).imp
      fun w (hw : value (k + 1) w = g) => hw ▸ hg
    -- `∂ᵢ(ψ u) = ψ ∂ᵢu + (∂ᵢψ) u`, and both summands lie in `W^{k,p}(Ω)` by induction. On `Ω` the
    -- derivative of `ψ` is its derivative within `U`, which is smooth on `U`.
    obtain ⟨d, hd⟩ := exists_hasWeakLineDerivOn_value k u (b i)
    obtain ⟨w₁, hw₁⟩ := ih hpsi d
    obtain ⟨w₂, hw₂⟩ := ih ((hpsi.fderivWithin hU (by simp)).clm_apply contDiffOn_const)
      (lowerOrder k u)
    refine ⟨w₁ + w₂, (((hd.contDiffOn_smul (hpsi.mono (subset_closure.trans hΩU))).congr_ae
      ?_).congr_ae_deriv ?_)⟩
    · filter_upwards [hg] with x hx
      rw [hx, smul_eq_mul]
    · filter_upwards [value_add k w₁ w₂ ▸ Lp.coeFn_add (value k w₁) (value k w₂), hw₁, hw₂,
        ae_restrict_mem Omega.isOpen.measurableSet] with x hx h₁ h₂ hxΩ
      rw [hx, Pi.add_apply, h₁, h₂, ← value_succ, smul_eq_mul, smul_eq_mul,
        fderivWithin_of_mem_nhds (mem_of_superset (Omega.isOpen.mem_nhds hxΩ)
          (subset_closure.trans hΩU))]

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

/-- A chosen product `ψ u` in `W^{k,p}(Ω)`; see `TauCeti.Wkp.uniqueDiffOnSMulL`. -/
private def uniqueDiffOnSMulAux (hU : UniqueDiffOn ℝ U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (hpsi : ContDiffOn ℝ ∞ psi U)
    (u : Wkp mu Omega p k) : Wkp mu Omega p k :=
  (exists_value_ae_eq_mul_of_uniqueDiffOn hU hΩ hΩU k hpsi u).choose

private theorem value_uniqueDiffOnSMulAux (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (hpsi : ContDiffOn ℝ ∞ psi U) (u : Wkp mu Omega p k) :
    (value k (uniqueDiffOnSMulAux hU hΩ hΩU k hpsi u) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => psi x * value k u x :=
  (exists_value_ae_eq_mul_of_uniqueDiffOn hU hΩ hΩU k hpsi u).choose_spec

/-- An element of `W^{k,p}(Ω)` is determined by having value `ψ u` almost everywhere. -/
private theorem eq_of_value_ae_eq_mul {k : ℕ} {u w w' : Wkp mu Omega p k}
    (hw : (value k w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => psi x * value k u x)
    (hw' : (value k w' : E → ℝ) =ᵐ[mu.restrict Omega] fun x => psi x * value k u x) :
    w = w' :=
  ext k (Lp.ext (hw.trans hw'.symm))

/-- Multiplication by `ψ` as a linear endomorphism of `W^{k,p}(Ω)`. -/
private def uniqueDiffOnSMulₗ (hU : UniqueDiffOn ℝ U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (hpsi : ContDiffOn ℝ ∞ psi U) :
    Wkp mu Omega p k →ₗ[ℝ] Wkp mu Omega p k where
  toFun := uniqueDiffOnSMulAux hU hΩ hΩU k hpsi
  map_add' u v := by
    refine eq_of_value_ae_eq_mul (u := u + v) (value_uniqueDiffOnSMulAux hU hΩ hΩU k hpsi _) ?_
    rw [value_add, value_add]
    filter_upwards [Lp.coeFn_add (value k (uniqueDiffOnSMulAux hU hΩ hΩU k hpsi u))
        (value k (uniqueDiffOnSMulAux hU hΩ hΩU k hpsi v)), Lp.coeFn_add (value k u) (value k v),
      value_uniqueDiffOnSMulAux hU hΩ hΩU k hpsi u, value_uniqueDiffOnSMulAux hU hΩ hΩU k hpsi v]
      with x h₁ h₂ h₃ h₄
    rw [h₁, h₂, Pi.add_apply, Pi.add_apply, h₃, h₄, mul_add]
  map_smul' c u := by
    refine eq_of_value_ae_eq_mul (u := c • u) (value_uniqueDiffOnSMulAux hU hΩ hΩU k hpsi _) ?_
    rw [RingHom.id_apply, value_smul, value_smul]
    filter_upwards [Lp.coeFn_smul c (value k (uniqueDiffOnSMulAux hU hΩ hΩU k hpsi u)),
      Lp.coeFn_smul c (value k u), value_uniqueDiffOnSMulAux hU hΩ hΩU k hpsi u]
      with x h₁ h₂ h₃
    rw [h₁, h₂, Pi.smul_apply, Pi.smul_apply, h₃, smul_eq_mul, smul_eq_mul, mul_left_comm]

/-- **Multiplication by a function smooth up to the boundary on `W^{k,p}(Ω)`.** If `Ω` has compact
closure inside a set `U` of unique differentiability and `ψ` is smooth on `U`, multiplication by
`ψ` is a continuous linear endomorphism of `W^{k,p}(Ω)`, for every order `k` and every
`1 ≤ p ≤ ∞`. Its value is the pointwise product (`TauCeti.Wkp.value_uniqueDiffOnSMulL_ae`). -/
def uniqueDiffOnSMulL (hU : UniqueDiffOn ℝ U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (hpsi : ContDiffOn ℝ ∞ psi U) :
    Wkp mu Omega p k →L[ℝ] Wkp mu Omega p k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := uniqueDiffOnSMulₗ hU hΩ hΩU k hpsi)
    fun u x y hu hy => by
    -- `ψ` is bounded on `Ω`, so the value of the product depends continuously on the value.
    obtain ⟨C, hC⟩ := hΩ.exists_bound_of_continuousOn (hpsi.continuousOn.mono hΩU)
    have hC' : ∀ z ∈ (Omega : Set E), ‖psi z‖ ≤ max C 0 :=
      fun z hz => (hC z (subset_closure hz)).trans (le_max_left _ _)
    set L := uniqueDiffOnSMulₗ (mu := mu) (p := p) hU hΩ hΩU k hpsi
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
        (value_uniqueDiffOnSMulAux hU hΩ hΩU k hpsi (u n - x))).trans
        (mul_le_mul_of_nonneg_left (norm_value_le k _) (le_max_right _ _))
    have hy' : Tendsto (fun n => value k (L (u n))) atTop (𝓝 (value k y)) := by
      simpa only [Function.comp_def, valueL_apply] using
        ((valueL (mu := mu) (Omega := Omega) (p := p) k).continuous.tendsto y).comp hy
    exact ext k (tendsto_nhds_unique hy' hval)

/-- The value of multiplication by `ψ` is the pointwise product almost everywhere on `Ω`. -/
theorem value_uniqueDiffOnSMulL_ae (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (hpsi : ContDiffOn ℝ ∞ psi U) (u : Wkp mu Omega p k) :
    (value k (uniqueDiffOnSMulL hU hΩ hΩU k hpsi u) : E → ℝ) =ᵐ[mu.restrict Omega]
      fun x => psi x * value k u x := by
  rw [uniqueDiffOnSMulL, ContinuousLinearMap.coeFn_ofSeqClosedGraph]
  exact value_uniqueDiffOnSMulAux hU hΩ hΩU k hpsi u

/-- Multiplication by `ψ` is characterized by its value: an element of `W^{k,p}(Ω)` equals `ψ u`
exactly when its value is `ψ u` almost everywhere on `Ω`. -/
theorem eq_uniqueDiffOnSMulL_iff (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (hpsi : ContDiffOn ℝ ∞ psi U) {u w : Wkp mu Omega p k} :
    w = uniqueDiffOnSMulL hU hΩ hΩU k hpsi u ↔
      (value k w : E → ℝ) =ᵐ[mu.restrict Omega] fun x => psi x * value k u x := by
  refine ⟨fun h => h ▸ value_uniqueDiffOnSMulL_ae hU hΩ hΩU k hpsi u, fun h => ?_⟩
  exact eq_of_value_ae_eq_mul h (value_uniqueDiffOnSMulL_ae hU hΩ hΩU k hpsi u)

/-- Multiplication by `ψ` commutes with forgetting the highest weak derivative. -/
theorem lowerOrder_uniqueDiffOnSMulL (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (hpsi : ContDiffOn ℝ ∞ psi U) (u : Wkp mu Omega p (k + 1)) :
    lowerOrder k (uniqueDiffOnSMulL hU hΩ hΩU (k + 1) hpsi u) =
      uniqueDiffOnSMulL hU hΩ hΩU k hpsi (lowerOrder k u) := by
  rw [eq_uniqueDiffOnSMulL_iff, ← value_succ, ← value_succ]
  exact value_uniqueDiffOnSMulL_ae hU hΩ hΩU (k + 1) hpsi u

/-- Multiplication by a constant function is scalar multiplication. -/
@[simp]
theorem uniqueDiffOnSMulL_const (hU : UniqueDiffOn ℝ U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) (c : ℝ) (u : Wkp mu Omega p k) :
    uniqueDiffOnSMulL hU hΩ hΩU k (psi := fun _ => c) contDiffOn_const u = c • u := by
  symm
  rw [eq_uniqueDiffOnSMulL_iff, value_smul]
  filter_upwards [Lp.coeFn_smul c (value k u)] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul]

/-- Multiplication is additive in the multiplier: `(ψ + φ) u = ψ u + φ u`. -/
theorem uniqueDiffOnSMulL_add (hU : UniqueDiffOn ℝ U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) {phi : E → ℝ} (hpsi : ContDiffOn ℝ ∞ psi U)
    (hphi : ContDiffOn ℝ ∞ phi U) :
    uniqueDiffOnSMulL (mu := mu) (p := p) hU hΩ hΩU k (hpsi.add hphi) =
      uniqueDiffOnSMulL hU hΩ hΩU k hpsi + uniqueDiffOnSMulL hU hΩ hΩU k hphi := by
  ext1 u
  symm
  rw [eq_uniqueDiffOnSMulL_iff, add_apply, value_add]
  filter_upwards [Lp.coeFn_add (value k (uniqueDiffOnSMulL hU hΩ hΩU k hpsi u))
      (value k (uniqueDiffOnSMulL hU hΩ hΩU k hphi u)),
    value_uniqueDiffOnSMulL_ae hU hΩ hΩU k hpsi u, value_uniqueDiffOnSMulL_ae hU hΩ hΩU k hphi u]
    with x h₁ h₂ h₃
  rw [h₁, Pi.add_apply, h₂, h₃, add_mul]

/-- Multiplication is multiplicative in the multiplier: `(ψ φ) u = ψ (φ u)`. -/
theorem uniqueDiffOnSMulL_mul (hU : UniqueDiffOn ℝ U) (hΩ : IsCompact (closure (Omega : Set E)))
    (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ) {phi : E → ℝ} (hpsi : ContDiffOn ℝ ∞ psi U)
    (hphi : ContDiffOn ℝ ∞ phi U) :
    uniqueDiffOnSMulL (mu := mu) (p := p) hU hΩ hΩU k (hpsi.mul hphi) =
      (uniqueDiffOnSMulL hU hΩ hΩU k hpsi).comp (uniqueDiffOnSMulL hU hΩ hΩU k hphi) := by
  ext1 u
  symm
  rw [eq_uniqueDiffOnSMulL_iff, ContinuousLinearMap.comp_apply]
  filter_upwards [value_uniqueDiffOnSMulL_ae hU hΩ hΩU k hpsi
      (uniqueDiffOnSMulL hU hΩ hΩU k hphi u),
    value_uniqueDiffOnSMulL_ae hU hΩ hΩU k hphi u] with x h₁ h₂
  rw [h₁, h₂, mul_assoc]

/-- If `|ψ| ≤ C` on `Ω`, the value of `ψ u` has `Lᵖ` norm at most `C` times that of `u`. -/
theorem norm_value_uniqueDiffOnSMulL_le (hU : UniqueDiffOn ℝ U)
    (hΩ : IsCompact (closure (Omega : Set E))) (hΩU : closure (Omega : Set E) ⊆ U) (k : ℕ)
    (hpsi : ContDiffOn ℝ ∞ psi U) {C : ℝ} (hC : ∀ x ∈ (Omega : Set E), ‖psi x‖ ≤ C)
    (u : Wkp mu Omega p k) :
    ‖value k (uniqueDiffOnSMulL hU hΩ hΩU k hpsi u)‖ ≤ C * ‖value k u‖ :=
  norm_lp_le_of_ae_eq_mul hC (value_uniqueDiffOnSMulL_ae hU hΩ hΩU k hpsi u)

end Wkp

end TauCeti
