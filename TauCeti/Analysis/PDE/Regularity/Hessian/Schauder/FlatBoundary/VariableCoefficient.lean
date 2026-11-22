/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.VariableCoefficient
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Analysis.Holder.Lp

/-!
# Schauder estimates up to a flat boundary for coefficients of small oscillation

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, with closure
`closure H = {x | c₀ ≤ ⟪x, ν⟫}`, and let `0 < α < 1`. This file proves an a priori `C^{2,α}`
estimate up to the boundary hyperplane for the non-divergence-form operator
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` whose coefficients are `α`-Hölder in `H` with constant `L` and within `ε` of
a constant elliptic matrix `A` there
(`exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_abs_sub_le_of_halfSpace`, in
the `TauCeti.PDE` namespace). Let `u` be `C²` on an open set containing `closure H`, vanishing on
the hyperplane `∂H`, with `D²u` `α`-Hölder on `closure H` and square integrable on `H`. With
`κ = C (Λ / λ)^(1 + (n+1)/4 + α/2)`, if

`2 κ (n+1)² (ε + L r^α) ≤ λ`,

then

`[D²u]_{α; closure H} ≤ 2 κ ([L u]_{α; H} / λ + Q ‖D²u‖_{L²(H)})`, where
`Q = (n+1)² L / λ |B_{r/2}|^(-1/2) + r^(-(n+1)/2-α)`.

The Hölder constant of `D²u` on `closure H` enters only qualitatively. This is the boundary
counterpart of the interior estimate
`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_abs_sub_le`,
and the estimate that a cutoff near a flat boundary portion reduces the boundary Schauder
estimate to.

## The argument

The proof is that of the interior estimate, with the constant-coefficient estimate up to the flat
boundary
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_halfSpace`)
in place of the interior one. Freezing the coefficients at `A`, the frozen operator `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu`
is `α`-Hölder in `H` with constant `[L u]_α + (n+1)² (ε J + B L)`, where `J` is the Hölder constant
of `D²u` on `closure H` and `B` bounds `D²u` there
(`TauCeti.PDE.holderOnWith_sum_smul_fderiv_fderiv_of_abs_sub_le`). The bound
`B ≤ J r^α + |B_{r/2}|^(-1/2) ‖D²u‖_{L²(H)}` comes from comparing `D²u` at a point
`x ∈ closure H` with its values on the ball of radius `r / 2` inside `H` whose centre is
`x + (r / (2 ‖ν‖)) ν` (`HolderOnWith.norm_le_add_eLpNorm_toReal`). The constant-coefficient
estimate applied to each two-point set `{x, y} ⊆ closure H` at the radius `r` bounds `J` by a
multiple of these quantities, and the smallness condition absorbs the terms in `J`
(`TauCeti.PDE.le_two_mul_of_le_mul_add_mul_add`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2, the boundary estimate by freezing coefficients (Lemma 6.4).
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped InnerProductSpace NNReal ENNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- For a point `x` of the closed half-space `{z | c₀ ≤ ⟪z, ν⟫}`, `ν ≠ 0`, the ball of radius `ρ`
about `x + (ρ / ‖ν‖) ν` lies in the open half-space `{z | c₀ < ⟪z, ν⟫}`. -/
private theorem ball_add_smul_subset_halfSpace {ν x : E} {c₀ ρ : ℝ} (hν : ν ≠ 0)
    (hx : c₀ ≤ ⟪x, ν⟫_ℝ) : ball (x + (ρ / ‖ν‖) • ν) ρ ⊆ {z | c₀ < ⟪z, ν⟫_ℝ} := by
  intro z hz
  have hν0 : 0 < ‖ν‖ := norm_pos_iff.2 hν
  set w := z - (x + (ρ / ‖ν‖) • ν)
  have hw : ‖w‖ * ‖ν‖ < ρ * ‖ν‖ :=
    mul_lt_mul_of_pos_right (by rw [← dist_eq_norm]; exact hz) hν0
  have hc : ⟪(ρ / ‖ν‖) • ν, ν⟫_ℝ = ρ * ‖ν‖ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hz' : ⟪z, ν⟫_ℝ = ⟪x, ν⟫_ℝ + ⟪(ρ / ‖ν‖) • ν, ν⟫_ℝ + ⟪w, ν⟫_ℝ := by
    simp only [w, inner_sub_left, inner_add_left]
    ring
  simp only [mem_ofPred_eq]
  linarith [neg_le_of_abs_le (abs_real_inner_le_norm w ν)]

/-- A function `g` that is `α`-Hölder with constant `J` on the closed half-space
`closure H = {z | c₀ ≤ ⟪z, ν⟫}` and square integrable on the open half-space `H` satisfies, at
every point of `closure H` and for every `r > 0`, `‖g x‖ ≤ J r^α + |B_{r/2}|^(-1/2) ‖g‖_{L²(H)}`:
compare `g x` with the values of `g` on the ball of radius `r / 2` in `H` whose centre is
`x + (r / (2 ‖ν‖)) ν`. -/
private theorem norm_le_of_holderOnWith_halfSpace {F : Type*} [NormedAddCommGroup F] {ν : E}
    {c₀ r : ℝ} {g : E → F} {J α : ℝ≥0} (hν : ν ≠ 0) (hr : 0 < r)
    (hJ : HolderOnWith J α g {z | c₀ ≤ ⟪z, ν⟫_ℝ})
    (hg : MemLp g 2 (volume.restrict {z | c₀ < ⟪z, ν⟫_ℝ})) {x : E} (hx : c₀ ≤ ⟪x, ν⟫_ℝ) :
    ‖g x‖ ≤ J * r ^ (α : ℝ) + (volume (ball (0 : E) (r / 2)) ^ (-((2 : ℝ)⁻¹))).toReal *
      (eLpNorm g 2 (volume.restrict {z | c₀ < ⟪z, ν⟫_ℝ})).toReal := by
  have hball : ball (x + (r / 2 / ‖ν‖) • ν) (r / 2) ⊆ {z | c₀ < ⟪z, ν⟫_ℝ} :=
    ball_add_smul_subset_halfSpace hν hx
  have hxc : dist x (x + (r / 2 / ‖ν‖) • ν) ≤ r / 2 := by
    rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg
      (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hν)]
  have hoc : {z | c₀ < ⟪z, ν⟫_ℝ} ⊆ {z | c₀ ≤ ⟪z, ν⟫_ℝ} := fun z hz => by
    simp only [mem_ofPred_eq] at hz ⊢
    exact hz.le
  have hle : eLpNorm g 2 (volume.restrict (ball (x + (r / 2 / ‖ν‖) • ν) (r / 2))) ≤
      eLpNorm g 2 (volume.restrict {z | c₀ < ⟪z, ν⟫_ℝ}) :=
    eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)
  have h := hJ.norm_le_add_eLpNorm_toReal (mu := volume) two_ne_zero ENNReal.ofNat_ne_top
    (half_pos hr) (by simpa only [mem_ofPred_eq] using hx) (hball.trans hoc) hxc
    (hle.trans_lt hg.eLpNorm_lt_top).ne
  rw [mul_div_cancel₀ _ two_ne_zero, ENNReal.toReal_ofNat] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono hg.eLpNorm_ne_top hle) ENNReal.toReal_nonneg))

/-- **Schauder estimate up to a flat boundary for coefficients of small oscillation.**
For `0 < α < 1` there is `C > 0`, depending only on the dimension and `α`, with the following
property. Put `κ = C (Λ / λ)^(1 + (n+1)/4 + α/2)`. Let `A` have ellipticity bounds `λ, Λ`, with
`λ > 0`, let `H = {x | c₀ < ⟪x, ν⟫}`, `ν ≠ 0`, and assume every coefficient entry is `α`-Hölder in
`H` with constant `L` and within `ε` of the corresponding entry of `A` there. If

`2 κ (n+1)² (ε + L r^α) ≤ λ`,

then every `u` that is `C²` on an open set containing the closed half-space `closure H`, vanishes
on the hyperplane `∂H`, and has `D²u` `α`-Hölder on `closure H` and in `L²(H)`, satisfies

`[D²u]_{α; closure H} ≤ 2 κ ([L u]_{α; H} / λ + Q ‖D²u‖_{L²(H)})`, where
`Q = (n+1)² L / λ |B_{r/2}|^(-1/2) + r^(-(n+1)/2-α)`.

The Hölder hypothesis on `D²u` is an a priori regularity assumption; its constant does not occur
in the conclusion. -/
theorem
    exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_abs_sub_le_of_halfSpace
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ},
      0 < lam → (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      (∀ ξ : E, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ {ν : E} {c₀ : ℝ} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {ε L K : ℝ≥0} {r : ℝ},
      ν ≠ 0 → 0 < r →
      2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        (ε + L * r ^ (α : ℝ)) ≤ lam →
      (∀ x, c₀ < ⟪x, ν⟫_ℝ → ∀ i j, |a x i j - A i j| ≤ ε) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) {x | c₀ < ⟪x, ν⟫_ℝ}) →
      ∀ {U : Set E} {u : E → ℝ}, IsOpen U → {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U → ContDiffOn ℝ 2 u U →
      (∀ x, ⟪x, ν⟫_ℝ = c₀ → u x = 0) →
      (∃ J, HolderOnWith J α (iteratedFDeriv ℝ 2 u) {x | c₀ ≤ ⟪x, ν⟫_ℝ}) →
      MemLp (iteratedFDeriv ℝ 2 u) 2 (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ}) →
      HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) {x | c₀ < ⟪x, ν⟫_ℝ} →
      HolderOnWith (2 * (C * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) *
        (K / lam + (((n : ℝ) + 1) ^ 2 * L / lam *
          (volume (ball (0 : E) (r / 2)) ^ (-((2 : ℝ)⁻¹))).toReal +
          r ^ (-(((n : ℝ) + 1) / 2 + α))) *
            (eLpNorm (iteratedFDeriv ℝ 2 u) 2
              (volume.restrict {x | c₀ < ⟪x, ν⟫_ℝ})).toReal)).toNNReal
        α (iteratedFDeriv ℝ 2 u) {x | c₀ ≤ ⟪x, ν⟫_ℝ} := by
  obtain ⟨C₀, hC₀, hS⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_halfSpace hα hα1 (n := n)
  refine ⟨C₀ + 1, by positivity, fun {A lam Lam} hlam hA hA' {ν c₀ a ε L K r} hν hr hsmall ha hL
    {U u} hU hHU hu hu0 hH hH2 hf => ?_⟩
  set Hc : Set E := {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  set Ho : Set E := {x | c₀ < ⟪x, ν⟫_ℝ}
  have hoc : Ho ⊆ Hc := fun x hx => by
    simp only [Ho, Hc, mem_ofPred_eq] at hx ⊢
    exact hx.le
  let H := iteratedFDeriv ℝ 2 u
  -- The best Hölder constant `J` of `D²u` on the closed half-space.
  obtain ⟨J₀, hJ₀⟩ := hH
  let J : ℝ≥0 := nnHolderNorm α (Hc.domRestrict H)
  have hJ : HolderOnWith J α H Hc := HolderWith.restrict_iff.1 hJ₀.holderWith.memHolder.holderWith
  let M : ℝ := (eLpNorm H 2 (volume.restrict Ho)).toReal
  let V : ℝ := (volume (ball (0 : E) (r / 2)) ^ (-((2 : ℝ)⁻¹))).toReal
  let κ : ℝ := (C₀ + 1) * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)
  have hLam : 0 < Lam :=
    hlam.trans_le (by simpa using (hA (EuclideanSpace.single 0 1)).trans (hA' _))
  -- Interpolation at scale `r`, on a ball of radius `r / 2` in `H` next to each point of
  -- `closure H`.
  have hsup (x : E) (hx : x ∈ Hc) : ‖H x‖ ≤ J * r ^ (α : ℝ) + V * M :=
    norm_le_of_holderOnWith_halfSpace hν hr hJ hH2 (by simpa only [Hc, mem_ofPred_eq] using hx)
  let B : ℝ≥0 := (J * r ^ (α : ℝ) + V * M).toNNReal
  have hBc : (B : ℝ) = J * r ^ (α : ℝ) + V * M := Real.coe_toNNReal _ (by positivity)
  have hg := holderOnWith_sum_smul_fderiv_fderiv_of_abs_sub_le ha hL (hJ.mono hoc)
    (fun x hx => (hsup x (hoc hx)).trans_eq hBc.symm) hf
  -- Apply the frozen estimate up to the boundary to each two-point set, with one common bound.
  have hglobal : HolderOnWith (κ * ((K + ((n + 1 : ℝ≥0) ^ 2) * (ε * J + B * L)) / lam +
      r ^ (-(((n : ℝ) + 1) / 2 + α)) * M)).toNNReal α H Hc := by
    refine HolderOnWith.of_dist_le fun x hx y hy => ?_
    have hxy := hS hlam hA hA' hν hU hu ((finite_singleton y).insert x).isBounded
      (by simp only [Hc, mem_ofPred_eq] at hx hy; rintro z (rfl | rfl) <;> assumption) hr
      (inter_subset_right.trans hHU) (fun z _ hz => hu0 z hz) (hg.mono inter_subset_right)
    have hb := hxy.dist_le (by simp : x ∈ ({x, y} : Set E)) (by simp : y ∈ ({x, y} : Set E))
    rw [Real.coe_toNNReal _ (by positivity)] at hb ⊢
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hLp : (eLpNorm H 2 (volume.restrict (thickening r ({x, y} : Set E) ∩ Ho))).toReal ≤ M :=
      ENNReal.toReal_mono hH2.eLpNorm_ne_top
        (eLpNorm_mono_measure H (Measure.restrict_mono inter_subset_right le_rfl))
    calc _ ≤ C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2) *
          ((K + ((n + 1 : ℝ≥0) ^ 2) * (ε * J + B * L)) / lam +
            r ^ (-(((n : ℝ) + 1) / 2 + α)) * M) := by push_cast; gcongr
      _ ≤ _ := by dsimp [κ]; gcongr; linarith
  -- Absorb the terms in `J` with the smallness condition.
  have hbound := (HolderWith.restrict_iff.2 hglobal).nnholderNorm_le
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)] at hbound
  have hfinal := le_two_mul_of_le_mul_add_mul_add (K := K) (V := V) (M := M)
    (Q := r ^ (-(((n : ℝ) + 1) / 2 + α))) J.coe_nonneg hlam hsmall
    (hbound.trans_eq (by push_cast; rw [hBc]))
  exact hJ.mono_const (by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (by positivity)]
    exact hfinal.trans_eq (by simp only [V, M]; ring))

end TauCeti.PDE
