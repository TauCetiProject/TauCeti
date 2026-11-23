/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.FlatBoundary
public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.VariableCoefficient
import TauCeti.Analysis.Holder.Lp
import TauCeti.Analysis.PDE.Ellipticity.Basic

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
`x + (r / (2 ‖ν‖)) ν` (`HolderOnWith.norm_le_add_eLpNorm_toReal_of_halfSpace`). The
constant-coefficient estimate applied to each two-point set `{x, y} ⊆ closure H` at the radius
`r` bounds `J` by a multiple of these quantities, and the smallness condition absorbs the terms
in `J` (`TauCeti.PDE.holderOnWith_of_forall_holderOnWith_dist_le`, shared with the interior
estimate).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2, the boundary estimate by freezing coefficients (Lemma 6.5).
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped InnerProductSpace NNReal ENNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

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
    {U u} hU hHU hu hu0 hJ₀ hH2 hf => ?_⟩
  set Hc : Set E := {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  set Ho : Set E := {x | c₀ < ⟪x, ν⟫_ℝ}
  have hoc : Ho ⊆ Hc := fun _ hx => mem_ofPred.2 (mem_ofPred.1 hx).le
  let H := iteratedFDeriv ℝ 2 u
  let M : ℝ := (eLpNorm H 2 (volume.restrict Ho)).toReal
  let V : ℝ := (volume (ball (0 : E) (r / 2)) ^ (-((2 : ℝ)⁻¹))).toReal
  have hLam : 0 < Lam := hlam.trans_le (le_of_mul_norm_sq_le_toQuadraticForm'_le hA hA')
  -- Absorbing the terms in `J` reduces the estimate to a two-point bound for each constant `J`.
  refine holderOnWith_of_forall_holderOnWith_dist_le hJ₀ hlam hsmall fun J hJ x hx y hy => ?_
  -- Interpolation at scale `r`, on a ball of radius `r / 2` in `H` next to each point.
  have hsup (x : E) (hx : x ∈ Hc) : ‖H x‖ ≤ J * r ^ (α : ℝ) + V * M := by
    simpa only [ENNReal.toReal_ofNat] using hJ.norm_le_add_eLpNorm_toReal_of_halfSpace
      (mu := volume) hν hr two_ne_zero ENNReal.ofNat_ne_top hH2 (mem_ofPred.1 hx)
  let B : ℝ≥0 := (J * r ^ (α : ℝ) + V * M).toNNReal
  have hBc : (B : ℝ) = J * r ^ (α : ℝ) + V * M := Real.coe_toNNReal _ (by positivity)
  have hg := holderOnWith_sum_smul_fderiv_fderiv_of_abs_sub_le ha hL (hJ.mono hoc)
    (fun x hx => (hsup x (hoc hx)).trans_eq hBc.symm) hf
  -- Apply the frozen estimate up to the boundary to the two-point set `{x, y}`.
  have hxy := hS hlam hA hA' hν hU hu ((finite_singleton y).insert x).isBounded
    (by simp only [Hc, mem_ofPred_eq] at hx hy; rintro z (rfl | rfl) <;> assumption) hr
    (inter_subset_right.trans hHU) (fun z _ hz => hu0 z hz) (hg.mono inter_subset_right)
  have hb := hxy.dist_le (by simp : x ∈ ({x, y} : Set E)) (by simp : y ∈ ({x, y} : Set E))
  rw [Real.coe_toNNReal _ (by positivity)] at hb
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have hLp : (eLpNorm H 2 (volume.restrict (thickening r ({x, y} : Set E) ∩ Ho))).toReal ≤ M :=
    ENNReal.toReal_mono hH2.eLpNorm_ne_top
      (eLpNorm_mono_measure H (Measure.restrict_mono inter_subset_right le_rfl))
  push_cast
  rw [hBc]
  gcongr
  linarith

end TauCeti.PDE
