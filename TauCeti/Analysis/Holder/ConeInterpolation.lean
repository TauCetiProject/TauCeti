/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.Interpolation
public import TauCeti.Analysis.InnerProductSpace.GraphPatch
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Normed.Operator.BallBound

/-!
# Interpolation inequalities up to the boundary

The local interpolation inequalities of `TauCeti.Analysis.Holder.Interpolation` bound `Du` and
`D²u` at the centre of a ball on which `u` is bounded and `D²u` is Hölder. At a point of the
boundary of a domain no such ball exists. A point `x` of a set `s` that *sees* a closed ball
`closedBall p ρ` through `s`, in the sense that every segment from `x` to a point of the ball lies
in `s`, is enough.

Along a segment from `x` to `x + w` in `s`, comparing the second-order Taylor expansions at
`x + w / 2` and at `x + w` gives `‖D²u(x) w w‖ ≤ 16 M + 12 H ‖w‖^(2 + α)`, where `|u| ≤ M` on `s`
and `D²u` is `α`-Hölder with constant `H` there
(`HolderOnWith.norm_apply_apply_le_of_hasFDerivWithinAt`). This bounds the quadratic form of
`D²u(x)` on the closed ball of directions `closedBall (p - x) ρ`, and by polarization
(`ContinuousLinearMap.opNorm_le_of_forall_mem_closedBall_norm_apply_self_le`) the whole
symmetric bilinear map: with `dist x p + ρ ≤ R`,

`‖D²u(x)‖ ≤ (64 M + 48 H R^(2 + α)) / ρ²`

(`HolderOnWith.norm_iteratedFDeriv_two_le_of_contDiffOn_of_forall_segment_subset`), and similarly

`‖Du(x)‖ ≤ (4 M + ‖D²u(x)‖ R² + 2 H R^(2 + α)) / ρ`

(`HolderOnWith.norm_fderiv_le_of_contDiffOn_of_forall_segment_subset`).

On the closure of a bounded domain with Lipschitz graph patches the uniform cone condition
(`TauCeti.exists_forall_segment_subset_closure`) supplies such a ball at every point, at every
small scale `ε`, with `ρ = θ ε` and `R = 2 ε` for a fixed aperture `θ`. This gives the
interpolation inequalities on `closure Ω`
(`TauCeti.exists_forall_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_closure`):

`‖Du‖ ≤ C (M / ε + H ε^(1 + α))` and `‖D²u‖ ≤ C (M / ε² + H ε^α)`

for all `ε ≤ ε₀`, with `C` and `ε₀` depending only on `Ω` and `α`. They remove the norms of `Du`
and `D²u` from global Schauder estimates, as in Gilbarg–Trudinger's Lemma 6.35.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.8 (interpolation inequalities, Lemma 6.35).
-/

public section

open Set Metric
open scoped NNReal InnerProductSpace

namespace HolderOnWith

section Segment

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The second derivative along a segment.** If `g` has derivative `g'` within `s`, `g'` has
derivative `g''` within `s`, `g''` is `α`-Hölder with constant `H` on `s` and `‖g‖ ≤ M` on `s`, then
for a segment from `x` to `x + w` contained in `s`,
`‖g'' x w w‖ ≤ 16 M + 12 H ‖w‖^(2 + α)`. -/
theorem norm_apply_apply_le_of_hasFDerivWithinAt {s : Set E} {g : E → F}
    {g' : E → E →L[ℝ] F} {g'' : E → E →L[ℝ] E →L[ℝ] F} {H α : ℝ≥0}
    (hH : HolderOnWith H α g'' s) (hg : ∀ y ∈ s, HasFDerivWithinAt g (g' y) s y)
    (hg' : ∀ y ∈ s, HasFDerivWithinAt g' (g'' y) s y) {M : ℝ} (hM : ∀ y ∈ s, ‖g y‖ ≤ M)
    {x w : E} (hxw : segment ℝ x (x + w) ⊆ s) :
    ‖g'' x w w‖ ≤ 16 * M + 12 * H * ‖w‖ ^ (2 + (α : ℝ)) := by
  -- Compare the second-order Taylor expansions at `x + w / 2` and at `x + w`.
  set y : E := (2 : ℝ)⁻¹ • w
  have hmid : x + y ∈ segment ℝ x (x + w) := by
    rw [segment_eq_image']
    exact ⟨(2 : ℝ)⁻¹, ⟨by norm_num, by norm_num⟩, by simp [y]⟩
  have hseg : segment ℝ x (x + y) ⊆ s :=
    ((convex_segment x (x + w)).segment_subset (left_mem_segment ℝ x (x + w)) hmid).trans hxw
  have hT₁ := hH.norm_image_sub_sub_sub_le_of_hasFDerivWithinAt hg hg' hseg
  have hT₂ := hH.norm_image_sub_sub_sub_le_of_hasFDerivWithinAt hg hg' hxw
  have hid : (4 : ℝ)⁻¹ • g'' x w w = (g (x + w) - (2 : ℝ) • g (x + y) + g x) -
      (g (x + w) - g x - g' x w - (2 : ℝ)⁻¹ • g'' x w w) +
      (2 : ℝ) • (g (x + y) - g x - g' x y - (2 : ℝ)⁻¹ • g'' x y y) := by
    simp only [y, map_smul, smul_apply]
    module
  have hy : ‖y‖ ^ (2 + (α : ℝ)) ≤ ‖w‖ ^ (2 + (α : ℝ)) := by
    refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by positivity)
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith [norm_nonneg w]
  have hMw := hM _ (hxw (right_mem_segment ℝ x (x + w)))
  have hMy := hM _ (hseg (right_mem_segment ℝ x (x + y)))
  have hMx := hM _ (hxw (left_mem_segment ℝ x (x + w)))
  have h := congrArg norm hid
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)] at h
  have h1 := norm_add_le (g (x + w) - (2 : ℝ) • g (x + y) + g x -
      (g (x + w) - g x - g' x w - (2 : ℝ)⁻¹ • g'' x w w))
    ((2 : ℝ) • (g (x + y) - g x - g' x y - (2 : ℝ)⁻¹ • g'' x y y))
  have h2 := norm_sub_le (g (x + w) - (2 : ℝ) • g (x + y) + g x)
    (g (x + w) - g x - g' x w - (2 : ℝ)⁻¹ • g'' x w w)
  have h3 := norm_add_le (g (x + w) - (2 : ℝ) • g (x + y)) (g x)
  have h4 := norm_sub_le (g (x + w)) ((2 : ℝ) • g (x + y))
  rw [norm_smul, Real.norm_two] at h1 h4
  nlinarith [mul_le_mul_of_nonneg_left hy H.coe_nonneg]

omit [NormedSpace ℝ E] in
/-- A direction `w` from `x` towards a point of `closedBall p ρ` has norm at most
`dist x p + ρ`. -/
private theorem add_mem_closedBall_and_norm_le {x p w : E} {ρ R : ℝ}
    (hR : dist x p + ρ ≤ R) (hw : w ∈ closedBall (p - x) ρ) :
    x + w ∈ closedBall p ρ ∧ ‖w‖ ≤ R := by
  rw [mem_closedBall, dist_eq_norm] at hw
  refine ⟨by rwa [mem_closedBall, dist_eq_norm, show x + w - p = w - (p - x) by abel], ?_⟩
  have := norm_le_norm_add_norm_sub' w (p - x)
  rw [dist_comm, dist_eq_norm] at hR
  linarith

/-- **Interpolation of the Hessian at a point seeing a ball.** Let `u` be `C²` on an open set
`U ⊇ s`, with `D²u` `α`-Hölder with constant `H` on `s` and `‖u‖ ≤ M` on `s`. If every segment
from `x` to a point of `closedBall p ρ` lies in `s`, and `dist x p + ρ ≤ R`, then
`‖D²u(x)‖ ≤ (64 M + 48 H R^(2 + α)) / ρ²`. -/
theorem norm_iteratedFDeriv_two_le_of_contDiffOn_of_forall_segment_subset {U s : Set E}
    {u : E → F} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hsU : s ⊆ U) {H α : ℝ≥0}
    (hH : HolderOnWith H α (iteratedFDeriv ℝ 2 u) s) {M : ℝ} (hM : ∀ y ∈ s, ‖u y‖ ≤ M)
    {x p : E} {ρ R : ℝ} (hρ : 0 < ρ) (hR : dist x p + ρ ≤ R)
    (hseg : ∀ z ∈ closedBall p ρ, segment ℝ x z ⊆ s) :
    ‖iteratedFDeriv ℝ 2 u x‖ ≤ (64 * M + 48 * H * R ^ (2 + (α : ℝ))) / ρ ^ 2 := by
  obtain ⟨hd1, hd2⟩ := hu.hasFDerivWithinAt_fderiv_and_fderiv_fderiv hU hsU
  have hH' := (TauCeti.holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two u).2 hH
  have hx : x ∈ s := hseg p (mem_closedBall_self hρ.le) (left_mem_segment ℝ x p)
  have hsymm := (hu.contDiffAt (hU.mem_nhds (hsU hx))).isSymmSndFDerivAt (by simp)
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  refine (ContinuousLinearMap.opNorm_le_of_forall_mem_closedBall_norm_apply_self_le hsymm hρ
    (d := p - x) (A := 16 * M + 12 * H * R ^ (2 + (α : ℝ))) fun w hw => ?_).trans_eq (by ring)
  obtain ⟨hxw, hwR⟩ := add_mem_closedBall_and_norm_le hR hw
  refine (hH'.norm_apply_apply_le_of_hasFDerivWithinAt hd1 hd2 hM (hseg _ hxw)).trans ?_
  gcongr

/-- **Interpolation of the gradient at a point seeing a ball.** Let `u` be `C²` on an open set
`U ⊇ s`, with `D²u` `α`-Hölder with constant `H` on `s` and `‖u‖ ≤ M` on `s`. If every segment
from `x` to a point of `closedBall p ρ` lies in `s`, and `dist x p + ρ ≤ R`, then
`‖Du(x)‖ ≤ (4 M + ‖D²u(x)‖ R² + 2 H R^(2 + α)) / ρ`. -/
theorem norm_fderiv_le_of_contDiffOn_of_forall_segment_subset {U s : Set E}
    {u : E → F} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U) (hsU : s ⊆ U) {H α : ℝ≥0}
    (hH : HolderOnWith H α (iteratedFDeriv ℝ 2 u) s) {M : ℝ} (hM : ∀ y ∈ s, ‖u y‖ ≤ M)
    {x p : E} {ρ R : ℝ} (hρ : 0 < ρ) (hR : dist x p + ρ ≤ R)
    (hseg : ∀ z ∈ closedBall p ρ, segment ℝ x z ⊆ s) :
    ‖fderiv ℝ u x‖ ≤
      (4 * M + ‖iteratedFDeriv ℝ 2 u x‖ * R ^ 2 + 2 * H * R ^ (2 + (α : ℝ))) / ρ := by
  obtain ⟨hd1, hd2⟩ := hu.hasFDerivWithinAt_fderiv_and_fderiv_fderiv hU hsU
  have hH' := (TauCeti.holderOnWith_fderiv_fderiv_iff_iteratedFDeriv_two u).2 hH
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  refine (ContinuousLinearMap.opNorm_le_of_forall_mem_closedBall_norm_apply_le hρ (d := p - x)
    (A := 2 * M + ‖fderiv ℝ (fderiv ℝ u) x‖ * R ^ 2 / 2 + H * R ^ (2 + (α : ℝ)))
    fun w hw => ?_).trans_eq (by ring)
  obtain ⟨hxw, hwR⟩ := add_mem_closedBall_and_norm_le hR hw
  have hsegw := hseg _ hxw
  -- `Du(x) w` is `u (x + w) - u x - D²u(x) w w / 2` up to the second-order Taylor remainder.
  have hT := hH'.norm_image_sub_sub_sub_le_of_hasFDerivWithinAt hd1 hd2 hsegw
  have hMw := hM _ (hsegw (right_mem_segment ℝ x (x + w)))
  have hMx := hM _ (hsegw (left_mem_segment ℝ x (x + w)))
  have hB : ‖fderiv ℝ (fderiv ℝ u) x w w‖ ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ * R ^ 2 := by
    refine (ContinuousLinearMap.le_opNorm₂ _ w w).trans ?_
    rw [mul_assoc, ← sq]
    gcongr
  have hRα : ‖w‖ ^ (2 + (α : ℝ)) ≤ R ^ (2 + (α : ℝ)) :=
    Real.rpow_le_rpow (norm_nonneg _) hwR (by positivity)
  have hid : fderiv ℝ u x w = (u (x + w) - u x - (2 : ℝ)⁻¹ • fderiv ℝ (fderiv ℝ u) x w w) -
      (u (x + w) - u x - fderiv ℝ u x w - (2 : ℝ)⁻¹ • fderiv ℝ (fderiv ℝ u) x w w) := by abel
  rw [hid]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_sub_le (u (x + w) - u x) ((2 : ℝ)⁻¹ • fderiv ℝ (fderiv ℝ u) x w w)
  have h2 := norm_sub_le (u (x + w)) (u x)
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)] at h1
  nlinarith [mul_le_mul_of_nonneg_left hRα H.coe_nonneg]

end Segment

end HolderOnWith

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Interpolation inequalities on a bounded domain.** Let `Ω` be a bounded set in a proper real
inner product space with a Lipschitz graph patch at every frontier point `x`:
`ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫}` for a unit vector `ν`, a radius `r > 0` and a
Lipschitz function `γ` invariant along `ν`. Let `α ≥ 0`. There are `C ≥ 0` and `ε₀ > 0`, depending
only on `Ω` and `α`, such that for every `0 < ε ≤ ε₀` and every `u` that is `C²` on an open set
containing `closure Ω`, with `‖u‖ ≤ M` on `closure Ω` and `D²u` `α`-Hölder with constant `H` there,

`‖Du‖ ≤ C (M / ε + H ε^(1 + α))` and `‖D²u‖ ≤ C (M / ε² + H ε^α)` on `closure Ω`. -/
theorem exists_forall_norm_fderiv_le_and_norm_iteratedFDeriv_two_le_closure {Ω : Set E}
    (hΩ : Bornology.IsBounded Ω)
    (hbdry : ∀ x ∈ frontier Ω, ∃ (ν : E) (γ : E → ℝ) (G : ℝ≥0) (r : ℝ), ‖ν‖ = 1 ∧
      LipschitzWith G γ ∧ (∀ z (t : ℝ), γ (z + t • ν) = γ z) ∧ 0 < r ∧
      ball x r ∩ Ω = ball x r ∩ {z | γ z < ⟪z, ν⟫_ℝ}) (α : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {U : Set E} {u : E → F} {H : ℝ≥0} {M : ℝ}, IsOpen U → closure Ω ⊆ U →
        ContDiffOn ℝ 2 u U → HolderOnWith H α (iteratedFDeriv ℝ 2 u) (closure Ω) →
        (∀ z ∈ closure Ω, ‖u z‖ ≤ M) → ∀ z ∈ closure Ω,
          ‖fderiv ℝ u z‖ ≤ C * (M / ε + H * ε ^ (1 + (α : ℝ))) ∧
          ‖iteratedFDeriv ℝ 2 u z‖ ≤ C * (M / ε ^ 2 + H * ε ^ (α : ℝ)) := by
  obtain ⟨θ, hθ, hθ1, ε₀, hε₀, hcone⟩ := exists_forall_segment_subset_closure hΩ hbdry
  set P : ℝ := 2 ^ (2 + (α : ℝ))
  set C₂ : ℝ := (64 + 48 * P) / θ ^ 2 with hC₂def
  set C₁ : ℝ := (4 + 4 * C₂ + 2 * P) / θ with hC₁def
  have hP : 0 ≤ P := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  have hC₁ : 0 ≤ C₁ := by positivity
  refine ⟨C₁ + C₂, by positivity, ε₀, hε₀, fun ε hε hεε₀ {U u H M} hU hΩU hu hH hM z hz => ?_⟩
  -- At the scale `ε`, `z` sees a ball of radius `ρ = θ ε` within `R = 2 ε` of it.
  obtain ⟨p, hzp, hseg⟩ := hcone ε hε hεε₀ z hz
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz)
  have hρ : 0 < θ * ε := mul_pos hθ hε
  have hR : dist z p + θ * ε ≤ 2 * ε := by nlinarith
  set q : ℝ := ε ^ (α : ℝ)
  have hpow : (2 * ε) ^ (2 + (α : ℝ)) = P * (ε ^ 2 * q) := by
    rw [Real.mul_rpow (by norm_num) hε.le, Real.rpow_add hε, Real.rpow_two]
  have hHq : 0 ≤ (H : ℝ) * (ε ^ 2 * q) := by positivity
  have hD2 : ‖iteratedFDeriv ℝ 2 u z‖ ≤ C₂ * (M / ε ^ 2 + H * q) := by
    refine (HolderOnWith.norm_iteratedFDeriv_two_le_of_contDiffOn_of_forall_segment_subset hU hu
      hΩU hH hM hρ hR hseg).trans ?_
    rw [hpow, div_le_iff₀ (by positivity), show C₂ * (M / ε ^ 2 + H * q) * (θ * ε) ^ 2 =
      (64 + 48 * P) * (M + H * (ε ^ 2 * q)) by rw [hC₂def]; field_simp]
    nlinarith
  have hD1 : ‖fderiv ℝ u z‖ ≤ C₁ * (M / ε + H * ε ^ (1 + (α : ℝ))) := by
    refine (HolderOnWith.norm_fderiv_le_of_contDiffOn_of_forall_segment_subset hU hu hΩU hH hM hρ
      hR hseg).trans ?_
    have h4 : ‖iteratedFDeriv ℝ 2 u z‖ * (2 * ε) ^ 2 ≤ 4 * C₂ * (M + H * (ε ^ 2 * q)) := by
      calc ‖iteratedFDeriv ℝ 2 u z‖ * (2 * ε) ^ 2 ≤ C₂ * (M / ε ^ 2 + H * q) * (2 * ε) ^ 2 := by
            gcongr
        _ = 4 * C₂ * (M + H * (ε ^ 2 * q)) := by field_simp; ring
    rw [hpow, Real.rpow_add hε, Real.rpow_one, div_le_iff₀ hρ,
      show C₁ * (M / ε + H * (ε * q)) * (θ * ε) = (4 + 4 * C₂ + 2 * P) * (M + H * (ε ^ 2 * q)) by
        rw [hC₁def]; field_simp]
    nlinarith [mul_nonneg hP hM0]
  have hb1 : 0 ≤ M / ε + H * ε ^ (1 + (α : ℝ)) := by positivity
  have hb2 : 0 ≤ M / ε ^ 2 + H * q := by positivity
  exact ⟨hD1.trans (by nlinarith), hD2.trans (by nlinarith)⟩

end TauCeti
