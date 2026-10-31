/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Slobodeckij

import TauCeti.Analysis.Calculus.Deriv.AddCircle
import TauCeti.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Circle diffeomorphisms act on the fractional Sobolev spaces `H^s`, `0 < s < 1`

A boundary circle of a cut Riemann surface carries no preferred coordinate, so the Sobolev spaces
of boundary maps must not depend on the parametrization: a fixed diffeomorphism `φ` of the circle
should induce a bounded isomorphism `u ↦ u ∘ φ` of `H^s`.
`TauCeti/Analysis/Sobolev/Circle/Diffeomorphism.lean` treats the integer orders. This file treats
the fractional orders `0 < s < 1`, which include the orders `1/2 < s < 1` at which `H^s` consists
of continuous functions.

The Fourier description of `H^s` does not see precomposition, but the Gagliardo–Slobodeckij
description does (`TauCeti.CircleSobolev.exists_inclusion_eq_iff_slobodeckijEnergy_ne_top`). The
energy of order `s` is the double integral

`∫∫ ‖u y - u x‖² / ‖y - x‖ ^ (1 + 2 s) dy dx`,

so if `φ` is `K`-Lipschitz and pushes Haar measure forward to at most `C` times Haar measure, then
the energy of `u ∘ φ` is at most `C² K ^ (1 + 2 s)` times the energy of `u`
(`TauCeti.CircleSobolev.slobodeckijEnergy_precomp_le`): the Lipschitz bound compares the two
kernels, and the measure bound is used once in each variable. Hence precomposition with `φ`
preserves `H^s`, and it is a continuous linear map of `H^s` by the closed graph theorem.

A map of the circle with a differentiable lift `F`, `0 < c ≤ F' ≤ M`, satisfies both bounds with
`K = M` and `C = c⁻¹`, and its inverse satisfies them with `K = c⁻¹` and `C = M`. So precomposition
with it is a continuous linear automorphism of `H^s` for every `0 < s < 1`. Only these two bounds
on `F'` are used: neither continuity nor higher regularity of `F'` is assumed, whereas the integer
orders of `TauCeti/Analysis/Sobolev/Circle/Diffeomorphism.lean` use a smooth derivative.

## Main definitions

* `TauCeti.CircleSobolev.precompFractional`: for `0 < s < 1` and a Lipschitz map `φ` of the
  circle pushing Haar measure forward to a bounded multiple of itself, the continuous linear map
  `u ↦ u ∘ φ` of `H^s`.
* `TauCeti.CircleSobolev.precompFractionalEquivOfLift`: for `0 < s < 1` and `φ` with lift `F`,
  `0 < c ≤ F' ≤ M`, the continuous linear automorphism `u ↦ u ∘ φ` of `H^s`.

## Main statements

* `TauCeti.CircleSobolev.slobodeckijEnergy_precomp_le`: the energy of `u ∘ φ` is at most
  `C² K ^ (1 + 2 s)` times the energy of `u`.
* `TauCeti.CircleSobolev.inclusion_precompFractional` and
  `TauCeti.CircleSobolev.inclusion_precompFractionalEquivOfLift`: in `H⁰` these operators are
  precomposition with `φ`.
* `TauCeti.CircleSobolev.precompFractionalEquivOfLift_symm_eq`: the inverse is precomposition
  with the inverse map of the circle, presented by any of its lifts.
* `TauCeti.CircleSobolev.inclusion_precompFractionalEquivOfLift_of_le`: the operators on the
  different fractional orders are compatible with the inclusions `H^s → H^t`, `t ≤ s`.

## References

* E. Di Nezza, G. Palatucci and E. Valdinoci, *Hitchhiker's guide to the fractional Sobolev
  spaces*, Bull. Sci. Math. **136** (2012), 521–573, for the Gagliardo seminorm.
* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, for the Sobolev spaces of boundary maps on which
  the Hardy decompositions of cut Riemann surfaces are carried out.
-/

public section

noncomputable section

open MeasureTheory AddCircle
open scoped ENNReal NNReal

namespace TauCeti

namespace CircleSobolev

variable {T : ℝ} [hT : Fact (0 < T)] {s : ℝ} {φ : AddCircle T → AddCircle T} {C : ℝ≥0∞}
  {K : ℝ≥0}

/-! ### Precomposition and the energy -/

omit hT in
/-- The kernels before and after a `K`-Lipschitz map: `‖y - x‖ ^ -(1 + 2 s)` is at most
`K ^ (1 + 2 s) ‖φ y - φ x‖ ^ -(1 + 2 s)` wherever the integrand `‖g (φ y) - g (φ x)‖²` is
nonzero. -/
private theorem enorm_sub_sq_mul_le (hs : 0 ≤ 1 + 2 * s) (hK : LipschitzWith K φ)
    (g : AddCircle T → ℂ) (x y : AddCircle T) :
    ‖g (φ y) - g (φ x)‖ₑ ^ 2 * ENNReal.ofReal (‖y - x‖ ^ (1 + 2 * s))⁻¹ ≤
      ENNReal.ofReal ((K : ℝ) ^ (1 + 2 * s)) *
        (‖g (φ y) - g (φ x)‖ₑ ^ 2 * ENNReal.ofReal (‖φ y - φ x‖ ^ (1 + 2 * s))⁻¹) := by
  by_cases hxy : φ y = φ x
  · simp [hxy]
  have hd : 0 < ‖φ y - φ x‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hle : ‖φ y - φ x‖ ≤ K * ‖y - x‖ := by
    simpa only [dist_eq_norm] using hK.dist_le_mul y x
  have hyx : 0 < ‖y - x‖ := pos_of_mul_pos_right (hd.trans_le hle) K.coe_nonneg
  have hK0 : 0 < (K : ℝ) := pos_of_mul_pos_left (hd.trans_le hle) (norm_nonneg _)
  have hpow : ‖φ y - φ x‖ ^ (1 + 2 * s) ≤ (K : ℝ) ^ (1 + 2 * s) * ‖y - x‖ ^ (1 + 2 * s) := by
    rw [← Real.mul_rpow K.coe_nonneg (norm_nonneg _)]
    exact Real.rpow_le_rpow hd.le hle hs
  have hreal : (‖y - x‖ ^ (1 + 2 * s))⁻¹ ≤
      (K : ℝ) ^ (1 + 2 * s) * (‖φ y - φ x‖ ^ (1 + 2 * s))⁻¹ := by
    have hKp : 0 < (K : ℝ) ^ (1 + 2 * s) := Real.rpow_pos_of_pos hK0 _
    calc (‖y - x‖ ^ (1 + 2 * s))⁻¹
        = (K : ℝ) ^ (1 + 2 * s) * ((K : ℝ) ^ (1 + 2 * s) * ‖y - x‖ ^ (1 + 2 * s))⁻¹ := by
          field_simp
      _ ≤ (K : ℝ) ^ (1 + 2 * s) * (‖φ y - φ x‖ ^ (1 + 2 * s))⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ (Real.rpow_pos_of_pos hd _) hpow) hKp.le
  rw [mul_left_comm, ← ENNReal.ofReal_mul (by positivity)]
  gcongr

/-- **Precomposition and the Gagliardo–Slobodeckij energy.** If `φ` is `K`-Lipschitz and pushes
Haar measure forward to at most `C` times Haar measure, then the energy of order `s` of `a ∘ φ`
is at most `C² K ^ (1 + 2 s)` times that of `a`, for every `s` with `1 + 2 s ≥ 0`. -/
theorem slobodeckijEnergy_precomp_le (hs : 0 ≤ 1 + 2 * s) (hK : LipschitzWith K φ)
    (hC : C ≠ ∞) (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (a : CircleSobolev 0 ℂ) :
    slobodeckijEnergy T s (precomp T hK.continuous.measurable hC hmap a) ≤
      C ^ 2 * ENNReal.ofReal ((K : ℝ) ^ (1 + 2 * s)) * slobodeckijEnergy T s a := by
  have hφm := hK.continuous.measurable
  -- A measurable representative `g` of the `L²` function of `a`; then `g ∘ φ` represents `a ∘ φ`.
  have hu := Lp.aestronglyMeasurable (toLpₗᵢ T a)
  set g := hu.mk
  have hgm : Measurable g := hu.stronglyMeasurable_mk.measurable
  have hgφ : toLpₗᵢ T (precomp T hφm hC hmap a) =ᵐ[haarAddCircle] g ∘ φ :=
    (toLpₗᵢ_precomp hφm hC hmap a).trans
      ((QuasiMeasurePreserving.of_map_le_smul hφm hmap).ae_eq_comp hu.ae_eq_mk)
  rw [slobodeckijEnergy_eq_lintegral_lintegral T (hgm.comp hφm) hgφ,
    slobodeckijEnergy_eq_lintegral_lintegral T hgm hu.ae_eq_mk]
  -- The integrand of the energy of `a`, as a function on the square.
  set Ψ : AddCircle T × AddCircle T → ℝ≥0∞ := fun z ↦
    ‖g z.2 - g z.1‖ₑ ^ 2 * ENNReal.ofReal (‖z.2 - z.1‖ ^ (1 + 2 * s))⁻¹
  have hΨ : Measurable Ψ := by fun_prop
  have hvol : (volume : Measure (AddCircle T)).map φ ≤ C • volume := by
    rw [volume_eq_smul_haarAddCircle, Measure.map_smul _ hφm.aemeasurable, smul_comm]
    gcongr
  set Kp := ENNReal.ofReal ((K : ℝ) ^ (1 + 2 * s))
  calc ∫⁻ x, ∫⁻ y, ‖(g ∘ φ) y - (g ∘ φ) x‖ₑ ^ 2 * ENNReal.ofReal (‖y - x‖ ^ (1 + 2 * s))⁻¹
        ∂volume ∂haarAddCircle
      ≤ ∫⁻ x, ∫⁻ y, Kp * Ψ (φ x, φ y) ∂volume ∂haarAddCircle :=
        lintegral_mono fun x ↦ lintegral_mono fun y ↦ enorm_sub_sq_mul_le hs hK g x y
    _ = Kp * ∫⁻ x, ∫⁻ y, Ψ (φ x, y) ∂(volume.map φ) ∂haarAddCircle := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x ↦ ?_
        rw [lintegral_map (f := fun y ↦ Ψ (φ x, y)) (hΨ.comp measurable_prodMk_left) hφm,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    -- The measure bound in the inner variable `y`.
    _ ≤ Kp * ∫⁻ x, C * ∫⁻ y, Ψ (φ x, y) ∂volume ∂haarAddCircle := by
        gcongr with x
        exact (lintegral_mono' hvol le_rfl).trans_eq (by rw [lintegral_smul_measure, smul_eq_mul])
    -- The measure bound in the outer variable `x`.
    _ = Kp * (C * ∫⁻ x, ∫⁻ y, Ψ (x, y) ∂volume ∂(haarAddCircle.map φ)) := by
        rw [lintegral_const_mul' _ _ hC,
          lintegral_map (f := fun x ↦ ∫⁻ y, Ψ (x, y) ∂volume) hΨ.lintegral_prod_right' hφm]
    _ ≤ Kp * (C * ∫⁻ x, ∫⁻ y, Ψ (x, y) ∂volume ∂(C • haarAddCircle)) := by
        gcongr
    _ = C ^ 2 * Kp * ∫⁻ x, ∫⁻ y, Ψ (x, y) ∂volume ∂haarAddCircle := by
        rw [lintegral_smul_measure, smul_eq_mul]
        ring

/-! ### Precomposition on `H^s` -/

/-- **Precomposition preserves `H^s`, `0 < s < 1`.** If `φ` is Lipschitz and pushes Haar measure
forward to at most `C` times Haar measure, then for `u ∈ H^s` the function `u ∘ φ ∈ H⁰` comes from
an element of `H^s`. -/
theorem exists_inclusion_eq_precomp (hs0 : 0 < s) (hs1 : s < 1) (hK : LipschitzWith K φ)
    (hC : C ≠ ∞) (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (a : CircleSobolev s ℂ) :
    ∃ b : CircleSobolev s ℂ,
      inclusion hs0.le b = precomp T hK.continuous.measurable hC hmap (inclusion hs0.le a) := by
  refine (exists_inclusion_eq_iff_slobodeckijEnergy_ne_top T hs0 hs1 _).2 ?_
  obtain ⟨D, -, hD⟩ := exists_slobodeckijEnergy_le (E := ℂ) T hs0 hs1
  refine ne_top_of_le_ne_top ?_ (slobodeckijEnergy_precomp_le (by linarith) hK hC hmap _)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top hC) ENNReal.ofReal_ne_top)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hD a))

/-- **Precomposition on `H^s`, `0 < s < 1`.** For a `K`-Lipschitz map `φ` of the circle pushing
Haar measure forward to at most `C` times Haar measure, `C < ∞`, the continuous linear map
`u ↦ u ∘ φ` of `H^s`. It is continuous by the closed graph theorem. -/
def precompFractional (hs0 : 0 < s) (hs1 : s < 1) (hK : LipschitzWith K φ) (hC : C ≠ ∞)
    (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle) :
    CircleSobolev s ℂ →L[ℂ] CircleSobolev s ℂ :=
  restrict hs0.le hs0.le (precomp T hK.continuous.measurable hC hmap)
    (exists_inclusion_eq_precomp hs0 hs1 hK hC hmap)

/-- In `H⁰`, `precompFractional` is the precomposition `precomp`: the inclusion of `u ∘ φ` into
`H⁰` is the precomposition of the inclusion of `u`. -/
@[simp]
theorem inclusion_precompFractional (hs0 : 0 < s) (hs1 : s < 1) (hK : LipschitzWith K φ)
    (hC : C ≠ ∞) (hmap : (haarAddCircle : Measure (AddCircle T)).map φ ≤ C • haarAddCircle)
    (a : CircleSobolev s ℂ) :
    inclusion hs0.le (precompFractional hs0 hs1 hK hC hmap a) =
      precomp T hK.continuous.measurable hC hmap (inclusion hs0.le a) :=
  inclusion_restrict _ _ _ _ a

/-! ### Circle diffeomorphisms -/

section Lift

variable {F F' : ℝ → ℝ} {c M : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
  (hF : ∀ x, HasDerivAt F (F' x) x) (hper : ∀ x, F (x + T) = F x + T) (hφ : ∀ x : ℝ, φ x = F x)
  (hc : 0 < c) (hcF : ∀ x, c ≤ F' x) (hMF : ∀ x, F' x ≤ M)

/-- Precomposition with `φ` on `H^s`, as a continuous linear map; its inclusion into `H⁰` is
`precompEquivOfLift`. -/
private def precompFractionalOfLift : CircleSobolev s ℂ →L[ℂ] CircleSobolev s ℂ :=
  precompFractional hs0 hs1
    (lipschitzWith_toNNReal_of_lift hF hφ (fun x ↦ hc.le.trans (hcF x)) hMF)
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hc).ne')
    (map_haarAddCircle_le_of_lift hF hper hφ hc hcF)

private theorem inclusion_precompFractionalOfLift (a : CircleSobolev s ℂ) :
    inclusion hs0.le (precompFractionalOfLift hs0 hs1 hF hper hφ hc hcF hMF a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion hs0.le a) :=
  (inclusion_precompFractional _ _ _ _ _ a).trans (precompEquivOfLift_apply _ _ _ _ _ _ _).symm

private theorem injective_precompFractionalOfLift :
    Function.Injective (precompFractionalOfLift hs0 hs1 hF hper hφ hc hcF hMF) := fun a b hab ↦
  inclusion_injective hs0.le ((precompEquivOfLift hF hper hφ hc hcF hMF).injective
    (by rw [← inclusion_precompFractionalOfLift hs0 hs1,
      ← inclusion_precompFractionalOfLift hs0 hs1, hab]))

/-- Precomposition on `H^s` is surjective: the inverse map of the circle has a lift with
derivative between `M⁻¹` and `c⁻¹`, so precomposition with it preserves `H^s` as well. -/
private theorem surjective_precompFractionalOfLift :
    Function.Surjective (precompFractionalOfLift hs0 hs1 hF hper hφ hc hcF hMF) := by
  intro b
  have hpos (x : ℝ) : 0 < F' x := hc.trans_le (hcF x)
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt
  obtain ⟨G, -, hFG, hperG, hG⟩ := exists_lift_inverse hF hper hpos
  -- The inverse map `ψ` of the circle, with lift `G`.
  set e := homeomorphOfLift φ (strictMono_of_hasDerivAt_pos hF hpos) hFc hper hφ
  have hψφ : Function.LeftInverse e.symm φ :=
    homeomorphOfLift_symm_apply_apply (strictMono_of_hasDerivAt_pos hF hpos) hFc hper hφ
  have hψ (y : ℝ) : e.symm y = G y :=
    calc e.symm y = e.symm (φ (G y)) := by rw [hφ, hFG y]
      _ = G y := hψφ _
  have hM : 0 < M⁻¹ := inv_pos.2 ((hpos 0).trans_le (hMF 0))
  have hMG (y : ℝ) : M⁻¹ ≤ (F' (G y))⁻¹ := inv_anti₀ (hpos _) (hMF _)
  have hcG (y : ℝ) : (F' (G y))⁻¹ ≤ c⁻¹ := inv_anti₀ hc (hcF _)
  refine ⟨precompFractionalOfLift hs0 hs1 hG hperG hψ hM hMG hcG b, inclusion_injective hs0.le ?_⟩
  rw [inclusion_precompFractionalOfLift, inclusion_precompFractionalOfLift,
    ← precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF hG hperG hψ hM hMG hcG hψφ,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **Circle diffeomorphisms act on `H^s`, `0 < s < 1`.** Let `φ` be the map of the circle with
lift `F`, so that `F (x + T) = F x + T` and `φ x = F x`, and suppose that `F` is differentiable
with `0 < c ≤ F' ≤ M`. Then for every `0 < s < 1`, `u ↦ u ∘ φ` is a continuous linear
automorphism of `H^s`. Its inverse is precomposition with the inverse map of the circle
(`TauCeti.CircleSobolev.precompFractionalEquivOfLift_symm_eq`). -/
def precompFractionalEquivOfLift : CircleSobolev s ℂ ≃L[ℂ] CircleSobolev s ℂ :=
  ContinuousLinearEquiv.ofBijective (precompFractionalOfLift hs0 hs1 hF hper hφ hc hcF hMF)
    (LinearMap.ker_eq_bot.2 (injective_precompFractionalOfLift hs0 hs1 hF hper hφ hc hcF hMF))
    (LinearMap.range_eq_top.2 (surjective_precompFractionalOfLift hs0 hs1 hF hper hφ hc hcF hMF))

/-- In `H⁰`, precomposition on `H^s` is the precomposition `precompEquivOfLift`: the inclusion of
`u ∘ φ` into `H⁰` is the precomposition of the inclusion of `u`. -/
@[simp]
theorem inclusion_precompFractionalEquivOfLift (a : CircleSobolev s ℂ) :
    inclusion hs0.le (precompFractionalEquivOfLift hs0 hs1 hF hper hφ hc hcF hMF a) =
      precompEquivOfLift hF hper hφ hc hcF hMF (inclusion hs0.le a) :=
  inclusion_precompFractionalOfLift hs0 hs1 hF hper hφ hc hcF hMF a

/-- In `H⁰`, the inverse of precomposition on `H^s` is the inverse of `precompEquivOfLift`. -/
@[simp]
theorem inclusion_precompFractionalEquivOfLift_symm (a : CircleSobolev s ℂ) :
    inclusion hs0.le ((precompFractionalEquivOfLift hs0 hs1 hF hper hφ hc hcF hMF).symm a) =
      (precompEquivOfLift hF hper hφ hc hcF hMF).symm (inclusion hs0.le a) := by
  rw [ContinuousLinearEquiv.eq_symm_apply, ← inclusion_precompFractionalEquivOfLift hs0 hs1,
    ContinuousLinearEquiv.apply_symm_apply]

/-- Precomposition on the different fractional orders is compatible with the inclusions
`H^s → H^t`. -/
theorem inclusion_precompFractionalEquivOfLift_of_le {t : ℝ} (ht0 : 0 < t) (hts : t ≤ s)
    (a : CircleSobolev s ℂ) :
    inclusion hts (precompFractionalEquivOfLift hs0 hs1 hF hper hφ hc hcF hMF a) =
      precompFractionalEquivOfLift ht0 (hts.trans_lt hs1) hF hper hφ hc hcF hMF
        (inclusion hts a) :=
  inclusion_injective ht0.le (by
    simp only [inclusion_inclusion, inclusion_precompFractionalEquivOfLift])

/-- The inverse of `precompFractionalEquivOfLift` is `precompFractionalEquivOfLift` for the
inverse map `ψ` of the circle, presented by any lift `G` of `ψ` with derivative between two
positive constants. -/
theorem precompFractionalEquivOfLift_symm_eq {ψ : AddCircle T → AddCircle T} {G G' : ℝ → ℝ}
    {c' M' : ℝ} (hG : ∀ x, HasDerivAt G (G' x) x) (hperG : ∀ x, G (x + T) = G x + T)
    (hψ : ∀ x : ℝ, ψ x = G x) (hc' : 0 < c') (hcG : ∀ x, c' ≤ G' x) (hMG : ∀ x, G' x ≤ M')
    (hψφ : Function.LeftInverse ψ φ) :
    (precompFractionalEquivOfLift hs0 hs1 hF hper hφ hc hcF hMF).symm =
      precompFractionalEquivOfLift hs0 hs1 hG hperG hψ hc' hcG hMG :=
  ContinuousLinearEquiv.ext <| funext fun a ↦ inclusion_injective hs0.le (by
    rw [inclusion_precompFractionalEquivOfLift_symm, inclusion_precompFractionalEquivOfLift,
      precompEquivOfLift_symm_eq hF hper hφ hc hcF hMF hG hperG hψ hc' hcG hMG hψφ])

end Lift

end CircleSobolev

end TauCeti
