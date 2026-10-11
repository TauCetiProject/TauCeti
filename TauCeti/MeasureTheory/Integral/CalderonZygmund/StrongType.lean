/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Adjoint
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.WeakType
public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.General

/-!
# Singular integral operators of strong type `(p, p)` for `1 < p < ∞`

Let `T` be a bounded linear operator on `L²(ℝⁿ)` satisfying the Calderón–Zygmund cancellation
condition, for instance one given by a kernel satisfying Hörmander's condition. The weak type
`(1, 1)` half of the **Calderón–Zygmund theorem** is
`ContinuousLinearMap.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`. Marcinkiewicz
interpolation between that bound and the `L²` bound
(`ContinuousLinearMap.eLpNorm_le_of_rpow_mul_meas_lt_le`) gives the strong type `(p, p)` bound

`‖T f‖_p ≤ (p / (p - 1) · 2 C + p / (2 - p) · 4 ‖T‖²) ^ (1 / p) ‖f‖_p`

for every `1 < p < 2` and every `f ∈ L²`, where `C = 2ⁿ (4 ‖T‖² + 1) + 4 B` is the weak type
`(1, 1)` constant. This constant blows up as `p → 1`, and also as `p → 2` when `‖T‖ > 0`. That
is a limitation of the interpolation argument, not of every operator satisfying the hypotheses
(the zero operator satisfies them), although classical singular integrals such as the Hilbert
transform are indeed not bounded on `L¹`.

For Hilbert space valued functions, the range `2 < p < ∞` follows by duality
(`ContinuousLinearMap.eLpNorm_le_of_eLpNorm_adjoint_le`): if the adjoint `T†` satisfies the
cancellation condition, the bound for `T†` at the conjugate exponent `p / (p - 1) ∈ (1, 2)` gives

`‖T f‖_p ≤ (p · 2 C + p / (p - 2) · 4 ‖T‖²) ^ (1 - 1 / p) ‖f‖_p`

for every `f ∈ L²`, with `C = 2ⁿ (4 ‖T‖² + 1) + 4 B` and `B` the cancellation constant of `T†`.
When `T` and `T†` both satisfy the cancellation condition, `T` is therefore bounded in the `Lᵖ`
norm for every `1 < p < ∞`.

Since `T` is only given on `L²`, the estimates are stated for `f ∈ L²`, and they are informative
for `f ∈ L² ∩ Lᵖ`. Extending `T` to a bounded operator on all of `Lᵖ` is a separate density
argument, not carried out here.

Points of `ℝⁿ` are functions `ι → ℝ`, so distances and balls are taken in the sup norm.

## Main declarations

* `ContinuousLinearMap.eLpNorm_le_of_setLIntegral_compl_closedBall_le`: an `L²`-bounded operator
  satisfying the cancellation condition is of strong type `(p, p)` for `1 < p < 2`.
* `ContinuousLinearMap.eLpNorm_le_of_hormander`: an `L²`-bounded operator with a kernel satisfying
  Hörmander's condition is of strong type `(p, p)` for `1 < p < 2`.
* `ContinuousLinearMap.eLpNorm_le_of_setLIntegral_compl_closedBall_adjoint_le`: an `L²`-bounded
  operator whose adjoint satisfies the cancellation condition is of strong type `(p, p)` for
  `2 < p < ∞`.
* `ContinuousLinearMap.eLpNorm_le_of_hormander_adjoint`: the same when the adjoint is given by a
  kernel satisfying Hörmander's condition.
* `ContinuousLinearMap.exists_eLpNorm_le_of_setLIntegral_compl_closedBall_le`: if an operator and
  its adjoint both satisfy the cancellation condition, the operator is of strong type `(p, p)` for
  every `1 < p < ∞`.

## References

* A. P. Calderón and A. Zygmund, *On the existence of certain singular integrals*, Acta Math.
  **88** (1952), 85–139.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter II, §2.
* L. Grafakos, *Classical Fourier Analysis*, Section 5.3.
-/

public section

namespace ContinuousLinearMap

open MeasureTheory Metric Set TauCeti
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞}

/-- **The Calderón–Zygmund theorem**, strong type `(p, p)` for `1 < p < 2`. Let `T` be a bounded
linear operator on `L²(ℝⁿ)` satisfying the cancellation condition: for every `b ∈ L²` vanishing off
a closed ball `closedBall y r` with integral zero, `∫_{ℝⁿ \ closedBall y (2r)} ‖T b‖ ≤ B ‖b‖₁`.
Then for every `1 < p < 2` and every `f ∈ L²`,

`‖T f‖_p ≤ (p / (p - 1) · 2 C + p / (2 - p) · 4 ‖T‖²) ^ (1 / p) ‖f‖_p`,

where `C = 2ⁿ (4 ‖T‖² + 1) + 4 B` is the weak type `(1, 1)` constant of
`ContinuousLinearMap.mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le`. The bound is
vacuous unless `f` also lies in `Lᵖ`. -/
theorem eLpNorm_le_of_setLIntegral_compl_closedBall_le
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ))) {B : ℝ≥0∞}
    (hT : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖T b x‖ₑ ≤ B * ∫⁻ x, ‖b x‖ₑ)
    (hp : 1 < p) (hp₂ : p < 2) (f : Lp E 2 (volume : Measure (ι → ℝ))) :
    eLpNorm (T f) p volume ≤
      (ENNReal.ofReal (p.toReal / (p.toReal - 1)) *
          (2 * (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B)) +
        ENNReal.ofReal (p.toReal / (2 - p.toReal)) * (4 * ‖T‖ₑ ^ 2)) ^ (1 / p.toReal) *
        eLpNorm f p volume := by
  have h := eLpNorm_le_of_rpow_mul_meas_lt_le T zero_lt_one hp hp₂ ENNReal.ofNat_ne_top
    (fun g s => by
      simpa using mul_volume_lt_enorm_le_of_setLIntegral_compl_closedBall_le T hT g s) f
  convert h using 6 <;> norm_num

/-- **The Calderón–Zygmund theorem** for an operator given by a kernel, strong type `(p, p)` for
`1 < p < 2`. Let `T` be a bounded linear operator on `L²(ℝⁿ)` such that `T b x = ∫ K x y (b y) dy`
for almost every `x` off any closed ball outside which `b` vanishes, where the kernel `K` satisfies
Hörmander's condition `∫_{dist x y' > 2 dist y y'} ‖K x y - K x y'‖ dx ≤ B` for all `y`, `y'`.
Then for every `1 < p < 2` and every `f ∈ L²`,

`‖T f‖_p ≤ (p / (p - 1) · 2 (2ⁿ (4 ‖T‖² + 1) + 4 B) + p / (2 - p) · 4 ‖T‖²) ^ (1 / p) ‖f‖_p`. -/
theorem eLpNorm_le_of_hormander [CompleteSpace F]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F} (hK : StronglyMeasurable (Function.uncurry K))
    {B : ℝ≥0∞} (hB : ∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖K x y - K x y'‖ₑ ≤ B)
    (hrep : ∀ (b : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) →
        ∀ᵐ x, x ∉ closedBall y r → T b x = ∫ z, K x z (b z))
    (hp : 1 < p) (hp₂ : p < 2) (f : Lp E 2 (volume : Measure (ι → ℝ))) :
    eLpNorm (T f) p volume ≤
      (ENNReal.ofReal (p.toReal / (p.toReal - 1)) *
          (2 * (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B)) +
        ENNReal.ofReal (p.toReal / (2 - p.toReal)) * (4 * ‖T‖ₑ ^ 2)) ^ (1 / p.toReal) *
        eLpNorm f p volume := by
  have h := eLpNorm_le_of_rpow_mul_meas_lt_le T zero_lt_one hp hp₂ ENNReal.ofNat_ne_top
    (fun g s => by simpa using mul_volume_lt_enorm_le_of_hormander T hK hB hrep g s) f
  convert h using 6 <;> norm_num

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- **The Calderón–Zygmund theorem**, strong type `(p, p)` for `2 < p < ∞`. Let `T` be a bounded
linear operator on `L²(ℝⁿ)` of Hilbert space valued functions whose adjoint `T†` satisfies the
cancellation condition: for every `b ∈ L²` vanishing off a closed ball `closedBall y r` with
integral zero, `∫_{ℝⁿ \ closedBall y (2r)} ‖T† b‖ ≤ B ‖b‖₁`. Then for every `2 < p < ∞` and every
`f ∈ L²`,

`‖T f‖_p ≤ (p · 2 C + p / (p - 2) · 4 ‖T‖²) ^ (1 - 1 / p) ‖f‖_p`,

where `C = 2ⁿ (4 ‖T‖² + 1) + 4 B`. This is the bound of
`ContinuousLinearMap.eLpNorm_le_of_setLIntegral_compl_closedBall_le` for `T†` at the conjugate
exponent `p / (p - 1) ∈ (1, 2)`, transferred to `T` by duality. -/
theorem eLpNorm_le_of_setLIntegral_compl_closedBall_adjoint_le
    (T : Lp H 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp K 2 (volume : Measure (ι → ℝ))) {B : ℝ≥0∞}
    (hT : ∀ (b : Lp K 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖adjoint T b x‖ₑ ≤ B * ∫⁻ x, ‖b x‖ₑ)
    (hp : 2 < p) (hp_top : p ≠ ∞) (f : Lp H 2 (volume : Measure (ι → ℝ))) :
    eLpNorm (T f) p volume ≤
      (ENNReal.ofReal p.toReal * (2 * (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B)) +
        ENNReal.ofReal (p.toReal / (p.toReal - 2)) * (4 * ‖T‖ₑ ^ 2)) ^ (1 - 1 / p.toReal) *
        eLpNorm f p volume := by
  set P := p.toReal
  have hP : 2 < P := by simpa using (ENNReal.toReal_lt_toReal (by norm_num) hp_top).2 hp
  -- The conjugate exponent `P' = P / (P - 1)` lies in `(1, 2)`.
  set P' := P / (P - 1)
  have hP'1 : 1 < P' := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hP'2 : P' < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
  have : p.HolderConjugate (ENNReal.ofReal P') := by
    refine ENNReal.HolderConjugate.of_toReal ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact Real.HolderConjugate.conjExponent (by linarith)
  have h := eLpNorm_le_of_eLpNorm_adjoint_le T (p := p) (q := p) hp_top (fun g =>
    eLpNorm_le_of_setLIntegral_compl_closedBall_le (adjoint T) hT
      (ENNReal.one_lt_ofReal.2 hP'1) ((ENNReal.ofReal_lt_ofReal_iff two_pos).2 hP'2 |>.trans_eq
        (ENNReal.ofReal_ofNat 2)) g) f
  have hP1 : P - 1 ≠ 0 := (by linarith : (0 : ℝ) < P - 1).ne'
  have hP'1' : P' - 1 = 1 / (P - 1) := by simp only [P']; field_simp; ring
  have hP'2' : 2 - P' = (P - 2) / (P - 1) := by simp only [P']; field_simp; ring
  have h₁ : P' / (P' - 1) = P := by rw [hP'1']; simp only [P']; field_simp
  have h₂ : P' / (2 - P') = P / (P - 2) := by
    rw [hP'2']; simp only [P']; rw [div_div_div_cancel_right₀ hP1]
  have h₃ : 1 / P' = 1 - 1 / P := by
    simp only [P']
    field_simp
  rwa [LinearIsometryEquiv.enorm_map, ENNReal.toReal_ofReal (by positivity), h₁, h₂, h₃] at h

/-- **The Calderón–Zygmund theorem** for an operator whose adjoint is given by a kernel, strong
type `(p, p)` for `2 < p < ∞`. Let `T` be a bounded linear operator on `L²(ℝⁿ)` of Hilbert space
valued functions such that `T† b x = ∫ k x y (b y) dy` for almost every `x` off any closed ball
outside which `b` vanishes, where `k` satisfies Hörmander's condition
`∫_{dist x y' > 2 dist y y'} ‖k x y - k x y'‖ dx ≤ B` for all `y`, `y'`. Then for every
`2 < p < ∞` and every `f ∈ L²`,

`‖T f‖_p ≤ (p · 2 (2ⁿ (4 ‖T‖² + 1) + 4 B) + p / (p - 2) · 4 ‖T‖²) ^ (1 - 1 / p) ‖f‖_p`.

Formally, if `T` has kernel `K`, then `T†` has kernel `k x y = (K y x)†`, and the hypothesis is
Hörmander's condition for `K` with the roles of its two variables exchanged. -/
theorem eLpNorm_le_of_hormander_adjoint
    (T : Lp H 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp K 2 (volume : Measure (ι → ℝ)))
    {k : (ι → ℝ) → (ι → ℝ) → K →L[ℝ] H} (hk : StronglyMeasurable (Function.uncurry k))
    {B : ℝ≥0∞} (hB : ∀ y y', ∫⁻ x in {x | 2 * dist y y' < dist x y'}, ‖k x y - k x y'‖ₑ ≤ B)
    (hrep : ∀ (b : Lp K 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) →
        ∀ᵐ x, x ∉ closedBall y r → adjoint T b x = ∫ z, k x z (b z))
    (hp : 2 < p) (hp_top : p ≠ ∞) (f : Lp H 2 (volume : Measure (ι → ℝ))) :
    eLpNorm (T f) p volume ≤
      (ENNReal.ofReal p.toReal * (2 * (2 ^ Fintype.card ι * (4 * ‖T‖ₑ ^ 2 + 1) + 4 * B)) +
        ENNReal.ofReal (p.toReal / (p.toReal - 2)) * (4 * ‖T‖ₑ ^ 2)) ^ (1 - 1 / p.toReal) *
        eLpNorm f p volume :=
  eLpNorm_le_of_setLIntegral_compl_closedBall_adjoint_le T
    (setLIntegral_compl_closedBall_enorm_apply_le_of_hormander (adjoint T) hk hB hrep) hp hp_top f

/-- **The Calderón–Zygmund theorem** on `Lᵖ`, `1 < p < ∞`. Let `T` be a bounded linear operator
on `L²(ℝⁿ)` of Hilbert space valued functions such that both `T` and its adjoint satisfy the
cancellation condition, with finite constants `B` and `B'`. Then for every `1 < p < ∞` there is a
constant `C` with `‖T f‖_p ≤ C ‖f‖_p` for every `f ∈ L²`. Explicit constants are given by
`ContinuousLinearMap.eLpNorm_le_of_setLIntegral_compl_closedBall_le` for `p < 2` and by
`ContinuousLinearMap.eLpNorm_le_of_setLIntegral_compl_closedBall_adjoint_le` for `p > 2`. -/
theorem exists_eLpNorm_le_of_setLIntegral_compl_closedBall_le
    (T : Lp H 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp K 2 (volume : Measure (ι → ℝ)))
    {B B' : ℝ≥0∞} (hB : B ≠ ∞) (hB' : B' ≠ ∞)
    (hT : ∀ (b : Lp H 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖T b x‖ₑ ≤ B * ∫⁻ x, ‖b x‖ₑ)
    (hT' : ∀ (b : Lp K 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (r : ℝ),
      (∀ᵐ x, x ∉ closedBall y r → b x = 0) → ∫ x, b x = 0 →
        ∫⁻ x in (closedBall y (2 * r))ᶜ, ‖adjoint T b x‖ₑ ≤ B' * ∫⁻ x, ‖b x‖ₑ)
    (hp : 1 < p) (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ f : Lp H 2 (volume : Measure (ι → ℝ)),
      eLpNorm (T f) p volume ≤ C * eLpNorm f p volume := by
  suffices ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ f : Lp H 2 (volume : Measure (ι → ℝ)),
      eLpNorm (T f) p volume ≤ C * eLpNorm f p volume by
    obtain ⟨C, hC, h⟩ := this
    exact ⟨C.toNNReal, by simpa [ENNReal.coe_toNNReal hC] using h⟩
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · exact ⟨_, ENNReal.rpow_ne_top_of_nonneg (by positivity) (by finiteness),
      eLpNorm_le_of_setLIntegral_compl_closedBall_le T hT hp hp2⟩
  · exact ⟨‖T‖ₑ, enorm_ne_top, fun f => by simpa only [Lp.enorm_def] using T.le_opENorm f⟩
  · refine ⟨_, ENNReal.rpow_ne_top_of_nonneg ?_ (by finiteness),
      eLpNorm_le_of_setLIntegral_compl_closedBall_adjoint_le T hT' hp2 hp_top⟩
    have : 1 ≤ p.toReal := by simpa using (ENNReal.toReal_le_toReal (by norm_num) hp_top).2 hp.le
    rw [sub_nonneg]
    exact div_le_one_of_le₀ this (by positivity)

end ContinuousLinearMap
