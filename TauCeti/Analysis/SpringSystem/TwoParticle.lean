/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import TauCeti.Analysis.SpringSystem.Basic

/-!
# Two particles on a spring, and the failure of the linearization on its transverse zero mode

Two particles rest at `p₁ = (0, 0)` and `p₂ = (1, 0)` in the plane, joined by a spring of
stiffness `κ` and rest length `1`. Displacing them by `u₁` and `u₂` changes the relative vector to
`(1, 0) + u₂ - u₁`, and the exact force on the first particle is
`TauCeti.springForce κ 1 ((1, 0) + u₂ - u₁)`, the second particle feeling its opposite. The
declarations specific to this example live in the namespace `TauCeti.TwoParticleSpring`.

**The linearization.** In the coordinate order `(x₁, y₁, x₂, y₂)` the linearized force is
`κ H u`, with `H = TauCeti.TwoParticleSpring.forceMatrix`: only the stretching of the spring along
the rest direction is felt to first order. Its eigenvectors are the stretching mode
`(1, 0, -1, 0)`, of eigenvalue `-2`, the two translations `(1, 0, 1, 0)` and `(0, 1, 0, 1)` and
the transverse mode `(0, 1, 0, -1)`, all three of eigenvalue `0`.

**The transverse zero mode, made exact.** Along the transverse displacement `u₁ = (0, ε)`,
`u₂ = (0, -ε)` the relative vector is `(1, -2ε)`, of length
`ℓ(ε) = √(1 + 4ε²)` (`TauCeti.TwoParticleSpring.transverseLength`), and the exact potential is

`E(ε) = (κ / 2) (ℓ(ε) - 1)² = 8 κ ε⁴ / (ℓ(ε) + 1)²`

(`TauCeti.TwoParticleSpring.transverseEnergy`, `TauCeti.TwoParticleSpring.transverseEnergy_eq_div`).
It vanishes at `ε = 0` to fourth order: `E(0) = E'(0) = E''(0) = 0`, yet `E(ε) > 0` for `ε ≠ 0`,
and `E(ε) / ε⁴ → 2κ` (`TauCeti.TwoParticleSpring.transverseEnergy_quartic`). The exact force on
the first particle is `κ (1 - 1/ℓ(ε)) (1, -2ε)`. It vanishes to first order at `ε = 0`, as the
linearization predicts, but its first coordinate is positive for `ε ≠ 0`. Hence the affine paths
`u₁(t) = (0, a t)`, `u₂(t) = (0, -a t)` with `a ≠ 0`, which solve the linearized equation because
`H` annihilates them, fail the exact Newton equation at every `t ≠ 0` and for every mass
(`TauCeti.TwoParticleSpring.mass_smul_deriv_deriv_ne_springForce_transverse`): their acceleration
is zero and the exact force is not.

The zero eigenvalue on the transverse mode is instead the tangent of a curve of rest
configurations: the clockwise rotations by `2ε`, `p₁(ε) = (½ - ½ cos 2ε, ½ sin 2ε)` and
`p₂(ε) = (½ + ½ cos 2ε, -½ sin 2ε)`, of the rest configuration about its midpoint keep the
particles at distance `1`, so they store no energy, and their velocity at `ε = 0` is
`(0, 1, 0, -1)` (`TauCeti.TwoParticleSpring.hasDerivAt_rotatedRestFirst_zero`,
`TauCeti.TwoParticleSpring.hasDerivAt_rotatedRestSecond_zero`). These are configuration curves,
not solutions of the spring equation.

## Main definitions

* `TauCeti.TwoParticleSpring.forceMatrix`: the linearized force matrix `H`.
* `TauCeti.TwoParticleSpring.transverseLength`, `TauCeti.TwoParticleSpring.transverseEnergy`: the
  exact length and potential along the transverse displacement.
* `TauCeti.TwoParticleSpring.rotatedRestFirst`, `TauCeti.TwoParticleSpring.rotatedRestSecond`: the
  rotated rest configurations.

## Main results

* `TauCeti.TwoParticleSpring.springPotential_transverse`,
  `TauCeti.TwoParticleSpring.springForce_transverse`: the exact potential and force along the
  transverse displacement.
* `TauCeti.TwoParticleSpring.hasDerivAt_springForce_transverse_zero`: that force vanishes to first
  order at `0`, as `H` predicts.
* `TauCeti.TwoParticleSpring.transverseEnergy_eq_div`: the closed form
  `E(ε) = 8 κ ε⁴ / (ℓ(ε) + 1)²`.
* `TauCeti.TwoParticleSpring.deriv_transverseEnergy_zero`,
  `TauCeti.TwoParticleSpring.deriv_deriv_transverseEnergy_zero`,
  `TauCeti.TwoParticleSpring.transverseEnergy_pos`: the potential vanishes to second order at `0`
  but is positive elsewhere.
* `TauCeti.TwoParticleSpring.transverseEnergy_quartic`: `E(ε) / ε⁴ → 2κ` as `ε → 0`, `ε ≠ 0`, and
  `TauCeti.TwoParticleSpring.transverseEnergy_div_pow_four_lt`: the quotient stays below `2κ`.
* `TauCeti.TwoParticleSpring.mass_smul_deriv_deriv_ne_springForce_transverse`: the affine
  transverse paths are not solutions of the exact equation of motion.

## References

* A. Knutson, *Group theory in physics: an example*, notes for Math 261 (Cornell, 2001),
  pp. 1–3 (the two-particle spring and the limitation of the linear approximation).
-/

public section

namespace TauCeti.TwoParticleSpring

open Real Filter Topology Matrix

/-! ### The linearized force matrix -/

/-- The **force matrix** `H` of the linearized system of two particles at `(0, 0)` and `(1, 0)`
joined by a spring of stiffness `κ` and rest length `1`, in the coordinate order
`(x₁, y₁, x₂, y₂)`: the linearized force is `κ H u`, in which only the stretching `x₂ - x₁` along
the rest direction is felt. Along the transverse mode `(0, 1, 0, -1)` this first-order vanishing
of the exact force is `TauCeti.TwoParticleSpring.hasDerivAt_springForce_transverse_zero`. -/
def forceMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 1, 0; 0, 0, 0, 0; 1, 0, -1, 0; 0, 0, 0, 0]

theorem forceMatrix_def :
    forceMatrix = !![-1, 0, 1, 0; 0, 0, 0, 0; 1, 0, -1, 0; 0, 0, 0, 0] :=
  (rfl)

/-- The stretching mode `(1, 0, -1, 0)` is an eigenvector of `H` of eigenvalue `-2`. -/
theorem forceMatrix_mulVec_stretch :
    forceMatrix *ᵥ ![1, 0, -1, 0] = ![-2, 0, 2, 0] := by
  ext i
  fin_cases i <;> simp [forceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    norm_num

/-- The horizontal translation `(1, 0, 1, 0)` is a zero mode of `H`. -/
theorem forceMatrix_mulVec_translation_x :
    forceMatrix *ᵥ ![1, 0, 1, 0] = 0 := by
  ext i
  fin_cases i <;> simp [forceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The vertical translation `(0, 1, 0, 1)` is a zero mode of `H`. -/
theorem forceMatrix_mulVec_translation_y :
    forceMatrix *ᵥ ![0, 1, 0, 1] = 0 := by
  ext i
  fin_cases i <;> simp [forceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The transverse displacement `(0, ε, 0, -ε)` is a zero mode of `H`. -/
theorem forceMatrix_mulVec_transverse (ε : ℝ) :
    forceMatrix *ᵥ ![0, ε, 0, -ε] = 0 := by
  ext i
  fin_cases i <;> simp [forceMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-! ### The exact length and potential along the transverse displacement -/

/-- The exact length `ℓ(ε) = √(1 + 4ε²)` of the spring at the transverse displacement
`u₁ = (0, ε)`, `u₂ = (0, -ε)`, with rest length `1`. -/
noncomputable def transverseLength (ε : ℝ) : ℝ :=
  √(1 + 4 * ε ^ 2)

/-- The exact potential `E(ε) = (κ / 2) (ℓ(ε) - 1)²` of the transverse displacement
`u₁ = (0, ε)`, `u₂ = (0, -ε)`, for a spring of stiffness `κ` and rest length `1`. -/
noncomputable def transverseEnergy (κ ε : ℝ) : ℝ :=
  κ / 2 * (transverseLength ε - 1) ^ 2

theorem transverseLength_def (ε : ℝ) : transverseLength ε = √(1 + 4 * ε ^ 2) :=
  (rfl)

theorem transverseEnergy_def (κ ε : ℝ) :
    transverseEnergy κ ε = κ / 2 * (transverseLength ε - 1) ^ 2 :=
  (rfl)

@[simp]
theorem transverseLength_zero : transverseLength 0 = 1 := by
  simp [transverseLength_def]

theorem sq_transverseLength (ε : ℝ) : transverseLength ε ^ 2 = 1 + 4 * ε ^ 2 :=
  sq_sqrt (by positivity)

theorem one_le_transverseLength (ε : ℝ) : 1 ≤ transverseLength ε :=
  one_le_sqrt.mpr (by nlinarith [sq_nonneg ε])

theorem one_lt_transverseLength {ε : ℝ} (hε : ε ≠ 0) : 1 < transverseLength ε :=
  lt_sqrt zero_le_one |>.mpr (by nlinarith [sq_pos_of_ne_zero hε])

theorem transverseLength_pos (ε : ℝ) : 0 < transverseLength ε :=
  zero_lt_one.trans_le (one_le_transverseLength ε)

theorem inv_transverseLength_lt_one {ε : ℝ} (hε : ε ≠ 0) : (transverseLength ε)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (one_lt_transverseLength hε)

theorem hasDerivAt_transverseLength (ε : ℝ) :
    HasDerivAt transverseLength (4 * ε / transverseLength ε) ε := by
  have h : HasDerivAt (fun x : ℝ ↦ 1 + 4 * x ^ 2) (8 * ε) ε := by
    convert ((hasDerivAt_pow 2 ε).const_mul (4 : ℝ)).const_add 1 using 1
    push_cast
    ring
  rw [show transverseLength = fun x ↦ √(1 + 4 * x ^ 2) from funext transverseLength_def]
  convert h.sqrt (by positivity) using 1
  field_simp [(transverseLength_pos ε).ne']
  ring

/-- The factor `1 - 1/ℓ(ε)` of the exact force has derivative `0` at `ε = 0`. -/
theorem hasDerivAt_one_sub_inv_transverseLength_zero :
    HasDerivAt (fun ε ↦ 1 - (transverseLength ε)⁻¹) 0 0 := by
  simpa using ((hasDerivAt_transverseLength 0).inv (transverseLength_pos 0).ne').const_sub 1

/-- The relative vector of the transverse displacement is `(1, -2ε)`. -/
private theorem transverse_relative (ε : ℝ) :
    !₂[1, 0] + !₂[0, -ε] - !₂[0, ε] = (!₂[1, -2 * ε] : EuclideanSpace ℝ (Fin 2)) := by
  ext i
  fin_cases i <;> simp [two_mul, sub_eq_add_neg]

private theorem norm_transverse_relative (ε : ℝ) :
    ‖(!₂[1, -2 * ε] : EuclideanSpace ℝ (Fin 2))‖ = transverseLength ε := by
  rw [EuclideanSpace.norm_eq, transverseLength_def]
  congr 1
  simp only [norm_eq_abs, sq_abs, Fin.sum_univ_two, cons_val_zero, one_pow, cons_val_one,
    cons_val_fin_one]
  ring

/-- The exact potential of the transverse displacement `u₁ = (0, ε)`, `u₂ = (0, -ε)` is
`TauCeti.TwoParticleSpring.transverseEnergy κ ε`. -/
theorem springPotential_transverse (κ ε : ℝ) :
    springPotential κ 1 (!₂[1, 0] + !₂[0, -ε] - !₂[0, ε] : EuclideanSpace ℝ (Fin 2)) =
      transverseEnergy κ ε := by
  rw [transverse_relative, springPotential_def, norm_transverse_relative, transverseEnergy_def]

/-- The exact force on the first particle at the transverse displacement `u₁ = (0, ε)`,
`u₂ = (0, -ε)` is `κ (1 - 1/ℓ(ε)) (1, -2ε)`. -/
theorem springForce_transverse (κ ε : ℝ) :
    springForce κ 1 (!₂[1, 0] + !₂[0, -ε] - !₂[0, ε] : EuclideanSpace ℝ (Fin 2)) =
      (κ * (1 - (transverseLength ε)⁻¹)) • !₂[1, -2 * ε] := by
  rw [transverse_relative, springForce_def, norm_transverse_relative]
  congr 1
  field_simp [(transverseLength_pos ε).ne']

/-- Away from `ε = 0` the first coordinate of the exact force on the first particle is positive:
the stretched spring pulls it towards the second particle. -/
theorem springForce_transverse_apply_zero_pos {κ ε : ℝ} (hκ : 0 < κ) (hε : ε ≠ 0) :
    0 < springForce κ 1 (!₂[1, 0] + !₂[0, -ε] - !₂[0, ε] : EuclideanSpace ℝ (Fin 2)) 0 := by
  rw [springForce_transverse]
  simp only [PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one]
  exact mul_pos hκ (sub_pos.mpr (inv_transverseLength_lt_one hε))

/-- **To first order the transverse displacement feels no force**: the exact force on the first
particle along `u₁ = (0, ε)`, `u₂ = (0, -ε)` has derivative `0` at `ε = 0`, in accordance with
`H (0, 1, 0, -1) = 0` (`TauCeti.TwoParticleSpring.forceMatrix_mulVec_transverse`). -/
theorem hasDerivAt_springForce_transverse_zero (κ : ℝ) :
    HasDerivAt (fun ε : ℝ ↦
      springForce κ 1 (!₂[1, 0] + !₂[0, -ε] - !₂[0, ε] : EuclideanSpace ℝ (Fin 2))) 0 0 := by
  simp_rw [springForce_transverse]
  have hc : HasDerivAt (fun ε ↦ κ * (1 - (transverseLength ε)⁻¹)) 0 0 := by
    simpa using hasDerivAt_one_sub_inv_transverseLength_zero.const_mul κ
  have hv : HasDerivAt (fun ε : ℝ ↦ (!₂[1, -2 * ε] : EuclideanSpace ℝ (Fin 2))) !₂[0, -2] 0 := by
    have h := ((hasDerivAt_id' (0 : ℝ)).smul_const (!₂[0, -2] : EuclideanSpace ℝ (Fin 2))).const_add
      (!₂[1, 0] : EuclideanSpace ℝ (Fin 2))
    convert h using 1
    · funext ε
      ext i
      fin_cases i <;> simp [mul_comm]
    · simp
  simpa using hc.fun_smul hv

/-! ### The potential vanishes to fourth order -/

/-- The **closed form** `E(ε) = 8 κ ε⁴ / (ℓ(ε) + 1)²`, from `(ℓ - 1)(ℓ + 1) = ℓ² - 1 = 4ε²`. -/
theorem transverseEnergy_eq_div (κ ε : ℝ) :
    transverseEnergy κ ε = 8 * κ * ε ^ 4 / (transverseLength ε + 1) ^ 2 := by
  have h := sq_transverseLength ε
  have hpos : transverseLength ε + 1 ≠ 0 := by linarith [transverseLength_pos ε]
  rw [transverseEnergy_def, eq_div_iff (pow_ne_zero 2 hpos)]
  linear_combination (κ / 2 * (transverseLength ε ^ 2 - 1 + 4 * ε ^ 2)) * h

@[simp]
theorem transverseEnergy_zero (κ : ℝ) : transverseEnergy κ 0 = 0 := by
  simp [transverseEnergy_def]

/-- The transverse displacement costs positive energy away from `ε = 0`. -/
theorem transverseEnergy_pos {κ ε : ℝ} (hκ : 0 < κ) (hε : ε ≠ 0) : 0 < transverseEnergy κ ε := by
  rw [transverseEnergy_eq_div]
  have := transverseLength_pos ε
  positivity

/-- The derivative `E'(ε) = 4 κ ε (1 - 1/ℓ(ε))`. -/
theorem hasDerivAt_transverseEnergy (κ ε : ℝ) :
    HasDerivAt (transverseEnergy κ) (4 * κ * ε * (1 - (transverseLength ε)⁻¹)) ε := by
  rw [show transverseEnergy κ = fun x ↦ κ / 2 * (transverseLength x - 1) ^ 2 from
    funext (transverseEnergy_def κ)]
  convert (((hasDerivAt_transverseLength ε).sub_const 1).fun_pow 2).const_mul (κ / 2) using 1
  field_simp [(transverseLength_pos ε).ne']
  ring

theorem deriv_transverseEnergy (κ : ℝ) :
    deriv (transverseEnergy κ) = fun ε ↦ 4 * κ * ε * (1 - (transverseLength ε)⁻¹) :=
  funext fun ε ↦ (hasDerivAt_transverseEnergy κ ε).deriv

/-- `E'(0) = 0`. -/
theorem deriv_transverseEnergy_zero (κ : ℝ) : deriv (transverseEnergy κ) 0 = 0 := by
  simp [deriv_transverseEnergy]

/-- `E''(0) = 0`: the transverse displacement is a zero mode of the linearization. -/
theorem deriv_deriv_transverseEnergy_zero (κ : ℝ) :
    deriv (deriv (transverseEnergy κ)) 0 = 0 := by
  rw [deriv_transverseEnergy]
  have h := ((hasDerivAt_id' (0 : ℝ)).const_mul (4 * κ)).fun_mul
    hasDerivAt_one_sub_inv_transverseLength_zero
  simpa using h.deriv

/-- Away from `ε = 0`, `E(ε) / ε⁴ = 8κ / (ℓ(ε) + 1)²`. -/
theorem transverseEnergy_div_pow_four (κ : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    transverseEnergy κ ε / ε ^ 4 = 8 * κ / (transverseLength ε + 1) ^ 2 := by
  have hpos : transverseLength ε + 1 ≠ 0 := by linarith [transverseLength_pos ε]
  rw [transverseEnergy_eq_div]
  field_simp

/-- Away from `ε = 0` the quotient `E(ε) / ε⁴ = 8κ / (ℓ(ε) + 1)²` lies below its limit `2κ`,
because `ℓ(ε) > 1`. At `ε = 1/2`, for instance, it is `8κ / (√2 + 1)²`. -/
theorem transverseEnergy_div_pow_four_lt {κ ε : ℝ} (hκ : 0 < κ) (hε : ε ≠ 0) :
    transverseEnergy κ ε / ε ^ 4 < 2 * κ := by
  have hl := one_lt_transverseLength hε
  rw [transverseEnergy_div_pow_four κ hε, div_lt_iff₀ (by positivity)]
  nlinarith [mul_pos hκ (by nlinarith : (0 : ℝ) < (transverseLength ε + 1) ^ 2 - 4)]

/-- **The quartic leading term.** `E(ε) / ε⁴ → 2κ` as `ε → 0` through `ε ≠ 0`: the linearized
force vanishes on the transverse mode while the exact potential is quartic, which is the
limitation of the linear approximation. The puncture is necessary, since the quotient is `0` at
`ε = 0`. -/
theorem transverseEnergy_quartic (κ : ℝ) :
    Tendsto (fun ε : ℝ ↦ transverseEnergy κ ε / ε ^ 4) (𝓝[≠] 0) (𝓝 (2 * κ)) := by
  have hl : Tendsto (fun ε ↦ (transverseLength ε + 1) ^ 2) (𝓝 0) (𝓝 4) := by
    have := ((hasDerivAt_transverseLength 0).continuousAt.tendsto.add_const 1).pow 2
    norm_num at this
    exact this
  have hcont : Tendsto (fun ε ↦ 8 * κ / (transverseLength ε + 1) ^ 2) (𝓝 0) (𝓝 (2 * κ)) := by
    convert tendsto_const_nhds.div hl four_ne_zero using 2
    ring
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (transverseEnergy_div_pow_four κ hε).symm

/-! ### The affine transverse paths are not solutions -/

/-- **The linearization fails on the transverse zero mode.** For `κ ≠ 0` and `a ≠ 0`, the affine
paths `u₁(t) = (0, a t)`, `u₂(t) = (0, -a t)` solve the linearized equation of motion, as `H`
annihilates them (`TauCeti.TwoParticleSpring.forceMatrix_mulVec_transverse`), but at every
`t ≠ 0` and for every mass `m` they violate the exact Newton equation `m u₁'' = F₁` of the first
particle: their acceleration is zero, while the exact force is not. -/
theorem mass_smul_deriv_deriv_ne_springForce_transverse {κ a t : ℝ} (hκ : κ ≠ 0) (ha : a ≠ 0)
    (ht : t ≠ 0) (m : ℝ) :
    m • deriv (deriv fun s : ℝ ↦ (!₂[0, a * s] : EuclideanSpace ℝ (Fin 2))) t ≠
      springForce κ 1 (!₂[1, 0] + !₂[0, -(a * t)] - !₂[0, a * t] : EuclideanSpace ℝ (Fin 2)) := by
  have hpath : (fun s : ℝ ↦ (!₂[0, a * s] : EuclideanSpace ℝ (Fin 2))) =
      fun s ↦ s • !₂[0, a] := by
    funext s
    ext i
    fin_cases i <;> simp [mul_comm]
  have hvel : deriv (fun s : ℝ ↦ (!₂[0, a * s] : EuclideanSpace ℝ (Fin 2))) = fun _ ↦ !₂[0, a] :=
    funext fun s ↦ by rw [hpath]; exact ((hasDerivAt_id' s).smul_const _).deriv.trans (one_smul _ _)
  rw [hvel, deriv_const, smul_zero, springForce_transverse]
  intro h
  have h0 := congr($h 0)
  simp only [PiLp.zero_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h0
  exact mul_ne_zero hκ (sub_ne_zero.mpr
    (inv_transverseLength_lt_one (mul_ne_zero ha ht)).ne') h0.symm

/-! ### The rotated rest configurations -/

/-- The first particle of the rest configuration rotated clockwise by `2ε` about its midpoint
`(½, 0)`: `p₁(ε) = (½ - ½ cos 2ε, ½ sin 2ε)`. -/
noncomputable def rotatedRestFirst (ε : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[1 / 2 - cos (2 * ε) / 2, sin (2 * ε) / 2]

/-- The second particle of the rest configuration rotated clockwise by `2ε` about its midpoint
`(½, 0)`: `p₂(ε) = (½ + ½ cos 2ε, -½ sin 2ε)`. -/
noncomputable def rotatedRestSecond (ε : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[1 / 2 + cos (2 * ε) / 2, -(sin (2 * ε) / 2)]

theorem rotatedRestFirst_def (ε : ℝ) :
    rotatedRestFirst ε = !₂[1 / 2 - cos (2 * ε) / 2, sin (2 * ε) / 2] :=
  (rfl)

theorem rotatedRestSecond_def (ε : ℝ) :
    rotatedRestSecond ε = !₂[1 / 2 + cos (2 * ε) / 2, -(sin (2 * ε) / 2)] :=
  (rfl)

@[simp]
theorem rotatedRestFirst_zero : rotatedRestFirst 0 = !₂[0, 0] := by
  ext i
  fin_cases i <;> norm_num [rotatedRestFirst_def]

@[simp]
theorem rotatedRestSecond_zero : rotatedRestSecond 0 = !₂[1, 0] := by
  ext i
  fin_cases i <;> norm_num [rotatedRestSecond_def]

/-- The rotated particles stay at distance `1`. -/
theorem norm_rotatedRestSecond_sub_rotatedRestFirst (ε : ℝ) :
    ‖rotatedRestSecond ε - rotatedRestFirst ε‖ = 1 := by
  rw [EuclideanSpace.norm_eq, sqrt_eq_one]
  simp only [rotatedRestSecond_def, rotatedRestFirst_def, PiLp.sub_apply, norm_eq_abs, sq_abs,
    Fin.sum_univ_two, cons_val_zero, cons_val_one, cons_val_fin_one]
  nlinarith [sin_sq_add_cos_sq (2 * ε)]

/-- The rotated rest configurations store no energy. Their displacements from the rest
configuration are `uᵢ = pᵢ(ε) - pᵢ(0)`, so their relative vector `(1, 0) + u₂ - u₁` is
`p₂(ε) - p₁(ε)`. -/
theorem springPotential_rotatedRest (κ ε : ℝ) :
    springPotential κ 1 (rotatedRestSecond ε - rotatedRestFirst ε) = 0 := by
  simp [springPotential_def, norm_rotatedRestSecond_sub_rotatedRestFirst]

theorem hasDerivAt_rotatedRestFirst (ε : ℝ) :
    HasDerivAt rotatedRestFirst !₂[sin (2 * ε), cos (2 * ε)] ε := by
  have h2 := (hasDerivAt_id' ε).const_mul (2 : ℝ)
  have h := ((h2.cos.div_const 2).const_sub (1 / 2)).smul_const
      (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) |>.add ((h2.sin.div_const 2).smul_const
      (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)))
  convert h using 1
  · funext x
    ext i
    fin_cases i <;> simp [rotatedRestFirst_def]
  · ext i
    fin_cases i <;> simp [neg_div]

theorem hasDerivAt_rotatedRestSecond (ε : ℝ) :
    HasDerivAt rotatedRestSecond !₂[-sin (2 * ε), -cos (2 * ε)] ε := by
  have h2 := (hasDerivAt_id' ε).const_mul (2 : ℝ)
  have h := ((h2.cos.div_const 2).const_add (1 / 2)).smul_const
      (!₂[1, 0] : EuclideanSpace ℝ (Fin 2)) |>.add ((h2.sin.div_const 2).neg.smul_const
      (!₂[0, 1] : EuclideanSpace ℝ (Fin 2)))
  convert h using 1
  · funext x
    ext i
    fin_cases i <;> simp [rotatedRestSecond_def]
  · ext i
    fin_cases i <;> simp [neg_div]

/-- At `ε = 0` the first rotated particle moves with velocity `(0, 1)`, the velocity of the first
particle along the transverse mode `(0, 1, 0, -1)`. -/
theorem hasDerivAt_rotatedRestFirst_zero : HasDerivAt rotatedRestFirst !₂[0, 1] 0 := by
  simpa using hasDerivAt_rotatedRestFirst 0

/-- At `ε = 0` the second rotated particle moves with velocity `(0, -1)`, the velocity of the
second particle along the transverse mode `(0, 1, 0, -1)`. -/
theorem hasDerivAt_rotatedRestSecond_zero : HasDerivAt rotatedRestSecond !₂[0, -1] 0 := by
  simpa using hasDerivAt_rotatedRestSecond 0

end TauCeti.TwoParticleSpring
