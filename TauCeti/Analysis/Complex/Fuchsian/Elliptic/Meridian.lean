/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Basic
public import Mathlib.Topology.Path
import Mathlib.Analysis.Complex.CoveringMap

/-!
# Elliptic meridians and their lifts

For a finite point stabilizer of order `m`, choose its positive generator by requiring its
rotation in the disc coordinate to be `exp (2πi/m)`. A counterclockwise meridian in the local
quotient coordinate `u = w^m` lifts from `w` to this generator applied to `w`, not its inverse.
More generally, `n` signed turns end at the `n`th power of the positive generator.

The explicit lifts stay at constant hyperbolic distance from the fixed point. Consequently they
stay in any invariant disc containing their starting point, and the quotient-chart formula
applies throughout the path. These lifts are unique, including at the fixed point where they
are constant. Reversing the meridian inverts its endpoint transformation. These conventions
specify the elliptic peripheral elements used alongside cusp meridians in oriented quotient
presentations. The comparison with finite vertex-cycle transformations of side-paired polygons
is in `TauCeti.Analysis.Complex.Fuchsian.Elliptic.Polygon`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Chapter 8.
* Svetlana Katok, *Fuchsian Groups*, §§2.4 and 4.3.
* Otto Forster, *Lectures on Riemann Surfaces*, §4 (the local power-map model).
-/

public noncomputable section

open Function MulAction Set Topology UpperHalfPlane
open scoped Complex.UnitDisc MatrixGroups Topology

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) (z : ℍ) [Finite (stabilizer Γ z)]

/-- The lift of `n` signed turns about an elliptic orbit. Its disc coordinate rotates through
`2πn/m`, where `m` is the stabilizer order. -/
def ellipticMeridianLift (n : ℤ) (τ : ℍ) :
    Path τ (positiveStabilizerGenerator Γ z ^ n • τ) where
  toFun t := (discCoordinateHomeomorph z).symm (.mk
    (discCoordinate z τ * Complex.exp
      (((2 * Real.pi * n * (t : ℝ) / Nat.card (stabilizer Γ z) : ℝ) : ℂ) * Complex.I))
    (by simpa only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      using norm_discCoordinate_lt_one z τ))
  continuous_toFun := (discCoordinateHomeomorph z).symm.continuous.comp
    (Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr (by
      simp only [Function.comp_def, Complex.UnitDisc.coe_mk]
      fun_prop))
  source' := by
    apply discCoordinate_injective z
    simp
  target' := by
    apply discCoordinate_injective z
    simp only [discCoordinate_discCoordinateHomeomorph_symm, Complex.UnitDisc.coe_mk,
      Set.Icc.coe_one, mul_one, discCoordinate_positiveStabilizerGenerator_zpow]

/-- The lift in the disc coordinate is a constant-speed circular arc. -/
@[simp]
theorem discCoordinate_ellipticMeridianLift (n : ℤ) (τ : ℍ) (t : unitInterval) :
    discCoordinate z (ellipticMeridianLift Γ z n τ t) = discCoordinate z τ *
      Complex.exp (((2 * Real.pi * n * (t : ℝ) / Nat.card (stabilizer Γ z) : ℝ) : ℂ) *
        Complex.I) := by
  unfold ellipticMeridianLift
  exact discCoordinate_discCoordinateHomeomorph_symm z _

/-- An elliptic meridian lift stays at constant distance from the fixed point. -/
@[simp]
theorem dist_ellipticMeridianLift (n : ℤ) (τ : ℍ) (t : unitInterval) :
    dist (ellipticMeridianLift Γ z n τ t) z = dist τ z := by
  have hnorm : ‖discCoordinate z (ellipticMeridianLift Γ z n τ t)‖ =
      ‖discCoordinate z τ‖ := by
    rw [discCoordinate_ellipticMeridianLift, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [norm_discCoordinate, norm_discCoordinate] at hnorm
  exact (div_left_inj' (by norm_num : (2 : ℝ) ≠ 0)).mp (Real.tanh_injective hnorm)

/-- The local power-map projection of an elliptic lift is the circular loop with `n` signed
turns. Positive turns are counterclockwise in the quotient coordinate. -/
theorem discCoordinate_ellipticMeridianLift_pow (n : ℤ) (τ : ℍ) (t : unitInterval) :
    discCoordinate z (ellipticMeridianLift Γ z n τ t) ^ Nat.card (stabilizer Γ z) =
      discCoordinate z τ ^ Nat.card (stabilizer Γ z) *
        Complex.exp (((2 * Real.pi * n * (t : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have hm : (Nat.card (stabilizer Γ z) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  have hangle : (Nat.card (stabilizer Γ z) : ℂ) *
      (((2 * Real.pi * n * (t : ℝ) / Nat.card (stabilizer Γ z) : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.pi * n * (t : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [hm]
  rw [discCoordinate_ellipticMeridianLift, mul_pow, ← Complex.exp_nat_mul, hangle]

/-- The meridian in the local quotient coordinate, defined as the power-map projection of its
explicit lift. At the fixed point itself this degenerates to the constant zero path. -/
def ellipticMeridian (n : ℤ) (τ : ℍ) :
    Path (discCoordinate z τ ^ Nat.card (stabilizer Γ z))
      (discCoordinate z τ ^ Nat.card (stabilizer Γ z)) :=
  ((ellipticMeridianLift Γ z n τ).map
    ((continuous_discCoordinate z).pow _)).cast rfl
      ((mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow Γ z).mp
        (mem_orbit τ (positiveStabilizerGenerator Γ z ^ n))).symm

/-- Evaluation of the local elliptic meridian as the projection of the lift. -/
theorem ellipticMeridian_apply (n : ℤ) (τ : ℍ) (t : unitInterval) :
    ellipticMeridian Γ z n τ t =
      discCoordinate z (ellipticMeridianLift Γ z n τ t) ^ Nat.card (stabilizer Γ z) := (rfl)

/-- Away from the fixed point, the elliptic meridian is the circular loop with `n` signed turns
around zero. The formula also holds at the fixed point, where both sides vanish. -/
@[simp]
theorem ellipticMeridian_eq_exp (n : ℤ) (τ : ℍ) (t : unitInterval) :
    ellipticMeridian Γ z n τ t = discCoordinate z τ ^ Nat.card (stabilizer Γ z) *
      Complex.exp (((2 * Real.pi * n * (t : ℝ) : ℝ) : ℂ) * Complex.I) :=
  discCoordinate_ellipticMeridianLift_pow Γ z n τ t

/-- On any precisely invariant disc containing the basepoint, the local quotient chart reads the
projected lift as the elliptic meridian for its entire duration. -/
theorem stabilizerBallQuotientChart_ellipticMeridianLift {ε : ℝ} (hε : 0 < ε)
    (hopen : IsOpenEmbedding (stabilizerBall Γ z ε).orbitRelQuotientMap)
    (n : ℤ) {τ : ℍ} (hτ : dist τ z < ε) (t : unitInterval) :
    stabilizerBallQuotientChart hε hopen (Quotient.mk _ (ellipticMeridianLift Γ z n τ t)) =
      ellipticMeridian Γ z n τ t := by
  rw [stabilizerBallQuotientChart_mk hε hopen (by simpa using hτ)]
  exact (ellipticMeridian_apply Γ z n τ t).symm

/-- The explicit elliptic lift is the unique continuous lift of the local meridian with the
specified starting point, including the constant lift at the fixed point. -/
theorem eq_ellipticMeridianLift_of_pow_eq (n : ℤ) {τ : ℍ}
    {f : unitInterval → ℍ} (hf : Continuous f) (h₀ : f 0 = τ)
    (hq : ∀ t, discCoordinate z (f t) ^ Nat.card (stabilizer Γ z) =
      ellipticMeridian Γ z n τ t) : f = ellipticMeridianLift Γ z n τ := by
  by_cases hτ : τ = z
  · funext t
    apply discCoordinate_injective z
    have hzero : discCoordinate z (f t) ^ Nat.card (stabilizer Γ z) = 0 := by
      simpa only [ellipticMeridian_eq_exp, hτ, discCoordinate_self, zero_pow (NeZero.ne _),
        zero_mul] using hq t
    simpa only [discCoordinate_ellipticMeridianLift, hτ, discCoordinate_self, zero_mul]
      using eq_zero_of_pow_eq_zero hzero
  have hτ0 : discCoordinate z τ ≠ 0 := discCoordinate_eq_zero_iff.not.mpr hτ
  have hmer (t : unitInterval) : ellipticMeridian Γ z n τ t ≠ 0 := by
    rw [ellipticMeridian_eq_exp]
    exact mul_ne_zero (pow_ne_zero _ hτ0) (Complex.exp_ne_zero _)
  have hf0 (t : unitInterval) : discCoordinate z (f t) ≠ 0 := by
    intro h
    exact hmer t (by rw [← hq t, h, zero_pow (NeZero.ne _)])
  have hlift0 (t : unitInterval) :
      discCoordinate z (ellipticMeridianLift Γ z n τ t) ≠ 0 := by
    rw [discCoordinate_ellipticMeridianLift]
    exact mul_ne_zero hτ0 (Complex.exp_ne_zero _)
  let F (t : unitInterval) : {w : ℂ // w ≠ 0} := ⟨discCoordinate z (f t), hf0 t⟩
  let L (t : unitInterval) : {w : ℂ // w ≠ 0} :=
    ⟨discCoordinate z (ellipticMeridianLift Γ z n τ t), hlift0 t⟩
  have he : (fun w : {w : ℂ // w ≠ 0} ↦
      (⟨w ^ Nat.card (stabilizer Γ z), pow_ne_zero _ w.2⟩ : {w : ℂ // w ≠ 0})) ∘ F =
      (fun w : {w : ℂ // w ≠ 0} ↦
        (⟨w ^ Nat.card (stabilizer Γ z), pow_ne_zero _ w.2⟩ : {w : ℂ // w ≠ 0})) ∘ L := by
    funext t
    apply Subtype.ext
    exact (hq t).trans (ellipticMeridian_apply Γ z n τ t)
  have hFL := (isCoveringMap_npow (𝕜 := ℂ) (Nat.card (stabilizer Γ z))
    (Nat.cast_ne_zero.mpr (NeZero.ne _))).eq_of_comp_eq
      (((continuous_discCoordinate z).comp hf).subtype_mk hf0)
      (((continuous_discCoordinate z).comp (ellipticMeridianLift Γ z n τ).continuous).subtype_mk
        hlift0) he 0 (Subtype.ext (by simp [h₀]))
  funext t
  exact discCoordinate_injective z (congrArg Subtype.val (congrFun hFL t))

/-- A continuous lift of an elliptic meridian ends at the corresponding signed power of the
positive stabilizer generator, including when the lift is constant at the fixed point. -/
theorem ellipticMeridian_lift_endpoint (n : ℤ) {τ : ℍ}
    {f : unitInterval → ℍ} (hf : Continuous f) (h₀ : f 0 = τ)
    (hq : ∀ t, discCoordinate z (f t) ^ Nat.card (stabilizer Γ z) =
      ellipticMeridian Γ z n τ t) : f 1 = positiveStabilizerGenerator Γ z ^ n • τ := by
  rw [eq_ellipticMeridianLift_of_pow_eq Γ z n hf h₀ hq]
  exact (ellipticMeridianLift Γ z n τ).target

/-- Negating the turns reverses the lifted path and translates it back by the inverse endpoint
transformation. -/
theorem ellipticMeridianLift_neg_apply (n : ℤ) (τ : ℍ) (t : unitInterval) :
    ellipticMeridianLift Γ z (-n) τ t =
      positiveStabilizerGenerator Γ z ^ (-n) • (ellipticMeridianLift Γ z n τ).symm t := by
  have hangle : (((2 * Real.pi * ((-n : ℤ) : ℝ) * (t : ℝ) /
      Nat.card (stabilizer Γ z) : ℝ) : ℂ) *
      Complex.I) =
      (((2 * Real.pi * n * (unitInterval.symm t : ℝ) /
        Nat.card (stabilizer Γ z) : ℝ) : ℂ) * Complex.I) +
      (((2 * Real.pi * ((-n : ℤ) : ℝ) / Nat.card (stabilizer Γ z) : ℝ) : ℂ) *
        Complex.I) := by
    rw [unitInterval.coe_symm_eq]
    push_cast
    ring
  apply discCoordinate_injective z
  simp only [Path.symm_apply, Function.comp_apply,
    discCoordinate_positiveStabilizerGenerator_zpow, discCoordinate_ellipticMeridianLift]
  rw [hangle, Complex.exp_add]
  exact (mul_assoc _ _ _).symm

/-- Reversing the meridian negates its turns, hence inverts its endpoint generator. -/
@[simp]
theorem ellipticMeridian_neg (n : ℤ) (τ : ℍ) :
    ellipticMeridian Γ z (-n) τ = (ellipticMeridian Γ z n τ).symm := by
  apply Path.ext
  funext t
  rw [ellipticMeridian_apply, ellipticMeridianLift_neg_apply]
  simp only [Path.symm_apply, Function.comp_apply]
  rw [ellipticMeridian_apply]
  exact (mem_orbit_stabilizer_iff_discCoordinate_pow_eq_pow Γ z).mp
    (mem_orbit _ (positiveStabilizerGenerator Γ z ^ (-n)))

/-- The zero-turn elliptic meridian is constant. -/
@[simp]
theorem ellipticMeridian_zero (τ : ℍ) :
    ellipticMeridian Γ z 0 τ = Path.refl (discCoordinate z τ ^ Nat.card (stabilizer Γ z)) := by
  apply Path.ext
  funext t
  simp

end Subgroup
