/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Elliptic.Basic
public import Mathlib.Topology.Path
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.SidePairing.Vertex.Stabilizer
import Mathlib.Analysis.Complex.CoveringMap

/-!
# Elliptic meridians and their lifts

For a finite point stabilizer of order `m`, choose its positive generator by requiring its
rotation in the disc coordinate to be `exp (2πi/m)`. A counterclockwise meridian in the local
quotient coordinate `u = w^m` lifts from `w` to this generator applied to `w`, not its inverse.
More generally, `n` signed turns end at the `n`th power of the positive generator.

The explicit lifts stay at constant hyperbolic distance from the fixed point. Consequently they
stay in any invariant disc containing their starting point, and the quotient-chart formula
applies throughout the path. Away from the fixed point these lifts are unique. Reversing the
meridian inverts its endpoint transformation. These conventions specify the elliptic peripheral
elements used alongside cusp meridians in oriented quotient presentations. For a side-paired
fundamental polygon, its finite vertex-cycle transformation is exactly this positive generator;
thus a positive meridian lifts to the cycle transformation, with no inversion.

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

/-- The generator of a finite point stabilizer whose rotation in the disc coordinate is
`exp (2πi/m)`, where `m` is the order of the stabilizer. -/
def positiveStabilizerGenerator : stabilizer Γ z :=
  (stabilizerRotationEquiv Γ z).symm
    (Complex.isPrimitiveRoot_exp (Nat.card (stabilizer Γ z)) (NeZero.ne _)).toRootsOfUnity

/-- The derivative of the positive generator is the counterclockwise primitive root. -/
@[simp]
theorem smulDeriv_positiveStabilizerGenerator :
    ((positiveStabilizerGenerator Γ z : Γ) : PSL(2, ℝ)).smulDeriv z =
      Complex.exp (2 * Real.pi * Complex.I / Nat.card (stabilizer Γ z)) := by
  rw [← stabilizerDeriv_apply Γ z (positiveStabilizerGenerator Γ z),
    ← coe_stabilizerRotation, ← coe_stabilizerRotationEquiv]
  simp [positiveStabilizerGenerator]

/-- The positive generator has exactly the order of the point stabilizer. -/
@[simp]
theorem orderOf_positiveStabilizerGenerator :
    orderOf (positiveStabilizerGenerator Γ z) = Nat.card (stabilizer Γ z) := by
  rw [← orderOf_injective (stabilizerDeriv Γ z) (stabilizerDeriv_injective Γ z),
    stabilizerDeriv_apply, smulDeriv_positiveStabilizerGenerator]
  exact (Complex.isPrimitiveRoot_exp _ (NeZero.ne _)).eq_orderOf.symm

/-- The powers of the positive generator exhaust the full stabilizer. -/
@[simp]
theorem zpowers_positiveStabilizerGenerator : zpowers (positiveStabilizerGenerator Γ z) = ⊤ := by
  rw [← card_eq_iff_eq_top, Nat.card_zpowers, orderOf_positiveStabilizerGenerator]

/-- Signed powers of the positive generator rotate the disc coordinate through `2πn/m`. -/
theorem discCoordinate_positiveStabilizerGenerator_zpow (n : ℤ) (τ : ℍ) :
    discCoordinate z (positiveStabilizerGenerator Γ z ^ n • τ) =
      discCoordinate z τ * Complex.exp
        (((2 * Real.pi * n / Nat.card (stabilizer Γ z) : ℝ) : ℂ) * Complex.I) := by
  have hangle : (n : ℂ) * (2 * Real.pi * Complex.I / Nat.card (stabilizer Γ z)) =
      ((2 * Real.pi * n / Nat.card (stabilizer Γ z) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [discCoordinate_smul_eq_rotation_smul, rootsOfUnity.smul_eq_mul, coe_stabilizerRotation,
    map_zpow, stabilizerDeriv_apply, smulDeriv_positiveStabilizerGenerator,
    ← Complex.exp_int_mul, hangle,
    mul_comm]

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

/-- Away from the fixed point, the explicit elliptic lift is the unique continuous lift of the
local meridian with the specified starting point. -/
theorem eq_ellipticMeridianLift_of_pow_eq (n : ℤ) {τ : ℍ} (hτ : τ ≠ z)
    {f : unitInterval → ℍ} (hf : Continuous f) (h₀ : f 0 = τ)
    (hq : ∀ t, discCoordinate z (f t) ^ Nat.card (stabilizer Γ z) =
      ellipticMeridian Γ z n τ t) : f = ellipticMeridianLift Γ z n τ := by
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

/-- A continuous lift of an elliptic meridian starting away from the fixed point ends at the
corresponding signed power of the positive stabilizer generator. -/
theorem ellipticMeridian_lift_endpoint (n : ℤ) {τ : ℍ} (hτ : τ ≠ z)
    {f : unitInterval → ℍ} (hf : Continuous f) (h₀ : f 0 = τ)
    (hq : ∀ t, discCoordinate z (f t) ^ Nat.card (stabilizer Γ z) =
      ellipticMeridian Γ z n τ t) : f 1 = positiveStabilizerGenerator Γ z ^ n • τ := by
  rw [eq_ellipticMeridianLift_of_pow_eq Γ z n hτ hf h₀ hq]
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
  rw [Path.symm_apply, Function.comp_apply, discCoordinate_positiveStabilizerGenerator_zpow,
    discCoordinate_ellipticMeridianLift, discCoordinate_ellipticMeridianLift, hangle,
    Complex.exp_add]
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

namespace TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing

open _root_.Subgroup
open scoped Pointwise

variable {N : ℕ} [NeZero N] {P : ConvexPolygon N} (σ : P.SidePairing)
  {Γ : Subgroup PSL(2, ℝ)} {j : Fin N} {z : ℍ} [Finite (stabilizer Γ z)]

/-- The finite vertex-cycle transformation of a fundamental polygon is the positive stabilizer
generator, not its inverse. Only disjointness of translated interiors is needed. -/
theorem cycleMap_eq_positiveStabilizerGenerator (hz : P.vertex j = .inl z)
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier)) :
    σ.cycleMap j = ((Γ.positiveStabilizerGenerator z : Γ) : PSL(2, ℝ)) := by
  have hfix : σ.cycleMap j • z = z := by
    simpa only [hz, Sum.smul_inl, Sum.inl.injEq] using σ.cycleMap_smul_vertex j
  -- View the same cycle transformation as an element of the vertex stabilizer so that the
  -- faithful derivative character compares it with the positive generator.
  let q : stabilizer Γ z := ⟨⟨σ.cycleMap j, σ.cycleMap_mem hmap j⟩, hfix⟩
  have hangle : ((σ.cycleAngleSum j : ℝ) : ℂ) * Complex.I =
      2 * Real.pi * Complex.I / Nat.card (stabilizer Γ z) := by
    rw [σ.cycleAngleSum_eq_two_pi_div hz hmap hdisj,
      ← σ.natCard_stabilizer_eq_orderOf_cycleMap hz hmap hdisj]
    push_cast
    ring
  have hq : q = Γ.positiveStabilizerGenerator z := by
    apply stabilizerDeriv_injective Γ z
    rw [stabilizerDeriv_apply, stabilizerDeriv_apply,
      σ.smulDeriv_cycleMap hz, smulDeriv_positiveStabilizerGenerator, hangle]
  exact congrArg (fun g : stabilizer Γ z ↦ ((g : Γ) : PSL(2, ℝ))) hq

/-- A positive meridian in the finite vertex quotient lifts to the polygon's cycle
transformation. Signed multiple turns give the corresponding signed power of that cycle. -/
theorem ellipticMeridian_lift_endpoint_eq_cycleMap_zpow_smul (hz : P.vertex j = .inl z)
    (hmap : ∀ i, σ.map i ∈ Γ)
    (hdisj : ∀ γ : Γ, γ ≠ 1 →
      Disjoint ((γ : PSL(2, ℝ)) • interior P.carrier) (interior P.carrier))
    (n : ℤ) {τ : ℍ} (hτ : τ ≠ z) {f : unitInterval → ℍ}
    (hf : Continuous f) (h₀ : f 0 = τ)
    (hq : ∀ t, discCoordinate z (f t) ^ Nat.card (stabilizer Γ z) =
      Γ.ellipticMeridian z n τ t) : f 1 = σ.cycleMap j ^ n • τ := by
  rw [σ.cycleMap_eq_positiveStabilizerGenerator hz hmap hdisj]
  -- Powers and actions in the stabilizer are restrictions of the ambient projective ones.
  exact Γ.ellipticMeridian_lift_endpoint z n hτ hf h₀ hq

end TauCeti.UpperHalfPlane.ConvexPolygon.SidePairing
