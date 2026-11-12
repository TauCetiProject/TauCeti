/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.SmoothTorus.ContinuousCocycle
public import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Algebra.Group.ZPow

/-!
# The gauge action on the smooth noncommutative torus

The two-torus acts by star-algebra automorphisms, multiplying the Fourier coefficient at
`(m,n)` by `z₁ ^ m * z₂ ^ n`. This action preserves every defining weighted ℓ¹ seminorm
and is jointly continuous. It commutes with the lattice derivations and preserves the
canonical trace and the continuous odd and fundamental cyclic cocycles.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §2 and Chapter IV, §6.
-/

public section

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace TauCeti.SmoothNoncommutativeTorus

variable {θ : ℝ}

private def gaugePhase (z : Circle × Circle) (x : ℤ × ℤ) : Circle :=
  z.1 ^ x.1 * z.2 ^ x.2

private theorem gaugePhase_add (z : Circle × Circle) (x y : ℤ × ℤ) :
    gaugePhase z (x + y) = gaugePhase z x * gaugePhase z y := by
  simp [gaugePhase, zpow_add, mul_mul_mul_comm]

private theorem gaugePhase_mul (z w : Circle × Circle) (x : ℤ × ℤ) :
    gaugePhase (z * w) x = gaugePhase z x * gaugePhase w x := by
  simp [gaugePhase, mul_zpow, mul_mul_mul_comm]

private theorem gaugePhase_neg (z : Circle × Circle) (x : ℤ × ℤ) :
    gaugePhase z (-x) = (gaugePhase z x)⁻¹ := by
  simp [gaugePhase, mul_comm]

private def gaugeMap (z : Circle × Circle) (a : SmoothNoncommutativeTorus θ) :
    SmoothNoncommutativeTorus θ :=
  ⟨fun x ↦ gaugePhase z x * a.coeff x,
    IsRapidDecay.mul_left_of_norm_le (C := 1) (n := 0)
      (fun x ↦ by simp) a.isRapidDecay_coeff⟩

private theorem coeff_gaugeMap (z : Circle × Circle) (a : SmoothNoncommutativeTorus θ)
    (x : ℤ × ℤ) : (gaugeMap z a).coeff x = gaugePhase z x * a.coeff x := (rfl)

private theorem gaugeMap_one (a : SmoothNoncommutativeTorus θ) : gaugeMap 1 a = a := by
  ext x
  simp [coeff_gaugeMap, gaugePhase]

private theorem gaugeMap_mul (z w : Circle × Circle) (a : SmoothNoncommutativeTorus θ) :
    gaugeMap (z * w) a = gaugeMap z (gaugeMap w a) := by
  ext x
  simp [coeff_gaugeMap, gaugePhase_mul, Circle.coe_mul, mul_assoc]

/-- The gauge automorphism multiplying the `(m,n)` Fourier coefficient by `z₁ ^ m * z₂ ^ n`.
It sends the two generators to `z₁ U₁` and `z₂ U₂`. -/
def gauge (z : Circle × Circle) :
    SmoothNoncommutativeTorus θ ≃⋆ₐ[ℂ] SmoothNoncommutativeTorus θ where
  toFun := gaugeMap z
  invFun := gaugeMap z⁻¹
  left_inv a := by rw [← gaugeMap_mul, inv_mul_cancel, gaugeMap_one]
  right_inv a := by rw [← gaugeMap_mul, mul_inv_cancel, gaugeMap_one]
  map_add' a b := by ext x; simp [coeff_gaugeMap, mul_add]
  map_mul' a b := by
    ext x
    simp only [coeff_gaugeMap, coeff_mul, ← tsum_mul_left]
    apply tsum_congr
    intro y
    have h : gaugePhase z x = gaugePhase z y * gaugePhase z (x - y) := by
      rw [← gaugePhase_add, add_sub_cancel]
    rw [h, Circle.coe_mul]
    ring
  map_smul' c a := by ext x; simp [coeff_gaugeMap, mul_left_comm]
  map_star' a := by
    ext x
    simp only [coeff_gaugeMap, coeff_star, map_mul, gaugePhase_neg,
      ← Circle.coe_inv_eq_conj, inv_inv]
    ring

/-- The characteristic coefficient equation for the gauge action. -/
@[simp]
theorem coeff_gauge (z : Circle × Circle) (a : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    (gauge z a).coeff x = ((z.1 ^ x.1 * z.2 ^ x.2 : Circle) : ℂ) * a.coeff x := (rfl)

/-- Multiplication in the two-torus is composition of gauge automorphisms. -/
theorem gauge_mul (z w : Circle × Circle) (a : SmoothNoncommutativeTorus θ) :
    gauge (z * w) a = gauge z (gauge w a) := gaugeMap_mul z w a

@[simp]
theorem gauge_one (a : SmoothNoncommutativeTorus θ) : gauge 1 a = a := gaugeMap_one a

/-- Inverting the two-torus parameter gives the inverse gauge automorphism. -/
theorem gauge_symm (z : Circle × Circle) : (gauge (θ := θ) z).symm = gauge z⁻¹ := by
  ext a x
  rfl

/-- The genuine action of the two-torus on the smooth algebra, with its coefficient formula
available through `gauge`. -/
instance : MulSemiringAction (Circle × Circle) (SmoothNoncommutativeTorus θ) where
  smul z a := gauge z a
  one_smul := gauge_one
  mul_smul := gauge_mul
  smul_zero z := map_zero (gauge z)
  smul_add z := map_add (gauge z)
  smul_one z := map_one (gauge z)
  smul_mul z := map_mul (gauge z)

/-- The action notation agrees with the bundled gauge automorphism. -/
theorem smul_eq_gauge (z : Circle × Circle) (a : SmoothNoncommutativeTorus θ) :
    z • a = gauge z a := (rfl)

/-- Gauge transformations are complex linear. -/
instance : SMulCommClass (Circle × Circle) ℂ (SmoothNoncommutativeTorus θ) where
  smul_comm z c a := map_smul (gauge z) c a

@[simp]
theorem gauge_single (z : Circle × Circle) (x : ℤ × ℤ) (c : ℂ) :
    gauge z (single x c : SmoothNoncommutativeTorus θ) =
      single x (((z.1 ^ x.1 * z.2 ^ x.2 : Circle) : ℂ) * c) := by
  ext y
  by_cases h : y = x
  · subst y; simp
  · simp [h]

/-- The first generator has the first coordinate as gauge weight. -/
theorem gauge_U₁ (z : Circle × Circle) :
    gauge z (U₁ θ : SmoothNoncommutativeTorus θ) = (z.1 : ℂ) • (U₁ θ : _) := by
  simp

/-- The second generator has the second coordinate as gauge weight. -/
theorem gauge_U₂ (z : Circle × Circle) :
    gauge z (U₂ θ : SmoothNoncommutativeTorus θ) = (z.2 : ℂ) • (U₂ θ : _) := by
  simp

/-- Every defining seminorm is invariant under the gauge action. -/
@[simp]
theorem seminorm_gauge (z : Circle × Circle) (k : ℕ) (a : SmoothNoncommutativeTorus θ) :
    seminorm θ k (gauge z a) = seminorm θ k a := by
  simp [seminorm_apply]

private theorem continuous_gaugePhase (x : ℤ × ℤ) :
    Continuous (fun z : Circle × Circle ↦ gaugePhase z x) :=
  (continuous_fst.zpow x.1).mul (continuous_snd.zpow x.2)

private theorem continuous_seminorm_gauge_sub (k : ℕ) (a : SmoothNoncommutativeTorus θ)
    (w : Circle × Circle) :
    Continuous (fun z : Circle × Circle ↦ seminorm θ k (gauge z a - gauge w a)) := by
  simp only [seminorm_apply, coeff_sub, Pi.sub_apply, coeff_gauge]
  apply continuous_tsum
  · intro x
    exact (((continuous_gaugePhase x).subtype_val.mul_const (a.coeff x)).sub
      continuous_const).norm.mul_const _
  · exact (a.isRapidDecay_coeff.summable_norm_mul_weight_pow k).mul_left 2
  · intro x z
    rw [Real.norm_of_nonneg (norm_mul_weight_pow_nonneg _ _ _)]
    calc ‖((z.1 ^ x.1 * z.2 ^ x.2 : Circle) : ℂ) * a.coeff x -
          ((w.1 ^ x.1 * w.2 ^ x.2 : Circle) : ℂ) * a.coeff x‖ * weight x ^ k
        ≤ (‖((z.1 ^ x.1 * z.2 ^ x.2 : Circle) : ℂ) * a.coeff x‖ +
          ‖((w.1 ^ x.1 * w.2 ^ x.2 : Circle) : ℂ) * a.coeff x‖) * weight x ^ k :=
            mul_le_mul_of_nonneg_right (norm_sub_le _ _) (pow_nonneg (weight_pos x).le _)
      _ = 2 * (‖a.coeff x‖ * weight x ^ k) := by simp; ring

/-- The gauge action is jointly continuous in the two-torus parameter and the smooth algebra. -/
@[fun_prop]
theorem continuous_gauge :
    Continuous (fun p : (Circle × Circle) × SmoothNoncommutativeTorus θ ↦ gauge p.1 p.2) := by
  apply continuous_iff_continuousAt.2
  rintro ⟨w, a⟩
  rw [ContinuousAt, (withSeminorms θ).tendsto_nhds]
  intro k ε hε
  have h₁ : Tendsto (fun p : (Circle × Circle) × SmoothNoncommutativeTorus θ ↦
      seminorm θ k (p.2 - a)) (𝓝 (w, a)) (𝓝 0) := by
    simpa [Function.comp_def] using
      (((withSeminorms θ).continuous_seminorm k).comp
        (continuous_snd.sub (continuous_const : Continuous
          (fun _ : (Circle × Circle) × SmoothNoncommutativeTorus θ ↦ a)))).tendsto (w, a)
  have h₂ : Tendsto (fun p : (Circle × Circle) × SmoothNoncommutativeTorus θ ↦
      seminorm θ k (gauge p.1 a - gauge w a)) (𝓝 (w, a)) (𝓝 0) := by
    simpa [Function.comp_def] using
      ((continuous_seminorm_gauge_sub k a w).comp continuous_fst).tendsto (w, a)
  filter_upwards [h₁.eventually (gt_mem_nhds (half_pos hε)),
    h₂.eventually (gt_mem_nhds (half_pos hε))] with p hp₁ hp₂
  have heq : gauge p.1 p.2 - gauge w a =
      gauge p.1 (p.2 - a) + (gauge p.1 a - gauge w a) := by
    rw [map_sub]; abel
  rw [seminormFamily_apply, heq]
  calc seminorm θ k (gauge p.1 (p.2 - a) + (gauge p.1 a - gauge w a))
      ≤ seminorm θ k (gauge p.1 (p.2 - a)) + seminorm θ k (gauge p.1 a - gauge w a) :=
        map_add_le_add _ _ _
    _ < ε := by rw [seminorm_gauge]; linarith

/-- The gauge action with its canonical action notation is continuous. -/
instance : ContinuousSMul (Circle × Circle) (SmoothNoncommutativeTorus θ) :=
  ⟨continuous_gauge⟩

/-- Gauge automorphisms commute with every lattice derivation. -/
@[simp]
theorem gaugeDerivation_gauge (ℓ : ℤ × ℤ →+ ℂ) (z : Circle × Circle)
    (a : SmoothNoncommutativeTorus θ) :
    (gaugeDerivation θ ℓ : Module.End ℂ _) (gauge z a) =
      gauge z ((gaugeDerivation θ ℓ : Module.End ℂ _) a) := by
  ext x
  simp [mul_left_comm]

/-- The first coordinate derivation commutes with the gauge action. -/
@[simp]
theorem derivation₁_gauge (z : Circle × Circle) (a : SmoothNoncommutativeTorus θ) :
    (derivation₁ θ : Module.End ℂ _) (gauge z a) =
      gauge z ((derivation₁ θ : Module.End ℂ _) a) := by
  rw [derivation₁_def]
  exact gaugeDerivation_gauge _ _ _

/-- The second coordinate derivation commutes with the gauge action. -/
@[simp]
theorem derivation₂_gauge (z : Circle × Circle) (a : SmoothNoncommutativeTorus θ) :
    (derivation₂ θ : Module.End ℂ _) (gauge z a) =
      gauge z ((derivation₂ θ : Module.End ℂ _) a) := by
  rw [derivation₂_def]
  exact gaugeDerivation_gauge _ _ _

/-- The canonical trace is gauge invariant. -/
theorem trace_gauge (z : Circle × Circle) (a : SmoothNoncommutativeTorus θ) :
    trace θ (gauge z a) = trace θ a := by
  simp [trace_apply]

/-- The first continuous odd cocycle is invariant under simultaneous gauge transport. -/
@[simp↓]
theorem continuousOddCocycle₁_gauge (z : Circle × Circle)
    (a : Fin 2 → SmoothNoncommutativeTorus θ) :
    (continuousOddCocycle₁ θ).1.1 (fun i ↦ gauge z (a i)) =
      (continuousOddCocycle₁ θ).1.1 a := by
  simp only [continuousOddCocycle₁_apply, derivation₁_gauge, ← map_mul, trace_gauge]

/-- The second continuous odd cocycle is invariant under simultaneous gauge transport. -/
@[simp↓]
theorem continuousOddCocycle₂_gauge (z : Circle × Circle)
    (a : Fin 2 → SmoothNoncommutativeTorus θ) :
    (continuousOddCocycle₂ θ).1.1 (fun i ↦ gauge z (a i)) =
      (continuousOddCocycle₂ θ).1.1 a := by
  simp only [continuousOddCocycle₂_apply, derivation₂_gauge, ← map_mul, trace_gauge]

/-- The continuous fundamental cocycle, including its orientation, is gauge invariant. -/
@[simp↓]
theorem continuousFundamentalCocycle_gauge (z : Circle × Circle)
    (a : Fin 3 → SmoothNoncommutativeTorus θ) :
    (continuousFundamentalCocycle θ).1.1 (fun i ↦ gauge z (a i)) =
      (continuousFundamentalCocycle θ).1.1 a := by
  simp only [continuousFundamentalCocycle_apply, fundamentalCocycle_apply,
    derivation₁_gauge, derivation₂_gauge, ← map_mul, ← map_sub, trace_gauge]

end TauCeti.SmoothNoncommutativeTorus
