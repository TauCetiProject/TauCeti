/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Extension
public import Mathlib.Analysis.Meromorphic.Order

/-!
# Meromorphic extension of functions of controlled growth at a cusp

Let `D` be normalized cusp data of width `w`. If an invariant holomorphic function grows no
faster than `exp (2 * π * n * y / w)` in the scaling coordinate, multiplication by `q^n`
makes it bounded. The removable-singularity theorem then gives an analytic numerator in the
q-coordinate, so the original function extends meromorphically with pole order at most `n`.

The analytic numerator is kept as `poleRemovedExtension D n f`. Besides recording the pole-order
bound, this makes the leading coefficient available to later q-expansion and local-order
arguments.

## Main declarations

* `TauCeti.Subgroup.CuspDatum.poleRemovedExtension`: the analytic numerator obtained after
  multiplying by `q^n`.
* `TauCeti.Subgroup.CuspDatum.analyticAt_poleRemovedExtension_zero`: controlled exponential
  growth makes that numerator analytic at the cusp.
* `TauCeti.Subgroup.CuspDatum.meromorphicAt_cuspExtension_zero`: the original q-extension is
  meromorphic at zero.
* `TauCeti.Subgroup.CuspDatum.neg_natCast_le_meromorphicOrderAt_cuspExtension`: its order is at
  least `-n`, equivalently its pole order is at most `n`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Asymptotics Filter Function Matrix.ProjectiveSpecialLinearGroup MulAction UpperHalfPlane
open scoped Complex.UnitDisc ContDiff Manifold MatrixGroups Topology

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)}

/-- Multiplication by the `n`th power of the cusp coordinate before descent. -/
def cuspTwist (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z ↦ coordinate D z ^ n * f z

/-- The cusp twist is pointwise multiplication by the corresponding power of the q-coordinate. -/
@[simp]
theorem cuspTwist_apply (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    cuspTwist D n f z = coordinate D z ^ n * f z :=
  (rfl)

/-- Twisting preserves invariance under the full cusp stabilizer. -/
theorem cuspTwist_smul (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (g : stabilizer Γ D.cusp) (z : ℍ) :
    cuspTwist D n f (g • z) = cuspTwist D n f z := by
  have hcoordinate : coordinate D (g • z) = coordinate D z := by
    simpa only [Subgroup.smul_def] using coordinate_smul D g.property z
  rw [cuspTwist_apply, cuspTwist_apply, hcoordinate, hf]

/-- Twisting a holomorphic function by a nonnegative power of the cusp coordinate preserves
holomorphy. -/
theorem mdifferentiable_cuspTwist (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cuspTwist D n f) := by
  have htwist : cuspTwist D n f = fun z ↦ coordinate D z ^ n * f z :=
    funext (cuspTwist_apply D n f)
  rw [htwist]
  intro z
  exact ((mdifferentiable_coordinate D z).pow n).mul (hf z)

/-- In the normalized scaling coordinate, twisting is multiplication by the usual width-`w`
q-parameter. -/
theorem cuspTwist_inv_smul (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    cuspTwist D n f (D.scaling⁻¹ • z) =
      Function.Periodic.qParam D.width z ^ n * f (D.scaling⁻¹ • z) := by
  have hcoordinate : coordinate D (D.scaling⁻¹ • z) =
      Function.Periodic.qParam D.width z := by
    rw [coordinate_apply, smul_inv_smul]
  rw [cuspTwist_apply, hcoordinate]

/-- The q-extension after cancelling a possible pole of order at most `n`. Under the growth
hypothesis of `analyticAt_poleRemovedExtension_zero`, this function is analytic at zero. -/
def poleRemovedExtension (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ) : ℂ → ℂ :=
  cuspExtension D (cuspTwist D n f)

/-- Pulling the pole-removed extension back along the cusp coordinate recovers `q^n f`. -/
@[simp]
theorem poleRemovedExtension_coordinate (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) (z : ℍ) :
    poleRemovedExtension D n f (coordinate D z) = coordinate D z ^ n * f z := by
  exact cuspExtension_coordinate D (cuspTwist D n f) (cuspTwist_smul D n f hf) z

/-- Exponential growth of rate at most `2πn / w` makes the pole-removed q-extension analytic at
zero. -/
theorem analyticAt_poleRemovedExtension_zero (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hgrowth : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * n * z.im / D.width)) :
    AnalyticAt ℂ (poleRemovedExtension D n f) 0 := by
  apply analyticAt_cuspExtension_zero D (cuspTwist D n f)
  · exact cuspTwist_smul D n f hf
  · exact mdifferentiable_cuspTwist D n f hhol
  · have hscaled : (fun z : ℍ ↦ cuspTwist D n f (D.scaling⁻¹ • z)) =
        fun z : ℍ ↦ Function.Periodic.qParam D.width z ^ n * f (D.scaling⁻¹ • z) := by
      funext z
      exact cuspTwist_inv_smul D n f z
    rw [hscaled]
    exact TauCeti.UpperHalfPlane.isBoundedAtImInfty_qParam_pow_mul_of_isBigO
      D.width n hgrowth

/-- Near the puncture, the original cusp extension is `q⁻ⁿ` times its analytic
pole-removed extension. -/
theorem cuspExtension_eventuallyEq_zpow_mul_poleRemovedExtension (D : Γ.CuspDatum) (n : ℕ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) :
    cuspExtension D f =ᶠ[𝓝[≠] 0]
      fun q ↦ q ^ (-(n : ℤ)) * poleRemovedExtension D n f q := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one), self_mem_nhdsWithin]
    with q hq hq_ne
  have hq_norm : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  let q' : {q : 𝔻 // q ≠ 0} :=
    ⟨Complex.UnitDisc.mk q hq_norm, fun h ↦ hq_ne (congrArg ((↑) : 𝔻 → ℂ) h)⟩
  let z := D.scaling⁻¹ • TauCeti.UpperHalfPlane.invQParamUpperHalfPlane
    D.width D.width_pos q'
  have hz : coordinate D z = q := by
    have h := congrArg (fun p : {q : 𝔻 // q ≠ 0} ↦ ((p : 𝔻) : ℂ))
      (qCoordinate_smul_invQParamUpperHalfPlane D q')
    have hq'_coe : ((q' : 𝔻) : ℂ) = q := rfl
    have hzq' : coordinate D z = ((q' : 𝔻) : ℂ) := by
      simpa only [z, coe_qCoordinate] using h
    exact hzq'.trans hq'_coe
  rw [← hz, cuspExtension_coordinate D f hf,
    poleRemovedExtension_coordinate D n f hf]
  rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ (coordinate_ne_zero D z)]
  simp

/-- A cusp-invariant holomorphic function with controlled exponential growth has a meromorphic
q-extension at the cusp. -/
theorem meromorphicAt_cuspExtension_zero (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hgrowth : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * n * z.im / D.width)) :
    MeromorphicAt (cuspExtension D f) 0 := by
  have han := analyticAt_poleRemovedExtension_zero D n f hf hhol hgrowth
  have hbase : MeromorphicAt
      (fun q : ℂ ↦ q ^ (-(n : ℤ)) * poleRemovedExtension D n f q) 0 := by
    fun_prop
  exact hbase.congr
    (cuspExtension_eventuallyEq_zpow_mul_poleRemovedExtension D n f hf).symm

/-- The meromorphic order of a cusp extension is at least `-n` when the function has exponential
growth of rate at most `2πn / w`; equivalently, its pole order is at most `n`. -/
theorem neg_natCast_le_meromorphicOrderAt_cuspExtension (D : Γ.CuspDatum) (n : ℕ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hgrowth : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * n * z.im / D.width)) :
    (-(n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0 := by
  have han := analyticAt_poleRemovedExtension_zero D n f hf hhol hgrowth
  have hrepr := cuspExtension_eventuallyEq_zpow_mul_poleRemovedExtension D n f hf
  have hfun : (fun q : ℂ ↦ q ^ (-(n : ℤ)) * poleRemovedExtension D n f q) =
      id ^ (-(n : ℤ)) * poleRemovedExtension D n f := rfl
  rw [meromorphicOrderAt_congr hrepr, hfun,
    meromorphicOrderAt_mul ((MeromorphicAt.id 0).zpow (-(n : ℤ))) han.meromorphicAt,
    meromorphicOrderAt_zpow (MeromorphicAt.id 0), meromorphicOrderAt_id]
  simpa using le_add_of_nonneg_right han.meromorphicOrderAt_nonneg

end TauCeti.Subgroup.CuspDatum
