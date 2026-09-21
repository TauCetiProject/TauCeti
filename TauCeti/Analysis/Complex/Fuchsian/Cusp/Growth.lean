/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Extension
public import TauCeti.Analysis.Complex.UpperHalfPlane.Growth
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

The dual decay statement is also proved: decay like `q^n` makes the quotient by `q^n` bounded,
so the cusp extension is analytic and has a zero of order at least `n`. The analytic factor after
division by `q^n` is `zeroRemovedExtension D n f`.

## Main declarations

* `TauCeti.Subgroup.CuspDatum.poleRemovedExtension`: the analytic numerator obtained after
  multiplying by `q^n`.
* `TauCeti.Subgroup.CuspDatum.analyticAt_poleRemovedExtension_zero`: controlled exponential
  growth makes that numerator analytic at the cusp.
* `TauCeti.Subgroup.CuspDatum.meromorphicAt_cuspExtension_zero`: the original q-extension is
  meromorphic at zero.
* `TauCeti.Subgroup.CuspDatum.neg_natCast_le_meromorphicOrderAt_cuspExtension`: its order is at
  least `-n`, equivalently its pole order is at most `n`.
* `TauCeti.Subgroup.CuspDatum.natCast_le_meromorphicOrderAt_cuspExtension`: exponential decay of
  order `n` forces the cusp extension to have order at least `n`.

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

/-- The value at zero of the pole-removed extension is the value at infinity of the twisted
function in the normalized scaling coordinate. -/
theorem poleRemovedExtension_zero_eq_valueAtInfty (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hgrowth : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * n * z.im / D.width)) :
    poleRemovedExtension D n f 0 = valueAtInfty (fun z : ℍ ↦
      Function.Periodic.qParam D.width z ^ n * f (D.scaling⁻¹ • z)) := by
  have hbounded : IsBoundedAtImInfty
      (fun z : ℍ ↦ cuspTwist D n f (D.scaling⁻¹ • z)) := by
    simpa only [cuspTwist_inv_smul] using
      TauCeti.UpperHalfPlane.isBoundedAtImInfty_qParam_pow_mul_of_isBigO
        D.width n hgrowth
  rw [poleRemovedExtension, cuspExtension_zero_eq_valueAtInfty D (cuspTwist D n f)
    (cuspTwist_smul D n f hf) (mdifferentiable_cuspTwist D n f hhol) hbounded]
  congr 1
  funext z
  exact cuspTwist_inv_smul D n f z

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
  obtain ⟨z, hz⟩ := (isOpenQuotientMap_qCoordinate D).surjective
    (⟨Complex.UnitDisc.mk q hq_norm, fun h ↦ hq_ne (congrArg ((↑) : 𝔻 → ℂ) h)⟩ :
      {q : 𝔻 // q ≠ 0})
  have hzq : coordinate D z = q := by
    rw [← coe_qCoordinate, hz]
    exact Complex.UnitDisc.coe_mk q hq_norm
  rw [← hzq, cuspExtension_coordinate D f hf,
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
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  exact ⟨-(n : ℤ), poleRemovedExtension D n f,
    analyticAt_poleRemovedExtension_zero D n f hf hhol hgrowth,
    (cuspExtension_eventuallyEq_zpow_mul_poleRemovedExtension D n f hf).mono
      fun q hq ↦ by simpa only [sub_zero, smul_eq_mul] using hq⟩

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

/-! ## Controlled zeros -/

/-- Division by the `n`th power of the cusp coordinate before descent. -/
def cuspUntwist (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z ↦ (coordinate D z)⁻¹ ^ n * f z

/-- The cusp untwist is pointwise division by the corresponding power of the q-coordinate. -/
@[simp]
theorem cuspUntwist_apply (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    cuspUntwist D n f z = (coordinate D z)⁻¹ ^ n * f z :=
  (rfl)

/-- Untwisting preserves invariance under the full cusp stabilizer. -/
theorem cuspUntwist_smul (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (g : stabilizer Γ D.cusp) (z : ℍ) :
    cuspUntwist D n f (g • z) = cuspUntwist D n f z := by
  have hcoordinate : coordinate D (g • z) = coordinate D z := by
    simpa only [Subgroup.smul_def] using coordinate_smul D g.property z
  rw [cuspUntwist_apply, cuspUntwist_apply, hcoordinate, hf]

/-- Untwisting a holomorphic function by a nonnegative power of the inverse cusp coordinate
preserves holomorphy on the upper half-plane. -/
theorem mdifferentiable_cuspUntwist (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cuspUntwist D n f) := by
  have huntwist : cuspUntwist D n f = fun z ↦ (coordinate D z)⁻¹ ^ n * f z :=
    funext (cuspUntwist_apply D n f)
  rw [huntwist]
  intro z
  exact (((mdifferentiable_coordinate D z).inv (coordinate_ne_zero D z)).pow n).mul (hf z)

/-- In the normalized scaling coordinate, untwisting is division by the usual width-`w`
q-parameter. -/
theorem cuspUntwist_inv_smul (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    cuspUntwist D n f (D.scaling⁻¹ • z) =
      (Function.Periodic.qParam D.width z)⁻¹ ^ n * f (D.scaling⁻¹ • z) := by
  have hcoordinate : coordinate D (D.scaling⁻¹ • z) =
      Function.Periodic.qParam D.width z := by
    rw [coordinate_apply, smul_inv_smul]
  rw [cuspUntwist_apply, hcoordinate]

/-- The q-extension after dividing out a prescribed zero of order `n`. Under the decay
hypothesis of `analyticAt_zeroRemovedExtension_zero`, this function is analytic at zero. -/
def zeroRemovedExtension (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ) : ℂ → ℂ :=
  cuspExtension D (cuspUntwist D n f)

/-- Pulling the zero-removed extension back along the cusp coordinate recovers `q⁻ⁿ f`. -/
@[simp]
theorem zeroRemovedExtension_coordinate (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) (z : ℍ) :
    zeroRemovedExtension D n f (coordinate D z) = (coordinate D z)⁻¹ ^ n * f z := by
  exact cuspExtension_coordinate D (cuspUntwist D n f) (cuspUntwist_smul D n f hf) z

/-- Exponential decay of rate at least `2πn / w` makes the zero-removed q-extension analytic at
zero. -/
theorem analyticAt_zeroRemovedExtension_zero (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hdecay : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * n * z.im / D.width)) :
    AnalyticAt ℂ (zeroRemovedExtension D n f) 0 := by
  apply analyticAt_cuspExtension_zero D (cuspUntwist D n f)
  · exact cuspUntwist_smul D n f hf
  · exact mdifferentiable_cuspUntwist D n f hhol
  · have hscaled : (fun z : ℍ ↦ cuspUntwist D n f (D.scaling⁻¹ • z)) =
        fun z : ℍ ↦ (Function.Periodic.qParam D.width z)⁻¹ ^ n *
          f (D.scaling⁻¹ • z) := by
      funext z
      exact cuspUntwist_inv_smul D n f z
    rw [hscaled]
    exact TauCeti.UpperHalfPlane.isBoundedAtImInfty_qParam_inv_pow_mul_of_isBigO
      D.width n hdecay

/-- The value at zero of the zero-removed extension is the value at infinity after division by
the corresponding power of the normalized q-parameter. -/
theorem zeroRemovedExtension_zero_eq_valueAtInfty (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hdecay : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * n * z.im / D.width)) :
    zeroRemovedExtension D n f 0 = valueAtInfty (fun z : ℍ ↦
      (Function.Periodic.qParam D.width z)⁻¹ ^ n * f (D.scaling⁻¹ • z)) := by
  have hbounded : IsBoundedAtImInfty
      (fun z : ℍ ↦ cuspUntwist D n f (D.scaling⁻¹ • z)) := by
    simpa only [cuspUntwist_inv_smul] using
      TauCeti.UpperHalfPlane.isBoundedAtImInfty_qParam_inv_pow_mul_of_isBigO
        D.width n hdecay
  rw [zeroRemovedExtension, cuspExtension_zero_eq_valueAtInfty D (cuspUntwist D n f)
    (cuspUntwist_smul D n f hf) (mdifferentiable_cuspUntwist D n f hhol) hbounded]
  congr 1
  funext z
  exact cuspUntwist_inv_smul D n f z

/-- Near the puncture, the original cusp extension is `qⁿ` times its analytic zero-removed
extension. -/
theorem cuspExtension_eventuallyEq_pow_mul_zeroRemovedExtension (D : Γ.CuspDatum) (n : ℕ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) :
    cuspExtension D f =ᶠ[𝓝[≠] 0]
      fun q ↦ q ^ n * zeroRemovedExtension D n f q := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one), self_mem_nhdsWithin]
    with q hq hq_ne
  have hq_norm : ‖q‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hq
  obtain ⟨z, hz⟩ := (isOpenQuotientMap_qCoordinate D).surjective
    (⟨Complex.UnitDisc.mk q hq_norm, fun h ↦ hq_ne (congrArg ((↑) : 𝔻 → ℂ) h)⟩ :
      {q : 𝔻 // q ≠ 0})
  have hzq : coordinate D z = q := by
    rw [← coe_qCoordinate, hz]
    exact Complex.UnitDisc.coe_mk q hq_norm
  rw [← hzq, cuspExtension_coordinate D f hf,
    zeroRemovedExtension_coordinate D n f hf]
  rw [← mul_assoc, ← mul_pow]
  simp only [mul_inv_cancel₀ (coordinate_ne_zero D z), one_pow, one_mul]

/-- A cusp-invariant holomorphic function with exponential decay of order `n` has a holomorphic
q-extension at the cusp. -/
theorem analyticAt_cuspExtension_zero_of_isBigO_exp_neg (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hdecay : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * n * z.im / D.width)) :
    AnalyticAt ℂ (cuspExtension D f) 0 := by
  have han := analyticAt_zeroRemovedExtension_zero D n f hf hhol hdecay
  cases n with
  | zero =>
      have huntwist : cuspUntwist D 0 f = f := by
        funext z
        simp only [cuspUntwist_apply, pow_zero, one_mul]
      rw [zeroRemovedExtension, huntwist] at han
      exact han
  | succ n =>
      have hc : 0 < 2 * Real.pi * (n + 1) / D.width := by
        exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (by positivity)) D.width_pos
      have hzero : IsZeroAtImInfty fun z : ℍ ↦ f (D.scaling⁻¹ • z) := by
        apply UpperHalfPlane.isZeroAtImInfty_of_isBigO_exp_neg hc
        exact hdecay.congr_right fun z ↦ by
          congr 1
          push_cast
          ring
      have hvalue : cuspExtension D f 0 = 0 := cuspExtension_zero_eq_zero D f hzero
      apply ((analyticAt_id.pow (n + 1)).mul han).congr
      filter_upwards [eventually_nhdsWithin_iff.mp
          (cuspExtension_eventuallyEq_pow_mul_zeroRemovedExtension D (n + 1) f hf).symm]
        with q hq
      by_cases hq0 : q = 0
      · subst q
        simp only [Pi.mul_apply, Pi.pow_apply, id_eq, zero_pow (Nat.succ_ne_zero n), zero_mul,
          hvalue]
      · exact hq hq0

/-- Exponential decay of rate at least `2πn / w` forces the meromorphic order of the cusp
extension to be at least `n`; equivalently, the extension has a zero of order at least `n`. -/
theorem natCast_le_meromorphicOrderAt_cuspExtension (D : Γ.CuspDatum) (n : ℕ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hdecay : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * n * z.im / D.width)) :
    ((n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0 := by
  have han := analyticAt_zeroRemovedExtension_zero D n f hf hhol hdecay
  have hrepr := cuspExtension_eventuallyEq_pow_mul_zeroRemovedExtension D n f hf
  have hfun : (fun q : ℂ ↦ q ^ n * zeroRemovedExtension D n f q) =
      id ^ n * zeroRemovedExtension D n f := rfl
  rw [meromorphicOrderAt_congr hrepr, hfun,
    meromorphicOrderAt_mul ((MeromorphicAt.id 0).pow n) han.meromorphicAt,
    meromorphicOrderAt_pow (MeromorphicAt.id 0), meromorphicOrderAt_id]
  simpa using le_add_of_nonneg_right han.meromorphicOrderAt_nonneg

end TauCeti.Subgroup.CuspDatum
