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

The integer-indexed `twistedExtension D k f` treats poles and zeros uniformly. Positive `k`
cancels growth by multiplying by `q^k`, while negative `k` cancels decay by dividing by a power
of `q`. This also makes the relevant coefficient available to later q-expansion and local-order
arguments.

## Main declarations

* `TauCeti.Subgroup.CuspDatum.twistedExtension`: the q-extension after an integer coordinate
  twist.
* `TauCeti.Subgroup.CuspDatum.analyticAt_twistedExtension_zero`: the matching exponential bound
  makes that extension analytic at the cusp.
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

/-- Multiplication by an integer power of the cusp coordinate before descent. -/
def cuspTwist (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  fun z ↦ coordinate D z ^ k * f z

/-- The cusp twist is pointwise multiplication by the corresponding integer power of the
q-coordinate. -/
@[simp]
theorem cuspTwist_apply (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    cuspTwist D k f z = coordinate D z ^ k * f z :=
  (rfl)

/-- Twisting preserves invariance under the full cusp stabilizer. -/
theorem cuspTwist_smul (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (g : stabilizer Γ D.cusp) (z : ℍ) :
    cuspTwist D k f (g • z) = cuspTwist D k f z := by
  have hcoordinate : coordinate D (g • z) = coordinate D z := by
    simpa only [Subgroup.smul_def] using coordinate_smul D g.property z
  rw [cuspTwist_apply, cuspTwist_apply, hcoordinate, hf]

/-- Twisting a holomorphic function by an integer power of the nonvanishing cusp coordinate
preserves holomorphy. -/
theorem mdifferentiable_cuspTwist (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cuspTwist D k f) := by
  intro z
  cases k with
  | ofNat n =>
      exact ((mdifferentiable_coordinate D z).pow n).mul (hf z)
  | negSucc n =>
      exact (((mdifferentiable_coordinate D z).pow (n + 1)).inv
        (pow_ne_zero _ (coordinate_ne_zero D z))).mul (hf z)

/-- In the normalized scaling coordinate, twisting is multiplication by the usual width-`w`
q-parameter. -/
theorem cuspTwist_inv_smul (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) (z : ℍ) :
    cuspTwist D k f (D.scaling⁻¹ • z) =
      Function.Periodic.qParam D.width z ^ k * f (D.scaling⁻¹ • z) := by
  rw [cuspTwist_apply, coordinate_inv_smul]

/-- Multiplying by the cusp coordinate to the power `k` cancels the corresponding exponential
growth in the scaling coordinate. In particular, the twisted function is bounded at the cusp. -/
theorem isBoundedAtImInfty_cuspTwist_inv_smul (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    IsBoundedAtImInfty fun z : ℍ ↦ cuspTwist D k f (D.scaling⁻¹ • z) := by
  have hscaled : (fun z : ℍ ↦ cuspTwist D k f (D.scaling⁻¹ • z)) =
      fun z : ℍ ↦ Function.Periodic.qParam D.width z ^ k * f (D.scaling⁻¹ • z) := by
    funext z
    exact cuspTwist_inv_smul D k f z
  rw [hscaled]
  exact TauCeti.UpperHalfPlane.isBoundedAtImInfty_qParam_zpow_mul_of_isBigO
    D.width k hbound

/-- The q-extension after twisting by an integer power of the cusp coordinate. Under the
corresponding hypothesis of `analyticAt_twistedExtension_zero`, it is analytic at zero. -/
def twistedExtension (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) : ℂ → ℂ :=
  cuspExtension D (cuspTwist D k f)

/-- The twisted extension is the cusp extension of the coordinate-twisted function. -/
theorem twistedExtension_def (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ) :
    twistedExtension D k f = cuspExtension D (cuspTwist D k f) := (rfl)

/-- Pulling the twisted extension back along the cusp coordinate recovers `q^k f`. -/
@[simp]
theorem twistedExtension_coordinate (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) (z : ℍ) :
    twistedExtension D k f (coordinate D z) = coordinate D z ^ k * f z := by
  exact cuspExtension_coordinate D (cuspTwist D k f) (cuspTwist_smul D k f hf) z

/-- The exponential bound corresponding to the integer twist `k` makes the twisted q-extension
analytic at zero. -/
theorem analyticAt_twistedExtension_zero (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    AnalyticAt ℂ (twistedExtension D k f) 0 := by
  apply analyticAt_cuspExtension_zero D (cuspTwist D k f)
  · exact cuspTwist_smul D k f hf
  · exact mdifferentiable_cuspTwist D k f hhol
  · exact isBoundedAtImInfty_cuspTwist_inv_smul D k f hbound

/-- The value at zero of the twisted extension is the value at infinity of the twisted
function in the normalized scaling coordinate. -/
theorem twistedExtension_zero_eq_valueAtInfty (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    twistedExtension D k f 0 = valueAtInfty (fun z : ℍ ↦
      Function.Periodic.qParam D.width z ^ k * f (D.scaling⁻¹ • z)) := by
  have hbounded : IsBoundedAtImInfty
      (fun z : ℍ ↦ cuspTwist D k f (D.scaling⁻¹ • z)) :=
    isBoundedAtImInfty_cuspTwist_inv_smul D k f hbound
  rw [twistedExtension, cuspExtension_zero_eq_valueAtInfty D (cuspTwist D k f)
    (cuspTwist_smul D k f hf) (mdifferentiable_cuspTwist D k f hhol) hbounded]
  congr 1
  funext z
  exact cuspTwist_inv_smul D k f z

/-- On the punctured unit disc, the original cusp extension is `q⁻ᵏ` times its twisted
extension. -/
theorem cuspExtension_eq_zpow_mul_twistedExtension_of_ne_zero_of_norm_lt_one
    (D : Γ.CuspDatum) (k : ℤ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    {q : ℂ} (hq : q ≠ 0) (hq_norm : ‖q‖ < 1) :
    cuspExtension D f q = q ^ (-k) * twistedExtension D k f q := by
  obtain ⟨z, hz⟩ := (isOpenQuotientMap_qCoordinate D).surjective
    (⟨Complex.UnitDisc.mk q hq_norm, fun h ↦ hq (congrArg ((↑) : 𝔻 → ℂ) h)⟩ :
      {q : 𝔻 // q ≠ 0})
  have hzq : coordinate D z = q := by
    rw [← coe_qCoordinate, hz]
    exact Complex.UnitDisc.coe_mk q hq_norm
  rw [← hzq, cuspExtension_coordinate D f hf,
    twistedExtension_coordinate D k f hf]
  rw [← mul_assoc, ← zpow_add₀ (coordinate_ne_zero D z)]
  simp

/-- Near the puncture, the original cusp extension is `q⁻ᵏ` times its twisted extension. -/
theorem cuspExtension_eventuallyEq_zpow_mul_twistedExtension (D : Γ.CuspDatum) (k : ℤ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) :
    cuspExtension D f =ᶠ[𝓝[≠] 0]
      fun q ↦ q ^ (-k) * twistedExtension D k f q := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one), self_mem_nhdsWithin]
    with q hq hq_ne
  exact cuspExtension_eq_zpow_mul_twistedExtension_of_ne_zero_of_norm_lt_one D k f hf hq_ne
    (by simpa only [Metric.mem_ball, dist_zero_right] using hq)

/-- A cusp-invariant holomorphic function satisfying the exponential bound for an integer twist
has a meromorphic q-extension at the cusp. -/
theorem meromorphicAt_cuspExtension_zero (D : Γ.CuspDatum) (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    MeromorphicAt (cuspExtension D f) 0 := by
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  exact ⟨-k, twistedExtension D k f,
    analyticAt_twistedExtension_zero D k f hf hhol hbound,
    (cuspExtension_eventuallyEq_zpow_mul_twistedExtension D k f hf).mono
      fun q hq ↦ by simpa only [sub_zero, smul_eq_mul] using hq⟩

/-- The meromorphic order of a cusp extension is at least `-k` under the exponential bound
corresponding to the integer coordinate twist `k`. -/
theorem neg_le_meromorphicOrderAt_cuspExtension (D : Γ.CuspDatum) (k : ℤ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * (k : ℝ) * z.im / D.width)) :
    ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0 := by
  have han := analyticAt_twistedExtension_zero D k f hf hhol hbound
  have hrepr := cuspExtension_eventuallyEq_zpow_mul_twistedExtension D k f hf
  have hfun : (fun q : ℂ ↦ q ^ (-k) * twistedExtension D k f q) =
      id ^ (-k) * twistedExtension D k f := rfl
  rw [meromorphicOrderAt_congr hrepr, hfun,
    meromorphicOrderAt_mul ((MeromorphicAt.id 0).zpow (-k)) han.meromorphicAt,
    meromorphicOrderAt_zpow (MeromorphicAt.id 0), meromorphicOrderAt_id]
  simpa using le_add_of_nonneg_right han.meromorphicOrderAt_nonneg

/-- Exponential growth of rate at most `2πn / w` forces the meromorphic order of the cusp
extension to be at least `-n`; equivalently, its pole order is at most `n`. -/
theorem neg_natCast_le_meromorphicOrderAt_cuspExtension (D : Γ.CuspDatum) (n : ℕ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hgrowth : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * n * z.im / D.width)) :
    (-(n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0 := by
  apply neg_le_meromorphicOrderAt_cuspExtension D (n : ℤ) f hf hhol
  simpa only [Int.cast_natCast] using hgrowth

/-! ## Controlled zeros -/

/-- A cusp-invariant holomorphic function with exponential decay of order `n` has a holomorphic
q-extension at the cusp. -/
theorem analyticAt_cuspExtension_zero_of_isBigO_exp_neg (D : Γ.CuspDatum) (n : ℕ) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hdecay : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * n * z.im / D.width)) :
    AnalyticAt ℂ (cuspExtension D f) 0 := by
  have hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * ((-(n : ℤ) : ℤ) : ℝ) * z.im / D.width) :=
    hdecay.congr_right fun z ↦ by
      congr 1
      push_cast
      ring
  have han := analyticAt_twistedExtension_zero D (-(n : ℤ)) f hf hhol hbound
  cases n with
  | zero =>
      have htwist : cuspTwist D (0 : ℤ) f = f := by
        funext z
        simp only [cuspTwist_apply, zpow_zero, one_mul]
      have han0 : AnalyticAt ℂ (cuspExtension D (cuspTwist D (0 : ℤ) f)) 0 := by
        simpa only [Nat.cast_zero, neg_zero, twistedExtension] using han
      rwa [htwist] at han0
  | succ n =>
      have hc : 0 < 2 * Real.pi * (n + 1) / D.width := by
        exact div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (by positivity)) D.width_pos
      have hzero : IsZeroAtImInfty fun z : ℍ ↦ f (D.scaling⁻¹ • z) := by
        apply TauCeti.UpperHalfPlane.isZeroAtImInfty_of_isBigO_exp_neg hc
        exact hdecay.congr_right fun z ↦ by
          congr 1
          push_cast
          ring
      have hvalue : cuspExtension D f 0 = 0 := cuspExtension_zero_eq_zero D f hzero
      apply ((analyticAt_id.pow (n + 1)).mul han).congr
      filter_upwards [eventually_nhdsWithin_iff.mp
          (cuspExtension_eventuallyEq_zpow_mul_twistedExtension
            D (-((n + 1 : ℕ) : ℤ)) f hf).symm]
        with q hq
      by_cases hq0 : q = 0
      · subst q
        simp only [Pi.mul_apply, Pi.pow_apply, id_eq, zero_pow (Nat.succ_ne_zero n), zero_mul,
          hvalue]
      · simpa only [Pi.mul_apply, Pi.pow_apply, id_eq, neg_neg, zpow_natCast] using hq hq0

/-- Exponential decay of rate at least `2πn / w` forces the meromorphic order of the cusp
extension to be at least `n`; equivalently, the extension has a zero of order at least `n`. -/
theorem natCast_le_meromorphicOrderAt_cuspExtension (D : Γ.CuspDatum) (n : ℕ)
    (f : ℍ → ℂ) (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hdecay : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * n * z.im / D.width)) :
    ((n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspExtension D f) 0 := by
  have hbound : (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (2 * Real.pi * ((-(n : ℤ) : ℤ) : ℝ) * z.im / D.width) :=
    hdecay.congr_right fun z ↦ by
      congr 1
      push_cast
      ring
  simpa only [neg_neg] using
    neg_le_meromorphicOrderAt_cuspExtension D (-(n : ℤ)) f hf hhol hbound

end TauCeti.Subgroup.CuspDatum
