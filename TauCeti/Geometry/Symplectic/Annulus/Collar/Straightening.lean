/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.UnitInterval
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Straightening a map of the strip near a boundary line

Let `h` be a `C¹` map of the plane commuting with the deck translation `(x, y) ↦ (x + 1, y)`,
injective on the strip `S = ℝ × [0, 1]`, which fixes the boundary line `y = 0` pointwise and is
tangent to the identity along it: `h (x, 0) = (x, 0)` and `Dh (x, 0) = id` for every `x`. Such a
map arises as the lift of a diffeomorphism of the closed annulus `(ℝ / ℤ) × [0, 1]` which fixes a
boundary circle together with its first-order jet there. This file deforms `h`, through the maps

`H_t (p) = p + (1 - t χ(y / ε)) (h p - p)`, `p = (x, y)`, `t ∈ [0, 1]`

(`TauCeti.stripCollarStraightening h χ ε t`), into a map that is the identity on a collar of the
line. Here `χ` is a `C¹` cut-off profile with compact support and values in `[0, 1]`, and `ε > 0`
is a width. The map `H_t` is the convex combination `(1 - λ) h + λ id` with the weight
`λ = t χ(y / ε)`, which depends on the height only. So `H_0 = h`, `H_t = h` wherever
`χ(y / ε) = 0`, and `H_1 = id` wherever `χ(y / ε) = 1`, for instance on the collar `ℝ × [0, ε]`
when `χ = 1` on `[0, 1]`. Every `H_t` fixes the line `y = 0` pointwise, commutes with the deck
translations, depends smoothly on `(t, p)` when `h` and `χ` are smooth, and maps the strip into
itself when `h` does.

The main result (`TauCeti.exists_pos_forall_injOn_stripCollarStraightening`) is that for every
small width `ε` all the maps `H_t`, `t ∈ [0, 1]`, are injective on the strip, with invertible
differential wherever `h` has one. So when `h` is a local diffeomorphism, the deformation runs
through injective local diffeomorphisms of the strip, and when moreover `χ = 1` near `0` it ends at
a map equal to the identity near the line `y = 0`.

The point is that a thin collar is harmless here because `h` is tangent to the identity along the
line. The derivative of `H_t - id = (1 - t χ(y / ε)) (h - id)` is

`(1 - t χ(y / ε)) D(h - id) - (t / ε) χ'(y / ε) (h - id) ⊗ dy`.

On a band `|y| < η` the first term is at most `sup ‖Dh - id‖`, which tends to zero with `η`, by
compactness modulo the deck translations, since `Dh = id` on the line. The second term is the
dangerous one, since `χ'(y / ε) / ε` is of order `1 / ε`. But `h - id` vanishes on the line, so the
mean value theorem along vertical segments bounds `‖h p - p‖` by `|y| sup ‖Dh - id‖`, and the
second term is at most `|u χ'(u)| sup ‖Dh - id‖` with `u = y / ε`, bounded independently of `ε`.
Hence `H_t - id` has small derivative on a band about the line, so `H_t` is injective there, and it
moves the points of the support of `χ(y / ε)` only by `O(ε)` in height. Away from the band
`H_t = h`, and `h` keeps the points of the strip at height at least `η` a positive distance from
the line, by injectivity and compactness modulo the deck translations. These two facts separate
the values of `H_t` on the two regions.

Without tangency to the identity the convex combination may fold: if `Dh (x, 0)` scales the
normal direction by `b < 1`, the normal derivative of the second coordinate of `H_t` is, up to
`O(ε)`, `b + t (1 - b) (u χ(u))'`, which at `t = 1` is negative where `(u χ(u))'` is below
`-b / (1 - b)`. The first order jet of `h` along the line has to be removed before this
deformation applies.

## Main definitions

* `TauCeti.stripCollarStraightening h χ ε t`: the map `p ↦ p + (1 - t χ(y / ε)) (h p - p)`.

## Main results

* `TauCeti.contDiff_stripCollarStraightening`: the family is jointly `C^n` in the time and the
  point.
* `TauCeti.mapsTo_stripCollarStraightening`: it maps the strip into itself when `h` does.
* `TauCeti.exists_pos_forall_injOn_stripCollarStraightening`: for every small width the maps
  `H_t`, `t ∈ [0, 1]`, are injective on the strip, with invertible differential wherever `h` has
  one.

## References

* S. Smale, *Diffeomorphisms of the 2-sphere*, Proc. Amer. Math. Soc. 10 (1959), 621–626
  (diffeomorphisms of the square that are the identity near the boundary).
* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

noncomputable section

open Set Filter Function
open scoped Topology

namespace TauCeti

/-- The **collar straightening** `H_t (p) = p + (1 - t χ(y / ε)) (h p - p)` of a map `h` of the
plane near the line `y = 0`, with cut-off profile `χ`, width `ε` and time `t`. It is the convex
combination `(1 - λ) h + λ id` with the weight `λ = t χ(y / ε)`: it is `h` at `t = 0` and wherever
`χ(y / ε) = 0`, and the identity at `t = 1` wherever `χ(y / ε) = 1`. -/
def stripCollarStraightening (h : ℝ × ℝ → ℝ × ℝ) (χ : ℝ → ℝ) (ε t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  p + (1 - t * χ (p.2 / ε)) • (h p - p)

variable {h : ℝ × ℝ → ℝ × ℝ} {χ : ℝ → ℝ} {ε t : ℝ}

/-- The defining formula of the collar straightening. -/
theorem stripCollarStraightening_apply (h : ℝ × ℝ → ℝ × ℝ) (χ : ℝ → ℝ) (ε t : ℝ)
    (p : ℝ × ℝ) :
    stripCollarStraightening h χ ε t p = p + (1 - t * χ (p.2 / ε)) • (h p - p) :=
  (rfl)

/-- At time `0` the collar straightening is the map itself. -/
@[simp]
theorem stripCollarStraightening_zero (h : ℝ × ℝ → ℝ × ℝ) (χ : ℝ → ℝ) (ε : ℝ) :
    stripCollarStraightening h χ ε 0 = h := by
  ext1 p
  simp [stripCollarStraightening_apply]

/-- Where the profile vanishes, the collar straightening is the map itself. -/
theorem stripCollarStraightening_of_eq_zero {p : ℝ × ℝ} (hp : χ (p.2 / ε) = 0) :
    stripCollarStraightening h χ ε t p = h p := by
  simp [stripCollarStraightening_apply, hp]

/-- At time `1`, where the profile is `1`, the collar straightening is the identity. -/
theorem stripCollarStraightening_one_of_eq_one {p : ℝ × ℝ} (hp : χ (p.2 / ε) = 1) :
    stripCollarStraightening h χ ε 1 p = p := by
  simp [stripCollarStraightening_apply, hp]

/-- The collar straightening fixes every point of the line `y = 0` that the map fixes. -/
theorem stripCollarStraightening_mk_zero {x : ℝ} (hx : h (x, 0) = (x, 0)) :
    stripCollarStraightening h χ ε t (x, 0) = (x, 0) := by
  simp [stripCollarStraightening_apply, hx]

/-- The collar straightening of a map commuting with the deck translations commutes with them. -/
theorem stripCollarStraightening_add_int
    (hper : ∀ (p : ℝ × ℝ) (k : ℤ), h (p + ((k : ℝ), 0)) = h p + ((k : ℝ), 0)) (p : ℝ × ℝ)
    (k : ℤ) :
    stripCollarStraightening h χ ε t (p + ((k : ℝ), 0)) =
      stripCollarStraightening h χ ε t p + ((k : ℝ), 0) := by
  simp only [stripCollarStraightening_apply, hper, Prod.snd_add, add_zero,
    add_sub_add_right_eq_sub]
  abel

/-- The collar straightening is `C^n` jointly in the time and the point when the map and the
profile are. -/
theorem contDiff_stripCollarStraightening {n : WithTop ℕ∞} (hh : ContDiff ℝ n h)
    (hχ : ContDiff ℝ n χ) (ε : ℝ) :
    ContDiff ℝ n fun q : ℝ × ℝ × ℝ ↦ stripCollarStraightening h χ ε q.1 q.2 := by
  simp only [stripCollarStraightening_apply, div_eq_mul_inv]
  fun_prop

/-- For `t ∈ [0, 1]` and a profile with values in `[0, 1]`, the collar straightening of a map of
the strip `ℝ × [0, 1]` into itself maps the strip into itself: its values are convex combinations
of a point and its image. -/
theorem mapsTo_stripCollarStraightening (hh : MapsTo h (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1))
    (hχ : ∀ u, χ u ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    MapsTo (stripCollarStraightening h χ ε t) (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1) :=
  fun _ hp ↦ (convex_univ.prod (convex_Icc 0 1)).add_smul_sub_mem hp (hh hp)
    (Icc.one_sub_mem (unitInterval.mul_mem ht (hχ _)))

/-! ### Estimates near the line -/

/-- If a `C¹` map commuting with the deck translations has derivative the identity along the line
`y = 0`, its derivative is uniformly close to the identity on a band `|y| < η`. -/
private theorem exists_pos_forall_norm_fderiv_sub_id_lt (hh : ContDiff ℝ 1 h)
    (hper : ∀ (p : ℝ × ℝ) (k : ℤ), h (p + ((k : ℝ), 0)) = h p + ((k : ℝ), 0))
    (hedge : ∀ x : ℝ, fderiv ℝ h (x, 0) = ContinuousLinearMap.id ℝ (ℝ × ℝ)) {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ η > 0, ∀ p : ℝ × ℝ, |p.2| < η →
      ‖fderiv ℝ h p - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ < κ := by
  set U := {p : ℝ × ℝ | ‖fderiv ℝ h p - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ < κ}
  have hU : IsOpen U := isOpen_lt
    ((hh.continuous_fderiv one_ne_zero).sub continuous_const).norm continuous_const
  have hUper (x y : ℝ) (k : ℤ) (hxy : (x, y) ∈ U) : (x + k, y) ∈ U := by
    have hk := periodic_fderiv_of_apply_add_eq_add (𝕜 := ℝ) (fun q ↦ hper q k) (x, y)
    simp only [Prod.mk_add_mk, add_zero] at hk
    simpa [U, hk] using hxy
  obtain ⟨η, hη, hsub⟩ := isCompact_singleton.exists_univ_prod_thickening_subset_open hU hUper
    fun p hp ↦ by
      obtain ⟨x, y⟩ := p
      obtain rfl : y = 0 := hp.2
      simpa [U, hedge] using hκ
  refine ⟨η, hη, fun p hp ↦ hsub ⟨mem_univ _, ?_⟩⟩
  rwa [Metric.thickening_singleton, Metric.mem_ball, Real.dist_0_eq_abs]

/-- A map fixing the line `y = 0` pointwise, whose derivative is within `κ` of the identity on a
band `|y| < η`, moves each point `p` of the band by at most `κ |p.2|`. -/
private theorem norm_sub_le_mul_abs_snd (hh : ContDiff ℝ 1 h) (hfix : ∀ x : ℝ, h (x, 0) = (x, 0))
    {η κ : ℝ}
    (hκ : ∀ p : ℝ × ℝ, |p.2| < η → ‖fderiv ℝ h p - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ ≤ κ)
    {p : ℝ × ℝ} (hp : |p.2| < η) : ‖h p - p‖ ≤ κ * |p.2| := by
  have hband : Convex ℝ (univ ×ˢ Ioo (-η) η) :=
    (convex_univ : Convex ℝ (univ : Set ℝ)).prod (convex_Ioo _ _)
  have hmem : ∀ q : ℝ × ℝ, q ∈ univ ×ˢ Ioo (-η) η ↔ |q.2| < η := fun q ↦ by
    simp [abs_lt]
  have hd : ∀ q, HasFDerivAt (fun q ↦ h q - q)
      (fderiv ℝ h q - ContinuousLinearMap.id ℝ (ℝ × ℝ)) q :=
    fun q ↦ (hh.differentiable one_ne_zero q).hasFDerivAt.sub (hasFDerivAt_id q)
  have hη : 0 < η := (abs_nonneg _).trans_lt hp
  have h₀ : ((p.1, 0) : ℝ × ℝ) ∈ univ ×ˢ Ioo (-η) η := (hmem _).2 (by simpa using hη)
  have := hband.norm_image_sub_le_of_norm_fderiv_le (fun q _ ↦ (hd q).differentiableAt)
    (fun q hq ↦ by rw [(hd q).fderiv]; exact hκ q ((hmem q).1 hq)) h₀ ((hmem p).2 hp)
  have hp' : p - (p.1, 0) = (0, p.2) := by ext <;> simp
  simpa [hfix, hp', Prod.norm_def] using this

/-- The derivative of `H_t - id = (1 - t χ(y / ε)) (h - id)`, bounded by the two terms of the
product rule. -/
private theorem exists_hasFDerivAt_sub_id (hh : ContDiff ℝ 1 h) (hχ : ContDiff ℝ 1 χ)
    (p : ℝ × ℝ) :
    ∃ D : (ℝ × ℝ) →L[ℝ] ℝ × ℝ,
      HasFDerivAt (fun q ↦ stripCollarStraightening h χ ε t q - q) D p ∧
      ‖D‖ ≤ |1 - t * χ (p.2 / ε)| * ‖fderiv ℝ h p - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ +
        |t| * |deriv χ (p.2 / ε)| * |ε|⁻¹ * ‖h p - p‖ := by
  set snd := ContinuousLinearMap.snd ℝ ℝ ℝ
  have h₁ : HasFDerivAt (fun q : ℝ × ℝ ↦ q.2 / ε) (ε⁻¹ • snd) p :=
    (hasFDerivAt_snd.mul_const ε⁻¹).congr_of_eventuallyEq
      (Eventually.of_forall fun q ↦ div_eq_mul_inv _ _)
  have h₂ := (((hχ.differentiable one_ne_zero (p.2 / ε)).hasDerivAt.comp_hasFDerivAt p
    h₁).const_mul t).const_sub 1
  have h₃ := (hh.differentiable one_ne_zero p).hasFDerivAt.sub (hasFDerivAt_id p)
  refine ⟨_, (h₂.smul h₃).congr_of_eventuallyEq (Eventually.of_forall fun q ↦ ?_), ?_⟩
  · simp [stripCollarStraightening_apply, comp_apply]
  · have hs : ‖snd‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · simp [norm_smul]
    · simp only [ContinuousLinearMap.norm_smulRight_apply, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_inv, mul_assoc, Pi.sub_apply, id_eq]
      gcongr
      exact mul_le_of_le_one_left (norm_nonneg _) hs

/-- On a band `|y| < η` on which the derivative of `h` is within `κ` of the identity, the
derivative of `H_t - id` is at most `κ (1 + B)`, where `B` bounds `|u| |χ'(u)|`. The factor `1 / ε`
of the derivative of `χ(y / ε)` is compensated by the bound `κ |y|` on the displacement
`h p - p`. -/
private theorem exists_hasFDerivAt_sub_id_norm_le (hh : ContDiff ℝ 1 h) (hχ : ContDiff ℝ 1 χ)
    (hfix : ∀ x : ℝ, h (x, 0) = (x, 0)) (hχ01 : ∀ u, χ u ∈ Icc (0 : ℝ) 1) {B : ℝ}
    (hB : ∀ u, |u| * |deriv χ u| ≤ B) {η κ : ℝ}
    (hκ : ∀ p : ℝ × ℝ, |p.2| < η → ‖fderiv ℝ h p - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ ≤ κ)
    (ht : t ∈ Icc (0 : ℝ) 1) {p : ℝ × ℝ} (hp : |p.2| < η) :
    ∃ D : (ℝ × ℝ) →L[ℝ] ℝ × ℝ,
      HasFDerivAt (fun q ↦ stripCollarStraightening h χ ε t q - q) D p ∧ ‖D‖ ≤ κ * (1 + B) := by
  obtain ⟨D, hD, hDle⟩ := exists_hasFDerivAt_sub_id (ε := ε) (t := t) hh hχ p
  refine ⟨D, hD, hDle.trans ?_⟩
  have hdisp := norm_sub_le_mul_abs_snd hh hfix hκ hp
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hκ p hp)
  have hu : |deriv χ (p.2 / ε)| * |ε|⁻¹ * |p.2| ≤ B := by
    calc |deriv χ (p.2 / ε)| * |ε|⁻¹ * |p.2| = |p.2 / ε| * |deriv χ (p.2 / ε)| := by
          rw [abs_div]; ring
      _ ≤ B := hB _
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  calc |1 - t * χ (p.2 / ε)| * ‖fderiv ℝ h p - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ +
        |t| * |deriv χ (p.2 / ε)| * |ε|⁻¹ * ‖h p - p‖
      ≤ 1 * κ + 1 * |deriv χ (p.2 / ε)| * |ε|⁻¹ * (κ * |p.2|) := by
        gcongr
        · have hw := Icc.one_sub_mem (unitInterval.mul_mem ht (hχ01 (p.2 / ε)))
          exact (abs_of_nonneg hw.1).trans_le hw.2
        · exact hκ p hp
    _ = κ + κ * (|deriv χ (p.2 / ε)| * |ε|⁻¹ * |p.2|) := by ring
    _ ≤ κ * (1 + B) := by nlinarith

section Band

variable {B η κ : ℝ}

/-- Let the derivative of `h` be within `κ` of the identity on the band `|y| < η`, with
`κ (1 + B) ≤ 1 / 2` where `B` bounds `|u| |χ'(u)|`. Then `H_t` is injective on the band, since
`H_t - id` is `1 / 2`-Lipschitz there. -/
private theorem injOn_stripCollarStraightening_band (hh : ContDiff ℝ 1 h)
    (hχ : ContDiff ℝ 1 χ) (hfix : ∀ x : ℝ, h (x, 0) = (x, 0)) (hχ01 : ∀ u, χ u ∈ Icc (0 : ℝ) 1)
    (hB : ∀ u, |u| * |deriv χ u| ≤ B)
    (hκ : ∀ p : ℝ × ℝ, |p.2| < η → ‖fderiv ℝ h p - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ ≤ κ)
    (hκB : κ * (1 + B) ≤ 1 / 2) (ht : t ∈ Icc (0 : ℝ) 1) :
    InjOn (stripCollarStraightening h χ ε t) (univ ×ˢ Ioo (-η) η) := by
  have hmem : ∀ r : ℝ × ℝ, r ∈ univ ×ˢ Ioo (-η) η → |r.2| < η := fun r hr ↦
    abs_lt.2 (mem_Ioo.1 hr.2)
  choose! D hDf hDle using fun (r : ℝ × ℝ) (hr : |r.2| < η) ↦
    exists_hasFDerivAt_sub_id_norm_le (ε := ε) hh hχ hfix hχ01 hB hκ ht hr
  have hlip : LipschitzOnWith (1 / 2) (fun q ↦ stripCollarStraightening h χ ε t q - q)
      (univ ×ˢ Ioo (-η) η) :=
    ((convex_univ : Convex ℝ (univ : Set ℝ)).prod
      (convex_Ioo (-η) η)).lipschitzOnWith_of_nnNorm_hasFDerivWithin_le
      (fun r hr ↦ (hDf r (hmem r hr)).hasFDerivWithinAt) fun r hr ↦ by
        rw [← NNReal.coe_le_coe, coe_nnNorm]
        simpa using (hDle r (hmem r hr)).trans hκB
  have happ : ApproximatesLinearOn (stripCollarStraightening h χ ε t)
      ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ) : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ)
      (univ ×ˢ Ioo (-η) η) (1 / 2) := fun p hp q hq ↦ by
    simpa [sub_sub_sub_comm] using hlip.norm_sub_le hp hq
  exact happ.injOn (Or.inr (by norm_num))

/-- Under the hypotheses of `injOn_stripCollarStraightening_band`, the differential of `H_t` is
invertible on the band `|y| < η`, being within `1 / 2` of the identity. -/
private theorem isInvertible_fderiv_stripCollarStraightening_band (hh : ContDiff ℝ 1 h)
    (hχ : ContDiff ℝ 1 χ) (hfix : ∀ x : ℝ, h (x, 0) = (x, 0)) (hχ01 : ∀ u, χ u ∈ Icc (0 : ℝ) 1)
    (hB : ∀ u, |u| * |deriv χ u| ≤ B)
    (hκ : ∀ p : ℝ × ℝ, |p.2| < η → ‖fderiv ℝ h p - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ ≤ κ)
    (hκB : κ * (1 + B) ≤ 1 / 2) (ht : t ∈ Icc (0 : ℝ) 1) {p : ℝ × ℝ} (hp : |p.2| < η) :
    (fderiv ℝ (stripCollarStraightening h χ ε t) p).IsInvertible := by
  obtain ⟨D, hDp, hDle⟩ := exists_hasFDerivAt_sub_id_norm_le (ε := ε) hh hχ hfix hχ01 hB hκ ht hp
  have hH : HasFDerivAt (stripCollarStraightening h χ ε t)
      (D + ContinuousLinearMap.id ℝ (ℝ × ℝ)) p :=
    (hDp.add (hasFDerivAt_id p)).congr_of_eventuallyEq (Eventually.of_forall fun q ↦ by simp)
  rw [hH.fderiv]
  refine ContinuousLinearMap.isInvertible_of_norm_sub_lt (ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)) ?_
  rw [← NNReal.coe_lt_coe]
  simpa [ContinuousLinearMap.norm_id] using
    (hDle.trans hκB).trans_lt (by norm_num : (1 / 2 : ℝ) < 1)

/-- Under the hypotheses of `injOn_stripCollarStraightening_band`, `H_t` at most doubles the
distance of a point of the band `|y| < η` to the line `y = 0`. -/
private theorem abs_snd_stripCollarStraightening_le (hh : ContDiff ℝ 1 h)
    (hfix : ∀ x : ℝ, h (x, 0) = (x, 0)) (hχ01 : ∀ u, χ u ∈ Icc (0 : ℝ) 1) (hB0 : 0 ≤ B)
    (hκ : ∀ p : ℝ × ℝ, |p.2| < η → ‖fderiv ℝ h p - ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ ≤ κ)
    (hκB : κ * (1 + B) ≤ 1 / 2) (ht : t ∈ Icc (0 : ℝ) 1) {p : ℝ × ℝ} (hp : |p.2| < η) :
    |(stripCollarStraightening h χ ε t p).2| ≤ 2 * |p.2| := by
  have hdisp := norm_sub_le_mul_abs_snd hh hfix hκ hp
  have hκ1 : κ ≤ 1 := by nlinarith [(norm_nonneg _).trans (hκ p hp)]
  have hsnd : |((1 - t * χ (p.2 / ε)) • (h p - p)).2| ≤ |p.2| := by
    rw [Prod.smul_snd, smul_eq_mul, abs_mul]
    calc |1 - t * χ (p.2 / ε)| * |(h p - p).2| ≤ 1 * (κ * |p.2|) := by
          gcongr
          · have hw := Icc.one_sub_mem (unitInterval.mul_mem ht (hχ01 (p.2 / ε)))
            exact (abs_of_nonneg hw.1).trans_le hw.2
          · exact (norm_snd_le (h p - p)).trans hdisp
      _ ≤ 1 * (1 * |p.2|) := by gcongr
      _ = |p.2| := by ring
  calc |(stripCollarStraightening h χ ε t p).2|
      ≤ |p.2| + |((1 - t * χ (p.2 / ε)) • (h p - p)).2| := by
        rw [stripCollarStraightening_apply, Prod.snd_add]
        exact abs_add_le _ _
    _ ≤ 2 * |p.2| := by linarith

end Band

/-- A `C¹` profile with compact support has `|u| |χ'(u)|` bounded and vanishes outside an
interval `(-R, R)`. -/
private theorem exists_bound_of_hasCompactSupport (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) :
    ∃ B R : ℝ, 0 ≤ B ∧ 0 < R ∧ (∀ u, |u| * |deriv χ u| ≤ B) ∧ ∀ u, R ≤ |u| → χ u = 0 := by
  obtain ⟨B, hB⟩ :=
    (continuous_id.mul (hχ.continuous_deriv le_rfl)).bounded_above_of_compact_support
      hχc.deriv.mul_left
  obtain ⟨R₀, hR₀⟩ := hχc.isCompact.isBounded.subset_closedBall 0
  refine ⟨B, max R₀ 0 + 1, (norm_nonneg _).trans (hB 0), by positivity,
    fun u ↦ by simpa [abs_mul] using hB u, fun u hu ↦ image_eq_zero_of_notMem_tsupport fun hu' ↦ ?_⟩
  have := hR₀ hu'
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  linarith [le_max_left R₀ 0]

/-- A continuous map commuting with the deck translations, injective on the strip and fixing the
line `y = 0`, keeps the points of the strip at height at least `η` a positive distance `m` from
the line. -/
private theorem exists_pos_le_abs_snd (hh : Continuous h)
    (hper : ∀ (p : ℝ × ℝ) (k : ℤ), h (p + ((k : ℝ), 0)) = h p + ((k : ℝ), 0))
    (hfix : ∀ x : ℝ, h (x, 0) = (x, 0)) (hinj : InjOn h (univ ×ˢ Icc 0 1)) {η : ℝ}
    (hη : 0 < η) :
    ∃ m > 0, ∀ q ∈ univ ×ˢ Icc (0 : ℝ) 1, η ≤ q.2 → m ≤ |(h q).2| := by
  rcases lt_or_ge 1 η with hη1 | hη1
  · exact ⟨1, one_pos, fun q hq hqη ↦ absurd (hqη.trans hq.2.2) (not_le.2 hη1)⟩
  set K := Icc (0 : ℝ) 1 ×ˢ Icc η 1
  obtain ⟨q₀, hq₀, hmin⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact K).exists_isMinOn
    ⟨(0, η), ⟨left_mem_Icc.2 zero_le_one, left_mem_Icc.2 hη1⟩⟩
    (continuous_snd.comp hh).abs.continuousOn
  refine ⟨|(h q₀).2|, abs_pos.2 fun h0 ↦ ?_, fun q hq hqη ↦ ?_⟩
  · -- A point of height zero in the image is the image of a point of the line.
    have h' : h q₀ = h ((h q₀).1, 0) := by rw [hfix]; ext <;> simp [h0]
    have := congrArg Prod.snd (hinj ⟨mem_univ _, hη.le.trans hq₀.2.1, hq₀.2.2⟩
      ⟨mem_univ _, le_rfl, zero_le_one⟩ h')
    exact (hη.trans_le hq₀.2.1).ne' this
  · -- Translate `q` by an integer into `K`.
    have hqK : q + (((-⌊q.1⌋ : ℤ) : ℝ), 0) ∈ K :=
      ⟨fst_add_neg_floor_mem q, by simpa using hqη, by simpa using hq.2.2⟩
    have := isMinOn_iff.1 hmin _ hqK
    rwa [comp_apply, comp_apply, hper, Prod.snd_add, add_zero] at this

/-! ### Injectivity -/

/-- `H_t` is injective on the strip `ℝ × [0, 1]` once it is injective on a band `|y| < η₀`, equal
to `h` above height `a`, and keeps the points below height `a` below height `m`, while `h` keeps
the points at height at least `η ∈ [a, η₀)` at height at least `m`. Two points at height at least
`η` have the same images under `H_t` and `h`. Two points below `η` lie in the band. In the mixed
case the lower point either lies above `a` too, or has image below height `m`, unlike the upper
one. -/
private theorem injOn_stripCollarStraightening_of_separated {a η η₀ m : ℝ}
    (hinj : InjOn h (univ ×ˢ Icc 0 1))
    (hband : InjOn (stripCollarStraightening h χ ε t) (univ ×ˢ Ioo (-η₀) η₀)) (haη : a ≤ η)
    (hηη₀ : η < η₀) (habove : ∀ q : ℝ × ℝ, a ≤ q.2 → χ (q.2 / ε) = 0)
    (hbelow : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, p.2 < a → |(stripCollarStraightening h χ ε t p).2| < m)
    (hmh : ∀ q ∈ univ ×ˢ Icc (0 : ℝ) 1, η ≤ q.2 → m ≤ |(h q).2|) :
    InjOn (stripCollarStraightening h χ ε t) (univ ×ˢ Icc 0 1) := by
  have hkey : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, ∀ q ∈ univ ×ˢ Icc (0 : ℝ) 1, η ≤ q.2 →
      stripCollarStraightening h χ ε t p = stripCollarStraightening h χ ε t q → p = q :=
    fun p hp q hq hqη hpq ↦ by
    have hHq : stripCollarStraightening h χ ε t q = h q :=
      stripCollarStraightening_of_eq_zero (habove q (haη.trans hqη))
    rcases lt_or_ge p.2 a with hpa | hpa
    · have hlt := hbelow p hp hpa
      rw [hpq, hHq] at hlt
      exact absurd (hmh q hq hqη) (not_le.2 hlt)
    · rw [hHq, stripCollarStraightening_of_eq_zero (habove p hpa)] at hpq
      exact hinj hp hq hpq
  intro p hp q hq hpq
  by_cases hqη : η ≤ q.2
  · exact hkey p hp q hq hqη hpq
  by_cases hpη : η ≤ p.2
  · exact (hkey q hq p hp hpη hpq.symm).symm
  have hmem : ∀ r : ℝ × ℝ, r ∈ univ ×ˢ Icc (0 : ℝ) 1 → ¬η ≤ r.2 → r ∈ univ ×ˢ Ioo (-η₀) η₀ :=
    fun r hr hrη ↦ mem_prod.2 ⟨mem_univ _,
      mem_Ioo.2 ⟨by linarith [hr.2.1], by linarith [not_le.1 hrη]⟩⟩
  exact hband (hmem p hp hpη) (hmem q hq hqη) hpq


/-- **Straightening a map of the strip near a boundary line.** Let `h` be a `C¹` map of the plane
commuting with the deck translations `(x, y) ↦ (x + k, y)`, injective on the strip
`ℝ × [0, 1]`, which fixes the line `y = 0` pointwise and has derivative the identity along it.
Let `χ` be a `C¹` profile with compact support and values in `[0, 1]`. Then for every small width
`ε > 0` and every `t ∈ [0, 1]`, the collar straightening
`H_t (p) = p + (1 - t χ(y / ε)) (h p - p)` is injective on the strip, and its differential at a
point of the strip is invertible wherever that of `h` is. -/
theorem exists_pos_forall_injOn_stripCollarStraightening (hh : ContDiff ℝ 1 h)
    (hper : ∀ (p : ℝ × ℝ) (k : ℤ), h (p + ((k : ℝ), 0)) = h p + ((k : ℝ), 0))
    (hfix : ∀ x : ℝ, h (x, 0) = (x, 0))
    (hedge : ∀ x : ℝ, fderiv ℝ h (x, 0) = ContinuousLinearMap.id ℝ (ℝ × ℝ))
    (hinj : InjOn h (univ ×ˢ Icc 0 1)) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (hχ01 : ∀ u, χ u ∈ Icc (0 : ℝ) 1) :
    ∃ ε₀ > 0, ∀ ε ∈ Ioc 0 ε₀, ∀ t ∈ Icc (0 : ℝ) 1,
      InjOn (stripCollarStraightening h χ ε t) (univ ×ˢ Icc 0 1) ∧
      ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, (fderiv ℝ h p).IsInvertible →
        (fderiv ℝ (stripCollarStraightening h χ ε t) p).IsInvertible := by
  -- The constants: `|u χ'(u)| ≤ B`, `χ` vanishes outside `(-R, R)`, the derivative of `h` is
  -- within `κ` of the identity on the band `|y| < η₀`, and `h` keeps the points of the strip at
  -- height at least `η` at height at least `m`. For `R ε ≤ η` and `2 R ε ≤ m`, the map `H_t` is
  -- injective on the band and equal to `h` above the collar `|y| < R ε`, and it keeps the collar
  -- below height `m`, which separates the two regions.
  obtain ⟨B, R, hB0, hR, hB, hχR⟩ := exists_bound_of_hasCompactSupport hχ hχc
  obtain ⟨κ, hκ, hκB⟩ : ∃ κ > 0, κ * (1 + B) = 1 / 2 :=
    ⟨(2 * (1 + B))⁻¹, by positivity, by field_simp⟩
  obtain ⟨η₀, hη₀, hDh⟩ := exists_pos_forall_norm_fderiv_sub_id_lt hh hper hedge hκ
  have hDh' := fun p hp ↦ (hDh p hp).le
  obtain ⟨η, hη, hηη₀⟩ : ∃ η > 0, η < η₀ := ⟨η₀ / 2, half_pos hη₀, half_lt_self hη₀⟩
  obtain ⟨m, hm, hmh⟩ := exists_pos_le_abs_snd hh.continuous hper hfix hinj hη
  refine ⟨min (η / R) (m / (2 * R)), lt_min (div_pos hη hR) (div_pos hm (by positivity)),
    fun ε hε t ht ↦ ?_⟩
  have hε0 := hε.1
  have hRε : R * ε ≤ η := by
    have := (le_div_iff₀' hR).1 (hε.2.trans (min_le_left _ _))
    linarith
  have hRεm : 2 * (R * ε) ≤ m := by
    have := (le_div_iff₀' (by positivity : (0 : ℝ) < 2 * R)).1 (hε.2.trans (min_le_right _ _))
    linarith
  -- Above height `R ε` the profile vanishes, so `H_t = h` there.
  have hout : ∀ q : ℝ × ℝ, R * ε ≤ q.2 → χ (q.2 / ε) = 0 := fun q hq ↦ hχR _ (by
    rw [abs_div, abs_of_pos hε0, le_div_iff₀ hε0, abs_of_pos ((mul_pos hR hε0).trans_le hq)]
    exact hq)
  -- Below height `R ε` the image stays below height `2 R ε ≤ m`.
  have hbelow : ∀ p ∈ univ ×ˢ Icc (0 : ℝ) 1, p.2 < R * ε →
      |(stripCollarStraightening h χ ε t p).2| < m := fun p hp hpR ↦ by
    have hp' : |p.2| < η₀ := by rw [abs_of_nonneg hp.2.1]; linarith
    have := abs_snd_stripCollarStraightening_le (ε := ε) hh hfix hχ01 hB0 hDh' hκB.le ht hp'
    rw [abs_of_nonneg hp.2.1] at this
    linarith
  refine ⟨injOn_stripCollarStraightening_of_separated hinj
    (injOn_stripCollarStraightening_band hh hχ hfix hχ01 hB hDh' hκB.le ht) hRε hηη₀ hout hbelow
    hmh, fun p hp hinv ↦ ?_⟩
  by_cases hpη₀ : |p.2| < η₀
  · exact isInvertible_fderiv_stripCollarStraightening_band hh hχ hfix hχ01 hB hDh' hκB.le ht
      hpη₀
  · -- Above the band, `H_t` agrees with `h` near `p`.
    have hp' : R * ε < p.2 := by
      rw [abs_of_nonneg hp.2.1] at hpη₀
      linarith
    have heq : stripCollarStraightening h χ ε t =ᶠ[𝓝 p] h := by
      filter_upwards [(continuous_snd.isOpen_preimage _ isOpen_Ioi).mem_nhds hp'] with q hq
      exact stripCollarStraightening_of_eq_zero (hout q (le_of_lt hq))
    rwa [heq.fderiv_eq]

end TauCeti
