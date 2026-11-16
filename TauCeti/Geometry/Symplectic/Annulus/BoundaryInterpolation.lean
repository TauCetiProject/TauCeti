/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The boundary interpolation isotopy of the annulus strip

Let `b₀, b₁ : ℝ → ℝ` be lifts of degree one circle maps (`CircleDeg1Lift`), for instance the lifts
of the two boundary maps of a diffeomorphism of the closed annulus `(ℝ / ℤ) × [0, 1]` preserving
each boundary component. This file constructs the explicit isotopy

`B_t(x, y) = ((1 - t) x + t ((1 - y) b₀(x) + y b₁(x)), y)`

(`TauCeti.stripBoundaryInterpolation`) of the strip `ℝ × [0, 1]`, which covers the annulus. It
preserves every horizontal line, commutes with the deck translation `T(x, y) = (x + 1, y)`, is the
identity at `t = 0`, and at `t = 1` it restricts to `b₀` on the lower boundary line and to `b₁` on
the upper one. When `b₀` and `b₁` have positive derivatives, composing the inverse of `B_1` with a
lift `F` of an annulus diffeomorphism whose boundary maps lift to `b₀` and `b₁` gives a map fixing
both boundary lines pointwise
(`TauCeti.stripBoundaryInterpolationPartialDiffeomorph_symm_apply_one_mk_zero` and
`TauCeti.stripBoundaryInterpolationPartialDiffeomorph_symm_apply_one_mk_one`). This is the first
reduction in the proof that every diffeomorphism of the closed annulus preserving orientation and
each boundary component is isotopic to the identity through such diffeomorphisms.

The `x`-derivative of the first component of `B_t` at `(x, y)` is the slope

`(1 - t) + t ((1 - y) b₀'(x) + y b₁'(x))`  (`TauCeti.stripBoundaryInterpolationSlope`),

a convex combination of `1`, `b₀'(x)` and `b₁'(x)` when `t, y ∈ [0, 1]`; it is positive there as
soon as `b₀' > 0` and `b₁' > 0`. Let `D` be the set of parameters `(t, (x, y))` at which this slope
is positive for every `x` (`TauCeti.stripBoundaryInterpolationDomain`). Since the slope is
`1`-periodic in `x` (`TauCeti.periodic_deriv_of_apply_add_eq_add`), this is an open set when the
derivatives of `b₀` and `b₁` are continuous, and it contains `[0, 1] × ℝ × [0, 1]` when the
derivatives of `b₀` and `b₁` are positive. On each horizontal line
over a parameter in `D`, the first component of `B_t` is a strictly increasing continuous lift, so a
homeomorphism of the line. The Jacobian of the track `(t, p) ↦ (t, B_t(p))` is invertible on `D`,
so by the inverse function theorem the track is a `C^n` partial diffeomorphism of `ℝ × ℝ × ℝ` with
source and target `D` (`TauCeti.stripBoundaryInterpolationPartialDiffeomorph`). Its inverse is
`C^n` jointly in `t` and `p`, so when `b₀' > 0` and `b₁' > 0` the family `B_t`, `t ∈ [0, 1]`, is a
`C^n` isotopy of diffeomorphisms of a neighbourhood of the strip. The inverse commutes with the
deck translations as well
(`TauCeti.stripBoundaryInterpolationPartialDiffeomorph_symm_apply_mk_add_int`).

## Main definitions

* `TauCeti.stripBoundaryInterpolation b₀ b₁ t`: the map `B_t` of the plane.
* `TauCeti.stripBoundaryInterpolationSlope b₀ b₁ t y x`: the `x`-derivative of `B_t` at `(x, y)`.
* `TauCeti.stripBoundaryInterpolationDomain b₀ b₁`: the parameters at which that slope is
  positive along the whole horizontal line.
* `TauCeti.stripBoundaryInterpolationPartialDiffeomorph`: the track `(t, p) ↦ (t, B_t(p))` as a
  `C^n` partial diffeomorphism with source and target the domain.

## Main results

* `TauCeti.stripBoundaryInterpolation_zero`, `TauCeti.stripBoundaryInterpolation_one_mk_zero`,
  `TauCeti.stripBoundaryInterpolation_one_mk_one`: `B_0 = id`, and `B_1` restricts to `b₀` and
  `b₁` on the boundary lines.
* `TauCeti.stripBoundaryInterpolation_mk_add_int`: `B_t` commutes with the deck translations.
* `TauCeti.isOpen_stripBoundaryInterpolationDomain`,
  `TauCeti.Icc_prod_subset_stripBoundaryInterpolationDomain`: the domain is open and contains
  `[0, 1] × ℝ × [0, 1]`.
* `TauCeti.strictMono_stripBoundaryInterpolation_fst`,
  `TauCeti.bijOn_stripBoundaryInterpolation`: for `t ∈ [0, 1]` and continuous strictly increasing
  `b₀`, `b₁`, the map `B_t` is strictly increasing along horizontal lines and a bijection of the
  strip.

## References

* D. B. A. Epstein, *Curves on 2-manifolds and isotopies*, Acta Math. 115 (1966), 83–107
  (isotopies of surface diffeomorphisms to the identity).
* C. Conley and E. Zehnder, *The Birkhoff–Lewis fixed point theorem and a conjecture of
  V. I. Arnold*, Invent. Math. 73 (1983), 33–49.
-/

public section

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace TauCeti

variable (b₀ b₁ : CircleDeg1Lift)

/-! ### The interpolation -/

/-- The **boundary interpolation** `B_t(x, y) = ((1 - t) x + t ((1 - y) b₀(x) + y b₁(x)), y)` of
the plane. It is the identity at `t = 0`, and at `t = 1` it restricts to the lifts `b₀` and `b₁` on
the two boundary lines. When `b₀` and `b₁` are continuous and strictly increasing, for `t ∈ [0, 1]`
it is a bijection of the strip `ℝ × [0, 1]` (`TauCeti.bijOn_stripBoundaryInterpolation`). For `C^n`
lifts with `b₀' > 0` and `b₁' > 0`, `TauCeti.stripBoundaryInterpolationPartialDiffeomorph` makes
the family `B_t` an isotopy. -/
def stripBoundaryInterpolation (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - t) * p.1 + t * ((1 - p.2) * b₀ p.1 + p.2 * b₁ p.1), p.2)

/-- The first component of the boundary interpolation. -/
@[simp]
theorem stripBoundaryInterpolation_fst (t : ℝ) (p : ℝ × ℝ) :
    (stripBoundaryInterpolation b₀ b₁ t p).1 =
      (1 - t) * p.1 + t * ((1 - p.2) * b₀ p.1 + p.2 * b₁ p.1) :=
  (rfl)

/-- The boundary interpolation preserves every horizontal line. -/
@[simp]
theorem stripBoundaryInterpolation_snd (t : ℝ) (p : ℝ × ℝ) :
    (stripBoundaryInterpolation b₀ b₁ t p).2 = p.2 :=
  (rfl)

/-- At time `0` the boundary interpolation is the identity. -/
@[simp]
theorem stripBoundaryInterpolation_zero : stripBoundaryInterpolation b₀ b₁ 0 = id := by
  ext p <;> simp

/-- On the lower boundary line the boundary interpolation interpolates from the identity to
`b₀`. -/
theorem stripBoundaryInterpolation_mk_zero (t x : ℝ) :
    stripBoundaryInterpolation b₀ b₁ t (x, 0) = ((1 - t) * x + t * b₀ x, 0) := by
  ext <;> simp

/-- On the upper boundary line the boundary interpolation interpolates from the identity to
`b₁`. -/
theorem stripBoundaryInterpolation_mk_one (t x : ℝ) :
    stripBoundaryInterpolation b₀ b₁ t (x, 1) = ((1 - t) * x + t * b₁ x, 1) := by
  ext <;> simp

/-- At time `1` the boundary interpolation restricts to `b₀` on the lower boundary line. -/
@[simp]
theorem stripBoundaryInterpolation_one_mk_zero (x : ℝ) :
    stripBoundaryInterpolation b₀ b₁ 1 (x, 0) = (b₀ x, 0) := by
  simp [stripBoundaryInterpolation_mk_zero]

/-- At time `1` the boundary interpolation restricts to `b₁` on the upper boundary line. -/
@[simp]
theorem stripBoundaryInterpolation_one_mk_one (x : ℝ) :
    stripBoundaryInterpolation b₀ b₁ 1 (x, 1) = (b₁ x, 1) := by
  simp [stripBoundaryInterpolation_mk_one]

/-- The boundary interpolation commutes with the deck translations `(x, y) ↦ (x + m, y)`. -/
theorem stripBoundaryInterpolation_mk_add_int (t x y : ℝ) (m : ℤ) :
    stripBoundaryInterpolation b₀ b₁ t (x + m, y) =
      stripBoundaryInterpolation b₀ b₁ t (x, y) + ((m : ℝ), 0) := by
  ext
  · simp only [stripBoundaryInterpolation_fst, CircleDeg1Lift.map_add_int, Prod.fst_add]
    ring
  · simp

/-- The boundary interpolation commutes with the deck translation `T(x, y) = (x + 1, y)`. -/
theorem stripBoundaryInterpolation_mk_add_one (t x y : ℝ) :
    stripBoundaryInterpolation b₀ b₁ t (x + 1, y) =
      stripBoundaryInterpolation b₀ b₁ t (x, y) + (1, 0) := by
  simpa using stripBoundaryInterpolation_mk_add_int b₀ b₁ t x y 1

/-- The boundary interpolation is `C^n` jointly in the time and the point when `b₀` and `b₁`
are. -/
theorem contDiff_stripBoundaryInterpolation {n : WithTop ℕ∞} (hb₀ : ContDiff ℝ n b₀)
    (hb₁ : ContDiff ℝ n b₁) :
    ContDiff ℝ n fun q : ℝ × ℝ × ℝ ↦ stripBoundaryInterpolation b₀ b₁ q.1 q.2 := by
  unfold stripBoundaryInterpolation
  fun_prop

/-! ### The slope along horizontal lines -/

/-- The **slope** `(1 - t) + t ((1 - y) b₀'(x) + y b₁'(x))`: the derivative in `x` of the first
component of the boundary interpolation `B_t` at `(x, y)`
(`TauCeti.hasDerivAt_stripBoundaryInterpolation_fst`). -/
def stripBoundaryInterpolationSlope (t y x : ℝ) : ℝ :=
  1 - t + t * ((1 - y) * deriv b₀ x + y * deriv b₁ x)

/-- The formula for the slope. -/
theorem stripBoundaryInterpolationSlope_def (t y x : ℝ) :
    stripBoundaryInterpolationSlope b₀ b₁ t y x =
      1 - t + t * ((1 - y) * deriv b₀ x + y * deriv b₁ x) :=
  (rfl)

/-- The slope is the derivative in `x` of the first component of the boundary interpolation. -/
theorem hasDerivAt_stripBoundaryInterpolation_fst {x : ℝ} (hb₀ : DifferentiableAt ℝ b₀ x)
    (hb₁ : DifferentiableAt ℝ b₁ x) (t y : ℝ) :
    HasDerivAt (fun x ↦ (stripBoundaryInterpolation b₀ b₁ t (x, y)).1)
      (stripBoundaryInterpolationSlope b₀ b₁ t y x) x := by
  have h := ((hasDerivAt_id x).const_mul (1 - t)).add
    (((hb₀.hasDerivAt.const_mul (1 - y)).add (hb₁.hasDerivAt.const_mul y)).const_mul t)
  convert h using 1
  · funext z
    simp only [stripBoundaryInterpolation_fst, Pi.add_apply, id]
  · rw [stripBoundaryInterpolationSlope_def]
    ring

/-- The slope is `1`-periodic along every horizontal line. -/
theorem stripBoundaryInterpolationSlope_periodic (t y : ℝ) :
    Periodic (stripBoundaryInterpolationSlope b₀ b₁ t y) 1 := fun x ↦ by
  simp [stripBoundaryInterpolationSlope_def, periodic_deriv_of_apply_add_eq_add b₀.map_add_one x,
    periodic_deriv_of_apply_add_eq_add b₁.map_add_one x]

/-- For `t, y ∈ [0, 1]` the slope is a convex combination of `1`, `b₀'(x)` and `b₁'(x)`, so it is
positive when the derivatives of `b₀` and `b₁` are. -/
theorem stripBoundaryInterpolationSlope_pos (h₀ : ∀ x, 0 < deriv b₀ x)
    (h₁ : ∀ x, 0 < deriv b₁ x) {t y : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (x : ℝ) : 0 < stripBoundaryInterpolationSlope b₀ b₁ t y x := by
  have h := convex_Ioi (0 : ℝ) (h₀ x) (h₁ x) (sub_nonneg.2 hy.2) hy.1 (sub_add_cancel 1 y)
  simpa [stripBoundaryInterpolationSlope_def] using
    convex_Ioi (0 : ℝ) one_pos h (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)

/-! ### The domain of positive slope -/

/-- The set of parameters `(t, (x, y))` at which the slope of the boundary interpolation `B_t` is
positive along the whole horizontal line through `(x, y)`. It depends only on `t` and `y`. -/
def stripBoundaryInterpolationDomain : Set (ℝ × ℝ × ℝ) :=
  {q | ∀ x, 0 < stripBoundaryInterpolationSlope b₀ b₁ q.1 q.2.2 x}

@[simp]
theorem mem_stripBoundaryInterpolationDomain {q : ℝ × ℝ × ℝ} :
    q ∈ stripBoundaryInterpolationDomain b₀ b₁ ↔
      ∀ x, 0 < stripBoundaryInterpolationSlope b₀ b₁ q.1 q.2.2 x :=
  Iff.rfl

/-- The domain of positive slope is open when the derivatives of `b₀` and `b₁` are continuous: by
periodicity of the slope, positivity along a whole horizontal line is positivity over the compact
period `[0, 1]`. -/
theorem isOpen_stripBoundaryInterpolationDomain (h₀ : Continuous (deriv b₀))
    (h₁ : Continuous (deriv b₁)) : IsOpen (stripBoundaryInterpolationDomain b₀ b₁) := by
  have hD : Continuous fun z : (ℝ × ℝ × ℝ) × ℝ ↦
      stripBoundaryInterpolationSlope b₀ b₁ z.1.1 z.1.2.2 z.2 := by
    simp only [stripBoundaryInterpolationSlope_def]
    fun_prop
  rw [isOpen_iff_eventually]
  intro q hq
  have key : ∀ᶠ q' in 𝓝 q, ∀ x ∈ Icc (0 : ℝ) 1,
      0 < stripBoundaryInterpolationSlope b₀ b₁ q'.1 q'.2.2 x :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun x _ ↦
      (hD.isOpen_preimage _ isOpen_Ioi).mem_nhds (hq x)
  filter_upwards [key] with q' hq' x
  obtain ⟨x', hx', hxx'⟩ :=
    Function.Periodic.exists_mem_Ico₀
      (stripBoundaryInterpolationSlope_periodic b₀ b₁ q'.1 q'.2.2) one_pos x
  rw [hxx']
  exact hq' x' (Ico_subset_Icc_self hx')

/-- When the derivatives of `b₀` and `b₁` are positive, the domain of positive slope contains
`[0, 1] × ℝ × [0, 1]`, the times `t ∈ [0, 1]` over the strip. -/
theorem Icc_prod_subset_stripBoundaryInterpolationDomain (h₀ : ∀ x, 0 < deriv b₀ x)
    (h₁ : ∀ x, 0 < deriv b₁ x) :
    Icc (0 : ℝ) 1 ×ˢ (univ ×ˢ Icc (0 : ℝ) 1) ⊆ stripBoundaryInterpolationDomain b₀ b₁ :=
  fun _ hq ↦ stripBoundaryInterpolationSlope_pos b₀ b₁ h₀ h₁ hq.1 hq.2.2

/-! ### The track of the isotopy -/

/-- The track `(t, p) ↦ (t, B_t(p))` of the boundary interpolation. -/
private def track (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (q.1, stripBoundaryInterpolation b₀ b₁ q.1 q.2)

/-- Over a parameter in the domain, the first component of `B_t` along the horizontal line is a
strictly increasing lift of a degree one circle map. -/
private theorem strictMono_fst_of_mem (hb₀ : Differentiable ℝ b₀) (hb₁ : Differentiable ℝ b₁)
    {t y : ℝ} (h : ∀ x, 0 < stripBoundaryInterpolationSlope b₀ b₁ t y x) :
    StrictMono fun x ↦ (stripBoundaryInterpolation b₀ b₁ t (x, y)).1 :=
  strictMono_of_deriv_pos fun x ↦
    (hasDerivAt_stripBoundaryInterpolation_fst b₀ b₁ (hb₀ x) (hb₁ x) t y).deriv ▸ h x

/-- When it is strictly increasing, the first component of `B_t` along a horizontal line is a
continuous lift of a degree one circle map, so it maps the line onto itself. -/
private theorem surjective_fst_of_strictMono (hb₀ : Continuous b₀) (hb₁ : Continuous b₁)
    {t y : ℝ} (h : StrictMono fun x ↦ (stripBoundaryInterpolation b₀ b₁ t (x, y)).1) :
    Surjective fun x ↦ (stripBoundaryInterpolation b₀ b₁ t (x, y)).1 := by
  let f : CircleDeg1Lift :=
    { toFun := fun x ↦ (stripBoundaryInterpolation b₀ b₁ t (x, y)).1
      monotone' := h.monotone
      map_add_one' := fun x ↦ by
        simp [stripBoundaryInterpolation_mk_add_one] }
  have hf : Continuous f := by
    simp only [f, CircleDeg1Lift.coe_mk, OrderHom.coe_mk, stripBoundaryInterpolation_fst]
    fun_prop
  exact f.continuous_iff_surjective.1 hf

private theorem injOn_track (hb₀ : Differentiable ℝ b₀) (hb₁ : Differentiable ℝ b₁) :
    InjOn (track b₀ b₁) (stripBoundaryInterpolationDomain b₀ b₁) := by
  rintro ⟨t, x, y⟩ hq ⟨t', x', y'⟩ - h
  have ht : t = t' := congr_arg Prod.fst h
  have hy : y = y' := congr_arg (fun q ↦ q.2.2) h
  have hx : (stripBoundaryInterpolation b₀ b₁ t (x, y)).1 =
      (stripBoundaryInterpolation b₀ b₁ t' (x', y')).1 := congr_arg (fun q ↦ q.2.1) h
  subst ht hy
  rw [(strictMono_fst_of_mem b₀ b₁ hb₀ hb₁ hq).injective hx]

private theorem image_track (hb₀ : Differentiable ℝ b₀) (hb₁ : Differentiable ℝ b₁) :
    track b₀ b₁ '' stripBoundaryInterpolationDomain b₀ b₁ =
      stripBoundaryInterpolationDomain b₀ b₁ := by
  refine Subset.antisymm ?_ fun q hq ↦ ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact hq
  obtain ⟨t, x, y⟩ := q
  obtain ⟨x', hx'⟩ := surjective_fst_of_strictMono b₀ b₁ hb₀.continuous hb₁.continuous
    (strictMono_fst_of_mem b₀ b₁ hb₀ hb₁ hq) x
  exact ⟨(t, x', y), hq, Prod.ext rfl (Prod.ext hx' rfl)⟩

/-- The derivative of the track is injective at every point of the domain: it fixes the time and
height components and acts on the `x`-direction by the positive slope. -/
private theorem injective_fderiv_track (hb₀ : Differentiable ℝ b₀) (hb₁ : Differentiable ℝ b₁)
    {q : ℝ × ℝ × ℝ} (hq : q ∈ stripBoundaryInterpolationDomain b₀ b₁) :
    Injective (fderiv ℝ (track b₀ b₁) q) := by
  have hdiff : Differentiable ℝ (track b₀ b₁) := by
    unfold track stripBoundaryInterpolation
    fun_prop
  set L := fderiv ℝ (track b₀ b₁) q
  have hL : HasFDerivAt (track b₀ b₁) L q := (hdiff q).hasFDerivAt
  -- The time component of the track is the time.
  have h₁ : ∀ v, (L v).1 = v.1 := fun v ↦ by
    have := hL.fst.unique (hasFDerivAt_fst (p := q))
    exact congr($this v)
  -- The height component of the track is the height.
  have h₃ : ∀ v, (L v).2.2 = v.2.2 := fun v ↦ by
    have hs : HasFDerivAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2)
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) q :=
      hasFDerivAt_snd.snd
    have := hL.snd.snd.unique hs
    exact congr($this v)
  -- Along the `x`-direction the middle component moves at the slope.
  have h₂ : (L (0, 1, 0)).2.1 = stripBoundaryInterpolationSlope b₀ b₁ q.1 q.2.2 q.2.1 := by
    have hc : HasDerivAt (fun s : ℝ ↦ ((q.1, s, q.2.2) : ℝ × ℝ × ℝ)) (0, 1, 0) q.2.1 :=
      HasDerivAt.prodMk (hasDerivAt_const _ _)
        (HasDerivAt.prodMk (hasDerivAt_id _) (hasDerivAt_const _ _))
    have h := hL.snd.fst.comp_hasDerivAt (x := q.2.1) hc
    exact h.unique (hasDerivAt_stripBoundaryInterpolation_fst b₀ b₁ (hb₀ _) (hb₁ _) q.1 q.2.2)
  intro v w hvw
  rw [← sub_eq_zero, ← map_sub] at hvw
  rw [← sub_eq_zero]
  set u := v - w
  have hu₁ : u.1 = 0 := by rw [← h₁, hvw]; rfl
  have hu₃ : u.2.2 = 0 := by rw [← h₃, hvw]; rfl
  have hu : u = u.2.1 • ((0, 1, 0) : ℝ × ℝ × ℝ) := by
    ext <;> simp [hu₁, hu₃]
  have hu₂ : u.2.1 * stripBoundaryInterpolationSlope b₀ b₁ q.1 q.2.2 q.2.1 = 0 := by
    have := congr(($hvw).2.1)
    rw [hu, map_smul] at this
    simpa [h₂] using this
  have hu₂' : u.2.1 = 0 := (mul_eq_zero.1 hu₂).resolve_right (hq q.2.1).ne'
  rw [hu, hu₂', zero_smul]

private theorem isLocalDiffeomorphOn_track {n : WithTop ℕ∞} (hb₀ : ContDiff ℝ n b₀)
    (hb₁ : ContDiff ℝ n b₁) (hn : 1 ≤ n) :
    IsLocalDiffeomorphOn 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) n (track b₀ b₁)
      (stripBoundaryInterpolationDomain b₀ b₁) := by
  have hC : ContDiff ℝ n (track b₀ b₁) :=
    contDiff_fst.prodMk (contDiff_stripBoundaryInterpolation b₀ b₁ hb₀ hb₁)
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  rintro ⟨q, hq⟩
  have hinj := injective_fderiv_track b₀ b₁ (hb₀.differentiable hn0) (hb₁.differentiable hn0) hq
  exact TauCeti.isLocalDiffeomorphAt_of_fderiv_eq hC.contDiffOn
    (isOpen_stripBoundaryInterpolationDomain b₀ b₁ (hb₀.continuous_deriv hn)
      (hb₁.continuous_deriv hn)) hq hn
    (e := (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv)
    (ContinuousLinearMap.ext fun v ↦ by simp)

/-- The track `(t, p) ↦ (t, B_t(p))` of the boundary interpolation, as a `C^n` partial
diffeomorphism of `ℝ × ℝ × ℝ` whose source and target are both the domain of positive slope.
Its inverse is `C^n` jointly in the time and the point. When `b₀' > 0` and `b₁' > 0`, the source
contains `[0, 1] × ℝ × [0, 1]` (`TauCeti.Icc_prod_subset_stripBoundaryInterpolationDomain`), so for
`t ∈ [0, 1]` the maps `B_t` form a `C^n` isotopy of diffeomorphisms of a neighbourhood of the
strip. -/
def stripBoundaryInterpolationPartialDiffeomorph {n : WithTop ℕ∞} (hb₀ : ContDiff ℝ n b₀)
    (hb₁ : ContDiff ℝ n b₁) (hn : 1 ≤ n) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ) n :=
  (isLocalDiffeomorphOn_track b₀ b₁ hb₀ hb₁ hn).partialDiffeomorphOfInjOn
    (isOpen_stripBoundaryInterpolationDomain b₀ b₁ (hb₀.continuous_deriv hn)
      (hb₁.continuous_deriv hn))
    (injOn_track b₀ b₁ (hb₀.differentiable (zero_lt_one.trans_le hn).ne')
      (hb₁.differentiable (zero_lt_one.trans_le hn).ne'))

section PartialDiffeomorph

variable {b₀ b₁} {n : WithTop ℕ∞} (hb₀ : ContDiff ℝ n b₀) (hb₁ : ContDiff ℝ n b₁) (hn : 1 ≤ n)

@[simp]
theorem stripBoundaryInterpolationPartialDiffeomorph_apply (q : ℝ × ℝ × ℝ) :
    stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn q =
      (q.1, stripBoundaryInterpolation b₀ b₁ q.1 q.2) :=
  congrFun (IsLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn ..) q

@[simp]
theorem stripBoundaryInterpolationPartialDiffeomorph_source :
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).source =
      stripBoundaryInterpolationDomain b₀ b₁ :=
  IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source ..

@[simp]
theorem stripBoundaryInterpolationPartialDiffeomorph_target :
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).target =
      stripBoundaryInterpolationDomain b₀ b₁ := by
  have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  rw [stripBoundaryInterpolationPartialDiffeomorph,
    IsLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target]
  exact image_track b₀ b₁ (hb₀.differentiable hn0) (hb₁.differentiable hn0)

/-- The track applied to the inverse of a point of the domain returns that point. -/
theorem stripBoundaryInterpolationPartialDiffeomorph_apply_symm_apply {q : ℝ × ℝ × ℝ}
    (hq : q ∈ stripBoundaryInterpolationDomain b₀ b₁) :
    stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn
      ((stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm q) = q := by
  rw [← stripBoundaryInterpolationPartialDiffeomorph_target hb₀ hb₁ hn] at hq
  simpa only [PartialDiffeomorph.symm_toPartialEquiv] using
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).right_inv hq

/-- The inverse of the track maps the domain into the domain. -/
theorem stripBoundaryInterpolationPartialDiffeomorph_symm_mem {q : ℝ × ℝ × ℝ}
    (hq : q ∈ stripBoundaryInterpolationDomain b₀ b₁) :
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm q ∈
      stripBoundaryInterpolationDomain b₀ b₁ := by
  rw [← stripBoundaryInterpolationPartialDiffeomorph_target hb₀ hb₁ hn] at hq
  rw [← stripBoundaryInterpolationPartialDiffeomorph_source hb₀ hb₁ hn]
  simpa only [PartialDiffeomorph.symm_toPartialEquiv] using
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).map_target hq

/-- On the domain, the inverse of the track undoes the track: `symm (t, B_t p) = (t, p)`. -/
theorem stripBoundaryInterpolationPartialDiffeomorph_symm_apply_apply {q : ℝ × ℝ × ℝ}
    (hq : q ∈ stripBoundaryInterpolationDomain b₀ b₁) :
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm
      (q.1, stripBoundaryInterpolation b₀ b₁ q.1 q.2) = q := by
  rw [← stripBoundaryInterpolationPartialDiffeomorph_source hb₀ hb₁ hn] at hq
  simpa only [PartialDiffeomorph.symm_toPartialEquiv,
    stripBoundaryInterpolationPartialDiffeomorph_apply] using
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).left_inv hq

/-- The inverse of the track preserves the time. -/
theorem stripBoundaryInterpolationPartialDiffeomorph_symm_apply_fst {q : ℝ × ℝ × ℝ}
    (hq : q ∈ stripBoundaryInterpolationDomain b₀ b₁) :
    ((stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm q).1 = q.1 := by
  conv_rhs => rw [← stripBoundaryInterpolationPartialDiffeomorph_apply_symm_apply hb₀ hb₁ hn hq,
    stripBoundaryInterpolationPartialDiffeomorph_apply]

/-- The inverse of the track preserves the height. -/
theorem stripBoundaryInterpolationPartialDiffeomorph_symm_apply_snd_snd {q : ℝ × ℝ × ℝ}
    (hq : q ∈ stripBoundaryInterpolationDomain b₀ b₁) :
    ((stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm q).2.2 = q.2.2 := by
  have h := stripBoundaryInterpolationPartialDiffeomorph_apply_symm_apply hb₀ hb₁ hn hq
  rw [stripBoundaryInterpolationPartialDiffeomorph_apply] at h
  conv_rhs => rw [← h]
  simp

/-- The inverse of the track commutes with the deck translations `(x, y) ↦ (x + m, y)`. -/
theorem stripBoundaryInterpolationPartialDiffeomorph_symm_apply_mk_add_int {t x y : ℝ}
    (hq : (t, x, y) ∈ stripBoundaryInterpolationDomain b₀ b₁) (m : ℤ) :
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm (t, x + m, y) =
      (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm (t, x, y) +
        (0, (m : ℝ), 0) := by
  have hs := stripBoundaryInterpolationPartialDiffeomorph_symm_mem hb₀ hb₁ hn hq
  have h := stripBoundaryInterpolationPartialDiffeomorph_apply_symm_apply hb₀ hb₁ hn hq
  rw [stripBoundaryInterpolationPartialDiffeomorph_apply] at h
  generalize (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm (t, x, y) = s
    at hs h ⊢
  obtain ⟨t', x', y'⟩ := s
  have ht : t' = t := congr_arg Prod.fst h
  have hy : y' = y := congr_arg (fun q ↦ q.2.2) h
  have hx : (stripBoundaryInterpolation b₀ b₁ t' (x', y')).1 = x := congr_arg (fun q ↦ q.2.1) h
  subst ht hy
  -- Membership in the domain depends only on the time and the height.
  have hs' : ((t', x' + m, y') : ℝ × ℝ × ℝ) ∈ stripBoundaryInterpolationDomain b₀ b₁ := by
    simpa using hs
  -- The translated point is the track of the translate of the preimage.
  have key : ((t', x + m, y') : ℝ × ℝ × ℝ) =
      (t', stripBoundaryInterpolation b₀ b₁ t' (x' + m, y')) := by
    rw [stripBoundaryInterpolation_mk_add_int]
    ext <;> simp [← hx]
  rw [key]
  exact (stripBoundaryInterpolationPartialDiffeomorph_symm_apply_apply hb₀ hb₁ hn hs').trans
    (by ext <;> simp)

/-- At time `1` the inverse of the track undoes `b₀` on the lower boundary line. Hence if a lift
`F` of an annulus map sends `(x, 0)` to `(b₀ x, 0)`, then `B_1⁻¹ ∘ F` fixes `(x, 0)`. -/
theorem stripBoundaryInterpolationPartialDiffeomorph_symm_apply_one_mk_zero
    (h₀ : ∀ x, 0 < deriv b₀ x) (x : ℝ) :
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm (1, b₀ x, 0) =
      (1, x, 0) := by
  have hq : ((1, x, 0) : ℝ × ℝ × ℝ) ∈ stripBoundaryInterpolationDomain b₀ b₁ := fun x' ↦ by
    simpa [stripBoundaryInterpolationSlope_def] using h₀ x'
  simpa using stripBoundaryInterpolationPartialDiffeomorph_symm_apply_apply hb₀ hb₁ hn hq

/-- At time `1` the inverse of the track undoes `b₁` on the upper boundary line. Hence if a lift
`F` of an annulus map sends `(x, 1)` to `(b₁ x, 1)`, then `B_1⁻¹ ∘ F` fixes `(x, 1)`. -/
theorem stripBoundaryInterpolationPartialDiffeomorph_symm_apply_one_mk_one
    (h₁ : ∀ x, 0 < deriv b₁ x) (x : ℝ) :
    (stripBoundaryInterpolationPartialDiffeomorph b₀ b₁ hb₀ hb₁ hn).symm (1, b₁ x, 1) =
      (1, x, 1) := by
  have hq : ((1, x, 1) : ℝ × ℝ × ℝ) ∈ stripBoundaryInterpolationDomain b₀ b₁ := fun x' ↦ by
    simpa [stripBoundaryInterpolationSlope_def] using h₁ x'
  simpa using stripBoundaryInterpolationPartialDiffeomorph_symm_apply_apply hb₀ hb₁ hn hq

end PartialDiffeomorph

/-- For `t, y ∈ [0, 1]`, the first component of `B_t` along the horizontal line at height `y` is
strictly increasing when `b₀` and `b₁` are. -/
theorem strictMono_stripBoundaryInterpolation_fst (h₀ : StrictMono b₀) (h₁ : StrictMono b₁)
    {t y : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    StrictMono fun x ↦ (stripBoundaryInterpolation b₀ b₁ t (x, y)).1 := fun x x' hxx' ↦ by
  have h := convex_Ioi (0 : ℝ) (sub_pos.2 (h₀ hxx')) (sub_pos.2 (h₁ hxx')) (sub_nonneg.2 hy.2)
    hy.1 (sub_add_cancel 1 y)
  have := convex_Ioi (0 : ℝ) (sub_pos.2 hxx') h (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
  simp only [mem_Ioi, smul_eq_mul] at this
  simp only [stripBoundaryInterpolation_fst]
  linarith

/-- For `t ∈ [0, 1]`, the boundary interpolation `B_t` maps the strip `ℝ × [0, 1]` bijectively
onto itself, when `b₀` and `b₁` are continuous and strictly increasing. -/
theorem bijOn_stripBoundaryInterpolation (hb₀ : Continuous b₀) (hb₁ : Continuous b₁)
    (h₀ : StrictMono b₀) (h₁ : StrictMono b₁) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    BijOn (stripBoundaryInterpolation b₀ b₁ t) (univ ×ˢ Icc (0 : ℝ) 1)
      (univ ×ˢ Icc (0 : ℝ) 1) := by
  refine ⟨fun p hp ↦ ⟨mem_univ _, by simpa using hp.2⟩, ?_, ?_⟩
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ - h
    simp only [Prod.ext_iff, stripBoundaryInterpolation_snd] at h
    obtain ⟨hx, rfl⟩ := h
    rw [(strictMono_stripBoundaryInterpolation_fst b₀ b₁ h₀ h₁ ht hp.2).injective hx]
  · rintro ⟨x, y⟩ hp
    obtain ⟨x', hx'⟩ := surjective_fst_of_strictMono b₀ b₁ hb₀ hb₁
      (strictMono_stripBoundaryInterpolation_fst b₀ b₁ h₀ h₁ ht hp.2) x
    exact ⟨(x', y), hp, Prod.ext hx' rfl⟩

end TauCeti
