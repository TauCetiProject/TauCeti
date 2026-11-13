/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem.Parametric
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import TauCeti.Analysis.Calculus.Deriv.AddCircle

/-!
# The boundary interpolation isotopy of the annulus strip

The closed annulus `(ℝ / ℤ) × [0, 1]` is covered by the strip `ℝ × [0, 1]`, with deck
translation `T (x, y) = (x + 1, y)`. An orientation-preserving diffeomorphism of the annulus
preserving both boundary circles has boundary maps whose lifts are increasing degree-one maps
`b₀, b₁ : ℝ → ℝ`, that is elements of `CircleDeg1Lift`. Interpolating them linearly in the
height `y`, and then linearly in time from the identity, gives the maps

`B_t (x, y) = ((1 - t) x + t ((1 - y) b₀ x + y b₁ x), y)`

(`CircleDeg1Lift.stripInterpolation b₀ b₁ t`). They commute with `T`
(`CircleDeg1Lift.stripInterpolation_mk_add_one`) and preserve every horizontal line, `B_0` is the
identity, and `B_1` restricts to `b₀` on the lower boundary line and to `b₁` on the upper one
(`CircleDeg1Lift.stripInterpolation_one_mk_zero`, `CircleDeg1Lift.stripInterpolation_one_mk_one`).
So if `b₀` and `b₁` are the boundary lifts of a diffeomorphism `F` of the strip, then `B_1⁻¹ ∘ F`
fixes both boundary lines pointwise: this is the first step in showing that a
boundary-preserving diffeomorphism of the annulus is isotopic to one fixing its boundary.

The horizontal component of `B_t` has `x`-derivative `1 - t + t ((1 - y) b₀' x + y b₁' x)`
(`CircleDeg1Lift.hasDerivAt_stripInterpolation_fst`). The parameters `(t, y)` at which this is
positive for every `x` form the set `CircleDeg1Lift.stripInterpolationDomain b₀ b₁`. It is open
when `b₀` and `b₁` are `C¹`, since `b₀'` and `b₁'` are periodic, and when `b₀' > 0` and `b₁' > 0` it
contains `[0, 1] × [0, 1]`, as a convex combination of positive numbers is positive. For `(t, y)`
in this set the horizontal map is an increasing degree-one bijection of `ℝ`
(`CircleDeg1Lift.bijective_stripInterpolation_fst`). Its inverse
`CircleDeg1Lift.stripInterpolationInv b₀ b₁ t` also commutes with `T`
(`CircleDeg1Lift.stripInterpolationInv_mk_add_one`) and is `C^n` jointly in `t` and the point when
`b₀` and `b₁` are `C^n` (`CircleDeg1Lift.contDiffOn_stripInterpolationInv`), by the inverse
function theorem for smooth families of diffeomorphisms
(`ContDiffOn.parametric_invFun_of_injective`). Hence, for
`0 ≤ t ≤ 1`, the maps `B_t` are bijections of the closed strip
(`CircleDeg1Lift.bijOn_stripInterpolation`) with positive `x`-derivative, depending smoothly on
`t` together with their inverses: a smooth isotopy from the identity to a map with boundary lifts
`b₀` and `b₁`. The inverse laws and the smoothness of the inverse hold on the whole open
neighbourhood of the strip on which `(t, y)` lies in the domain.

## Main definitions

* `CircleDeg1Lift.stripInterpolation b₀ b₁ t`: the map `B_t` of the strip.
* `CircleDeg1Lift.stripInterpolationDomain b₀ b₁`: the parameters `(t, y)` at which the horizontal
  component of `B_t` has positive derivative everywhere.
* `CircleDeg1Lift.stripInterpolationInv b₀ b₁ t`: the inverse of `B_t`.

## Main results

* `CircleDeg1Lift.contDiff_stripInterpolation`: `(t, p) ↦ B_t p` is `C^n` when `b₀`, `b₁` are.
* `CircleDeg1Lift.isOpen_stripInterpolationDomain`,
  `CircleDeg1Lift.Icc_prod_Icc_subset_stripInterpolationDomain`: the domain is an open
  neighbourhood of `[0, 1] × [0, 1]`.
* `CircleDeg1Lift.stripInterpolationInv_stripInterpolation`,
  `CircleDeg1Lift.stripInterpolation_stripInterpolationInv`: the inverse laws.
* `CircleDeg1Lift.stripInterpolationInv_mk_add_one`: the inverse commutes with the deck
  translation.
* `CircleDeg1Lift.contDiffOn_stripInterpolationInv`: `(t, p) ↦ B_t⁻¹ p` is `C^n`.
* `CircleDeg1Lift.bijOn_stripInterpolation`: for `0 ≤ t ≤ 1`, `B_t` is a bijection of the closed
  strip `ℝ × [0, 1]`.

## References

* D. B. A. Epstein, *Curves on 2-manifolds and isotopies*, Acta Math. 115 (1966), 83–107,
  Theorem 6.4: an orientation-preserving diffeomorphism of the annulus preserving each boundary
  component is isotopic to the identity.
-/

public section

noncomputable section

open Function Set Filter
open scoped Topology

namespace CircleDeg1Lift

variable (b₀ b₁ : CircleDeg1Lift) {n : WithTop ℕ∞} {t y : ℝ}

/-- The **boundary interpolation** `B_t (x, y) = ((1 - t) x + t ((1 - y) b₀ x + y b₁ x), y)` of
two degree-one lifts `b₀`, `b₁` on the strip `ℝ × [0, 1]`. For `t = 1` it restricts to `b₀` on the
lower boundary line and to `b₁` on the upper one, and for `t = 0` it is the identity. -/
def stripInterpolation (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - t) * p.1 + t * ((1 - p.2) * b₀ p.1 + p.2 * b₁ p.1), p.2)

theorem stripInterpolation_apply (t : ℝ) (p : ℝ × ℝ) :
    b₀.stripInterpolation b₁ t p =
      ((1 - t) * p.1 + t * ((1 - p.2) * b₀ p.1 + p.2 * b₁ p.1), p.2) :=
  (rfl)

/-- The boundary interpolation preserves every horizontal line. -/
@[simp]
theorem stripInterpolation_snd (t : ℝ) (p : ℝ × ℝ) : (b₀.stripInterpolation b₁ t p).2 = p.2 :=
  (rfl)

/-- At time `0` the boundary interpolation is the identity. -/
@[simp]
theorem stripInterpolation_zero (p : ℝ × ℝ) : b₀.stripInterpolation b₁ 0 p = p := by
  simp [stripInterpolation_apply]

/-- On the lower boundary line the boundary interpolation moves from the identity to `b₀`. -/
theorem stripInterpolation_mk_zero (t x : ℝ) :
    b₀.stripInterpolation b₁ t (x, 0) = ((1 - t) * x + t * b₀ x, 0) := by
  simp [stripInterpolation_apply]

/-- On the upper boundary line the boundary interpolation moves from the identity to `b₁`. -/
theorem stripInterpolation_mk_one (t x : ℝ) :
    b₀.stripInterpolation b₁ t (x, 1) = ((1 - t) * x + t * b₁ x, 1) := by
  simp [stripInterpolation_apply]

/-- At time `1` the boundary interpolation restricts to `b₀` on the lower boundary line. -/
@[simp]
theorem stripInterpolation_one_mk_zero (x : ℝ) : b₀.stripInterpolation b₁ 1 (x, 0) = (b₀ x, 0) := by
  simp [stripInterpolation_mk_zero]

/-- At time `1` the boundary interpolation restricts to `b₁` on the upper boundary line. -/
@[simp]
theorem stripInterpolation_one_mk_one (x : ℝ) : b₀.stripInterpolation b₁ 1 (x, 1) = (b₁ x, 1) := by
  simp [stripInterpolation_mk_one]

/-- The boundary interpolation commutes with the deck translation `(x, y) ↦ (x + 1, y)` of the
annulus. -/
theorem stripInterpolation_mk_add_one (t x y : ℝ) :
    b₀.stripInterpolation b₁ t (x + 1, y) = b₀.stripInterpolation b₁ t (x, y) + (1, 0) := by
  simp only [stripInterpolation_apply, map_add_one, Prod.mk_add_mk, add_zero]
  congr 1
  ring

/-- The boundary interpolation is `C^n` jointly in time and the point when `b₀` and `b₁` are
`C^n`. -/
theorem contDiff_stripInterpolation (h₀ : ContDiff ℝ n b₀) (h₁ : ContDiff ℝ n b₁) :
    ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) ↦ b₀.stripInterpolation b₁ q.1 q.2 := by
  simp only [stripInterpolation_apply]
  fun_prop

/-- The horizontal component of the boundary interpolation has `x`-derivative
`1 - t + t ((1 - y) b₀' x + y b₁' x)`. -/
theorem hasDerivAt_stripInterpolation_fst {x : ℝ} (h₀ : DifferentiableAt ℝ b₀ x)
    (h₁ : DifferentiableAt ℝ b₁ x) (t y : ℝ) :
    HasDerivAt (fun x ↦ (b₀.stripInterpolation b₁ t (x, y)).1)
      (1 - t + t * ((1 - y) * deriv b₀ x + y * deriv b₁ x)) x := by
  have h := ((hasDerivAt_id x).const_mul (1 - t)).add
    (((h₀.hasDerivAt.const_mul (1 - y)).add (h₁.hasDerivAt.const_mul y)).const_mul t)
  convert h using 1
  · ext x'
    simp only [stripInterpolation_apply, Pi.add_apply, id]
  · ring

/-- The parameters `(t, y)` at which `1 - t + t ((1 - y) b₀' x + y b₁' x) > 0` for every `x`. For
differentiable `b₀`, `b₁` this is the derivative of the horizontal component `x ↦ (B_t (x, y)).1`
of the boundary interpolation (`CircleDeg1Lift.hasDerivAt_stripInterpolation_fst`). -/
def stripInterpolationDomain : Set (ℝ × ℝ) :=
  {q | ∀ x, 0 < 1 - q.1 + q.1 * ((1 - q.2) * deriv b₀ x + q.2 * deriv b₁ x)}

theorem mem_stripInterpolationDomain {q : ℝ × ℝ} :
    q ∈ b₀.stripInterpolationDomain b₁ ↔
      ∀ x, 0 < 1 - q.1 + q.1 * ((1 - q.2) * deriv b₀ x + q.2 * deriv b₁ x) :=
  Iff.rfl

/-- For `C¹` lifts the domain of the boundary interpolation is open: the derivatives are
periodic, so positivity need only be checked on the compact interval `[0, 1]`. -/
theorem isOpen_stripInterpolationDomain (h₀ : ContDiff ℝ 1 b₀) (h₁ : ContDiff ℝ 1 b₁) :
    IsOpen (b₀.stripInterpolationDomain b₁) := by
  set h : ℝ × ℝ → ℝ → ℝ := fun q x ↦ 1 - q.1 + q.1 * ((1 - q.2) * deriv b₀ x + q.2 * deriv b₁ x)
  have hc : Continuous fun z : (ℝ × ℝ) × ℝ ↦ h z.1 z.2 := by
    have := h₀.continuous_deriv le_rfl
    have := h₁.continuous_deriv le_rfl
    fun_prop
  have hper₀ := AddCircle.periodic_deriv_of_lift
    (fun x ↦ (h₀.differentiable one_ne_zero x).hasDerivAt) b₀.map_add_one
  have hper₁ := AddCircle.periodic_deriv_of_lift
    (fun x ↦ (h₁.differentiable one_ne_zero x).hasDerivAt) b₁.map_add_one
  have hper : ∀ q, Periodic (h q) 1 := fun q x ↦ by
    simp only [h, hper₀ x, hper₁ x]
  refine isOpen_iff_mem_nhds.2 fun q₀ hq₀ ↦ ?_
  have hK : ∀ᶠ q in 𝓝 q₀, ∀ x ∈ Icc (0 : ℝ) 1, 0 < h q x :=
    isCompact_Icc.eventually_forall_of_forall_eventually fun x _ ↦
      (hc.tendsto (q₀, x)).eventually_const_lt (hq₀ x)
  filter_upwards [hK] with q hq x
  obtain ⟨x', hx', hxx'⟩ := (hper q).exists_mem_Ico₀ one_pos x
  have hx := hq x' (Ico_subset_Icc_self hx')
  rwa [← hxx'] at hx

/-- If `b₀` and `b₁` have positive derivative, the domain of the boundary interpolation contains
`[0, 1] × [0, 1]`. -/
theorem Icc_prod_Icc_subset_stripInterpolationDomain (h₀ : ∀ x, 0 < deriv b₀ x)
    (h₁ : ∀ x, 0 < deriv b₁ x) :
    Icc 0 1 ×ˢ Icc 0 1 ⊆ b₀.stripInterpolationDomain b₁ := by
  rintro ⟨t, y⟩ ⟨⟨ht₀, ht₁⟩, ⟨hy₀, hy₁⟩⟩ x
  have hD : 0 < (1 - y) * deriv b₀ x + y * deriv b₁ x := by
    rcases hy₁.lt_or_eq with hy₁ | rfl
    · nlinarith [h₀ x, h₁ x]
    · simpa using h₁ x
  exact AddCircle.one_sub_add_mul_pos ht₀ ht₁ hD

variable {b₀ b₁}

/-- For parameters in the domain, the horizontal component of the boundary interpolation is
strictly increasing. -/
theorem strictMono_stripInterpolation_fst (h₀ : Differentiable ℝ b₀) (h₁ : Differentiable ℝ b₁)
    (h : (t, y) ∈ b₀.stripInterpolationDomain b₁) :
    StrictMono fun x ↦ (b₀.stripInterpolation b₁ t (x, y)).1 :=
  strictMono_of_deriv_pos fun x ↦ by
    rw [(b₀.hasDerivAt_stripInterpolation_fst b₁ (h₀ x) (h₁ x) t y).deriv]
    exact h x

/-- For parameters in the domain, the horizontal component of the boundary interpolation is an
increasing degree-one bijection of `ℝ`. -/
theorem bijective_stripInterpolation_fst (h₀ : Differentiable ℝ b₀) (h₁ : Differentiable ℝ b₁)
    (h : (t, y) ∈ b₀.stripInterpolationDomain b₁) :
    Bijective fun x ↦ (b₀.stripInterpolation b₁ t (x, y)).1 := by
  have hmono := strictMono_stripInterpolation_fst h₀ h₁ h
  refine ⟨hmono.injective, ?_⟩
  let L : CircleDeg1Lift :=
    ⟨⟨fun x ↦ (b₀.stripInterpolation b₁ t (x, y)).1, hmono.monotone⟩, fun x ↦ by
      simp only [stripInterpolation_apply, map_add_one]
      ring⟩
  exact L.continuous_iff_surjective.1 <| continuous_iff_continuousAt.2 fun x ↦
    (b₀.hasDerivAt_stripInterpolation_fst b₁ (h₀ x) (h₁ x) t y).continuousAt

variable (b₀ b₁) in
/-- The inverse of the boundary interpolation `B_t`: on each horizontal line it inverts the
horizontal component of `B_t`. It is the inverse of `B_t` on the lines whose height `y` has
`(t, y)` in `CircleDeg1Lift.stripInterpolationDomain b₀ b₁`. -/
def stripInterpolationInv (t : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (invFun (fun x ↦ (b₀.stripInterpolation b₁ t (x, p.2)).1) p.1, p.2)

theorem stripInterpolationInv_apply (t : ℝ) (p : ℝ × ℝ) :
    b₀.stripInterpolationInv b₁ t p =
      (invFun (fun x ↦ (b₀.stripInterpolation b₁ t (x, p.2)).1) p.1, p.2) :=
  (rfl)

/-- The inverse of the boundary interpolation preserves every horizontal line. -/
@[simp]
theorem stripInterpolationInv_snd (t : ℝ) (p : ℝ × ℝ) :
    (b₀.stripInterpolationInv b₁ t p).2 = p.2 :=
  (rfl)

/-- At time `0` the inverse of the boundary interpolation is the identity. -/
@[simp]
theorem stripInterpolationInv_zero (p : ℝ × ℝ) : b₀.stripInterpolationInv b₁ 0 p = p := by
  have e : (fun x ↦ (b₀.stripInterpolation b₁ 0 (x, p.2)).1) = id := funext fun x ↦ by simp
  rw [stripInterpolationInv_apply, e]
  exact Prod.ext (leftInverse_invFun injective_id p.1) rfl

/-- On a horizontal line whose parameters lie in the domain, `B_t⁻¹ ∘ B_t` is the identity. -/
@[simp]
theorem stripInterpolationInv_stripInterpolation (h₀ : Differentiable ℝ b₀)
    (h₁ : Differentiable ℝ b₁) {p : ℝ × ℝ} (h : (t, p.2) ∈ b₀.stripInterpolationDomain b₁) :
    b₀.stripInterpolationInv b₁ t (b₀.stripInterpolation b₁ t p) = p :=
  Prod.ext (leftInverse_invFun (bijective_stripInterpolation_fst h₀ h₁ h).1 p.1) rfl

/-- On a horizontal line whose parameters lie in the domain, `B_t ∘ B_t⁻¹` is the identity. -/
@[simp]
theorem stripInterpolation_stripInterpolationInv (h₀ : Differentiable ℝ b₀)
    (h₁ : Differentiable ℝ b₁) {p : ℝ × ℝ} (h : (t, p.2) ∈ b₀.stripInterpolationDomain b₁) :
    b₀.stripInterpolation b₁ t (b₀.stripInterpolationInv b₁ t p) = p :=
  Prod.ext (rightInverse_invFun (bijective_stripInterpolation_fst h₀ h₁ h).2 p.1) rfl

/-- On a horizontal line whose parameters lie in the domain, the inverse of the boundary
interpolation commutes with the deck translation `(x, y) ↦ (x + 1, y)` of the annulus. -/
theorem stripInterpolationInv_mk_add_one (h₀ : Differentiable ℝ b₀) (h₁ : Differentiable ℝ b₁)
    {x y : ℝ} (h : (t, y) ∈ b₀.stripInterpolationDomain b₁) :
    b₀.stripInterpolationInv b₁ t (x + 1, y) = b₀.stripInterpolationInv b₁ t (x, y) + (1, 0) := by
  set q := b₀.stripInterpolationInv b₁ t (x, y)
  have hq : b₀.stripInterpolation b₁ t (q + (1, 0)) = (x + 1, y) := by
    have e : q + (1, 0) = (q.1 + 1, q.2) := Prod.ext rfl (add_zero _)
    rw [e, stripInterpolation_mk_add_one, Prod.mk.eta,
      stripInterpolation_stripInterpolationInv h₀ h₁ h, Prod.mk_add_mk, add_zero]
  rw [← hq]
  exact stripInterpolationInv_stripInterpolation h₀ h₁ (by simpa [q] using h)

/-- **The inverse of the boundary interpolation is smooth.** For `C^n` lifts `b₀`, `b₁` with
`1 ≤ n`, the map `(t, p) ↦ B_t⁻¹ p` is `C^n` on the open set of `(t, (x, y))` with `(t, y)` in the
domain of the boundary interpolation. -/
theorem contDiffOn_stripInterpolationInv (hn : 1 ≤ n) (h₀ : ContDiff ℝ n b₀)
    (h₁ : ContDiff ℝ n b₁) :
    ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) ↦ b₀.stripInterpolationInv b₁ q.1 q.2)
      {q | (q.1, q.2.2) ∈ b₀.stripInterpolationDomain b₁} := by
  have hn0 : n ≠ 0 := by rintro rfl; exact absurd hn (by simp)
  have hd₀ := h₀.differentiable hn0
  have hd₁ := h₁.differentiable hn0
  -- The horizontal component, as a family over the parameters `(t, y)`.
  set g : (ℝ × ℝ) × ℝ → ℝ := fun r ↦ (b₀.stripInterpolation b₁ r.1.1 (r.2, r.1.2)).1
  have hσ : ContDiff ℝ n fun r : (ℝ × ℝ) × ℝ ↦ (r.1.1, (r.2, r.1.2)) := by fun_prop
  have hg : ContDiff ℝ n g := contDiff_fst.comp ((contDiff_stripInterpolation b₀ b₁ h₀ h₁).comp hσ)
  have hinv := hg.contDiffOn.parametric_invFun_of_injective
    (isOpen_stripInterpolationDomain b₀ b₁ (h₀.of_le hn) (h₁.of_le hn)) hn
    (fun q hq ↦ bijective_stripInterpolation_fst hd₀ hd₁ hq) fun q hq x u v huv ↦ by
      have hd : HasDerivAt (fun x ↦ g (q, x)) _ x :=
        b₀.hasDerivAt_stripInterpolation_fst b₁ (hd₀ x) (hd₁ x) q.1 q.2
      rw [hd.hasFDerivAt.fderiv] at huv
      simpa [(hq x).ne'] using huv
  have hτ : ContDiff ℝ n fun q : ℝ × (ℝ × ℝ) ↦ ((q.1, q.2.2), q.2.1) := by fun_prop
  exact (hinv.comp hτ.contDiffOn fun q hq ↦ ⟨hq, mem_univ _⟩).prodMk contDiff_snd.snd.contDiffOn

/-- **The boundary interpolation is a bijection of the closed strip.** If `b₀` and `b₁` have
positive derivative, then for `0 ≤ t ≤ 1` the map `B_t` is a bijection of `ℝ × [0, 1]`, with inverse
`CircleDeg1Lift.stripInterpolationInv b₀ b₁ t`. -/
theorem bijOn_stripInterpolation (h₀ : ∀ x, 0 < deriv b₀ x) (h₁ : ∀ x, 0 < deriv b₁ x)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    BijOn (b₀.stripInterpolation b₁ t) (univ ×ˢ Icc 0 1) (univ ×ˢ Icc 0 1) := by
  have hd₀ : Differentiable ℝ b₀ := fun x ↦ differentiableAt_of_deriv_ne_zero (h₀ x).ne'
  have hd₁ : Differentiable ℝ b₁ := fun x ↦ differentiableAt_of_deriv_ne_zero (h₁ x).ne'
  have hdom : ∀ p ∈ (univ : Set ℝ) ×ˢ Icc (0 : ℝ) 1,
      (t, p.2) ∈ b₀.stripInterpolationDomain b₁ := fun p hp ↦
    Icc_prod_Icc_subset_stripInterpolationDomain b₀ b₁ h₀ h₁ (mk_mem_prod ht hp.2)
  refine InvOn.bijOn (f' := b₀.stripInterpolationInv b₁ t)
    ⟨fun p hp ↦ stripInterpolationInv_stripInterpolation hd₀ hd₁ (hdom p hp),
      fun p hp ↦ stripInterpolation_stripInterpolationInv hd₀ hd₁ (hdom p hp)⟩
    (fun p hp ↦ ⟨mem_univ _, hp.2⟩) fun p hp ↦ ⟨mem_univ _, hp.2⟩

end CircleDeg1Lift
