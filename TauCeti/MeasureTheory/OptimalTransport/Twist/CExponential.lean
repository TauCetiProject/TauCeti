/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import TauCeti.MeasureTheory.OptimalTransport.Twist.Basic

/-!
# The `c`-exponential, `c`-segments and `c`-convex sets

Let `c : E × Y → ℝ` be a cost on a real normed space `E` and a type `Y`. Seen from a source point
`x`, a target point `y` has the *momentum* `-Dₓ c (x, y)`, a continuous linear functional on `E`.
The twist condition on a target set `V` says that a point of `V` is determined by its momentum:
`y ↦ Dₓ c (x, y)` is injective on `V`. The *`c`-exponential* `TauCeti.cExp c V x` inverts the
momentum map: it sends a momentum `p` to the point of `V` whose momentum at `x` is `p`,

`-Dₓ c (x, cExp c V x p) = p`.

For the quadratic cost `‖x - y‖ ^ 2 / 2` on a Hilbert space this is `x + p`, once `p` is identified
with a vector by the Riesz isomorphism, which explains the name. In general `cExp c V x p` is
specified only when `p` is the momentum of a point of `V`; elsewhere it is an unspecified point.

The `c`-exponential is how the twist condition turns a dual potential into a transport map. At a
contact point `(x, y)` of a dual feasible pair whose first potential `φ` is differentiable at `x`,
the first-order condition `D φ (x) = Dₓ c (x, y)` gives `y = cExp c V x (-D φ (x))`. Hence a plan
certified by such a pair is concentrated on the graph of `x ↦ cExp c V x (-D φ (x))`.

The *nondegeneracy condition* asks that the mixed derivative `D²ₓᵧ c (x, y)`, the derivative of
`y ↦ Dₓ c (x, y)`, be invertible; in finite dimensions with `dim E = dim Y` it says
`det D²ₓᵧ c (x, y) ≠ 0`. By the inverse function theorem, if `Y` is a Banach space, the cost is
twisted on `V`, and it is nondegenerate at an interior point `y` of `V`, then the `c`-exponential
is strictly differentiable at the momentum of `y`, with derivative `-(D²ₓᵧ c (x, y))⁻¹`.

The *`c`-segment* from `y₀` to `y₁` seen from `x` is the curve
`t ↦ cExp c V x ((1 - t) • p₀ + t • p₁)` whose momenta interpolate linearly between the momenta
`p₀` and `p₁` of its endpoints. A target set `V` is *`c`-convex* with respect to a source set `U`
(`TauCeti.IsCConvexSet c U V`) when, for every `x ∈ U`, the momenta of the points of `V` form a
convex set; then the `c`-segments between points of `V` stay in `V`. For the quadratic cost,
`c`-segments are ordinary segments and `c`-convexity is ordinary convexity. These are the
first-order notions of the regularity theory of optimal maps for general costs, whose hypotheses
ask the target to be `c`-convex with respect to the source and the source to be `c`-convex with
respect to the target for the swapped cost `fun z ↦ c z.swap`.

## Main definitions

* `TauCeti.cExp c V x p` — the `c`-exponential: the point of `V` with momentum `p` at `x`;
* `TauCeti.cSegment c V x y₀ y₁ t` — the `c`-segment from `y₀` to `y₁` seen from `x`;
* `TauCeti.IsCConvexSet c U V` — the set `V` is `c`-convex with respect to `U`.

## Main statements

* `TauCeti.neg_fderiv_cExp` and `TauCeti.cExp_neg_fderiv` — the `c`-exponential is a right
  inverse of the momentum map on its image, and, for a twisted cost, a left inverse on `V`;
* `TauCeti.hasStrictFDerivAt_cExp` — the derivative of the `c`-exponential of a twisted
  nondegenerate cost is minus the inverse of the mixed derivative;
* `TauCeti.eq_cExp_of_mem_contactSet` — a contact partner `y ∈ V` of `x` is
  `cExp c V x (-D φ (x))`;
* `TauCeti.IsDualCertificate.ae_eq_cExp` — a certified plan of a twisted cost is concentrated on
  the graph of `x ↦ cExp c V x (-D φ (x))`;
* `TauCeti.IsCConvexSet.cSegment_mem` and `TauCeti.IsCConvexSet.neg_fderiv_cSegment` — the
  `c`-segments of a `c`-convex set stay in it, with linearly interpolated momenta;
* `TauCeti.cExp_norm_sub_sq_div_two`, `TauCeti.cSegment_norm_sub_sq_div_two` and
  `TauCeti.isCConvexSet_norm_sub_sq_div_two_iff` — for the quadratic cost, the `c`-exponential
  is `x + p`, `c`-segments are segments, and `c`-convexity is convexity;
* `TauCeti.cExp_sqrt_one_add_norm_sub_sq` — for the cost `√(1 + ‖x - y‖ ^ 2)`, the
  `c`-exponential of a momentum `q` with `‖q‖ < 1` is `x + q / √(1 - ‖q‖ ^ 2)` whenever that
  point lies in `V`.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 10 for
  the `c`-exponential and Chapter 12 for `c`-segments and `c`-convex sets.
* X.-N. Ma, N. S. Trudinger and X.-J. Wang, *Regularity of potential functions of the optimal
  transportation problem*, Arch. Ration. Mech. Anal. 177 (2005), 151--183.
* G. Loeper, *On the regularity of solutions of optimal transportation problems*, Acta Math.
  202 (2009), 241--283.
-/

public section

noncomputable section

open Set Filter Function MeasureTheory
open scoped Topology

namespace TauCeti

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Convex

variable {c : E × Y → ℝ} {U : Set E} {V : Set Y} {x : E} {y₀ y₁ : Y} {t : ℝ}

/-- A target set `V` is **`c`-convex with respect to** a source set `U` when, for every `x ∈ U`,
the momenta `-Dₓ c (x, y)` of the points `y ∈ V` form a convex set. Source `c`-convexity of `U`
with respect to `V` is this condition for the swapped cost `fun z ↦ c z.swap`. -/
def IsCConvexSet (c : E × Y → ℝ) (U : Set E) (V : Set Y) : Prop :=
  ∀ x ∈ U, Convex ℝ ((fun y ↦ -fderiv ℝ (fun x' ↦ c (x', y)) x) '' V)

theorem isCConvexSet_iff : IsCConvexSet c U V ↔
    ∀ x ∈ U, Convex ℝ ((fun y ↦ -fderiv ℝ (fun x' ↦ c (x', y)) x) '' V) :=
  Iff.rfl

theorem IsCConvexSet.convex (hV : IsCConvexSet c U V) (hx : x ∈ U) :
    Convex ℝ ((fun y ↦ -fderiv ℝ (fun x' ↦ c (x', y)) x) '' V) :=
  hV x hx

theorem IsCConvexSet.mono {U' : Set E} (hV : IsCConvexSet c U V) (hU : U' ⊆ U) :
    IsCConvexSet c U' V :=
  fun x hx ↦ hV x (hU hx)

/-- In a `c`-convex set, convex combinations of momenta are momenta. -/
theorem IsCConvexSet.add_smul_mem_image (hV : IsCConvexSet c U V) (hx : x ∈ U) (hy₀ : y₀ ∈ V)
    (hy₁ : y₁ ∈ V) (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) • -fderiv ℝ (fun x' ↦ c (x', y₀)) x + t • -fderiv ℝ (fun x' ↦ c (x', y₁)) x ∈
      (fun y ↦ -fderiv ℝ (fun x' ↦ c (x', y)) x) '' V :=
  hV x hx (mem_image_of_mem _ hy₀) (mem_image_of_mem _ hy₁) (sub_nonneg.2 ht.2) ht.1
    (sub_add_cancel 1 t)

end Convex

section Exponential

variable [Nonempty Y] {c : E × Y → ℝ} {U : Set E} {V : Set Y} {x : E} {p : StrongDual ℝ E}
  {y y₀ y₁ : Y} {t : ℝ}

/-- The **`c`-exponential** of a cost `c` with respect to a target set `V`: the point of `V` whose
momentum `-Dₓ c (x, y)` at the source point `x` is `p`. It is specified only when `p` is the
momentum of some point of `V`, and it is that point when the cost is twisted on `V`. -/
def cExp (c : E × Y → ℝ) (V : Set Y) (x : E) (p : StrongDual ℝ E) : Y :=
  invFunOn (fun y ↦ -fderiv ℝ (fun x' ↦ c (x', y)) x) V p

theorem cExp_def :
    cExp c V x p = invFunOn (fun y ↦ -fderiv ℝ (fun x' ↦ c (x', y)) x) V p :=
  (rfl)

/-- The `c`-exponential of the momentum of a point of `V` lies in `V`. -/
theorem cExp_mem (hp : p ∈ (fun y ↦ -fderiv ℝ (fun x' ↦ c (x', y)) x) '' V) :
    cExp c V x p ∈ V :=
  invFunOn_mem hp

/-- The momentum of `cExp c V x p` at `x` is `p`, when `p` is the momentum of a point of `V`. -/
@[simp]
theorem neg_fderiv_cExp (hp : p ∈ (fun y ↦ -fderiv ℝ (fun x' ↦ c (x', y)) x) '' V) :
    -fderiv ℝ (fun x' ↦ c (x', cExp c V x p)) x = p :=
  invFunOn_eq hp

/-- For a cost twisted on `V` at `x`, the `c`-exponential recovers a point of `V` from its
momentum. -/
@[simp]
theorem cExp_neg_fderiv (htw : InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) V) (hy : y ∈ V) :
    cExp c V x (-fderiv ℝ (fun x' ↦ c (x', y)) x) = y :=
  (neg_injective.comp_injOn htw).leftInvOn_invFunOn hy

/-- For a cost twisted on `V` at `x`, the `c`-exponential of a momentum of a point of `V` is the
unique point of `V` with that momentum. -/
theorem cExp_eq_iff (htw : InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) V) (hy : y ∈ V)
    (hp : p ∈ (fun y ↦ -fderiv ℝ (fun x' ↦ c (x', y)) x) '' V) :
    cExp c V x p = y ↔ -fderiv ℝ (fun x' ↦ c (x', y)) x = p := by
  constructor
  · rintro rfl
    exact neg_fderiv_cExp hp
  · rintro rfl
    exact cExp_neg_fderiv htw hy

/-! ### Contact partners -/

/-- **Contact partners are given by the `c`-exponential.** Let the dual constraint
`φ x' + ψ y ≤ c (x', y)` hold for `x'` near `x`, with equality at `x`, and let `φ` be finite near
`x` and differentiable at `x`. If the cost section `c (·, y)` is differentiable at `x` and the cost
is twisted on a set `V ∋ y` at `x`, then `y = cExp c V x (-D φ (x))`. -/
theorem eq_cExp_of_mem_contactSet {φ : E → EReal} {ψ : Y → EReal}
    (hfeas : ∀ᶠ x' in 𝓝 x, φ x' + ψ y ≤ (c (x', y) : EReal))
    (hfin : ∀ᶠ x' in 𝓝 x, φ x' ≠ ⊥) (hxy : (x, y) ∈ contactSet c φ ψ)
    (hφ : DifferentiableAt ℝ (fun x' ↦ (φ x').toReal) x)
    (hc : DifferentiableAt ℝ (fun x' ↦ c (x', y)) x)
    (htw : InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) V) (hy : y ∈ V) :
    y = cExp c V x (-fderiv ℝ (fun x' ↦ (φ x').toReal) x) := by
  rw [fderiv_eq_of_mem_contactSet hfeas hfin hxy hφ hc, cExp_neg_fderiv htw hy]

/-- **A certified plan is concentrated on the graph of the `c`-exponential map.** Let a coupling
`π` of `μ` and `ν` be certified by real potentials `φ`, `ψ` for a nonnegative cost, let `ν` be
carried by a set `V`, and, for `μ`-almost every `x`, let the potential `φ` be differentiable at `x`,
the cost sections of the contact partners of `x` in `V` be differentiable at `x`, and the cost be
twisted on `V` at `x`. Then `π`-almost every pair `(x, y)` satisfies
`y = cExp c V x (-D φ (x))`. -/
theorem IsDualCertificate.ae_eq_cExp [MeasurableSpace E] [MeasurableSpace Y] {μ : Measure E}
    {ν : Measure Y} {π : Measure (E × Y)} {φ : E → ℝ} {ψ : Y → ℝ} (hc₀ : ∀ z, 0 ≤ c z)
    (h : IsDualCertificate (fun z ↦ ENNReal.ofReal (c z)) π μ ν φ ψ) (hV : ∀ᵐ y ∂ν, y ∈ V)
    (hφ : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x)
    (hc : ∀ᵐ x ∂μ, ∀ y ∈ V, (x, y) ∈ contactSet c (fun x ↦ (φ x : EReal))
      (fun y ↦ (ψ y : EReal)) → DifferentiableAt ℝ (fun x' ↦ c (x', y)) x)
    (htw : ∀ᵐ x ∂μ, InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) V) :
    ∀ᵐ z ∂π, z.2 = cExp c V z.1 (-fderiv ℝ φ z.1) := by
  have hfst {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) : ∀ᵐ z ∂π, P z.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (by rwa [← Measure.fst, h.fst_eq])
  have hsnd : ∀ᵐ z ∂π, z.2 ∈ V :=
    ae_of_ae_map measurable_snd.aemeasurable (by rwa [← Measure.snd, h.snd_eq])
  have hcontact : ∀ᵐ z ∂π, z ∈ contactSet c (fun x ↦ (φ x : EReal)) (fun y ↦ (ψ y : EReal)) := by
    simpa only [← dualContactSet_ofReal hc₀] using h.ae_mem_dualContactSet
  have hfeas (x' : E) (y : Y) : (φ x' : EReal) + (ψ y : EReal) ≤ (c (x', y) : EReal) := by
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    exact (dualFeasible_ofReal_iff hc₀ φ ψ).1 h.dualFeasible x' y
  filter_upwards [hfst hφ, hfst hc, hfst htw, hsnd, hcontact] with z hφz hcz htwz hz hzc
  simpa using eq_cExp_of_mem_contactSet (.of_forall fun x' ↦ hfeas x' z.2)
    (.of_forall fun _ ↦ EReal.coe_ne_bot _) hzc (by simpa using hφz) (hcz z.2 hz hzc) htwz hz

/-! ### `c`-segments and `c`-convex sets -/

/-- The **`c`-segment** from `y₀` to `y₁` seen from `x`, at time `t`: the `c`-exponential of the
convex combination `(1 - t) • p₀ + t • p₁` of the momenta of `y₀` and `y₁` at `x`. -/
def cSegment (c : E × Y → ℝ) (V : Set Y) (x : E) (y₀ y₁ : Y) (t : ℝ) : Y :=
  cExp c V x ((1 - t) • -fderiv ℝ (fun x' ↦ c (x', y₀)) x + t • -fderiv ℝ (fun x' ↦ c (x', y₁)) x)

theorem cSegment_def : cSegment c V x y₀ y₁ t =
    cExp c V x ((1 - t) • -fderiv ℝ (fun x' ↦ c (x', y₀)) x +
      t • -fderiv ℝ (fun x' ↦ c (x', y₁)) x) :=
  (rfl)

/-- For a cost twisted on `V` at `x`, the `c`-segment from a point `y₀ ∈ V` starts at `y₀`. -/
@[simp]
theorem cSegment_zero (htw : InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) V) (hy₀ : y₀ ∈ V) :
    cSegment c V x y₀ y₁ 0 = y₀ := by
  simpa [cSegment_def] using cExp_neg_fderiv htw hy₀

/-- For a cost twisted on `V` at `x`, the `c`-segment to a point `y₁ ∈ V` ends at `y₁`. -/
@[simp]
theorem cSegment_one (htw : InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) V) (hy₁ : y₁ ∈ V) :
    cSegment c V x y₀ y₁ 1 = y₁ := by
  simpa [cSegment_def] using cExp_neg_fderiv htw hy₁

/-- The `c`-segments between points of a `c`-convex set stay in the set. -/
theorem IsCConvexSet.cSegment_mem (hV : IsCConvexSet c U V) (hx : x ∈ U) (hy₀ : y₀ ∈ V)
    (hy₁ : y₁ ∈ V) (ht : t ∈ Icc (0 : ℝ) 1) : cSegment c V x y₀ y₁ t ∈ V :=
  cExp_mem (hV.add_smul_mem_image hx hy₀ hy₁ ht)

/-- Along a `c`-segment between points of a `c`-convex set, the momentum interpolates linearly
between the momenta of the endpoints. -/
theorem IsCConvexSet.neg_fderiv_cSegment (hV : IsCConvexSet c U V) (hx : x ∈ U) (hy₀ : y₀ ∈ V)
    (hy₁ : y₁ ∈ V) (ht : t ∈ Icc (0 : ℝ) 1) :
    -fderiv ℝ (fun x' ↦ c (x', cSegment c V x y₀ y₁ t)) x =
      (1 - t) • -fderiv ℝ (fun x' ↦ c (x', y₀)) x + t • -fderiv ℝ (fun x' ↦ c (x', y₁)) x :=
  neg_fderiv_cExp (hV.add_smul_mem_image hx hy₀ hy₁ ht)

/-- For a cost twisted on a `c`-convex set `V`, the point of a `c`-segment at time `t ∈ [0, 1]` is
the unique point of `V` whose momentum is the corresponding convex combination of the momenta of
the endpoints. -/
theorem IsCConvexSet.cSegment_eq_iff (hV : IsCConvexSet c U V) (hx : x ∈ U)
    (htw : InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) V) (hy₀ : y₀ ∈ V) (hy₁ : y₁ ∈ V)
    (ht : t ∈ Icc (0 : ℝ) 1) (hy : y ∈ V) :
    cSegment c V x y₀ y₁ t = y ↔ -fderiv ℝ (fun x' ↦ c (x', y)) x =
      (1 - t) • -fderiv ℝ (fun x' ↦ c (x', y₀)) x + t • -fderiv ℝ (fun x' ↦ c (x', y₁)) x :=
  cExp_eq_iff htw hy (hV.add_smul_mem_image hx hy₀ hy₁ ht)

end Exponential

/-! ### Differentiability of the `c`-exponential -/

section Nondegenerate

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {c : E × F → ℝ} {V : Set F} {x : E} {y : F}

/-- **The derivative of the `c`-exponential.** Let the cost be twisted on `V` at `x`, let `y` be an
interior point of `V`, and let the cost be *nondegenerate* at `(x, y)`: the map
`y' ↦ Dₓ c (x, y')` is strictly differentiable at `y`, with derivative an isomorphism `L`, the
mixed derivative `D²ₓᵧ c (x, y)`. Then the `c`-exponential is strictly differentiable at the
momentum `-Dₓ c (x, y)` of `y`, with derivative `-L⁻¹`. -/
theorem hasStrictFDerivAt_cExp (htw : InjOn (fun y ↦ fderiv ℝ (fun x' ↦ c (x', y)) x) V)
    (hV : V ∈ 𝓝 y) {L : F ≃L[ℝ] StrongDual ℝ E}
    (hL : HasStrictFDerivAt (fun y' ↦ fderiv ℝ (fun x' ↦ c (x', y')) x)
      (L : F →L[ℝ] StrongDual ℝ E) y) :
    HasStrictFDerivAt (cExp c V x) (-(L.symm : StrongDual ℝ E →L[ℝ] F))
      (-fderiv ℝ (fun x' ↦ c (x', y)) x) := by
  have hneg : HasStrictFDerivAt (fun y' ↦ -fderiv ℝ (fun x' ↦ c (x', y')) x)
      ((L.trans (ContinuousLinearEquiv.neg ℝ) : F ≃L[ℝ] StrongDual ℝ E) :
        F →L[ℝ] StrongDual ℝ E) y :=
    hL.neg.congr_fderiv (by ext; simp)
  exact (hneg.to_local_left_inverse (eventually_of_mem hV fun y' hy' ↦
    cExp_neg_fderiv htw hy')).congr_fderiv (by ext; simp)

end Nondegenerate

/-! ### The quadratic cost -/

section Quadratic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- For the quadratic cost `‖x - y‖ ^ 2 / 2` on a real Hilbert space, the `c`-exponential with
respect to the whole space is `x + p`, where `p` is identified with a vector by the Riesz
isomorphism. -/
theorem cExp_norm_sub_sq_div_two [CompleteSpace F] (x : F) (p : StrongDual ℝ F) :
    cExp (fun z : F × F ↦ ‖z.1 - z.2‖ ^ 2 / 2) univ x p =
      x + (InnerProductSpace.toDual ℝ F).symm p := by
  have hp : -fderiv ℝ (fun x' ↦ ‖x' - (x + (InnerProductSpace.toDual ℝ F).symm p)‖ ^ 2 / 2) x
      = p := by
    ext v
    simp [fderiv_norm_sub_sq_div_two]
  exact (cExp_eq_iff (fderiv_norm_sub_sq_div_two_injective x).injOn (mem_univ _)
    ⟨_, mem_univ _, hp⟩).2 hp

/-- For the quadratic cost `‖x - y‖ ^ 2 / 2` on a real inner product space, `c`-segments are
segments: the `c`-segment from `y₀` to `y₁` seen from any `x` is `t ↦ (1 - t) • y₀ + t • y₁`. -/
theorem cSegment_norm_sub_sq_div_two (x y₀ y₁ : F) (t : ℝ) :
    cSegment (fun z : F × F ↦ ‖z.1 - z.2‖ ^ 2 / 2) univ x y₀ y₁ t = (1 - t) • y₀ + t • y₁ := by
  have hp : -fderiv ℝ (fun x' ↦ ‖x' - ((1 - t) • y₀ + t • y₁)‖ ^ 2 / 2) x =
      (1 - t) • -fderiv ℝ (fun x' ↦ ‖x' - y₀‖ ^ 2 / 2) x +
        t • -fderiv ℝ (fun x' ↦ ‖x' - y₁‖ ^ 2 / 2) x := by
    ext v
    simp [fderiv_norm_sub_sq_div_two]
    ring
  exact (cExp_eq_iff (fderiv_norm_sub_sq_div_two_injective x).injOn (mem_univ _)
    ⟨_, mem_univ _, hp⟩).2 hp

/-- For the quadratic cost `‖x - y‖ ^ 2 / 2` on a real inner product space, `c`-convexity with
respect to a nonempty source set is convexity. -/
theorem isCConvexSet_norm_sub_sq_div_two_iff {U V : Set F} (hU : U.Nonempty) :
    IsCConvexSet (fun z : F × F ↦ ‖z.1 - z.2‖ ^ 2 / 2) U V ↔ Convex ℝ V := by
  -- At `x`, the momentum of `y` is the affine injective function `y ↦ ⟪y - x, ·⟫` of `y`.
  let A (x : F) : F →ᵃ[ℝ] StrongDual ℝ F :=
    (innerSL ℝ : F →L[ℝ] StrongDual ℝ F).toLinearMap.toAffineMap -
      AffineMap.const ℝ F (innerSL ℝ x)
  have hA (x : F) : (fun y ↦ -fderiv ℝ (fun x' ↦ ‖x' - y‖ ^ 2 / 2) x) = A x := by
    ext y v
    simp [A, fderiv_norm_sub_sq_div_two]
  have hAinj (x : F) : Injective (A x) := by
    intro y₁ y₂ h
    simpa [A] using h
  simp only [isCConvexSet_iff, hA]
  refine ⟨fun h ↦ ?_, fun h x _ ↦ h.affine_image (A x)⟩
  obtain ⟨x, hx⟩ := hU
  simpa only [preimage_image_eq _ (hAinj x)] using (h x hx).affine_preimage (A x)

end Quadratic

/-! ### The cost `√(1 + ‖x - y‖ ^ 2)` -/

section SqrtOneAddNormSubSq

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **The `c`-exponential of `√(1 + ‖x - y‖ ^ 2)`.** A momentum `q` with `‖q‖ < 1` is the
momentum at `x` of `x + q / √(1 - ‖q‖ ^ 2)`, where `q` is identified with a vector by the Riesz
isomorphism; when this point lies in `V`, it is the `c`-exponential of `q` with respect to `V`. -/
theorem cExp_sqrt_one_add_norm_sub_sq {V : Set F} {x : F} {q : StrongDual ℝ F} (hq : ‖q‖ < 1)
    (hV : x + OpenPartialHomeomorph.univUnitBall.symm ((InnerProductSpace.toDual ℝ F).symm q) ∈ V) :
    cExp (fun z : F × F ↦ √(1 + ‖z.1 - z.2‖ ^ 2)) V x q =
      x + OpenPartialHomeomorph.univUnitBall.symm ((InnerProductSpace.toDual ℝ F).symm q) := by
  have hmom : -fderiv ℝ (fun x' ↦ √(1 + ‖x' - (x + OpenPartialHomeomorph.univUnitBall.symm
      ((InnerProductSpace.toDual ℝ F).symm q))‖ ^ 2)) x = q := by
    apply (InnerProductSpace.toDual ℝ F).symm.injective
    rw [toDual_symm_neg_fderiv_sqrt_one_add_norm_sub_sq, add_sub_cancel_left,
      OpenPartialHomeomorph.univUnitBall.right_inv
        (by simpa [OpenPartialHomeomorph.univUnitBall_target] using hq)]
  exact (cExp_eq_iff (fderiv_sqrt_one_add_norm_sub_sq_injective x).injOn hV ⟨_, hV, hmom⟩).2 hmom

end SqrtOneAddNormSubSq

end TauCeti
