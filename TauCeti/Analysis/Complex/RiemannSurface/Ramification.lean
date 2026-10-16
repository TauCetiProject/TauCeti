/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor
public import Mathlib.Topology.DiscreteSubset

/-!
# The ramification divisor of a finite holomorphic map

Let `f : X → Y` be a finite holomorphic map of Riemann surfaces with `X` connected. Its local
multiplicity `e_x = localMultiplicity f x` is at least `1` everywhere, and `x` is a
*ramification point* when `e_x > 1`. Near every point of `X` the map has multiplicity `1` at all
other points (`TauCeti.RiemannSurface.eventually_localMultiplicity_eq_one`), so the ramification
points form a codiscrete complement; when `X` is moreover compact there are only finitely many of
them. The **ramification divisor** is the effective divisor

`R_f = ∑ₓ (e_x - 1) [x]`

on `X`, and the **ramification degree** is its degree `∑ₓ (e_x - 1)`, the correction term in
the Riemann–Hurwitz formula `2 g_X - 2 = deg f · (2 g_Y - 2) + deg R_f`.

Over each point `y` of a connected target, the fibre has `deg f - ∑_{x ∈ f⁻¹(y)} (e_x - 1)`
points; equivalently, the pushforward of `R_f` to `Y` has coefficient `deg f - #f⁻¹(y)` at `y`.
This is the count of missing sheets over the branch points that enters the Euler-characteristic
form of Riemann–Hurwitz. The ramification divisor of a composite satisfies the chain rule
`R_{g ∘ f} = R_f + f^* R_g`, so ramification degrees satisfy
`deg R_{g ∘ f} = deg R_f + deg f · deg R_g`.

## Main declarations

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.eventually_codiscrete_localMultiplicity_eq_one`
  and `TauCeti.RiemannSurface.FiniteHolomorphicMap.finite_setOf_one_lt_localMultiplicity`: the
  ramification points of a finite holomorphic map are isolated, and finite on a compact source.
* `TauCeti.RiemannSurface.ramificationDivisor`: the ramification divisor, with its coefficients
  `TauCeti.RiemannSurface.coeff_ramificationDivisor` and its support
  `TauCeti.RiemannSurface.support_ramificationDivisor`.
* `TauCeti.RiemannSurface.ramificationDegree`: the ramification degree, and
  `TauCeti.RiemannSurface.degree_ramificationDivisor`: it is the degree of the ramification
  divisor.
* `TauCeti.RiemannSurface.card_fiber_add_sum_localMultiplicity_sub_one` and
  `TauCeti.RiemannSurface.coeff_pushforward_ramificationDivisor`: the fibre count.
* `TauCeti.RiemannSurface.ramificationDivisor_comp` and
  `TauCeti.RiemannSurface.ramificationDegree_comp`: the chain rule for composites.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17 (the total branching order and the Riemann–Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4 (ramification and branch points, Hurwitz's
  formula).
-/

public noncomputable section

open Filter Function Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry

variable {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- The **ramification degree** of a map `f : X → Y` of Riemann surfaces: the sum of
`localMultiplicity f x - 1` over all points `x`. For a finite holomorphic map from a compact
connected Riemann surface the sum is finite and is the degree of the ramification divisor
(`TauCeti.RiemannSurface.degree_ramificationDivisor`); by the convention for `finsum`, it is `0`
when infinitely many points have local multiplicity at least `2`. -/
def ramificationDegree (f : X → Y) : ℕ := ∑ᶠ x, (localMultiplicity f x - 1)

theorem ramificationDegree_def (f : X → Y) :
    ramificationDegree f = ∑ᶠ x, (localMultiplicity f x - 1) :=
  (rfl)

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] [PreconnectedSpace X]

/-- The ramification points of a finite holomorphic map from a connected Riemann surface are
isolated: the local multiplicity is `1` away from a closed discrete set. -/
theorem FiniteHolomorphicMap.eventually_codiscrete_localMultiplicity_eq_one
    (f : FiniteHolomorphicMap X Y) : ∀ᶠ x in codiscrete X, localMultiplicity f x = 1 :=
  eventually_codiscrete_iff_forall_eventually_nhdsNE.2 fun x ↦
    eventually_localMultiplicity_eq_one (.of_forall fun y ↦ f.holomorphic y)
      (f.not_eventuallyConst x)

/-- A finite holomorphic map from a compact connected Riemann surface has only finitely many
ramification points. -/
theorem FiniteHolomorphicMap.finite_setOf_one_lt_localMultiplicity [CompactSpace X]
    (f : FiniteHolomorphicMap X Y) : {x | 1 < localMultiplicity f x}.Finite :=
  (Filter.eventually_cofinite.1
    (cofinite_le_codiscrete f.eventually_codiscrete_localMultiplicity_eq_one)).subset
    fun _ hx ↦ hx.ne'

/-- For a finite holomorphic map from a connected Riemann surface, `e_x - 1` vanishes exactly at
the unramified points. -/
private theorem intCast_localMultiplicity_sub_one_ne_zero_iff (f : FiniteHolomorphicMap X Y)
    (x : X) : (localMultiplicity f x : ℤ) - 1 ≠ 0 ↔ 1 < localMultiplicity f x := by
  rw [ne_eq, sub_eq_zero, Nat.cast_eq_one]
  exact ⟨fun h ↦ Nat.lt_of_le_of_ne (localMultiplicity_pos f x) (Ne.symm h), fun h ↦ h.ne'⟩

variable [CompactSpace X]

/-- The **ramification divisor** `∑ₓ (e_x - 1) [x]` of a finite holomorphic map from a compact
connected Riemann surface, where `e_x` is the local multiplicity at `x`. Its support is the finite
set of ramification points (`TauCeti.RiemannSurface.support_ramificationDivisor`). -/
def ramificationDivisor (f : FiniteHolomorphicMap X Y) : WeilDivisor X :=
  Finsupp.ofSupportFinite (fun x ↦ (localMultiplicity f x : ℤ) - 1) <|
    f.finite_setOf_one_lt_localMultiplicity.subset fun x hx ↦
      (intCast_localMultiplicity_sub_one_ne_zero_iff f x).1 hx

/-- The coefficient of the ramification divisor at `x` is the local multiplicity minus one. -/
@[simp]
theorem coeff_ramificationDivisor (f : FiniteHolomorphicMap X Y) (x : X) :
    WeilDivisor.coeff (ramificationDivisor f) x = (localMultiplicity f x : ℤ) - 1 :=
  (rfl)

/-- The ramification divisor is effective. -/
theorem isEffective_ramificationDivisor (f : FiniteHolomorphicMap X Y) :
    WeilDivisor.IsEffective (ramificationDivisor f) := by
  rw [WeilDivisor.isEffective_iff]
  intro x
  rw [coeff_ramificationDivisor, sub_nonneg, Nat.one_le_cast]
  exact localMultiplicity_pos f x

/-- The support of the ramification divisor is the set of ramification points. -/
@[simp]
theorem support_ramificationDivisor (f : FiniteHolomorphicMap X Y) :
    ↑(ramificationDivisor f).support = {x | 1 < localMultiplicity f x} := by
  ext x
  rw [Finset.mem_coe, WeilDivisor.mem_support_iff, coeff_ramificationDivisor]
  exact intCast_localMultiplicity_sub_one_ne_zero_iff f x

/-- A finite holomorphic map is unramified, that is, has local multiplicity `1` everywhere,
exactly when its ramification divisor vanishes. -/
theorem ramificationDivisor_eq_zero_iff (f : FiniteHolomorphicMap X Y) :
    ramificationDivisor f = 0 ↔ ∀ x, localMultiplicity f x = 1 := by
  refine ⟨fun h x ↦ ?_, fun h ↦ WeilDivisor.ext fun x ↦ ?_⟩
  · have hx := WeilDivisor.coeff_zero x ▸ congrArg (WeilDivisor.coeff · x) h
    rw [coeff_ramificationDivisor, sub_eq_zero, Nat.cast_eq_one] at hx
    exact hx
  · rw [coeff_ramificationDivisor, h, WeilDivisor.coeff_zero, Nat.cast_one, sub_self]

/-- The ramification degree of a finite holomorphic map from a compact connected Riemann surface
is the degree of its ramification divisor. -/
@[simp]
theorem degree_ramificationDivisor (f : FiniteHolomorphicMap X Y) :
    WeilDivisor.degree (ramificationDivisor f) = ramificationDegree f := by
  classical
  rw [WeilDivisor.degree_apply, ramificationDegree_def,
    finsum_eq_sum_of_support_subset (s := (ramificationDivisor f).support), Nat.cast_sum]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [Nat.cast_sub (localMultiplicity_pos f x), Nat.cast_one]
    exact coeff_ramificationDivisor f x
  · intro x hx
    rw [support_ramificationDivisor]
    exact Nat.lt_of_sub_ne_zero hx

section Fiber

variable [T2Space X] [T2Space Y] [PreconnectedSpace Y]

/-- **The fibre count.** Over every point `y` of a connected target, the number of points of the
fibre plus the sum of `e_x - 1` over the fibre is the degree of a finite holomorphic map from a
compact connected Riemann surface. -/
theorem card_fiber_add_sum_localMultiplicity_sub_one (f : FiniteHolomorphicMap X Y) (y : Y) :
    (f.finite_fiber y).toFinset.card +
        ∑ x ∈ (f.finite_fiber y).toFinset, (localMultiplicity f x - 1) = degree f := by
  rw [degree_eq_fiber_sum f y, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ ↦ Nat.add_sub_of_le (localMultiplicity_pos f x)

/-- The pushforward of the ramification divisor has coefficient `deg f - #f⁻¹(y)` at `y`: it
counts the sheets of `f` that come together over `y`. -/
theorem coeff_pushforward_ramificationDivisor (f : FiniteHolomorphicMap X Y) (y : Y) :
    WeilDivisor.coeff (WeilDivisor.pushforward f (ramificationDivisor f)) y =
      (degree f : ℤ) - (f.finite_fiber y).toFinset.card := by
  classical
  rw [← card_fiber_add_sum_localMultiplicity_sub_one f y, WeilDivisor.coeff_pushforward]
  push_cast
  rw [add_sub_cancel_left]
  -- Both sums run over the fibre: the ramification divisor vanishes at its unramified points.
  refine Finset.sum_subset_zero_on_sdiff (fun x hx ↦ ?_) (fun x hx ↦ ?_) fun x _ ↦ ?_
  · exact (f.finite_fiber y).mem_toFinset.2 (Finset.mem_filter.1 hx).2
  · obtain ⟨hxf, hxR⟩ := Finset.mem_sdiff.1 hx
    have hfx : f x = y := (f.finite_fiber y).mem_toFinset.1 hxf
    have hx1 : ¬ 1 < localMultiplicity f x := fun h ↦ hxR <| Finset.mem_filter.2
      ⟨by rw [← Finset.mem_coe, support_ramificationDivisor]; exact h, hfx⟩
    rw [Nat.sub_eq_zero_of_le (not_lt.1 hx1), Nat.cast_zero]
  · rw [Nat.cast_sub (localMultiplicity_pos f x), Nat.cast_one]
    exact coeff_ramificationDivisor f x

end Fiber

section Comp

variable [IsManifold 𝓘(ℂ) 1 Z] [T2Space X] [T2Space Y] [PreconnectedSpace Y] [CompactSpace Y]

/-- **The chain rule for ramification divisors.** The ramification divisor of a composite of
finite holomorphic maps between compact connected Riemann surfaces is `R_{g ∘ f} = R_f + f^* R_g`:
at `x` this is `e_g e_f - 1 = (e_f - 1) + e_f (e_g - 1)`. -/
theorem ramificationDivisor_comp (g : FiniteHolomorphicMap Y Z) (f : FiniteHolomorphicMap X Y) :
    ramificationDivisor (g.comp f) =
      ramificationDivisor f + divisorPullback f (ramificationDivisor g) := by
  refine WeilDivisor.ext fun x ↦ ?_
  rw [WeilDivisor.coeff_add, coeff_ramificationDivisor, coeff_ramificationDivisor,
    coeff_divisorPullback, coeff_ramificationDivisor, localMultiplicity_comp]
  push_cast
  ring

/-- The ramification degree of a composite of finite holomorphic maps between compact connected
Riemann surfaces is `deg R_f + deg f · deg R_g`. -/
theorem ramificationDegree_comp (g : FiniteHolomorphicMap Y Z) (f : FiniteHolomorphicMap X Y) :
    ramificationDegree (g.comp f) = ramificationDegree f + degree f * ramificationDegree g := by
  have h := congrArg WeilDivisor.degree (ramificationDivisor_comp g f)
  rw [map_add, degree_divisorPullback, degree_ramificationDivisor, degree_ramificationDivisor,
    degree_ramificationDivisor] at h
  exact_mod_cast h

end Comp

end TauCeti.RiemannSurface

end
