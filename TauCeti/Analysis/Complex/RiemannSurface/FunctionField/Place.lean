/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.PointSeparation
public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Map
public import TauCeti.FieldTheory.FunctionField.Place.OfAddValuation
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Fibre
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order

/-!
# The points of a compact Riemann surface are the places of its function field

Let `X` be a compact connected Riemann surface and `M(X)` its field of meromorphic functions. The
order `ord_x` of meromorphic functions at a point `x` is a discrete valuation of `M(X)`, trivial
on the constants `ℂ` and onto `ℤ` because some meromorphic function has a simple zero at `x`.
It is therefore a place of the field extension `M(X) / ℂ`, in the sense of algebraic function
fields (`TauCeti.Place`). This file proves that `x ↦ ord_x` is a bijection from the points of `X`
onto the places of `M(X) / ℂ`, and that it matches the analytic and the algebraic ramification
of a finite holomorphic map `β : X → ℙ¹`.

* Different points give different places, because meromorphic functions separate points.
* Every place is rational, since `M(X)` is an algebraic function field over the algebraically
  closed field `ℂ`.
* Along such a map `β`, with `ℂ(t)` acting on `M(X)` by pullback, the place at `x` lies over the
  place of `ℂ(t)` at `β x`, with ramification index the local multiplicity of `β` at `x`.
* Every place is the place at a point. On the sphere the places of `ℂ(t)` are known: the finite
  places `t - a` and the place at infinity, which are the places at the points `a` and `∞`. For
  general `X`, the places of `M(X)` over the place of `ℂ(t)` at `y` include the places at the `n`
  points of the fibre `β⁻¹(y)`, counted with ramification indices summing to `n = deg β`, while
  the fundamental inequality bounds the total by `[M(X) : ℂ(t)] = n`. So there is no room for
  another place.

## Main definitions

* `TauCeti.RiemannSurface.MeromorphicFunction.place`: the place `ord_x` of `M(X) / ℂ` at a point
  `x`.
* `TauCeti.RiemannSurface.MeromorphicFunction.placeEquiv`: the points of `X` are the places of
  `M(X) / ℂ`.

## Main results

* `TauCeti.RiemannSurface.MeromorphicFunction.place_injective` and
  `TauCeti.RiemannSurface.MeromorphicFunction.place_surjective`.
* `TauCeti.RiemannSurface.MeromorphicFunction.degree_place`: every place at a point is rational.
* `TauCeti.RiemannSurface.MeromorphicFunction.restrict_place` and
  `TauCeti.RiemannSurface.MeromorphicFunction.ramificationIdx_place`: the place at `x` lies over
  the place at `β x`, with ramification index the local multiplicity of `β` at `x`.
* `TauCeti.RiemannSurface.MeromorphicFunction.map_place_coe` and
  `TauCeti.RiemannSurface.MeromorphicFunction.map_place_infty`: on the sphere, the places at `a`
  and at `∞` are the places of `ℂ(t)` at `t - a` and at infinity.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, Springer, 1981, §8 (pullbacks of meromorphic
  functions and the degree of a covering) and Theorem 14.12 (functions with a single pole).
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.2 (the places of the rational function field) and Theorem 3.1.11 (the fundamental
  inequality).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, CUP, 2012, Remark 1.94 (compact Riemann surfaces and function
  fields of one variable over `ℂ`).
-/

public noncomputable section

open OnePoint TauCeti.AlgebraicGeometry
open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]

/-! ### The place at a point -/

/-- The **place at a point** `x` of a compact connected Riemann surface: the order `ord_x` of
meromorphic functions at `x`, a normalized discrete valuation of `M(X)` trivial on `ℂ`. -/
def place (x : X) : Place ℂ (MeromorphicFunction X) :=
  Place.ofAddValuation (order x) (order_surjective x) fun _ hc ↦ order_algebraMap hc

/-- The order function of the place at `x` is the order `ord_x`, read in `ℤ` with the junk value
`0` at the zero function. -/
@[simp]
theorem ord_place (x : X) (f : MeromorphicFunction X) :
    (place x).ord f = (order x f).untopD 0 :=
  Place.ord_ofAddValuation f

/-- For `f ≠ 0`, the order of `f` at the place at `x` is `ord_x f`. -/
theorem coe_ord_place (x : X) {f : MeromorphicFunction X} (hf : f ≠ 0) :
    ((place x).ord f : WithTop ℤ) = order x f :=
  Place.coe_ord_ofAddValuation hf

/-- A meromorphic function is integral at the place at `x` exactly when `x` is not a pole. -/
theorem mem_integers_place_iff {x : X} {f : MeromorphicFunction X} :
    f ∈ (place x).integers ↔ f x ≠ ∞ := by
  rw [place, Place.mem_integers_ofAddValuation_iff, order_nonneg_iff]

/-- The valuation of the place at `x` is at most `1` at `f` exactly when `x` is not a pole of
`f`. -/
@[simp]
theorem valuation_place_le_one_iff {x : X} {f : MeromorphicFunction X} :
    (place x).valuation f ≤ 1 ↔ f x ≠ ∞ := by
  rw [← Place.mem_integers_iff, mem_integers_place_iff]

/-- A nonzero meromorphic function has positive order at the place at `x` exactly when it
vanishes at `x`. -/
theorem ord_place_pos_iff {x : X} {f : MeromorphicFunction X} (hf : f ≠ 0) :
    0 < (place x).ord f ↔ f x = ((0 : ℂ) : OnePoint ℂ) := by
  rw [← WithTop.coe_lt_coe, coe_ord_place x hf, WithTop.coe_zero, order_pos_iff]

/-- A meromorphic function lies in the maximal ideal of the place at `x` exactly when it
vanishes at `x`. -/
theorem valuation_place_lt_one_iff {x : X} {f : MeromorphicFunction X} :
    (place x).valuation f < 1 ↔ f x = ((0 : ℂ) : OnePoint ℂ) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rw [Place.valuation_lt_one_iff_ord_pos _ hf, ord_place_pos_iff hf]

/-- **Different points give different places**, since meromorphic functions separate the points
of a compact connected Riemann surface. -/
theorem place_injective : Function.Injective (place (X := X)) :=
  fun _ _ h ↦ order_injective (Place.ofAddValuation_inj.mp h)

/-- Two points have the same place exactly when they are equal. -/
@[simp]
theorem place_inj {x y : X} : place x = place y ↔ x = y :=
  place_injective.eq_iff

/-- **The place at a point is rational**: its residue field is `ℂ`. -/
theorem degree_place (x : X) : (place x).degree = 1 :=
  (place x).degree_eq_one_of_isAlgClosed_of_isFunctionField isFunctionField

/-! ### Pullback along a finite holomorphic map to the sphere -/

section RatFunc

variable (β : FiniteHolomorphicMap X (OnePoint ℂ))
  [Algebra (RatFunc ℂ) (MeromorphicFunction X)]

/-- **The order of a pullback at a place.** At the place at `x`, the pullback along `β` of a
rational function `r` has order the local multiplicity of `β` at `x` times the order of `r` at
the place at `β x` of the sphere. -/
theorem ord_place_algebraMap
    (h : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
      ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom)
    (x : X) (r : RatFunc ℂ) :
    (place x).ord (algebraMap (RatFunc ℂ) (MeromorphicFunction X) r) =
      localMultiplicity β x * (place (β x)).ord (ratFuncEquiv r) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hpull : algebraMap (RatFunc ℂ) (MeromorphicFunction X) r =
      comap β β.holomorphic β.nonconstant (ratFuncEquiv r) := by
    simp [h, comapₐ_apply]
  rw [← WithTop.coe_inj, coe_ord_place x ((map_ne_zero _).mpr hr), WithTop.coe_mul,
    coe_ord_place (β x) ((map_ne_zero ratFuncEquiv).mpr hr), hpull, order_apply, order_apply,
    meromorphicOrderAt_finitePart_comap, mul_comm]
  norm_cast

variable [IsScalarTower ℂ (RatFunc ℂ) (MeromorphicFunction X)]
  [Algebra.IsIntegral (RatFunc ℂ) (MeromorphicFunction X)]

/-- **The place at `x` lies over the place at `β x`.** With `ℂ(t)` acting on `M(X)` by pullback
along `β`, and the places of `ℂ(t)` identified with those of the meromorphic functions on the
sphere, the place at `x` restricts to the place at `β x`. -/
theorem restrict_place
    (h : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
      ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom)
    (x : X) :
    (place x).restrict ℂ (RatFunc ℂ) = (place (β x)).map ratFuncEquiv.symm :=
  (Place.restrict_eq_iff_exists_ord_eq ℂ (RatFunc ℂ) (place x) _).mpr
    ⟨localMultiplicity β x, localMultiplicity_pos β x, fun r ↦ by
      rw [ord_place_algebraMap β h, Place.ord_map, AlgEquiv.symm_symm]⟩

/-- **Analytic and algebraic ramification agree.** With `ℂ(t)` acting on `M(X)` by pullback along
`β`, the ramification index of the place at `x` over `ℂ(t)` is the local multiplicity of `β` at
`x`. -/
theorem ramificationIdx_place
    (h : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
      ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom)
    (x : X) :
    Place.ramificationIdx (RatFunc ℂ) (place x) = localMultiplicity β x :=
  Place.ramificationIdx_eq_of_forall_ord_eq ℂ (RatFunc ℂ) (place x) fun r ↦ by
    rw [ord_place_algebraMap β h, restrict_place β h, Place.ord_map, AlgEquiv.symm_symm]

end RatFunc

/-! ### The places of the sphere -/

section Sphere

/-- The place at `∞` of the sphere is the place at infinity of `ℂ(t)`, at which the coordinate
has a pole. -/
theorem map_place_infty : (place (∞ : OnePoint ℂ)).map ratFuncEquiv.symm = Place.infty ℂ := by
  rw [← Place.X_notMem_integers_iff_eq_infty, Place.mem_integers_map_iff, AlgEquiv.symm_symm,
    ratFuncEquiv_X, mem_integers_place_iff, coordinate_apply, not_not]

/-- The place at a finite point `a` of the sphere is the place of `ℂ(t)` at `t - a`, at which
`t - a` vanishes. -/
theorem map_place_coe (a : ℂ) :
    (place (a : OnePoint ℂ)).map ratFuncEquiv.symm =
      Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a) := by
  have heq : ratFuncEquiv (RatFunc.X - RatFunc.C a) =
      coordinate - algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) a := by
    rw [map_sub, ratFuncEquiv_X, ← RatFunc.algebraMap_eq_C, AlgEquiv.commutes]
  have hne : coordinate - algebraMap ℂ (MeromorphicFunction (OnePoint ℂ)) a ≠ 0 := by
    refine sub_ne_zero.mpr fun hc ↦ OnePoint.coe_ne_infty a ?_
    simpa [coordinate_apply] using (congrArg (· ∞) hc).symm
  rw [← Place.ord_X_sub_C_pos_iff, Place.ord_map, AlgEquiv.symm_symm, heq, ord_place_pos_iff hne,
    sub_apply_of_eq_coe (coordinate_apply _) (by rw [coe_algebraMap]), sub_self]

/-- **Every place of `ℂ(t)` is the place at a point of the sphere**: at infinity if `t` has a
pole there, and otherwise at the value of `t` in the residue field `ℂ`. -/
theorem exists_map_place_eq (Q : Place ℂ (RatFunc ℂ)) :
    ∃ y : OnePoint ℂ, (place y).map ratFuncEquiv.symm = Q := by
  by_cases hX : RatFunc.X ∈ Q.integers
  · obtain ⟨a, ha⟩ := Q.degree_eq_one_iff_forall_exists_valuation_sub_lt_one.mp
      (Q.degree_eq_one_of_isAlgClosed_of_isFunctionField (IsFunctionField.ratFunc ℂ)) _ hX
    refine ⟨a, (map_place_coe a).trans (Place.ord_X_sub_C_pos_iff.mp ?_).symm⟩
    rw [RatFunc.algebraMap_eq_C] at ha
    exact (Q.valuation_lt_one_iff_ord_pos (RatFunc.X_sub_C_ne_zero a)).mp ha
  · exact ⟨∞, map_place_infty.trans (Place.X_notMem_integers_iff_eq_infty.mp hX).symm⟩

end Sphere

/-! ### Every place is the place at a point -/

/-- **Every place of `M(X) / ℂ` is the place at a point.** For a finite holomorphic map
`β : X → ℙ¹`, a place `P` of `M(X)` lies over the place of `ℂ(t)` at some `y`. The places at the
points of the fibre `β⁻¹(y)` also lie over it, with ramification indices summing to `deg β`, which
is the degree `[M(X) : ℂ(t)]`; by the fundamental inequality they are all the places over it. -/
theorem place_surjective : Function.Surjective (place (X := X)) := by
  classical
  intro P
  obtain ⟨β, -⟩ := exists_finiteHolomorphicMap_degree_le_analyticGenus_add_one (X := X)
  let := ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom.toAlgebra
  have := isScalarTower_ratFunc β rfl
  have := finiteDimensional_ratFunc β rfl
  obtain ⟨y, hy⟩ := exists_map_place_eq (P.restrict ℂ (RatFunc ℂ))
  by_contra hP
  have hPs : P ∉ (β.finite_fiber y).toFinset.image place := by
    simpa using fun x _ hx ↦ hP ⟨x, hx⟩
  -- The places at the points of the fibre, together with `P`, all lie over the place at `y`.
  have hle := Place.sum_ramificationIdx_mul_relativeDegree_le_finrank ℂ (RatFunc ℂ)
    (P.restrict ℂ (RatFunc ℂ)) (insert P ((β.finite_fiber y).toFinset.image place)) fun Q hQ ↦ by
      obtain rfl | hQ := Finset.mem_insert.mp hQ
      · rfl
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hQ
      rw [restrict_place β rfl, ← hy, (Set.Finite.mem_toFinset _).mp hx]
  rw [Finset.sum_insert hPs, Finset.sum_image place_injective.injOn,
    finrank_ratFunc_eq_degree β rfl, degree_eq_fiber_sum β y] at hle
  -- Each point of the fibre contributes at least its local multiplicity, and `P` at least `1`.
  have hfib : ∑ x ∈ (β.finite_fiber y).toFinset, localMultiplicity β x ≤
      ∑ x ∈ (β.finite_fiber y).toFinset, Place.ramificationIdx (RatFunc ℂ) (place x) *
        Place.relativeDegree ℂ (RatFunc ℂ) (place x) :=
    Finset.sum_le_sum fun x _ ↦ by
      rw [ramificationIdx_place β rfl]
      exact Nat.le_mul_of_pos_right _ (Place.one_le_relativeDegree ℂ (RatFunc ℂ) _)
  have hP1 := Nat.mul_le_mul (Place.ramificationIdx_pos (RatFunc ℂ) P)
    (Place.one_le_relativeDegree ℂ (RatFunc ℂ) P)
  omega

/-- **The points of a compact connected Riemann surface are the places of its function field**:
`x ↦ ord_x` is a bijection from `X` onto the places of `M(X) / ℂ`. -/
def placeEquiv : X ≃ Place ℂ (MeromorphicFunction X) :=
  Equiv.ofBijective place ⟨place_injective, place_surjective⟩

@[simp]
theorem placeEquiv_apply (x : X) : placeEquiv x = place x :=
  (rfl)

end TauCeti.RiemannSurface.MeromorphicFunction
