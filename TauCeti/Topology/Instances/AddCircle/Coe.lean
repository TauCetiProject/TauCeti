/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Functions on an additive circle read on the underlying group

A function `g` on `AddCircle p` gives the function `t ↦ g t` on `𝕜` by composing with the quotient
map `𝕜 → AddCircle p`. This file records that this function is `p`-periodic, and continuous when
`g` is, and that continuous maps on `AddCircle p` agreeing at every element of `𝕜` are equal.
Conversely, the descent of a continuous periodic function is continuous. A bijection of
`𝕜 × Y` commuting with the translation by `p` in the first coordinate
descends to a bijection of `AddCircle p × Y`, and a map of `AddCircle p × Y` with a continuous
lift to `𝕜 × Y` is continuous.

## Main results

* `TauCeti.AddCircle.periodic_comp_coe`: `t ↦ g t` is `p`-periodic.
* `TauCeti.AddCircle.continuous_comp_coe`: `t ↦ g t` is continuous for a continuous `g`.
* `TauCeti.AddCircle.continuousMap_ext_coe`: continuous maps on `AddCircle p` are determined by
  their values at elements of `𝕜`.
* `Function.Periodic.continuous_lift`: the descent of a continuous periodic function is continuous.
* `AddCircle.prodEquivOfLift`: the bijection of `AddCircle p × Y` induced by a bijection of
  `𝕜 × Y` that commutes with the translation by `p`.
* `AddCircle.continuous_prod_of_lift`: a map `AddCircle p × Y → AddCircle p × Y'` with a
  continuous lift `𝕜 × Y → 𝕜 × Y'` is continuous.
-/

public section

namespace TauCeti.AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] {p : 𝕜} {Y : Type*}

/-- A map on `AddCircle p`, regarded as a map on `𝕜`, is `p`-periodic. -/
theorem periodic_comp_coe (g : AddCircle p → Y) : Function.Periodic (fun t : 𝕜 => g t) p :=
  fun t => by simp only [AddCircle.coe_add_period]

variable [TopologicalSpace 𝕜] [TopologicalSpace Y]

/-- A continuous map on `AddCircle p`, regarded as a map on `𝕜`, is continuous. -/
theorem continuous_comp_coe (g : C(AddCircle p, Y)) : Continuous fun t : 𝕜 => g t :=
  g.continuous.comp (AddCircle.continuous_mk' p)

/-- Two continuous maps on `AddCircle p` are equal if they agree at every element of `𝕜`. -/
theorem continuousMap_ext_coe {g g' : C(AddCircle p, Y)} (h : ∀ t : 𝕜, g t = g' t) : g = g' :=
  ContinuousMap.ext <| QuotientAddGroup.mk_surjective.forall.2 h

end TauCeti.AddCircle

namespace Function.Periodic

variable {A X : Type*} [AddCommGroup A] [TopologicalSpace A] [TopologicalSpace X]
  {p : A} {f : A → X}

/-- The descent of a continuous periodic function to the additive circle is continuous. -/
theorem continuous_lift (hp : Periodic f p) (hf : Continuous f) : Continuous hp.lift :=
  (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
    (by simpa only [Function.comp_def, hp.lift_coe] using hf)

end Function.Periodic

namespace AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] {p : 𝕜} {Y : Type*}

/-- The inverse of a bijection `e` of `𝕜 × Y` that commutes with the translation by `p` in the
first coordinate commutes with it as well. -/
private theorem symm_add_period_of_lift (e : 𝕜 × Y ≃ 𝕜 × Y)
    (he : ∀ (x : 𝕜) y, e (x + p, y) = ((e (x, y)).1 + p, (e (x, y)).2)) (x : 𝕜) (y : Y) :
    e.symm (x + p, y) = ((e.symm (x, y)).1 + p, (e.symm (x, y)).2) :=
  e.symm_apply_eq.2 (by rw [he, Prod.mk.eta, e.apply_symm_apply])

/-- If a map `g` of `𝕜 × Y` commutes with the translation by `p` in the first coordinate, then for
each `y` the class of `g (x, y)` in `AddCircle p × Y` is `p`-periodic in `x`. -/
private theorem periodic_prod_of_lift {g : 𝕜 × Y → 𝕜 × Y}
    (hg : ∀ (x : 𝕜) y, g (x + p, y) = ((g (x, y)).1 + p, (g (x, y)).2)) (y : Y) :
    Function.Periodic (fun x : 𝕜 ↦ (((g (x, y)).1 : AddCircle p), (g (x, y)).2)) p := fun x ↦ by
  simp [hg]

/-- A bijection `e` of `𝕜 × Y` that commutes with the translation by `p` in the first coordinate
descends to a bijection of `AddCircle p × Y` (`AddCircle.prodEquivOfLift_coe`). -/
def prodEquivOfLift (e : 𝕜 × Y ≃ 𝕜 × Y)
    (he : ∀ (x : 𝕜) y, e (x + p, y) = ((e (x, y)).1 + p, (e (x, y)).2)) :
    AddCircle p × Y ≃ AddCircle p × Y where
  toFun x := (periodic_prod_of_lift he x.2).lift x.1
  invFun x := (periodic_prod_of_lift (symm_add_period_of_lift e he) x.2).lift x.1
  left_inv := by
    rintro ⟨θ, y⟩
    induction θ using QuotientAddGroup.induction_on with | H s => ?_
    simp
  right_inv := by
    rintro ⟨θ, y⟩
    induction θ using QuotientAddGroup.induction_on with | H s => ?_
    simp

/-- The bijection `prodEquivOfLift e` sends the class of `(x, y)` to the class of `e (x, y)`. -/
@[simp]
theorem prodEquivOfLift_coe (e : 𝕜 × Y ≃ 𝕜 × Y)
    (he : ∀ (x : 𝕜) y, e (x + p, y) = ((e (x, y)).1 + p, (e (x, y)).2)) (x : 𝕜) (y : Y) :
    prodEquivOfLift e he ((x : AddCircle p), y) = (((e (x, y)).1 : AddCircle p), (e (x, y)).2) := by
  simp [prodEquivOfLift]

/-- The inverse of `prodEquivOfLift e` sends the class of `(x, y)` to the class of
`e.symm (x, y)`. -/
@[simp]
theorem prodEquivOfLift_symm_coe (e : 𝕜 × Y ≃ 𝕜 × Y)
    (he : ∀ (x : 𝕜) y, e (x + p, y) = ((e (x, y)).1 + p, (e (x, y)).2)) (x : 𝕜) (y : Y) :
    (prodEquivOfLift e he).symm ((x : AddCircle p), y) =
      (((e.symm (x, y)).1 : AddCircle p), (e.symm (x, y)).2) := by
  simp [prodEquivOfLift]

/-- A map `AddCircle p × Y → AddCircle p × Y'` is continuous when it lifts along the projections
from `𝕜 × Y` and `𝕜 × Y'` to a continuous map `𝕜 × Y → 𝕜 × Y'`. -/
theorem continuous_prod_of_lift [TopologicalSpace 𝕜] [SeparatelyContinuousAdd 𝕜] {Y' : Type*}
    [TopologicalSpace Y] [TopologicalSpace Y'] {ψ : AddCircle p × Y → AddCircle p × Y'}
    {G : 𝕜 × Y → 𝕜 × Y'} (hG : Continuous G)
    (hψ : ∀ (x : 𝕜) y, ψ (x, y) = (((G (x, y)).1 : AddCircle p), (G (x, y)).2)) :
    Continuous ψ := by
  have hq : IsOpenQuotientMap (Prod.map ((↑) : 𝕜 → AddCircle p) (id : Y → Y)) :=
    QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id
  rw [← hq.continuous_comp_iff]
  convert (QuotientAddGroup.continuous_mk.prodMap continuous_id).comp hG using 1
  funext ⟨x, y⟩
  exact hψ x y

end AddCircle
