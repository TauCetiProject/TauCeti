/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.LaurentSeries
public import TauCeti.RingTheory.HahnSeries.Map
public import TauCeti.RingTheory.HahnSeries.PowerSeries

/-!
# Power series and Laurent series as functors of the coefficients

For a commutative ring `k`, the power series `R⟦X⟧` and the Laurent series `R⸨X⸩` over a
commutative `k`-algebra `R` are commutative `k`-algebras, functorially in `R`: a `k`-algebra map
`f : R → S` acts on coefficients. The inclusion `R⟦X⟧ → R⸨X⸩` is natural in `R`. These are the
formal disc and the punctured formal disc as functors of the coefficient algebra: composing them
with the functor of points of an affine group gives its positive loop group and its loop group.

The `k`-algebra structure of `R⸨X⸩` used here is the coefficientwise one,
`HahnSeries.instAlgebra`, under which `algebraMap k R⸨X⸩` is `HahnSeries.C ∘ algebraMap k R`.
Instance search finds instead the structure inherited from `R⟦X⟧` through
`HahnSeries.powerSeriesAlgebra`, which agrees with it only propositionally. The coefficientwise
structure is the one for which the coefficient maps `HahnSeries.mapAlgHom` and the inclusion
`HahnSeries.ofPowerSeriesAlg` are `k`-algebra maps; files working with `laurentSeries k` should
select it with `attribute [local instance 1100] HahnSeries.instAlgebra`.

## Main definitions

* `CommAlgCat.powerSeries k`: the functor `R ↦ R⟦X⟧` on commutative `k`-algebras.
* `CommAlgCat.laurentSeries k`: the functor `R ↦ R⸨X⸩` on commutative `k`-algebras.
* `CommAlgCat.ofPowerSeries k`: the natural inclusion `R⟦X⟧ → R⸨X⸩`, injective at every `R`
  (`CommAlgCat.ofPowerSeries_app_injective`).
-/

public section

open CategoryTheory

universe u w

namespace CommAlgCat

variable (k : Type u) [CommRing k]

attribute [local instance 1100] HahnSeries.instAlgebra

/-- The power series functor `R ↦ R⟦X⟧` on commutative `k`-algebras, acting on coefficients. -/
noncomputable abbrev powerSeries : CommAlgCat.{w} k ⥤ CommAlgCat.{w} k where
  obj R := of k (PowerSeries R)
  map f := ofHom (PowerSeries.mapAlgHom f.hom)
  map_id R := by ext; simp [PowerSeries.mapAlgHom_apply]
  map_comp f g := by ext; simp [PowerSeries.mapAlgHom_apply]

/-- The power series functor sends `R` to `R⟦X⟧`. -/
lemma powerSeries_obj (R : CommAlgCat.{w} k) : (powerSeries k).obj R = of k (PowerSeries R) :=
  (rfl)

/-- The power series functor applies a morphism to every coefficient. -/
lemma powerSeries_map_hom {R S : CommAlgCat.{w} k} (f : R ⟶ S) :
    ((powerSeries k).map f).hom = PowerSeries.mapAlgHom f.hom :=
  (rfl)

/-- The Laurent series functor `R ↦ R⸨X⸩` on commutative `k`-algebras, acting on coefficients,
for the coefficientwise `k`-algebra structure `HahnSeries.instAlgebra` of `R⸨X⸩`. -/
noncomputable abbrev laurentSeries : CommAlgCat.{w} k ⥤ CommAlgCat.{w} k where
  obj R := of k (LaurentSeries R)
  map f := ofHom (HahnSeries.mapAlgHom f.hom)
  map_id R := by ext; simp
  map_comp f g := by ext; simp

/-- The Laurent series functor sends `R` to `R⸨X⸩`, with its coefficientwise `k`-algebra
structure. -/
lemma laurentSeries_obj (R : CommAlgCat.{w} k) :
    (laurentSeries k).obj R = of k (LaurentSeries R) :=
  (rfl)

/-- The Laurent series functor applies a morphism to every coefficient. -/
lemma laurentSeries_map_hom {R S : CommAlgCat.{w} k} (f : R ⟶ S) :
    ((laurentSeries k).map f).hom = HahnSeries.mapAlgHom f.hom :=
  (rfl)

/-- The inclusion `R⟦X⟧ → R⸨X⸩` of power series into Laurent series, natural in `R`. -/
noncomputable def ofPowerSeries : powerSeries.{u, w} k ⟶ laurentSeries k where
  app R := ofHom (HahnSeries.ofPowerSeriesAlg ℤ k)
  naturality R S f := by
    ext p : 2
    simp only [hom_comp, hom_ofHom, AlgHom.coe_comp, Function.comp_apply,
      HahnSeries.coe_ofPowerSeriesAlg, HahnSeries.mapAlgHom_apply, PowerSeries.mapAlgHom_apply]
    exact (HahnSeries.map_ofPowerSeries (f.hom : R →+* S) p).symm

/-- The component of `ofPowerSeries` at `R` is the inclusion `R⟦X⟧ → R⸨X⸩`. -/
@[simp]
lemma ofPowerSeries_app_hom (R : CommAlgCat.{w} k) :
    ((ofPowerSeries k).app R).hom = HahnSeries.ofPowerSeriesAlg ℤ k :=
  (rfl)

/-- Power series embed into Laurent series. -/
lemma ofPowerSeries_app_injective (R : CommAlgCat.{w} k) :
    Function.Injective ((ofPowerSeries k).app R).hom :=
  HahnSeries.ofPowerSeries_injective

end CommAlgCat
