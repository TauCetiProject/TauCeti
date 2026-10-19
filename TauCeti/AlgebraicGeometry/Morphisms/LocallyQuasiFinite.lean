/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Locally quasi-finite morphisms

Formal unramifiedness together with local finite type implies local quasi-finiteness.

A locally quasi-finite morphism is strictly monotone for the specialization order on points
(`x ≤ y` when `y` generizes `x`): it preserves specializations because it is continuous, and two
distinct points of one fibre never specialize to each other because the fibres are discrete. This
is incomparability for quasi-finite morphisms. Consequently the codimension of a point is at most
the codimension of its image.

## Main results

* `AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified`: a formally unramified morphism
  locally of finite type is locally quasi-finite.
* `AlgebraicGeometry.Scheme.Hom.strictMono`: a locally quasi-finite morphism
  is strictly monotone for the specialization order.
* `AlgebraicGeometry.Scheme.Hom.coheight_le_coheight_apply`: under a locally quasi-finite morphism
  the coheight of a point is at most the coheight of its image.

## References

* The strict monotonicity is a scheme form of `Pcf.height_eq_one_of_liesOver_heightOne` in
  T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0), `lean/Pcf/Bounding/Divisors.lean`,
  whose incomparability step is proved there for integral extensions of rings.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A formally unramified morphism that is locally of finite type is locally quasi-finite. -/
instance (priority := low) LocallyQuasiFinite.of_formallyUnramified {X Y : Scheme.{u}}
    (f : X ⟶ Y) [hform : FormallyUnramified f] [htype : LocallyOfFiniteType f] :
    LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff]
  intro U hU V hV e
  have hform := hform.formallyUnramified_appLE hU hV e
  have htype := htype.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- A locally quasi-finite morphism is strictly monotone for the specialization order. -/
theorem Scheme.Hom.strictMono {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] : StrictMono f := by
  -- `f` preserves specializations, and two points of one fibre that specialize to each other are
  -- equal because the fibre is discrete.
  intro x y hxy
  have hle : f x ≤ f y := (le_iff_specializes.mp hxy.le).map f.continuous
  refine lt_of_le_not_ge hle fun hge ↦ hxy.not_ge ?_
  have hfxy : f x = f y :=
    (inseparable_iff_specializes_and.mpr ⟨le_iff_specializes.mp hge,
      le_iff_specializes.mp hle⟩).eq
  have hxy_eq : y = x :=
    (f.isDiscrete_preimage_singleton (f x)).eq_of_specializes (le_iff_specializes.mp hxy.le)
      hfxy.symm rfl
  exact hxy_eq ▸ le_rfl

/-- Under a locally quasi-finite morphism the coheight of a point is at most the coheight of its
image. -/
theorem Scheme.Hom.coheight_le_coheight_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (x : X) : Order.coheight x ≤ Order.coheight (f x) :=
  Order.coheight_le_coheight_apply_of_strictMono _ f.strictMono x

end AlgebraicGeometry
