/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
public import TauCeti.AlgebraicGeometry.Modules.Products
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
public import TauCeti.Topology.LocallyConstant.Fiber

/-!
# Exterior powers of `𝒪_X`-modules in a locally constant degree

For a locally constant function `r : X → ℕ` on a scheme `X`, the exterior power `⋀^r M` of an
`𝒪_X`-module `M` is the `𝒪_X`-module which over each open set `r⁻¹{n}` is the `n`-th exterior
power `⋀ⁿ M`. The sets `r⁻¹{n}` form a cover of `X` by pairwise disjoint open sets, and `⋀^r M` is
the product over `n` of the pushforwards of the restrictions of `⋀ⁿ M` to `r⁻¹{n}`: its sections
over an open `V` are the families of sections of the `⋀ⁿ M` over the sets `V ∩ r⁻¹{n}`. Over an
open set on which `r` is constantly `n`, the other factors have no nonzero sections, so `⋀^r M`
restricts there to `⋀ⁿ M` (`restrictLocallyConstantExteriorPowerIso`), and if `r` is constantly
`n` then `⋀^r M ≅ ⋀ⁿ M` (`locallyConstantExteriorPowerIso`). Both isomorphisms are the projection
onto the `n`-th factor, read through the unit of the restriction--pushforward adjunction.

## Main declarations

* `TauCeti.AlgebraicGeometry.locallyConstantExteriorPower r`: the exterior power `⋀^r` of
  `𝒪_X`-modules in a locally constant degree `r`;
* `TauCeti.AlgebraicGeometry.locallyConstantExteriorPowerπ r n`: the projection of `⋀^r` onto its
  `n`-th factor;
* `TauCeti.AlgebraicGeometry.restrictLocallyConstantExteriorPowerIso` and
  `TauCeti.AlgebraicGeometry.locallyConstantExteriorPowerIso`: over an open set where `r` is
  constantly `n`, and if `r` is constantly `n`, `⋀^r` is the `n`-th exterior power.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

/-- The `n`-th factor of `locallyConstantExteriorPower r`: the `n`-th exterior power, restricted
to the fiber `r⁻¹{n}` and pushed forward to `X`. -/
abbrev locallyConstantExteriorPowerFactor (r : LocallyConstant X ℕ) (n : ℕ) :
    X.Modules ⥤ X.Modules :=
  SheafOfModules.exteriorPower X.sheaf n ⋙ restrictFunctor (Scheme.Opens.ι (r.fiberOpens n)) ⋙
    pushforward (Scheme.Opens.ι (r.fiberOpens n))

/-- The exterior power `⋀^r M` of an `𝒪_X`-module `M` in a locally constant degree
`r : X → ℕ`: the `𝒪_X`-module whose restriction to each open set `r⁻¹{n}` is the `n`-th exterior
power of `M` there (`restrictLocallyConstantExteriorPowerIso`). It is the product over `n` of
the pushforwards of these restrictions, whose sections over an open `V` are the families of
sections of `⋀ⁿ M` over the sets `V ∩ r⁻¹{n}`. -/
@[expose] def locallyConstantExteriorPower (r : LocallyConstant X ℕ) : X.Modules ⥤ X.Modules where
  obj M := ∏ᶜ fun n ↦ (locallyConstantExteriorPowerFactor r n).obj M
  map φ := Limits.Pi.map fun n ↦ (locallyConstantExteriorPowerFactor r n).map φ
  map_id M := by simp
  map_comp φ ψ := by simp [Limits.Pi.map_comp_map]

/-- The projection of `⋀^r M` onto its `n`-th factor, the pushforward of the restriction of
`⋀ⁿ M` to `r⁻¹{n}`. -/
@[expose] def locallyConstantExteriorPowerπ (r : LocallyConstant X ℕ) (n : ℕ) :
    locallyConstantExteriorPower r ⟶ locallyConstantExteriorPowerFactor r n where
  app M := Pi.π (fun m ↦ (locallyConstantExteriorPowerFactor r m).obj M) n
  naturality _ _ _ := by simp [locallyConstantExteriorPower]

/-- The projection `locallyConstantExteriorPowerπ r n` is the product projection. -/
@[simp]
lemma locallyConstantExteriorPowerπ_app (r : LocallyConstant X ℕ) (n : ℕ) (M : X.Modules) :
    (locallyConstantExteriorPowerπ r n).app M =
      Pi.π (fun m ↦ (locallyConstantExteriorPowerFactor r m).obj M) n :=
  rfl

/-- Over an open `V` on which `r` is constantly `n`, the projection of `⋀^r M` onto its `n`-th
factor is an isomorphism on sections. -/
theorem isIso_locallyConstantExteriorPowerπ_app_app (r : LocallyConstant X ℕ) (M : X.Modules)
    {n : ℕ} {V : X.Opens} (hV : ∀ x ∈ V, r x = n) :
    IsIso (((locallyConstantExteriorPowerπ r n).app M).app V) := by
  refine (ConcreteCategory.isIso_iff_bijective _).2 <|
    bijective_app_π_of_subsingleton _ n V fun m hm ↦ ?_
  -- The sections over `V` of the `m`-th factor are those of a module on `r⁻¹{m}` over the
  -- preimage of `V`, which is empty; they form a module over the zero ring `Γ(r⁻¹{m}, ∅)`.
  have h : (Scheme.Opens.ι (r.fiberOpens m)) ⁻¹ᵁ V = ⊥ :=
    eq_bot_iff.2 fun x hx ↦ hm ((LocallyConstant.mem_fiberOpens.1 x.2).symm.trans (hV x.1 hx))
  change Subsingleton Γ((pushforward (Scheme.Opens.ι (r.fiberOpens m))).obj _, V)
  rw [pushforward_obj_obj]
  exact h ▸ Module.subsingleton Γ((Scheme.Opens.toScheme (r.fiberOpens m)), ⊥) _

/-- The unit `⋀ⁿ M ⟶ (r⁻¹{n}).ι_* (⋀ⁿ M|_{r⁻¹{n}})` of the restriction--pushforward adjunction,
as a natural transformation into the `n`-th factor of `⋀^r`. -/
private def factorι (r : LocallyConstant X ℕ) (n : ℕ) :
    SheafOfModules.exteriorPower X.sheaf n ⟶ locallyConstantExteriorPowerFactor r n where
  app _ := (restrictAdjunction (Scheme.Opens.ι (r.fiberOpens n))).unit.app _
  naturality _ _ _ := (restrictAdjunction (Scheme.Opens.ι (r.fiberOpens n))).unit.naturality _

private theorem isIso_factorι_app_app (r : LocallyConstant X ℕ) (M : X.Modules) {n : ℕ}
    {V : X.Opens} (hV : ∀ x ∈ V, r x = n) :
    IsIso (Scheme.Modules.Hom.app ((factorι r n).app M) V) :=
  isIso_restrictAdjunction_unit_app_app (r.fiberOpens n) _ fun x hx ↦ hV x hx

/-- Over an open `U` on which `r` is constantly `n`, the restricted unit
`(⋀ⁿ M)|_U ⟶ ((r⁻¹{n}).ι_* (⋀ⁿ M|_{r⁻¹{n}}))|_U` is an isomorphism, naturally in `M`. -/
private def restrictFactorιIso (r : LocallyConstant X ℕ) {n : ℕ} (U : X.Opens)
    (hU : ∀ x ∈ U, r x = n) :
    SheafOfModules.exteriorPower X.sheaf n ⋙ restrictFunctor U.ι ≅
      locallyConstantExteriorPowerFactor r n ⋙ restrictFunctor U.ι :=
  have : ∀ M, IsIso ((Functor.whiskerRight (factorι r n) (restrictFunctor U.ι)).app M) :=
    fun M ↦ isIso_restrictFunctor_map_of_isIso_app _ U fun _ hV ↦
      isIso_factorι_app_app r M fun x hx ↦ hU x (hV hx)
  have := NatIso.isIso_of_isIso_app (Functor.whiskerRight (factorι r n) (restrictFunctor U.ι))
  asIso (Functor.whiskerRight (factorι r n) (restrictFunctor U.ι))

/-- **Restriction of `⋀^r M` to an open where `r` is constant.** Over an open `U` on which the
locally constant function `r` takes the value `n`, the restriction of `⋀^r M` is the restriction
of the `n`-th exterior power `⋀ⁿ M`, naturally in `M`. -/
def restrictLocallyConstantExteriorPowerIso (r : LocallyConstant X ℕ) {n : ℕ} (U : X.Opens)
    (hU : ∀ x ∈ U, r x = n) :
    locallyConstantExteriorPower r ⋙ restrictFunctor U.ι ≅
      SheafOfModules.exteriorPower X.sheaf n ⋙ restrictFunctor U.ι :=
  have : ∀ M, IsIso
      ((Functor.whiskerRight (locallyConstantExteriorPowerπ r n) (restrictFunctor U.ι)).app M) :=
    fun M ↦ isIso_restrictFunctor_map_of_isIso_app _ U fun _ hV ↦
      isIso_locallyConstantExteriorPowerπ_app_app r M fun x hx ↦ hU x (hV hx)
  have := NatIso.isIso_of_isIso_app
    (Functor.whiskerRight (locallyConstantExteriorPowerπ r n) (restrictFunctor U.ι))
  asIso (Functor.whiskerRight (locallyConstantExteriorPowerπ r n) (restrictFunctor U.ι)) ≪≫
    (restrictFactorιIso r U hU).symm

/-- `restrictLocallyConstantExteriorPowerIso` is the restricted projection onto the `n`-th
factor, read through the restricted unit `⋀ⁿ M ⟶ (r⁻¹{n}).ι_* (⋀ⁿ M|_{r⁻¹{n}})`. -/
@[reassoc]
lemma restrictLocallyConstantExteriorPowerIso_hom_app_comp (r : LocallyConstant X ℕ) {n : ℕ}
    (U : X.Opens) (hU : ∀ x ∈ U, r x = n) (M : X.Modules) :
    (restrictLocallyConstantExteriorPowerIso r U hU).hom.app M ≫
        (restrictFunctor U.ι).map ((restrictAdjunction (Scheme.Opens.ι (r.fiberOpens n))).unit.app
          ((SheafOfModules.exteriorPower X.sheaf n).obj M)) =
      (restrictFunctor U.ι).map ((locallyConstantExteriorPowerπ r n).app M) :=
  -- The isomorphism is the restricted projection followed by the inverse of the restricted
  -- unit `restrictFactorιIso`, whose forward map is the second factor on the left.
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((restrictFactorιIso r U hU).inv_hom_id_app M)).trans (Category.comp_id _)

/-- If `r` is constantly `n`, the unit `⋀ⁿ M ⟶ (r⁻¹{n}).ι_* (⋀ⁿ M|_{r⁻¹{n}})` is an
isomorphism, naturally in `M`. -/
private def factorιIso (r : LocallyConstant X ℕ) {n : ℕ} (hr : ∀ x, r x = n) :
    SheafOfModules.exteriorPower X.sheaf n ≅ locallyConstantExteriorPowerFactor r n :=
  have : ∀ M, IsIso ((factorι r n).app M) := fun M ↦
    Hom.isIso_iff_isIso_app.2 fun _ ↦ isIso_factorι_app_app r M fun x _ ↦ hr x
  have := NatIso.isIso_of_isIso_app (factorι r n)
  asIso (factorι r n)

/-- **`⋀^r M` in constant degree.** If the locally constant function `r` is constantly `n`,
then `⋀^r M` is the `n`-th exterior power `⋀ⁿ M`, naturally in `M`. -/
def locallyConstantExteriorPowerIso (r : LocallyConstant X ℕ) {n : ℕ} (hr : ∀ x, r x = n) :
    locallyConstantExteriorPower r ≅ SheafOfModules.exteriorPower X.sheaf n :=
  have : ∀ M, IsIso ((locallyConstantExteriorPowerπ r n).app M) := fun M ↦
    Hom.isIso_iff_isIso_app.2 fun _ ↦
      isIso_locallyConstantExteriorPowerπ_app_app r M fun x _ ↦ hr x
  have := NatIso.isIso_of_isIso_app (locallyConstantExteriorPowerπ r n)
  asIso (locallyConstantExteriorPowerπ r n) ≪≫ (factorιIso r hr).symm

/-- `locallyConstantExteriorPowerIso` is the projection onto the `n`-th factor, read through the
unit `⋀ⁿ M ⟶ (r⁻¹{n}).ι_* (⋀ⁿ M|_{r⁻¹{n}})`. -/
@[reassoc]
lemma locallyConstantExteriorPowerIso_hom_app_comp (r : LocallyConstant X ℕ) {n : ℕ}
    (hr : ∀ x, r x = n) (M : X.Modules) :
    (locallyConstantExteriorPowerIso r hr).hom.app M ≫
        (restrictAdjunction (Scheme.Opens.ι (r.fiberOpens n))).unit.app
          ((SheafOfModules.exteriorPower X.sheaf n).obj M) =
      (locallyConstantExteriorPowerπ r n).app M :=
  -- The isomorphism is the projection followed by the inverse of the unit `factorιIso`, whose
  -- forward map is the second factor on the left.
  (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) ((factorιIso r hr).inv_hom_id_app M)).trans (Category.comp_id _)

end

end TauCeti.AlgebraicGeometry
