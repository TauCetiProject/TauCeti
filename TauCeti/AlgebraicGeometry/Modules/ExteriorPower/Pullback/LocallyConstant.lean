/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.LocallyConstant
public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Quasicoherent

/-!
# Pullback of exterior powers in a locally constant degree

Let `f : X ⟶ Y` be a morphism of schemes and `r : Y → ℕ` a locally constant function. The
exterior power `⋀^r M` of an `𝒪_Y`-module is the `n`-th exterior power over each open set
`r⁻¹{n}` (`TauCeti.AlgebraicGeometry.locallyConstantExteriorPower`). Its pullback is compared
with the exterior power of `f^* M` in the locally constant degree `r ∘ f`:

`f^* (⋀^r M) ⟶ ⋀^{r ∘ f} (f^* M)`.

Since `⋀^{r ∘ f}` is the product of the pushforwards of its restrictions to the open sets
`(r ∘ f)⁻¹{n} = f⁻¹ (r⁻¹{n})`, the comparison is determined by its restrictions to these sets.
There it is the `n`-th exterior power comparison `f^* (⋀ⁿ M) ⟶ ⋀ⁿ (f^* M)`, read through the
identifications of `⋀^r` and `⋀^{r ∘ f}` with `⋀ⁿ` over `r⁻¹{n}` and `f⁻¹ (r⁻¹{n})` and through
the commutation of pullback with restriction to opens
(`restrictFunctor_map_pullbackLocallyConstantExteriorPowerComparison_app_comp`). The open sets
`f⁻¹ (r⁻¹{n})` cover `X`, so the comparison is an isomorphism whenever all the `n`-th
comparisons are (`isIso_pullbackLocallyConstantExteriorPowerComparison_app_of_isIso`), in
particular for quasicoherent `M` (`isIso_pullbackLocallyConstantExteriorPowerComparison_app`).

## Main declarations

* `TauCeti.AlgebraicGeometry.pullbackLocallyConstantExteriorPowerComparison f r`: the natural
  comparison `f^* (⋀^r M) ⟶ ⋀^{r ∘ f} (f^* M)`;
* `restrictFunctor_map_pullbackLocallyConstantExteriorPowerComparison_app_comp`: over
  `f⁻¹ (r⁻¹{n})` it is the `n`-th exterior power comparison;
* `TauCeti.AlgebraicGeometry.isIso_pullbackLocallyConstantExteriorPowerComparison_app_of_isIso`
  and `TauCeti.AlgebraicGeometry.isIso_pullbackLocallyConstantExteriorPowerComparison_app`: it is
  an isomorphism when every `n`-th exterior power comparison is, in particular on quasicoherent
  modules.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.Modules

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : LocallyConstant Y ℕ)

/-- Over the fiber `f⁻¹ (r⁻¹{n})`, the restriction of `f^* (⋀^r M)` is that of `f^* (⋀ⁿ M)`:
pullback commutes with restriction, and `⋀^r` restricts to `⋀ⁿ` over `r⁻¹{n}`. -/
private def restrictPullbackIsoFiber (n : ℕ) :
    locallyConstantExteriorPower r ⋙ pullback f ⋙
        restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens) ≅
      SheafOfModules.exteriorPower Y.sheaf n ⋙ pullback f ⋙
        restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens) :=
  Functor.isoWhiskerLeft (locallyConstantExteriorPower r)
      (restrictPullbackIso f _ _ (r.comap_toOpens_fiberClopens f.base.hom n).ge) ≪≫
    Functor.isoWhiskerRight (restrictLocallyConstantExteriorPowerIso r (r.fiberClopens n).toOpens
      fun _ hx ↦ LocallyConstant.mem_fiberClopens.1 hx) _ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.exteriorPower Y.sheaf n)
      (restrictPullbackIso f _ _ (r.comap_toOpens_fiberClopens f.base.hom n).ge).symm

/-- The restriction of the comparison to the fiber `f⁻¹ (r⁻¹{n})`: the identification
`restrictPullbackIsoFiber` followed by the restricted `n`-th exterior power comparison. -/
private def comparisonFiber (n : ℕ) :
    locallyConstantExteriorPower r ⋙ pullback f ⋙
        restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens) ⟶
      pullback f ⋙ SheafOfModules.exteriorPower X.sheaf n ⋙
        restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens) where
  app M := (restrictPullbackIsoFiber f r n).hom.app M ≫
    (restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens)).map
      ((pullbackExteriorPowerComparison f n).app M)
  naturality M N φ := by
    let R := restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens)
    -- The composites below are only type-correct up to unfolding `SheafOfModules.exteriorPower`,
    -- which defeats `rw` and `simp`; so the naturality squares are composed as terms.
    have h := (R.map_comp _ _).symm.trans ((congrArg R.map
      ((pullbackExteriorPowerComparison f n).naturality φ)).trans (R.map_comp _ _))
    exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ R.map ((pullbackExteriorPowerComparison f n).app N))
        ((restrictPullbackIsoFiber f r n).hom.naturality φ)).trans <|
      (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h)

/-- The restricted comparison is an isomorphism when the `n`-th exterior power comparison is. -/
private lemma isIso_comparisonFiber_app (n : ℕ) (M : Y.Modules)
    (h : IsIso ((pullbackExteriorPowerComparison f n).app M)) :
    IsIso ((comparisonFiber f r n).app M) :=
  IsIso.comp_isIso' inferInstance (Functor.map_isIso
    (restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens)) _)

/-- The `n`-th component of the comparison, into the `n`-th factor of `⋀^{r ∘ f}`: the transpose
of `comparisonFiber` under the restriction--pushforward adjunction. -/
private def comparisonπ (n : ℕ) :
    locallyConstantExteriorPower r ⋙ pullback f ⟶
      pullback f ⋙ locallyConstantExteriorPowerFactor (r.comap f.base.hom) n where
  app M :=
    (restrictAdjunction (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens)).homEquiv
      _ _ ((comparisonFiber f r n).app M)
  naturality M N φ := by
    rw [← Adjunction.homEquiv_naturality_left]
    exact (congrArg _ ((comparisonFiber f r n).naturality φ)).trans
      (Adjunction.homEquiv_naturality_right _ _ _)

/-- **The pullback comparison for exterior powers in a locally constant degree.** For a morphism
of schemes `f : X ⟶ Y` and a locally constant `r : Y → ℕ`, the natural map
`f^* (⋀^r M) ⟶ ⋀^{r ∘ f} (f^* M)` which over each open set `f⁻¹ (r⁻¹{n})` is the `n`-th exterior
power comparison `f^* (⋀ⁿ M) ⟶ ⋀ⁿ (f^* M)`
(`restrictFunctor_map_pullbackLocallyConstantExteriorPowerComparison_app_comp`). -/
def pullbackLocallyConstantExteriorPowerComparison :
    locallyConstantExteriorPower r ⋙ pullback f ⟶
      pullback f ⋙ locallyConstantExteriorPower (r.comap f.base.hom) where
  app M := Limits.Pi.lift fun n ↦ (comparisonπ f r n).app M
  naturality M N φ := by
    refine Limits.Pi.hom_ext _ _ fun n ↦ ?_
    -- `⋀^{r ∘ f}` of a map is by definition a product of maps; state the goal with that product,
    -- where the composites are type-correct at instance transparency.
    have h : ((locallyConstantExteriorPower r ⋙ Scheme.Modules.pullback f).map φ ≫
          Limits.Pi.lift fun n ↦ (comparisonπ f r n).app N) ≫ Limits.Pi.π _ n =
        ((Limits.Pi.lift fun n ↦ (comparisonπ f r n).app M) ≫
          Limits.Pi.map fun n ↦ (locallyConstantExteriorPowerFactor (r.comap f.base.hom) n).map
            ((Scheme.Modules.pullback f).map φ)) ≫ Limits.Pi.π _ n := by
      simp only [Category.assoc, Limits.Pi.lift_comp_π, Limits.Pi.map_π,
        Limits.Pi.lift_comp_π_assoc]
      exact (comparisonπ f r n).naturality φ
    exact h

/-- The projection of the comparison onto the `n`-th factor of `⋀^{r ∘ f}` is the transpose of
its restriction to `f⁻¹ (r⁻¹{n})`. -/
private lemma comparison_app_π (n : ℕ) (M : Y.Modules) :
    (pullbackLocallyConstantExteriorPowerComparison f r).app M ≫
        (locallyConstantExteriorPowerπ (r.comap f.base.hom) n).app
          ((Scheme.Modules.pullback f).obj M) =
      (comparisonπ f r n).app M :=
  (congrArg (_ ≫ ·) (locallyConstantExteriorPowerπ_app _ _ _)).trans (Limits.Pi.lift_comp_π _ n)

/-- **The comparison over a fiber.** Over the open set `f⁻¹ (r⁻¹{n})`, on which `r ∘ f` is
constantly `n`, the comparison `f^* (⋀^r M) ⟶ ⋀^{r ∘ f} (f^* M)`, followed by the identification
of `⋀^{r ∘ f}` with `⋀ⁿ` there, is the `n`-th exterior power comparison
`f^* (⋀ⁿ M) ⟶ ⋀ⁿ (f^* M)`, read through the commutation of pullback with restriction
(`Scheme.Modules.restrictPullbackIso`) and the identification of `⋀^r` with `⋀ⁿ` over
`r⁻¹{n}`. -/
theorem restrictFunctor_map_pullbackLocallyConstantExteriorPowerComparison_app_comp (n : ℕ)
    (M : Y.Modules) :
    (restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens)).map
        ((pullbackLocallyConstantExteriorPowerComparison f r).app M) ≫
      (restrictLocallyConstantExteriorPowerIso (r.comap f.base.hom)
          ((r.comap f.base.hom).fiberClopens n).toOpens
          fun _ hx ↦ LocallyConstant.mem_fiberClopens.1 hx).hom.app
            ((Scheme.Modules.pullback f).obj M) =
      (restrictPullbackIso f _ _ (r.comap_toOpens_fiberClopens f.base.hom n).ge).hom.app
          ((locallyConstantExteriorPower r).obj M) ≫
        (Scheme.Modules.pullback (f.resLE _ _ (r.comap_toOpens_fiberClopens f.base.hom n).ge)).map
          ((restrictLocallyConstantExteriorPowerIso r (r.fiberClopens n).toOpens
            fun _ hx ↦ LocallyConstant.mem_fiberClopens.1 hx).hom.app M) ≫
        (restrictPullbackIso f _ _ (r.comap_toOpens_fiberClopens f.base.hom n).ge).inv.app
          ((SheafOfModules.exteriorPower Y.sheaf n).obj M) ≫
        (restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens)).map
          ((pullbackExteriorPowerComparison f n).app M) := by
  let adj := restrictAdjunction (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens)
  let R := restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens)
  let e := restrictLocallyConstantExteriorPowerIso (r.comap f.base.hom)
    ((r.comap f.base.hom).fiberClopens n).toOpens fun _ hx ↦ LocallyConstant.mem_fiberClopens.1 hx
  -- The right-hand side is `(comparisonFiber f r n).app M`. Insert the triangle identity
  -- `R η ≫ ε = 𝟙`: the restricted unit turns `e` into the restricted projection onto the `n`-th
  -- factor (`restrictLocallyConstantExteriorPowerIso_hom_app_comp`), and transposing the
  -- projected comparison back along the adjunction gives `comparisonFiber`. As in
  -- `comparisonFiber`, the steps are composed as terms.
  -- `comparisonFiber` is private, so the statement spells out its component; `change` folds it
  -- back.
  change _ = (comparisonFiber f r n).app M
  calc R.map ((pullbackLocallyConstantExteriorPowerComparison f r).app M) ≫
        e.hom.app ((Scheme.Modules.pullback f).obj M)
      = R.map ((pullbackLocallyConstantExteriorPowerComparison f r).app M) ≫
          (e.hom.app ((Scheme.Modules.pullback f).obj M) ≫
            R.map (adj.unit.app ((SheafOfModules.exteriorPower X.sheaf n).obj
              ((Scheme.Modules.pullback f).obj M)))) ≫
          adj.counit.app (R.obj ((SheafOfModules.exteriorPower X.sheaf n).obj
            ((Scheme.Modules.pullback f).obj M))) :=
        (Category.comp_id _).symm.trans <| (congrArg (_ ≫ ·)
          (adj.left_triangle_components _).symm).trans
          (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm) |>.trans (Category.assoc _ _ _).symm
          |>.trans (Category.assoc _ _ _)
    _ = R.map ((pullbackLocallyConstantExteriorPowerComparison f r).app M ≫
          (locallyConstantExteriorPowerπ (r.comap f.base.hom) n).app
            ((Scheme.Modules.pullback f).obj M)) ≫ adj.counit.app _ :=
        (congrArg (fun x ↦ R.map ((pullbackLocallyConstantExteriorPowerComparison f r).app M) ≫
          x ≫ adj.counit.app _)
          (restrictLocallyConstantExteriorPowerIso_hom_app_comp _ _ _ _)).trans <|
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (R.map_comp _ _).symm)
    _ = (comparisonFiber f r n).app M :=
        (congrArg (fun x ↦ R.map x ≫ adj.counit.app _) (comparison_app_π f r n M)).trans <|
          (adj.homEquiv_counit _ _ _).symm.trans (Equiv.symm_apply_apply _ _)

/-- The comparison `f^* (⋀^r M) ⟶ ⋀^{r ∘ f} (f^* M)` is an isomorphism as soon as every exterior
power comparison `f^* (⋀ⁿ M) ⟶ ⋀ⁿ (f^* M)` is. -/
theorem isIso_pullbackLocallyConstantExteriorPowerComparison_app_of_isIso (M : Y.Modules)
    (h : ∀ n, IsIso ((pullbackExteriorPowerComparison f n).app M)) :
    IsIso ((pullbackLocallyConstantExteriorPowerComparison f r).app M) := by
  -- Being an isomorphism is checked over the open cover of `X` by the fibers of `r ∘ f`, where
  -- the comparison is the `n`-th exterior power comparison.
  rw [isIso_iff_of_isOpenCover (IsOpenCover.mk (r.comap f.base.hom).iSup_toOpens_fiberClopens)]
  intro n
  rw [← NatIso.isIso_map_iff (restrictFunctorIsoPullback _)]
  let e := restrictLocallyConstantExteriorPowerIso (r.comap f.base.hom)
    ((r.comap f.base.hom).fiberClopens n).toOpens fun _ hx ↦ LocallyConstant.mem_fiberClopens.1 hx
  have : IsIso ((restrictFunctor (Scheme.Opens.ι ((r.comap f.base.hom).fiberClopens n).toOpens)).map
      ((pullbackLocallyConstantExteriorPowerComparison f r).app M) ≫
        e.hom.app ((Scheme.Modules.pullback f).obj M)) :=
    (restrictFunctor_map_pullbackLocallyConstantExteriorPowerComparison_app_comp f r n M) ▸
      isIso_comparisonFiber_app f r n M (h n)
  exact IsIso.of_isIso_comp_right _ (e.hom.app ((Scheme.Modules.pullback f).obj M))

/-- **Exterior powers in a locally constant degree commute with pullback of quasicoherent
sheaves**: for every morphism of schemes `f : X ⟶ Y`, every locally constant `r : Y → ℕ` and every
quasicoherent `𝒪_Y`-module `M`, the comparison `f^* (⋀^r M) ⟶ ⋀^{r ∘ f} (f^* M)` is an
isomorphism. -/
instance isIso_pullbackLocallyConstantExteriorPowerComparison_app (M : Y.Modules)
    [M.IsQuasicoherent] : IsIso ((pullbackLocallyConstantExteriorPowerComparison f r).app M) :=
  isIso_pullbackLocallyConstantExteriorPowerComparison_app_of_isIso f r M fun _ ↦ inferInstance

end

end TauCeti.AlgebraicGeometry
