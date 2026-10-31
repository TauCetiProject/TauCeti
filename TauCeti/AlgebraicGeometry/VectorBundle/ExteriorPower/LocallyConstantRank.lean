/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.LocallyConstant
public import TauCeti.AlgebraicGeometry.VectorBundle.ExteriorPower.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# Exterior powers of finite locally free sheaves in a locally constant degree

For a locally constant function `r : X → ℕ`, the exterior power `⋀^r` of `𝒪_X`-modules
(`TauCeti.AlgebraicGeometry.locallyConstantExteriorPower r`) restricts over each open set
`r⁻¹{n}` to the `n`-th exterior power. Since `⋀ⁿ` preserves finite local freeness, so does `⋀^r`,
and it restricts to an endofunctor of the category of finite locally free sheaves on `X`. The rank
of `⋀^r E` at `x` is `(rank E x).choose (r x)`.

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.locallyConstantExteriorPower X r`: the
  exterior power `⋀^r` of finite locally free sheaves;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.rank_locallyConstantExteriorPower_apply`: the
  rank of `⋀^r E` at `x` is `(rank E x).choose (r x)`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

namespace FiniteLocallyFreeSheaf

/-- The pullback of `⋀^r E` to the open set `r⁻¹{n}` is the pullback of `⋀ⁿ E`. -/
private def pullbackFiberIso (r : LocallyConstant X ℕ) (n : ℕ) (M : X.Modules) :
    (Scheme.Modules.pullback (Scheme.Opens.ι (r.fiberOpens n))).obj
        ((locallyConstantExteriorPower r).obj M) ≅
      (Scheme.Modules.pullback (Scheme.Opens.ι (r.fiberOpens n))).obj
        ((SheafOfModules.exteriorPower X.sheaf n).obj M) :=
  ((restrictFunctorIsoPullback (Scheme.Opens.ι (r.fiberOpens n))).app _).symm ≪≫
    (restrictLocallyConstantExteriorPowerIso r (r.fiberOpens n) fun _ hx ↦ hx).app M ≪≫
    (restrictFunctorIsoPullback (Scheme.Opens.ι (r.fiberOpens n))).app _

/-- The exterior power `⋀^r E` of a finite locally free sheaf in a locally constant degree `r` is
finite locally free: over each open set `r⁻¹{n}` it is the finite locally free sheaf `⋀ⁿ E`. -/
theorem isFiniteLocallyFree_locallyConstantExteriorPower (r : LocallyConstant X ℕ)
    (E : FiniteLocallyFreeSheaf X) :
    Scheme.Modules.isFiniteLocallyFree X ((locallyConstantExteriorPower r).obj E.obj) := by
  rw [isFiniteLocallyFree_iff_forall_pullback
    (X.openCoverOfIsOpenCover r.fiberOpens (IsOpenCover.mk r.iSup_fiberOpens))]
  intro (n : ℕ)
  have h := ((pullback (Scheme.Opens.ι (r.fiberOpens n))).obj ((exteriorPower X n).obj E)).property
  rw [pullback_obj_obj, exteriorPower_obj_obj] at h
  exact (Scheme.Modules.isFiniteLocallyFree _).prop_of_iso (pullbackFiberIso r n E.obj).symm h

variable (X) in
/-- The exterior power `E ↦ ⋀^r E` of finite locally free sheaves in a locally constant degree
`r : X → ℕ`: over each open set `r⁻¹{n}` it is the `n`-th exterior power. -/
def locallyConstantExteriorPower (r : LocallyConstant X ℕ) :
    FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf X :=
  (Scheme.Modules.isFiniteLocallyFree X).lift
    ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ AlgebraicGeometry.locallyConstantExteriorPower r)
    (isFiniteLocallyFree_locallyConstantExteriorPower r)

/-- The underlying sheaf of `⋀^r E` is `⋀^r` of the underlying `𝒪_X`-module of `E`. -/
@[simp]
lemma locallyConstantExteriorPower_obj_obj (r : LocallyConstant X ℕ)
    (E : FiniteLocallyFreeSheaf X) :
    ((locallyConstantExteriorPower X r).obj E).obj =
      (AlgebraicGeometry.locallyConstantExteriorPower r).obj E.obj :=
  (rfl)

/-- The exterior power `⋀^r` acts on morphisms of finite locally free sheaves through the
underlying morphisms of `𝒪_X`-modules. -/
@[simp]
lemma locallyConstantExteriorPower_map_hom (r : LocallyConstant X ℕ)
    {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) :
    ((locallyConstantExteriorPower X r).map φ).hom =
      eqToHom (locallyConstantExteriorPower_obj_obj r E) ≫
        (AlgebraicGeometry.locallyConstantExteriorPower r).map φ.hom ≫
          eqToHom (locallyConstantExteriorPower_obj_obj r F).symm := by
  -- Both `eqToHom`s are identities.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The pullback of `⋀^r E` to the open set `r⁻¹{n}` is the pullback of `⋀ⁿ E`, as finite
locally free sheaves. -/
private def pullbackFiberIso' (r : LocallyConstant X ℕ) (n : ℕ) (E : FiniteLocallyFreeSheaf X) :
    ((pullback (Scheme.Opens.ι (r.fiberOpens n))).obj
        ((locallyConstantExteriorPower X r).obj E)).obj ≅
      ((pullback (Scheme.Opens.ι (r.fiberOpens n))).obj ((exteriorPower X n).obj E)).obj :=
  eqToIso (by rw [pullback_obj_obj, locallyConstantExteriorPower_obj_obj]) ≪≫
    pullbackFiberIso r n E.obj ≪≫ eqToIso (by rw [pullback_obj_obj, exteriorPower_obj_obj])

/-- The rank of `⋀^r E` at `x` is `(E.rank x).choose (r x)`. -/
@[simp]
theorem rank_locallyConstantExteriorPower_apply (r : LocallyConstant X ℕ)
    (E : FiniteLocallyFreeSheaf X) (x : X) :
    ((locallyConstantExteriorPower X r).obj E).rank x = (E.rank x).choose (r x) := by
  -- Compute the rank after pulling back to the open set `r⁻¹{r x}` containing `x`.
  let y : Scheme.Opens.toScheme (r.fiberOpens (r x)) := ⟨x, rfl⟩
  calc ((locallyConstantExteriorPower X r).obj E).rank x
      = ((pullback (Scheme.Opens.ι (r.fiberOpens (r x)))).obj
          ((locallyConstantExteriorPower X r).obj E)).rank y :=
        by rw [rank_pullback_apply, Scheme.Opens.ι_apply]
    _ = ((pullback (Scheme.Opens.ι (r.fiberOpens (r x)))).obj
          ((exteriorPower X (r x)).obj E)).rank y := by
        rw [rank_eq_of_iso (pullbackFiberIso' r (r x) E)]
    _ = (E.rank x).choose (r x) :=
        by rw [rank_pullback_apply, Scheme.Opens.ι_apply, rank_exteriorPower_apply]

end FiniteLocallyFreeSheaf

end

end TauCeti.AlgebraicGeometry
