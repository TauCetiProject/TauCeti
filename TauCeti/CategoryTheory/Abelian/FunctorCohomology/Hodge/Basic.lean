/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.Ext.WithAction
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Comparison
public import TauCeti.CategoryTheory.Abelian.FunctorCohomology.Hodge.Pair

/-!
# Hodge cohomology of functors on algebras

Let `k` be a commutative ring and `N` a functor from commutative `k`-algebras to abelian groups.
Its *Hodge cohomology* in degree `q` is
```
  H^q_Hdg(N) = Ext^q((A, Aⁿ) ↦ N(A ⊕ Aⁿ), (A, Aⁿ) ↦ ⋀_A Aⁿ),
```
the Ext group, in the abelian category of functors from Hodge pairs over `k` to abelian groups
(`TauCeti.HodgePair`), from `N` evaluated on the square-zero extensions `A ⊕ Aⁿ` to the exterior
algebras `⋀_A Aⁿ`. It is a `k`-module through the action of `k` on the exterior algebras. For a
functor `X` on `k`-algebras with values in sets, `H^q_Hdg(X)` is the Hodge cohomology of the free
abelian group functor `X ⋙ AddCommGrpCat.free`, and for a subfunctor `U` of `X` the relative groups
`H^q_Hdg(X, U)` are those of the quotient `ℤ[X] / ℤ[U]`, the cokernel of `ℤ[U] ⟶ ℤ[X]`.

These groups stand in for the coherent cohomology groups `H^q(X, Ωᵖ)` of a smooth variety, the
scaling `s_t` playing the part of the grading by `p`; no comparison with coherent cohomology is
made here.

## Main definitions

* `CategoryTheory.Functor.HodgeCohomology N q`: the Hodge cohomology `H^q_Hdg(N)`, a `k`-module.
* `CategoryTheory.Functor.HodgeCohomology.pullback α q`: the `k`-linear pull-back
  `H^q_Hdg(N) → H^q_Hdg(N')` along a natural transformation `α : N' ⟶ N`.
* `CategoryTheory.Functor.HodgeCohomology.scale t N q`: the scaling `s_t` of `H^q_Hdg(N)`, induced
  by `(a, m) ↦ (a, t • m)` on the square-zero extensions.
* `CategoryTheory.Functor.HodgeCohomology.baseChange f N q`: for a ring map `f : k →+* K`, the
  `f`-semilinear base change `H^q_Hdg(N) → H^q_Hdg(N|_K)`, where `N|_K` is `N` restricted to
  `K`-algebras, induced by restriction of scalars on Hodge pairs.

## Main results

* `CategoryTheory.Functor.HodgeCohomology.pullback_comp`,
  `CategoryTheory.Functor.HodgeCohomology.scale_mul`,
  `CategoryTheory.Functor.HodgeCohomology.pullback_scale`: pull-backs are functorial, the scalings
  form an action of the multiplicative monoid of `k`, and they commute with pull-backs.
* `CategoryTheory.Functor.HodgeCohomology.baseChange_pullback` and
  `CategoryTheory.Functor.HodgeCohomology.baseChange_scale`: base change commutes with pull-backs
  and carries `s_t` to `s_{f t}`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Hodge/Site.lean` (declarations `New.Variety.hodgeCoeff`,
  `New.Variety.HodgeH`, `New.Variety.HodgeH.map`, `New.Variety.HodgeH.scale`,
  `New.Variety.HodgeH.baseChange`); Apache 2.0, Copyright 2026 Anthropic, PBC. The definitions
  are adapted from these declarations, with the `k`-module structure taken from
  `TauCeti.Abelian.ExtWithAction` and base change written as a comparison map
  (`CategoryTheory.Functor.extComparison`).
-/

public section

open CategoryTheory Abelian TauCeti TauCeti.Abelian

universe t t' w u u' u''

namespace CategoryTheory

namespace Functor

variable {k : Type u'} [CommRing k] [HasExt.{t} (HodgePair.{u} k ⥤ AddCommGrpCat.{max u w})]

/-- The *Hodge cohomology* `H^q_Hdg(N)` of a functor `N` from commutative `k`-algebras to abelian
groups: the Ext group `Ext^q((A, Aⁿ) ↦ N(A ⊕ Aⁿ), (A, Aⁿ) ↦ ⋀_A Aⁿ)` in the category of functors
from Hodge pairs over `k` to abelian groups, with the `k`-module structure induced by the action of
`k` on the exterior algebras. -/
abbrev HodgeCohomology (N : CommAlgCat.{u} k ⥤ AddCommGrpCat.{max u w}) (q : ℕ) : Type t :=
  ExtWithAction (HodgePair.exteriorAction.{w, u} k) (HodgePair.sqZero k ⋙ N) q

namespace HodgeCohomology

variable {N N' N'' : CommAlgCat.{u} k ⥤ AddCommGrpCat.{max u w}} {q : ℕ}

/-! ### Pull-backs -/

/-- The *pull-back* `H^q_Hdg(N) →ₗ[k] H^q_Hdg(N')` along a natural transformation `α : N' ⟶ N`:
precomposition with `α` evaluated on the square-zero extensions. -/
noncomputable def pullback (α : N' ⟶ N) (q : ℕ) :
    N.HodgeCohomology.{t} q →ₗ[k] N'.HodgeCohomology.{t} q :=
  ExtWithAction.precompLinearMap _ (Ext.mk₀ (whiskerLeft (HodgePair.sqZero k) α)) (zero_add q)

@[simp]
lemma toExt_pullback (α : N' ⟶ N) (x : N.HodgeCohomology.{t} q) :
    ExtWithAction.toExt _ (pullback α q x) =
      (Ext.mk₀ (whiskerLeft (HodgePair.sqZero k) α)).comp (ExtWithAction.toExt _ x) (zero_add q) :=
  ExtWithAction.toExt_precompLinearMap _ _ _ x

@[simp]
lemma pullback_id (N : CommAlgCat.{u} k ⥤ AddCommGrpCat.{max u w}) (q : ℕ) :
    pullback.{t} (𝟙 N) q = LinearMap.id := by
  ext x
  apply (ExtWithAction.toExt _).injective
  rw [toExt_pullback, whiskerLeft_id', Ext.mk₀_id_comp, LinearMap.id_apply]

/-- Pull-backs are contravariantly functorial. -/
lemma pullback_comp (α : N'' ⟶ N') (β : N' ⟶ N) (q : ℕ) :
    pullback.{t} (α ≫ β) q = (pullback α q).comp (pullback β q) := by
  ext x
  apply (ExtWithAction.toExt _).injective
  rw [LinearMap.comp_apply, toExt_pullback, toExt_pullback, toExt_pullback, whiskerLeft_comp,
    ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]

/-! ### Scaling -/

/-- The *scaling* `s_c : H^q_Hdg(N) →ₗ[k] H^q_Hdg(N)` by `c : k`, induced by the natural
endomorphism `(a, m) ↦ (a, c • m)` of the square-zero extensions (`TauCeti.HodgePair.sqZeroScale`).
-/
noncomputable def scale (c : k) (N : CommAlgCat.{u} k ⥤ AddCommGrpCat.{max u w}) (q : ℕ) :
    N.HodgeCohomology.{t} q →ₗ[k] N.HodgeCohomology.{t} q :=
  ExtWithAction.precompLinearMap _ (Ext.mk₀ (whiskerRight (HodgePair.sqZeroScale k c) N))
    (zero_add q)

@[simp]
lemma toExt_scale (c : k) (x : N.HodgeCohomology.{t} q) :
    ExtWithAction.toExt _ (scale c N q x) =
      (Ext.mk₀ (whiskerRight (HodgePair.sqZeroScale k c) N)).comp (ExtWithAction.toExt _ x)
        (zero_add q) :=
  ExtWithAction.toExt_precompLinearMap _ _ _ x

@[simp]
lemma scale_one (N : CommAlgCat.{u} k ⥤ AddCommGrpCat.{max u w}) (q : ℕ) :
    scale.{t} 1 N q = LinearMap.id := by
  ext x
  apply (ExtWithAction.toExt _).injective
  rw [toExt_scale, HodgePair.sqZeroScale_one, whiskerRight_id', Ext.mk₀_id_comp,
    LinearMap.id_apply]

/-- The scalings form an action of the multiplicative monoid of `k`. -/
lemma scale_mul (c d : k) (N : CommAlgCat.{u} k ⥤ AddCommGrpCat.{max u w}) (q : ℕ) :
    scale.{t} (c * d) N q = (scale d N q).comp (scale c N q) := by
  ext x
  apply (ExtWithAction.toExt _).injective
  rw [LinearMap.comp_apply, toExt_scale, toExt_scale, toExt_scale, HodgePair.sqZeroScale_mul,
    whiskerRight_comp, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero]

/-- Pull-backs commute with the scalings. -/
lemma pullback_scale (α : N' ⟶ N) (c : k) (x : N.HodgeCohomology.{t} q) :
    pullback α q (scale c N q x) = scale c N' q (pullback α q x) := by
  apply (ExtWithAction.toExt _).injective
  rw [toExt_pullback, toExt_scale, toExt_scale, toExt_pullback,
    ← Ext.comp_assoc_of_second_deg_zero, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀]
  congr 2
  ext P : 2
  exact (α.naturality _).symm

/-! ### Base change -/

variable {K : Type u''} [CommRing K] [HasExt.{t'} (HodgePair.{u} K ⥤ AddCommGrpCat.{max u w})]

/-- *Base change* along a ring map `f : k →+* K`: the `f`-semilinear map
`H^q_Hdg(N) → H^q_Hdg(N|_K)`, where `N|_K` is `N` restricted to `K`-algebras through restriction of
scalars. It restricts classes along the restriction of scalars from Hodge pairs over `K` to Hodge
pairs over `k`, which preserves square-zero extensions and exterior algebras. -/
noncomputable def baseChange (f : k →+* K) (N : CommAlgCat.{u} k ⥤ AddCommGrpCat.{max u w})
    (q : ℕ) :
    N.HodgeCohomology.{t} q →ₛₗ[f] (CommAlgCat.restrictScalars f ⋙ N).HodgeCohomology.{t'} q where
  toFun x := (ExtWithAction.toExt _).symm (extComparison (HodgePair.restrictScalars f)
    (HodgePair.exteriorRestrictScalars f) (whiskerRight (HodgePair.sqZeroRestrictScalars f) N) q
    (ExtWithAction.toExt _ x))
  map_add' x y := by simp
  map_smul' c x := by
    apply (ExtWithAction.toExt _).injective
    rw [AddEquiv.apply_symm_apply, ExtWithAction.toExt_smul, ExtWithAction.toExt_smul,
      AddEquiv.apply_symm_apply, extComparison_comp_mk₀ _
        (HodgePair.whiskerLeft_exteriorAction_comp_exteriorRestrictScalars f c)]

@[simp]
lemma toExt_baseChange (f : k →+* K) (x : N.HodgeCohomology.{t} q) :
    ExtWithAction.toExt _ (baseChange.{t, t'} f N q x) =
      extComparison (HodgePair.restrictScalars f) (HodgePair.exteriorRestrictScalars f)
        (whiskerRight (HodgePair.sqZeroRestrictScalars f) N) q (ExtWithAction.toExt _ x) :=
  AddEquiv.apply_symm_apply _ _

/-- Base change commutes with pull-backs. -/
lemma baseChange_pullback (f : k →+* K) (α : N' ⟶ N) (x : N.HodgeCohomology.{t} q) :
    baseChange.{t, t'} f N' q (pullback α q x) =
      pullback (whiskerLeft (CommAlgCat.restrictScalars f) α) q (baseChange f N q x) := by
  apply (ExtWithAction.toExt _).injective
  rw [toExt_baseChange, toExt_pullback, toExt_pullback, toExt_baseChange]
  refine (mk₀_comp_extComparison _ _ ?_ _).symm
  ext P : 2
  exact (α.naturality _).symm

/-- Base change carries the scaling `s_c` to the scaling `s_{f c}`. -/
lemma baseChange_scale (f : k →+* K) (c : k) (x : N.HodgeCohomology.{t} q) :
    baseChange.{t, t'} f N q (scale c N q x) = scale (f c) _ q (baseChange f N q x) := by
  apply (ExtWithAction.toExt _).injective
  rw [toExt_baseChange, toExt_scale, toExt_scale, toExt_baseChange]
  refine (mk₀_comp_extComparison _ _ ?_ _).symm
  have h := congrArg (fun γ ↦ whiskerRight γ N)
    (HodgePair.whiskerRight_sqZeroScale_comp_sqZeroRestrictScalars f c)
  ext P : 2
  have hP := NatTrans.congr_app h P
  simp only [whiskerRight_comp, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.comp_map] at hP ⊢
  exact hP

end HodgeCohomology

end Functor

end CategoryTheory
