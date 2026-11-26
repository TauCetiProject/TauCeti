/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Ring
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange

/-!
# The transfer on projective `K₀` along a finite projective ring homomorphism

Let `f : R →+* S` be a ring homomorphism of possibly noncommutative rings making `S` a finitely
generated projective left `R`-module. Restriction of scalars along `f` then sends finitely
generated projective `S`-modules to finitely generated projective `R`-modules
(`RingHom.finiteProjectiveModulesRestrictScalars`), and it is additive, so it induces the
**transfer**

```text
f_* : K₀(S) →+ K₀(R),   [M] ↦ [M viewed as an R-module through f],
```

on the split Grothendieck groups of finitely generated projective left modules. No resolution is
needed here: this is the transfer on projective classes, contravariantly functorial in `f`. It is
not an inverse of extension of scalars `f^* : K₀(R) → K₀(S)`, `[P] ↦ [S ⊗_R P]`.

For commutative rings `K₀` is a commutative ring under the tensor product, and the transfer
satisfies the **projection formula** `f_*(y · f^* x) = f_*(y) · x`. This comes from the
`R`-linear isomorphism `Q ⊗_S (S ⊗_R P) ≅ Q ⊗_R P`
(`TauCeti.BalancedExtension.restrictScalarsTensorIso`). Taking `y = 1` gives
`f_* (f^* x) = [S] · x`, where `[S]` is the class of `S` as an `R`-module. When `S` has a basis of
`n` elements over `R` this is `n • x`; so, for instance, extension along the diagonal
`k → k × k` followed by the transfer is multiplication by `2` on `K₀(k)`.

## Main definitions

* `RingHom.finiteProjectiveModulesK0Restrict`: the transfer `K₀(S) →+ K₀(R)`.

## Main results

* `RingHom.finiteProjectiveModulesK0Restrict_of`: the transfer sends the class of a module to the
  class of its restriction of scalars, and
  `RingHom.finiteProjectiveModulesK0Restrict_of_linearEquiv` to the class of any module isomorphic
  to it.
* `RingHom.finiteProjectiveModulesK0Restrict_id'` and
  `RingHom.finiteProjectiveModulesK0Restrict_comp'`: the transfer is contravariantly functorial,
  with `RingHom.finiteProjectiveModulesK0Restrict_id` and
  `RingHom.finiteProjectiveModulesK0Restrict_comp` their forms for the literal identity and
  composite.
* `RingHom.finiteProjectiveModulesK0Restrict_mul_map_extendScalars` and
  `RingHom.finiteProjectiveModulesK0Restrict_map_extendScalars_mul`: the projection formula for
  commutative rings.
* `RingHom.finiteProjectiveModulesK0Restrict_map_extendScalars`: `f_* (f^* x) = [S] · x`, and
  `RingHom.finiteProjectiveModulesK0Restrict_map_extendScalars_of_basis`: `f_* (f^* x) = n • x`
  when `S` has a basis of `n` elements over `R`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2.8, for
  the transfer on `K₀` along a ring homomorphism making `S` a finitely generated projective
  `R`-module and its projection formula, and Chapter V, §3.3, for the general transfer.
-/

public section

open CategoryTheory MonoidalCategory TauCeti

universe u

namespace RingHom

section Ring

variable {R S T : Type u} [Ring R] [Ring S] [Ring T] (f : R →+* S)
  (hfin : letI := f.toModule; Module.Finite R S)
  (hproj : letI := f.toModule; Module.Projective R S)

/-- **The transfer on projective `K₀`.** A ring homomorphism `f : R →+* S` making `S` a finitely
generated projective `R`-module induces `K₀(S) →+ K₀(R)`, sending the class of a finitely
generated projective `S`-module to the class of the same module with scalars restricted along
`f`. -/
noncomputable def finiteProjectiveModulesK0Restrict :
    SplitK0.{u} (finiteProjectiveModules S).FullSubcategory →+
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  SplitK0.map.{u, u} (f.finiteProjectiveModulesRestrictScalars hfin hproj)

@[simp]
theorem finiteProjectiveModulesK0Restrict_of (M : (finiteProjectiveModules S).FullSubcategory) :
    f.finiteProjectiveModulesK0Restrict hfin hproj (SplitK0.of.{u} M) =
      SplitK0.of.{u} ((f.finiteProjectiveModulesRestrictScalars hfin hproj).obj M) :=
  SplitK0.map_of.{u, u} _ M

/-- The transfer sends the class of `M` to the class of any finitely generated projective
`R`-module isomorphic to `M` with scalars restricted along `f`. -/
theorem finiteProjectiveModulesK0Restrict_of_linearEquiv
    (M : (finiteProjectiveModules S).FullSubcategory)
    (N : (finiteProjectiveModules R).FullSubcategory)
    (e : (ModuleCat.restrictScalars f).obj M.obj ≃ₗ[R] N.obj) :
    f.finiteProjectiveModulesK0Restrict hfin hproj (SplitK0.of.{u} M) = SplitK0.of.{u} N :=
  (f.finiteProjectiveModulesK0Restrict_of hfin hproj M).trans <| SplitK0.of_congr <|
    ObjectProperty.isoMk _
      ((f.finiteProjectiveModulesRestrictScalarsCompιIso hfin hproj).app M ≪≫ e.toModuleIso)

/-! ### Functoriality in the ring homomorphism

As for `G₀` (`RingHom.finiteModulesK0Restrict_comp'`), the primed forms take an equation of ring
homomorphisms, so they apply to ring homomorphisms that are only propositionally an identity or a
composite. -/

/-- The transfer along a ring endomorphism equal to the identity is the identity. -/
theorem finiteProjectiveModulesK0Restrict_id' (f : R →+* R) (h : f = RingHom.id R)
    (hfin : letI := f.toModule; Module.Finite R R)
    (hproj : letI := f.toModule; Module.Projective R R) :
    f.finiteProjectiveModulesK0Restrict hfin hproj = AddMonoidHom.id _ :=
  SplitK0.hom_ext fun M ↦ f.finiteProjectiveModulesK0Restrict_of_linearEquiv hfin hproj M M
    (ModuleCat.restrictScalarsId'App f h M.obj).toLinearEquiv

/-- The transfer along the identity ring homomorphism is the identity. -/
@[simp]
theorem finiteProjectiveModulesK0Restrict_id
    (hfin : letI := (RingHom.id R).toModule; Module.Finite R R)
    (hproj : letI := (RingHom.id R).toModule; Module.Projective R R) :
    (RingHom.id R).finiteProjectiveModulesK0Restrict hfin hproj = AddMonoidHom.id _ :=
  finiteProjectiveModulesK0Restrict_id' _ rfl hfin hproj

/-- **Transfer in a tower.** The transfer along a ring homomorphism equal to a composite `g ∘ f`
is the composite of the transfers along `g` and along `f`, in the reverse order. -/
theorem finiteProjectiveModulesK0Restrict_comp' (g : S →+* T) (gf : R →+* T) (h : gf = g.comp f)
    (hgfin : letI := g.toModule; Module.Finite S T)
    (hgproj : letI := g.toModule; Module.Projective S T)
    (hgffin : letI := gf.toModule; Module.Finite R T)
    (hgfproj : letI := gf.toModule; Module.Projective R T) :
    gf.finiteProjectiveModulesK0Restrict hgffin hgfproj =
      (f.finiteProjectiveModulesK0Restrict hfin hproj).comp
        (g.finiteProjectiveModulesK0Restrict hgfin hgproj) :=
  SplitK0.hom_ext fun M ↦ by
    refine (gf.finiteProjectiveModulesK0Restrict_of_linearEquiv hgffin hgfproj M _
      (ModuleCat.restrictScalarsComp'App f g gf h M.obj ≪≫
        (ModuleCat.restrictScalars f).mapIso
          ((g.finiteProjectiveModulesRestrictScalarsCompιIso hgfin hgproj).app M).symm ≪≫
        ((f.finiteProjectiveModulesRestrictScalarsCompιIso hfin hproj).app _).symm).toLinearEquiv
      ).trans ?_
    rw [AddMonoidHom.comp_apply, finiteProjectiveModulesK0Restrict_of,
      finiteProjectiveModulesK0Restrict_of]

/-- **Transfer in a tower.** The transfer along a composite `g ∘ f` is the composite of the
transfers along `g` and along `f`, in the reverse order. -/
@[simp]
theorem finiteProjectiveModulesK0Restrict_comp (g : S →+* T)
    (hgfin : letI := g.toModule; Module.Finite S T)
    (hgproj : letI := g.toModule; Module.Projective S T)
    (hgffin : letI := (g.comp f).toModule; Module.Finite R T)
    (hgfproj : letI := (g.comp f).toModule; Module.Projective R T) :
    (g.comp f).finiteProjectiveModulesK0Restrict hgffin hgfproj =
      (f.finiteProjectiveModulesK0Restrict hfin hproj).comp
        (g.finiteProjectiveModulesK0Restrict hgfin hgproj) :=
  f.finiteProjectiveModulesK0Restrict_comp' hfin hproj g _ rfl hgfin hgproj hgffin hgfproj

end Ring

/-! ### The projection formula -/

section CommRing

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (hfin : letI := f.toModule; Module.Finite R S)
  (hproj : letI := f.toModule; Module.Projective R S)

/-- The projection formula on classes: `f_*([Q] · [S ⊗_R P]) = f_*[Q] · [P]`. -/
private theorem finiteProjectiveModulesK0Restrict_of_mul_map_extendScalars_of
    (Q : (finiteProjectiveModules S).FullSubcategory)
    (P : (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesK0Restrict hfin hproj
        (SplitK0.of.{u} Q *
          SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars (SplitK0.of.{u} P)) =
      f.finiteProjectiveModulesK0Restrict hfin hproj (SplitK0.of.{u} Q) * SplitK0.of.{u} P := by
  rw [SplitK0.map_of, SplitK0.of_mul_of, finiteProjectiveModulesK0Restrict_of,
    finiteProjectiveModulesK0Restrict_of, SplitK0.of_mul_of]
  -- `Q ⊗_S (S ⊗_R P)`, with scalars restricted to `R`, is `Q ⊗_R P`.
  exact SplitK0.of_congr <| ObjectProperty.isoMk _ <|
    eqToIso (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj _) ≪≫
      (ModuleCat.restrictScalars f).mapIso
        (whiskerLeftIso Q.obj (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj P))) ≪≫
      BalancedExtension.restrictScalarsTensorIso f Q.obj P.obj ≪≫
      whiskerRightIso
        (eqToIso (f.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj Q).symm) P.obj

/-- **The projection formula.** For commutative rings, the transfer satisfies
`f_*(y · f^* x) = f_*(y) · x`, where `f^*` is extension of scalars. -/
theorem finiteProjectiveModulesK0Restrict_mul_map_extendScalars
    (y : SplitK0.{u} (finiteProjectiveModules S).FullSubcategory)
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesK0Restrict hfin hproj
        (y * SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
      f.finiteProjectiveModulesK0Restrict hfin hproj y * x := by
  -- Both sides are biadditive, so it suffices to compare them on classes.
  have h (Q : (finiteProjectiveModules S).FullSubcategory) :
      (f.finiteProjectiveModulesK0Restrict hfin hproj).comp
          ((AddMonoidHom.mulLeft (SplitK0.of.{u} Q)).comp
            (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars)) =
        AddMonoidHom.mulLeft (f.finiteProjectiveModulesK0Restrict hfin hproj (SplitK0.of Q)) :=
    SplitK0.hom_ext
      (f.finiteProjectiveModulesK0Restrict_of_mul_map_extendScalars_of hfin hproj Q)
  have h' : (f.finiteProjectiveModulesK0Restrict hfin hproj).comp
      (AddMonoidHom.mulRight (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x)) =
        (AddMonoidHom.mulRight x).comp (f.finiteProjectiveModulesK0Restrict hfin hproj) :=
    SplitK0.hom_ext fun Q ↦ DFunLike.congr_fun (h Q) x
  exact DFunLike.congr_fun h' y

/-- **The projection formula.** For commutative rings, the transfer satisfies
`f_*(f^* x · y) = x · f_*(y)`, where `f^*` is extension of scalars. -/
theorem finiteProjectiveModulesK0Restrict_map_extendScalars_mul
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory)
    (y : SplitK0.{u} (finiteProjectiveModules S).FullSubcategory) :
    f.finiteProjectiveModulesK0Restrict hfin hproj
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x * y) =
      x * f.finiteProjectiveModulesK0Restrict hfin hproj y := by
  rw [mul_comm, finiteProjectiveModulesK0Restrict_mul_map_extendScalars, mul_comm]

/-- **Transfer after extension of scalars.** For commutative rings, `f_* (f^* x) = [S] · x`,
where `[S]` is the class of `S` as an `R`-module through `f`. -/
theorem finiteProjectiveModulesK0Restrict_map_extendScalars
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesK0Restrict hfin hproj
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
      SplitK0.of.{u} ((f.finiteProjectiveModulesRestrictScalars hfin hproj).obj
        (finiteProjectiveModulesRegular S)) * x := by
  have h := f.finiteProjectiveModulesK0Restrict_mul_map_extendScalars hfin hproj 1 x
  rwa [one_mul, ← FiniteProjectiveModules.splitK0_of_finiteProjectiveModulesRegular,
    finiteProjectiveModulesK0Restrict_of] at h

/-- **Transfer after extension of scalars along a free extension.** For commutative rings, if `S`
has a basis of `n` elements as an `R`-module through `f`, then `f_* (f^* x) = n • x`. For a finite
field extension of degree `d` this is multiplication by `d`. -/
theorem finiteProjectiveModulesK0Restrict_map_extendScalars_of_basis {ι : Type*} [Fintype ι]
    (b : letI := f.toModule; Module.Basis ι R S)
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    f.finiteProjectiveModulesK0Restrict (letI := f.toModule; .of_basis b)
        (letI := f.toModule; .of_basis b)
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
      Fintype.card ι • x := by
  let := f.toModule
  -- `S`, as an `R`-module through `f`, is `R^ι`. The ascription relies on the module structure
  -- `f.toModule` of `b` being, by definition, that of `ModuleCat.restrictScalars f` on `S`.
  let e : (ModuleCat.restrictScalars f).obj (ModuleCat.of S S) ≃ₗ[R] (Fin (Fintype.card ι) → R) :=
    (b.reindex (Fintype.equivFin ι)).equivFun
  rw [finiteProjectiveModulesK0Restrict_map_extendScalars,
    SplitK0.of_eq_nsmul_of_linearEquiv_fin (R' := finiteProjectiveModulesRegular R)
      (((f.finiteProjectiveModulesRestrictScalarsCompιIso _ _).app
        (finiteProjectiveModulesRegular S)).toLinearEquiv.trans e) (.refl _ _),
    FiniteProjectiveModules.splitK0_of_finiteProjectiveModulesRegular, nsmul_one, nsmul_eq_mul]

end CommRing

end RingHom
