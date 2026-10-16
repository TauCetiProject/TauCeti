/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.ExactOrder.Scheme
public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem

/-!
# The moduli problem `[Γ₁(N)]`

Following Katz and Mazur, a `[Γ₁(N)]`-structure on an elliptic curve `E` over a scheme `S` is an
`S`-point `P` of `E` of exact order `N`: the divisor `[P] + [2P] + ⋯ + [NP]` on `E` is a subgroup
scheme (`EllipticCurveGeom.IsOfExactOrder`). This is Drinfeld's notion, which makes sense over
every base, including bases on which `N` is not invertible.

An arrow `(E'/S') ⟶ (E/S)` of `Ell/B` exhibits `E'` as the base change of `E`, so every `S`-point
of `E` has a base change, an `S'`-point of `E'` (`EllipticCurveGeom.pointsPullback`), and points
of exact order `N` pull back to points of exact order `N`
(`EllipticCurveGeom.IsOfExactOrder.pointsPullback`). Base change of points is functorial, so the
`[Γ₁(N)]`-structures form a moduli problem over `Ell/B` (`ModuliProblem.gammaOne`). For `N = 1`
the only point of exact order one is the zero section, so `[Γ₁(1)]` is the trivial moduli problem
`[Γ(1)]` (`ModuliProblem.gammaOneOneIso`).

The problem `[Γ₁(N)]` is relatively representable (`ModuliProblem.gammaOneRelRepData`): for an
object `(E/S)` and a scheme `T` over `S`, the `[Γ₁(N)]`-structures on the base change `E_T` are the
morphisms from `T` to the exact-order scheme `E.exactOrderScheme N` over `S`
(`ModuliProblem.gammaOneBaseChangeEquiv`), the closed subscheme of `E` on which the universal point
has exact order `N`. It lies in `E[N]`, so for `N ≠ 0` the problem `[Γ₁(N)]` is finite over `Ell/B`
(`ModuliProblem.hasProperty_isFinite_gammaOneRelRepData`). No hypothesis is placed on `B`.

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOne B N`: the moduli problem `[Γ₁(N)]` over
  `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneEquiv`: the `[Γ₁(N)]`-structures on an object
  `(E/S)` of `Ell/B` are the `S`-points of `E` of exact order `N`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneBaseChangeEquiv`: the `[Γ₁(N)]`-structures on
  the base change `E_T` are the morphisms from `T` to the exact-order scheme of `E`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneRelRepData`: `[Γ₁(N)]` is relatively
  representable, by the exact-order scheme.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneEquiv_map`: the pull-back of a
  `[Γ₁(N)]`-structure along an arrow of `Ell/B` is the base change of its point.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneOneIso`: `[Γ₁(1)]` is the trivial moduli
  problem.
* `TauCeti.AlgebraicGeometry.ModuliProblem.gammaOneBaseChangeEquiv_map`: the correspondence with
  morphisms to the exact-order scheme is natural in `T`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.hasProperty_isFinite_gammaOneRelRepData`: for `N ≠ 0`,
  `[Γ₁(N)]` is finite over `Ell/B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.4 (points of exact order
  `N`), §3.2 (the moduli problem `[Γ₁(N)]`), 3.6.0 (its relative representability by a finite
  scheme) and Chapter 4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry
  MonObj

universe u

namespace TauCeti.AlgebraicGeometry

variable {B : Scheme.{u}}

namespace ModuliProblem

variable (B) (N : ℕ)

/-- **The moduli problem `[Γ₁(N)]`** over `Ell/B` (Katz–Mazur, §3.2). A `[Γ₁(N)]`-structure on an
object `(E/S)` of `Ell/B` is an `S`-point of `E` of exact order `N` (`gammaOneEquiv`), and it pulls
back along an arrow of `Ell/B` by base change of points (`gammaOneEquiv_map`). -/
noncomputable def gammaOne : ModuliProblem B where
  obj X := ULift.{u + 1}
    {P : 𝟙_ (Over X.unop.base) ⟶ Over.mk X.unop.curve.structureMap //
      X.unop.curve.IsOfExactOrder P N}
  map φ := TypeCat.ofHom fun P ↦
    ⟨⟨EllipticCurveGeom.pointsPullback φ.unop.isPullback φ.unop.zero_total P.down.1,
      P.down.2.pointsPullback φ.unop.isPullback φ.unop.zero_total⟩⟩
  map_id X := by
    ext P
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm
  map_comp φ ψ := by
    ext P
    exact congrArg Over.Hom.left ((EllipticCurveGeom.eq_pointsPullback_iff _ _).mpr
      (by simp)).symm

variable {B N}

/-- The `[Γ₁(N)]`-structures on an object `(E/S)` of `Ell/B` are the `S`-points of `E` of exact
order `N`. -/
noncomputable def gammaOneEquiv (X : EllObj B) :
    (gammaOne B N).obj (op X) ≃
      {P : 𝟙_ (Over X.base) ⟶ Over.mk X.curve.structureMap // X.curve.IsOfExactOrder P N} :=
  Equiv.ulift

/-- The pull-back of a `[Γ₁(N)]`-structure along an arrow `φ` of `Ell/B` is the base change of its
point along `φ`. -/
@[simp]
theorem gammaOneEquiv_map {X Y : EllObj B} (φ : X ⟶ Y) (α : (gammaOne B N).obj (op Y)) :
    (gammaOneEquiv X ((gammaOne B N).map φ.op α)).1 =
      EllipticCurveGeom.pointsPullback φ.isPullback φ.zero_total (gammaOneEquiv Y α).1 :=
  (rfl)

/-- An `S`-point of exact order one is the zero section, so an object of `Ell/B` has exactly one
`[Γ₁(1)]`-structure. -/
noncomputable instance (X : (EllObj B)ᵒᵖ) : Unique ((gammaOne B 1).obj X) where
  default := (gammaOneEquiv X.unop).symm ⟨1, EllipticCurveGeom.isOfExactOrder_one_iff.mpr rfl⟩
  uniq α := (gammaOneEquiv X.unop).injective <| Subtype.ext <| by
    simpa using EllipticCurveGeom.isOfExactOrder_one_iff.mp (gammaOneEquiv X.unop α).2

variable (B) in
/-- **`[Γ₁(1)]` is the trivial moduli problem** `[Γ(1)]`: the only point of exact order one of an
elliptic curve is its zero section. -/
noncomputable def gammaOneOneIso : gammaOne B 1 ≅ 𝟙_ (ModuliProblem B) :=
  isoTensorUnitOfUnique _

/-! ### Relative representability of `[Γ₁(N)]` -/

section RelRep

/-- **`[Γ₁(N)]`-structures on base changes are points of the exact-order scheme.** For an object
`X = (E/S)` of `Ell/B` and a scheme `T` over `S`, the `[Γ₁(N)]`-structures on the base change `E_T`
of `E` correspond to the morphisms `T ⟶ E.exactOrderScheme N` over `S`: a structure, a `T`-point
`P` of `E_T` of exact order `N`, corresponds to the morphism whose image in `E` is `P` followed by
the projection `E_T ⟶ E` (`gammaOneBaseChangeEquiv_apply_left_comp`). -/
noncomputable def gammaOneBaseChangeEquiv (X : EllObj B) (T : Over X.base) :
    (gammaOne B N).obj (op (X.baseChangeFunctor.obj T)) ≃ (T ⟶ X.curve.exactOrderScheme N) :=
  (gammaOneEquiv _).trans <|
    EllipticCurveGeom.exactOrderPointsEquivOfIsPullback (E' := X.curve.baseChange T.hom) N
      (X.curve.isPullback_baseChange T.hom) (by simp)

/-- The morphism `T ⟶ E.exactOrderScheme N` of a `[Γ₁(N)]`-structure on `E_T`, followed by the
inclusion of the exact-order scheme in `E`, is the point of the structure followed by the
projection `E_T ⟶ E`. -/
@[reassoc (attr := simp)]
theorem gammaOneBaseChangeEquiv_apply_left_comp (X : EllObj B) (T : Over X.base)
    (α : (gammaOne B N).obj (op (X.baseChangeFunctor.obj T))) :
    (gammaOneBaseChangeEquiv X T α).left ≫ (X.curve.exactOrderLocus N).subschemeι =
      (gammaOneEquiv _ α).1.left ≫ (X.curve.baseChangeIso T.hom).hom ≫ pullback.fst _ _ :=
  EllipticCurveGeom.exactOrderPointsEquivOfIsPullback_apply_left_comp _ _ _

/-- **Naturality of `gammaOneBaseChangeEquiv`.** Along a morphism `k : T' ⟶ T` of schemes over the
base of `X`, the morphism `T' ⟶ E.exactOrderScheme N` of the pull-back to `E_{T'}` of a
`[Γ₁(N)]`-structure on `E_T` is the composite of `k` with the morphism of the structure. -/
theorem gammaOneBaseChangeEquiv_map (X : EllObj B) {T' T : Over X.base} (k : T' ⟶ T)
    (α : (gammaOne B N).obj (op (X.baseChangeFunctor.obj T))) :
    gammaOneBaseChangeEquiv X T' ((gammaOne B N).map (X.baseChangeFunctor.map k).op α) =
      k ≫ gammaOneBaseChangeEquiv X T α := by
  -- both sides are compared as points of `E` with values in `T'`
  refine (cancel_mono (X.curve.exactOrderSchemeι N)).mp ?_
  ext1
  simp only [Over.comp_left, Category.assoc, EllipticCurveGeom.exactOrderSchemeι_left,
    gammaOneBaseChangeEquiv_apply_left_comp, gammaOneEquiv_map]
  -- the morphism `E_{T'} ⟶ E_T` lies over `k` and composes with `E_T ⟶ E` to `E_{T'} ⟶ E`
  have hk := congrArg EllObj.Hom.total (X.baseChangeFunctor_map_baseChangeFunctorHom k)
  simp only [EllObj.comp_total, EllObj.baseChangeFunctorHom_total] at hk
  -- the composites are formed by terms, since the base change `E_{T'}` appears both as
  -- `(X.baseChangeFunctor.obj T').curve` and as `X.curve.baseChange T'.hom`
  exact (congrArg (fun m ↦ (EllipticCurveGeom.pointsPullback (X.baseChangeFunctor.map k).isPullback
    (X.baseChangeFunctor.map k).zero_total (gammaOneEquiv _ α).1).left ≫ m) hk.symm).trans
      (EllipticCurveGeom.pointsPullback_left_comp_assoc _ _ _ _)

/-- Naturality of `gammaOneBaseChangeEquiv`, read backwards: the `[Γ₁(N)]`-structure on `E_{T'}` of
the composite of `k : T' ⟶ T` with a morphism `T ⟶ E.exactOrderScheme N` is the pull-back of the
structure on `E_T` of that morphism. -/
theorem gammaOneBaseChangeEquiv_symm_comp (X : EllObj B) {T' T : Over X.base} (k : T' ⟶ T)
    (a : T ⟶ X.curve.exactOrderScheme N) :
    (gammaOneBaseChangeEquiv X T').symm (k ≫ a) =
      (gammaOne B N).map (X.baseChangeFunctor.map k).op ((gammaOneBaseChangeEquiv X T).symm a) := by
  rw [Equiv.symm_apply_eq, gammaOneBaseChangeEquiv_map, Equiv.apply_symm_apply]

variable (B N) in
/-- **The moduli problem `[Γ₁(N)]` is relatively representable** (Katz–Mazur, 3.6.0). For an
object `X = (E/S)` of `Ell/B`, the functor `T ↦ [Γ₁(N)](E_T/T)` on schemes over `S` is represented
by the exact-order scheme `E.exactOrderScheme N`, the closed subscheme of `E` of points of exact
order `N`, through `gammaOneBaseChangeEquiv`. No hypothesis is placed on `B`, and `N` need not be
invertible on it. -/
noncomputable def gammaOneRelRepData : (gammaOne B N).RelRepData where
  rep X := X.curve.exactOrderScheme N
  representableBy X :=
    { homEquiv := (gammaOneBaseChangeEquiv X _).symm
      homEquiv_comp k a := (gammaOneBaseChangeEquiv_symm_comp X k a).trans
        -- the fibre of `[Γ₁(N)]` over `X` at `T` is `[Γ₁(N)](E_T/T)` after unfolding `fibre`
        rfl }

/-- The scheme representing `[Γ₁(N)]`-structures on base changes of `X = (E/S)` is the exact-order
scheme of `E`. -/
@[simp]
theorem gammaOneRelRepData_rep (X : EllObj B) :
    (gammaOneRelRepData B N).rep X = X.curve.exactOrderScheme N :=
  (rfl)

/-- The `[Γ₁(N)]`-structure on `E_T` of a morphism from `T` to the representing scheme is the one
given by `gammaOneBaseChangeEquiv`, after identifying the representing scheme with the exact-order
scheme through `gammaOneRelRepData_rep`. -/
@[simp]
theorem gammaOneRelRepData_homEquiv (X : EllObj B) {T : Over X.base}
    (a : T ⟶ (gammaOneRelRepData B N).rep X) :
    ((gammaOneRelRepData B N).representableBy X).homEquiv a =
      (gammaOneBaseChangeEquiv X T).symm (a ≫ eqToHom (gammaOneRelRepData_rep X)) :=
  congrArg (gammaOneBaseChangeEquiv X T).symm (Category.comp_id a).symm

variable (B N) in
/-- **The moduli problem `[Γ₁(N)]` is finite over `Ell/B`** (Katz–Mazur, 3.6.0) for `N ≠ 0`: each
representing scheme, the exact-order scheme of an elliptic curve `E/S`, is a closed subscheme of
`E[N]` and hence finite over `S`. -/
theorem hasProperty_isFinite_gammaOneRelRepData [NeZero N] :
    (gammaOneRelRepData B N).HasProperty @IsFinite :=
  (RelRepData.hasProperty_iff _).mpr fun X ↦
    EllipticCurveGeom.isFinite_exactOrderScheme_hom X.curve N

end RelRep

end ModuliProblem

end TauCeti.AlgebraicGeometry
