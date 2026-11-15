/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.ModuliProblem

/-!
# Base change of moduli problems along morphisms of base schemes

Let `f : B' ⟶ B` be a morphism of schemes. Postcomposing the structure morphism `S ⟶ B'` of an
object `X = (E/S)` of `Ell/B'` with `f` defines a functor `EllObj.map f : EllObj B' ⥤ EllObj B`,
analogous to `Over.map f` on `Sch/B'`. Restricting a moduli problem `𝒫` on `Ell/B` along
`EllObj.map f` defines the **restricted** (or **base-changed**) moduli problem
`𝒫.baseChange f : ModuliProblem B'` on `Ell/B'` (Katz–Mazur, 4.1–4.3).

Conversely, an object `U = (E/M)` of `Ell/B` pulls back along `f` to the object
`U.pullbackObj f` of `Ell/B'` with base `M ×_B B'`, structure morphism `pullback.snd`, and curve
`E.baseChange pullback.fst`. Arrows `X ⟶ U.pullbackObj f` in `Ell/B'` correspond naturally to
arrows `(EllObj.map f).obj X ⟶ U` in `Ell/B` (`EllObj.homPullbackObjEquiv`), making
`U ↦ U.pullbackObj f` right adjoint to `EllObj.map f` (`EllObj.mapPullbackAdj`).

Consequently:
* **Representability commutes with base change** (`ModuliProblem.representableByPullbackObj`): if
  `𝒫` is represented on `Ell/B` by `U = (E_univ / M)`, then `𝒫.baseChange f` is represented on
  `Ell/B'` by `U.pullbackObj f`, whose base is `M ×_B B'`.
* **Relative representability commutes with base change** (`ModuliProblem.RelRepData.baseChange`):
  relative-representability data `D` for `𝒫` restricts to relative-representability data
  `D.baseChange f` for `𝒫.baseChange f` with the same representing schemes over each
  `X : EllObj B'`, preserving every `HasProperty W`
  (`ModuliProblem.RelRepData.HasProperty.baseChange`).

## Main definitions

* `TauCeti.AlgebraicGeometry.EllObj.map f`: the functor `Ell/B' ⥤ Ell/B` postcomposing structure
  morphisms with `f : B' ⟶ B`.
* `TauCeti.AlgebraicGeometry.EllObj.pullbackObj U f` and `EllObj.pullbackFst U f`: the pullback of
  `U : EllObj B` to `Ell/B'` over `U.base ×_B B'`, and its canonical projection to `U`.
* `TauCeti.AlgebraicGeometry.EllObj.homPullbackObjEquiv` and `EllObj.mapPullbackAdj`: the natural
  bijection `(X ⟶ U.pullbackObj f) ≃ ((EllObj.map f).obj X ⟶ U)` and the adjunction
  `EllObj.map f ⊣ EllObj.pullbackFunctor f`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.baseChange f P`: restriction of `P : ModuliProblem B`
  to `Ell/B'`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.representableByPullbackObj`: base change of a
  representing object `U` to `U.pullbackObj f`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.baseChange`: restriction of
  relative-representability data along `f : B' ⟶ B`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §§4.2–4.3.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllObj

variable {B' B : Scheme.{u}} (f : B' ⟶ B)

/-! ### Pushing objects of `Ell/B'` forward to `Ell/B` -/

/-- **Pushforward of `Ell/B'` along `f : B' ⟶ B`.** Postcomposing the structure morphism
`S ⟶ B'` with `f` views an elliptic curve `E/S` over `B'` as an elliptic curve over `B`, leaving
both `S` and `E` definitionally unchanged. -/
@[expose, simps obj_base obj_structureMap obj_curve map_base map_total]
def map : EllObj B' ⥤ EllObj B where
  obj X := ⟨X.base, X.structureMap ≫ f, X.curve⟩
  map k :=
    { base := k.base
      base_structureMap := by simp
      total := k.total
      isPullback := k.isPullback
      zero_total := k.zero_total }
  map_id _ := hom_ext rfl
  map_comp _ _ := hom_ext rfl

/-- For `X : EllObj B'`, pushing `X.baseChangeFunctor` forward along `f : B' ⟶ B` is naturally
isomorphic to `((EllObj.map f).obj X).baseChangeFunctor`: at each `T : Over X.base`, the base
scheme and elliptic curve are definitionally identical and the structure morphisms differ only by
associativity. -/
noncomputable def mapBaseChangeFunctorIso (X : EllObj B') :
    X.baseChangeFunctor ⋙ map f ≅ ((map f).obj X).baseChangeFunctor :=
  NatIso.ofComponents
    (fun T ↦
      { hom :=
          { base := 𝟙 T.left
            base_structureMap := by dsimp [map, baseChangeFunctor]; simp
            total := 𝟙 (X.curve.baseChange T.hom).carrier
            isPullback := by dsimp [map, baseChangeFunctor]; exact .of_horiz_isIso ⟨by simp⟩
            zero_total := by dsimp [map, baseChangeFunctor]; simp }
        inv :=
          { base := 𝟙 T.left
            base_structureMap := by dsimp [map, baseChangeFunctor]; simp
            total := 𝟙 (X.curve.baseChange T.hom).carrier
            isPullback := by dsimp [map, baseChangeFunctor]; exact .of_horiz_isIso ⟨by simp⟩
            zero_total := by dsimp [map, baseChangeFunctor]; simp }
        hom_inv_id := hom_ext (by dsimp [map, baseChangeFunctor]; simp)
        inv_hom_id := hom_ext (by dsimp [map, baseChangeFunctor]; simp) })
    fun _ ↦ hom_ext (by dsimp [map, baseChangeFunctor]; simp)

/-! ### Pulling objects of `Ell/B` back along `f : B' ⟶ B` -/

/-- **Pullback of an object of `Ell/B` along `f : B' ⟶ B`.** For `U = (E/M)` in `Ell/B`, this is
the object of `Ell/B'` with base `M ×_B B'`, structure morphism `pullback.snd`, and elliptic curve
`E.baseChange pullback.fst`. -/
@[expose, simps]
noncomputable def pullbackObj (U : EllObj B) : EllObj B' where
  base := pullback U.structureMap f
  structureMap := pullback.snd U.structureMap f
  curve := U.curve.baseChange (pullback.fst U.structureMap f)

/-- The canonical projection in `Ell/B` from `U.pullbackObj f` (viewed over `B` via `EllObj.map f`)
to `U`, lying over `pullback.fst U.structureMap f`. -/
noncomputable def pullbackFst (U : EllObj B) : (map f).obj (U.pullbackObj f) ⟶ U where
  base := pullback.fst U.structureMap f
  base_structureMap := pullback.condition
  total := (U.curve.baseChangeIso (pullback.fst U.structureMap f)).hom ≫ pullback.fst _ _
  isPullback := U.curve.isPullback_baseChange (pullback.fst U.structureMap f)
  zero_total := (U.curve.zero_baseChangeIso_hom_assoc (pullback.fst U.structureMap f) _).trans
    (pullbackSection_fst _ _ _ _)

@[simp]
theorem pullbackFst_base (U : EllObj B) :
    (U.pullbackFst f).base = pullback.fst U.structureMap f :=
  (rfl)

@[simp]
theorem pullbackFst_total (U : EllObj B) :
    (U.pullbackFst f).total =
      (U.curve.baseChangeIso (pullback.fst U.structureMap f)).hom ≫ pullback.fst _ _ :=
  (rfl)

private noncomputable def homPullbackObjLift (X : EllObj B') (U : EllObj B)
    (g : (map f).obj X ⟶ U) :
    (map f).obj X ⟶ (map f).obj (U.pullbackObj f) :=
  Hom.lift (U.pullbackFst f) g (pullback.lift g.base X.structureMap g.base_structureMap)
    (pullback.lift_fst _ _ _)

private theorem homPullbackObjLift_base (X : EllObj B') (U : EllObj B)
    (g : (map f).obj X ⟶ U) :
    (homPullbackObjLift f X U g).base =
      pullback.lift g.base X.structureMap g.base_structureMap :=
  Hom.lift_base _ _ _ _

/-- **Universal property of `pullbackObj`.** Arrows `X ⟶ U.pullbackObj f` in `Ell/B'` correspond
bijectively to arrows `(EllObj.map f).obj X ⟶ U` in `Ell/B`, by pushing forward along `EllObj.map f`
and composing with `U.pullbackFst f`. -/
noncomputable def homPullbackObjEquiv (X : EllObj B') (U : EllObj B) :
    (X ⟶ U.pullbackObj f) ≃ ((map f).obj X ⟶ U) where
  toFun k := (map f).map k ≫ U.pullbackFst f
  invFun g :=
    { base := (homPullbackObjLift f X U g).base
      base_structureMap :=
        (homPullbackObjLift_base f X U g =≫ pullback.snd U.structureMap f).trans
          (pullback.lift_snd _ _ _)
      total := (homPullbackObjLift f X U g).total
      isPullback := (homPullbackObjLift f X U g).isPullback
      zero_total := (homPullbackObjLift f X U g).zero_total }
  left_inv k := by
    have hl : homPullbackObjLift f X U ((map f).map k ≫ U.pullbackFst f) = (map f).map k := by
      refine hom_ext_of_comp (U.pullbackFst f) (Hom.lift_comp _ _ _ _) ?_
      refine (homPullbackObjLift_base f X U _).trans ?_
      refine pullback.hom_ext ((pullback.lift_fst _ _ _).trans ?_)
        ((pullback.lift_snd _ _ _).trans ?_)
      · simp; rfl
      · exact k.base_structureMap.symm
    exact hom_ext (congrArg (fun m ↦ m.total) hl)
  right_inv g := Hom.lift_comp (U.pullbackFst f) g _ (pullback.lift_fst _ _ _)

@[simp]
theorem homPullbackObjEquiv_apply (X : EllObj B') (U : EllObj B) (k : X ⟶ U.pullbackObj f) :
    homPullbackObjEquiv f X U k = (map f).map k ≫ U.pullbackFst f :=
  (rfl)

theorem homPullbackObjEquiv_comp {X' X : EllObj B'} (U : EllObj B)
    (i : X' ⟶ X) (k : X ⟶ U.pullbackObj f) :
    homPullbackObjEquiv f X' U (i ≫ k) = (map f).map i ≫ homPullbackObjEquiv f X U k := by
  simp

@[simp]
theorem homPullbackObjEquiv_symm_base (X : EllObj B') (U : EllObj B)
    (g : (map f).obj X ⟶ U) :
    ((homPullbackObjEquiv f X U).symm g).base =
      pullback.lift g.base X.structureMap g.base_structureMap :=
  homPullbackObjLift_base f X U g

/-- **Pullback functor `Ell/B ⥤ Ell/B'`.** Sends `U` to `U.pullbackObj f`, and an arrow `q : U ⟶ V`
to the unique arrow classified by `U.pullbackFst f ≫ q`. -/
@[expose, simps]
noncomputable def pullbackFunctor : EllObj B ⥤ EllObj B' where
  obj U := U.pullbackObj f
  map {U V} q := (homPullbackObjEquiv f (U.pullbackObj f) V).symm (U.pullbackFst f ≫ q)
  map_id U := by
    apply (homPullbackObjEquiv f (U.pullbackObj f) U).injective
    simp
  map_comp {U V W} q r := by
    apply (homPullbackObjEquiv f (U.pullbackObj f) W).injective
    rw [Equiv.apply_symm_apply, homPullbackObjEquiv_comp, Equiv.apply_symm_apply,
      ← Category.assoc ((map f).map _), ← homPullbackObjEquiv_apply, Equiv.apply_symm_apply,
      Category.assoc]

/-- **`EllObj.map f` is left adjoint to `EllObj.pullbackFunctor f`.** -/
noncomputable def mapPullbackAdj : map f ⊣ pullbackFunctor f :=
  Adjunction.mkOfHomEquiv
    { homEquiv X U := (homPullbackObjEquiv f X U).symm
      homEquiv_naturality_left_symm {_ _ U} i k := homPullbackObjEquiv_comp f U i k
      homEquiv_naturality_right {X U V} g q :=
        (homPullbackObjEquiv f X V).injective <| Eq.symm <|
          (homPullbackObjEquiv_comp f V ((homPullbackObjEquiv f X U).symm g)
            ((pullbackFunctor f).map q)).trans <|
            (congrArg ((map f).map _ ≫ ·)
              ((homPullbackObjEquiv f (U.pullbackObj f) V).apply_symm_apply _)).trans <|
              (Category.assoc _ _ _).symm.trans <|
                (congrArg (· ≫ q) ((homPullbackObjEquiv f X U).apply_symm_apply g)).trans <|
                  ((homPullbackObjEquiv f X V).apply_symm_apply (g ≫ q)).symm }

end EllObj

namespace ModuliProblem

variable {B' B : Scheme.{u}} (f : B' ⟶ B)

/-- **Base change (restriction) of a moduli problem along `f : B' ⟶ B`** (Katz–Mazur, 4.1–4.3):
restricts `P : ModuliProblem B` along `EllObj.map f : EllObj B' ⥤ EllObj B`. -/
@[expose, simps!]
def baseChange (P : ModuliProblem B) : ModuliProblem B' :=
  (EllObj.map f).op ⋙ P

/-- The fibre of `P.baseChange f` over `X : EllObj B'` is naturally isomorphic to the fibre of `P`
over `(EllObj.map f).obj X`. -/
noncomputable def baseChangeFibreIso (P : ModuliProblem B) (X : EllObj B') :
    (P.baseChange f).fibre X ≅ P.fibre ((EllObj.map f).obj X) :=
  Functor.isoWhiskerRight (NatIso.op (X.mapBaseChangeFunctorIso f)).symm P

/-- **Representability commutes with base change.** If `P : ModuliProblem B` is represented by
`U : EllObj B`, then `P.baseChange f` is represented on `Ell/B'` by `U.pullbackObj f` (whose base
scheme is `pullback U.structureMap f`). -/
noncomputable def representableByPullbackObj {P : ModuliProblem B} {U : EllObj B}
    (R : P.RepresentableBy U) : (P.baseChange f).RepresentableBy (U.pullbackObj f) where
  homEquiv {X} := (EllObj.homPullbackObjEquiv f X U).trans R.homEquiv
  homEquiv_comp i k := by
    rw [baseChange_map]
    exact (congrArg R.homEquiv (EllObj.homPullbackObjEquiv_comp f U i k)).trans
      (R.homEquiv_comp _ _)

@[simp]
theorem representableByPullbackObj_homEquiv {P : ModuliProblem B} {U : EllObj B}
    (R : P.RepresentableBy U) {X : EllObj B'} (k : X ⟶ U.pullbackObj f) :
    (representableByPullbackObj f R).homEquiv k =
      R.homEquiv ((EllObj.map f).map k ≫ U.pullbackFst f) :=
  (rfl)

namespace RelRepData

/-- **Relative representability commutes with base change.** Relative-representability data `D` for
`P : ModuliProblem B` restricts along `f : B' ⟶ B` to relative-representability data for
`P.baseChange f`, with representing scheme `D.rep ((EllObj.map f).obj X)` over each `X : EllObj B'`.
-/
noncomputable def baseChange {P : ModuliProblem B} (D : P.RelRepData) :
    (P.baseChange f).RelRepData where
  rep X := D.rep ((EllObj.map f).obj X)
  representableBy X :=
    (D.representableBy ((EllObj.map f).obj X)).ofIso (P.baseChangeFibreIso f X).symm

@[simp]
theorem baseChange_rep {P : ModuliProblem B} (D : P.RelRepData) (X : EllObj B') :
    (D.baseChange f).rep X = D.rep ((EllObj.map f).obj X) :=
  (rfl)

/-- Any morphism property `W` held by the representing morphisms of `D` over `Ell/B` also holds for
the restricted data `D.baseChange f` over `Ell/B'`. -/
theorem HasProperty.baseChange {P : ModuliProblem B} {D : P.RelRepData}
    {W : MorphismProperty Scheme.{u}} (h : D.HasProperty W) :
    (D.baseChange f).HasProperty W :=
  (D.baseChange f).hasProperty_iff.mpr fun X ↦ D.hasProperty_iff.mp h ((EllObj.map f).obj X)

end RelRepData

end ModuliProblem

end TauCeti.AlgebraicGeometry
