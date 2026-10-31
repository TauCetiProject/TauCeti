/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Basic

/-!
# The relative spectrum of the symmetric algebra of `M~` on `Spec R`

For a commutative ring `R` and an `R`-module `M`, the relative spectrum
`Spec_{Spec R} (Sym M~)` of the symmetric algebra of the quasicoherent sheaf `M~` on `Spec R`
(`AlgebraicGeometry.tildeEquiv`) is the spectrum `Spec (Sym_R M)` of the symmetric algebra of `M`,
as affine schemes over `Spec R` (`relativeSpecSymmetricAlgebraTildeIso`).

Both schemes represent `R`-linear maps from `M` to global functions. For a scheme `q : T ⟶ Spec R`,
a morphism `T ⟶ Spec_{Spec R} (Sym M~)` over `Spec R` is a module map `M~ ⟶ q_* 𝒪_T`
(`relativeSpecSymmetricAlgebraHomEquiv`), that is an `R`-linear map from `M` to the global sections
of `q_* 𝒪_T`, by the adjunction between `M ↦ M~` and global sections (`tilde.adjunction`); this is
`relativeSpecSymmetricAlgebraTildeHomEquiv`. A morphism `T ⟶ Spec (Sym_R M)` over `Spec R` is an
`R`-algebra map `Sym_R M → Γ(T, ⊤)` by Mathlib's `algΓAlgSpecAdjunction`, that is an `R`-linear
map `M → Γ(T, ⊤)`. Both descriptions are natural in `T`, so the Yoneda lemma gives the isomorphism.
It pulls back the coordinate function `m ∈ M ⊆ Sym_R M` along a point to the value at `m` of the
linear map of the point (`appTop_comp_relativeSpecSymmetricAlgebraTildeIso_hom_left_ι`). This
follows the proof of `relativeSpecSymmetricAlgebraFreeIso` in
`TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.AffineSpace`, which compares
`Spec_X (Sym 𝒪_X^I)` with affine space in the same way.

For a finitely generated projective `R`-module `P`, the dual of the vector bundle `P~` is the sheaf
associated with the dual module of `P`, so this computes the geometric total space of `P~` as
`Spec (Sym_R P^∨)` over `Spec R`.

## Main declarations

* `TauCeti.AlgebraicGeometry.specSymmetricAlgebraOver M`: the spectrum `Spec (Sym_R M)` as an
  affine scheme over `Spec R`;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraTildeHomEquiv`: morphisms
  `T ⟶ Spec_{Spec R} (Sym M~)` over `Spec R` are `R`-linear maps from `M` to the global sections
  of `q_* 𝒪_T`, naturally in `T` (`relativeSpecSymmetricAlgebraTildeHomEquiv_comp`);
* `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraΓLinearEquiv`: for `q : X ⟶ Spec R`,
  the global sections of `q_* 𝒪_X` are the global functions on `X`, as `R`-modules;
* `TauCeti.AlgebraicGeometry.relativeSpecSymmetricAlgebraTildeIso`: the isomorphism
  `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)` of affine schemes over `Spec R`.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique II*, 1.7.
-/

public section

open CategoryTheory MonoidalCategory Opposite

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-! ### Points of `Spec_{Spec R} (Sym M~)` -/

/-- **Points of `Spec_{Spec R} (Sym M~)`.** For an `R`-module `M` and a scheme `q : T ⟶ Spec R`,
morphisms `T ⟶ Spec_{Spec R} (Sym M~)` over `Spec R` correspond to `R`-linear maps from `M` to the
global sections of `q_* 𝒪_T`. It is `relativeSpecSymmetricAlgebraHomEquiv` followed by the
adjunction `tilde.adjunction` between `M ↦ M~` and global sections. -/
def relativeSpecSymmetricAlgebraTildeHomEquiv (T : Over (Spec R)) :
    (T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
          (tildeEquiv.functor.obj M))))) ≃
      (M ⟶ moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward T.hom).obj (𝟙_ T.left.Modules))) :=
  (relativeSpecSymmetricAlgebraHomEquiv _ T).trans (tilde.adjunction.homEquiv _ _)

/-- The linear map of a point of `Spec_{Spec R} (Sym M~)` is the transpose under `tilde.adjunction`
of its module map `M~ ⟶ q_* 𝒪_T`. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_apply (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
      ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
        (tildeEquiv.functor.obj M))))) :
    relativeSpecSymmetricAlgebraTildeHomEquiv M T t =
      tilde.adjunction.homEquiv _ _ (relativeSpecSymmetricAlgebraHomEquiv _ T t) :=
  (rfl)

/-- The bijection `relativeSpecSymmetricAlgebraTildeHomEquiv` is natural in the scheme over
`Spec R`: composing a point with `g : T' ⟶ T` over `Spec R` composes its linear map with pullback
of regular functions along `g`. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_comp {T' T : Over (Spec R)} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
      ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
        (tildeEquiv.functor.obj M))))) :
    relativeSpecSymmetricAlgebraTildeHomEquiv M T' (g ≫ t) =
      relativeSpecSymmetricAlgebraTildeHomEquiv M T t ≫
        moduleSpecΓFunctor.map
          (Scheme.Hom.pushforwardStructureAlgebraMap g.left (Over.w g)).hom.hom := by
  rw [relativeSpecSymmetricAlgebraTildeHomEquiv_apply,
    relativeSpecSymmetricAlgebraTildeHomEquiv_apply, relativeSpecSymmetricAlgebraHomEquiv_comp]
  exact tilde.adjunction.homEquiv_naturality_right _ _

/-! ### The comparison with global functions -/

/-- For a scheme `q : X ⟶ Spec R`, the global sections of `q_* 𝒪_X`, as an `R`-module, are the
global functions on `X`, as an `R`-algebra through `q` (`AlgebraicGeometry.algΓ`). The underlying
map is the inverse of `pushforwardStructureAlgebraΓRingEquiv`. -/
def _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraΓLinearEquiv {X : Scheme.{u}}
    (q : X ⟶ Spec R) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj (𝟙_ X.Modules)) ≃ₗ[R]
      ((algΓ R).obj (Over.mk q)).unop where
  toFun x := q.pushforwardStructureAlgebraΓRingEquiv.symm x
  invFun y := q.pushforwardStructureAlgebraΓRingEquiv y
  map_add' := map_add q.pushforwardStructureAlgebraΓRingEquiv.symm
  -- `R` acts on the global sections of a module on `Spec R` through
  -- `algebraMap R Γ(Spec R, ⊤)`, by definition of `moduleSpecΓFunctor`, and on `Γ(X, ⊤)` through
  -- its pullback along `q`, by definition of `algΓ`.
  map_smul' r x := (q.pushforwardStructureAlgebraΓRingEquiv_symm_smul
    (algebraMap R Γ(Spec R, ⊤) r) x).trans
      (Algebra.smul_def (A := ((algΓ R).obj (Over.mk q)).unop) r _).symm
  left_inv := q.pushforwardStructureAlgebraΓRingEquiv.apply_symm_apply
  right_inv := q.pushforwardStructureAlgebraΓRingEquiv.symm_apply_apply

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraΓLinearEquiv_apply
    {X : Scheme.{u}} (q : X ⟶ Spec R)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward q).obj (𝟙_ X.Modules))) :
    q.pushforwardStructureAlgebraΓLinearEquiv x = q.pushforwardStructureAlgebraΓRingEquiv.symm x :=
  (rfl)

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraΓLinearEquiv_symm_apply
    {X : Scheme.{u}} (q : X ⟶ Spec R) (y : ((algΓ R).obj (Over.mk q)).unop) :
    q.pushforwardStructureAlgebraΓLinearEquiv.symm y = q.pushforwardStructureAlgebraΓRingEquiv y :=
  (rfl)

/-- Points of `Spec_{Spec R} (Sym M~)` over `T` are `R`-linear maps `M → Γ(T, ⊤)`. -/
private def relativeSpecLinearEquiv (T : Over (Spec R)) :
    (T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
          (tildeEquiv.functor.obj M))))) ≃ (M →ₗ[R] ((algΓ R).obj T).unop) :=
  (relativeSpecSymmetricAlgebraTildeHomEquiv M T).trans <| ModuleCat.homEquiv.trans
    (LinearEquiv.congrRight T.hom.pushforwardStructureAlgebraΓLinearEquiv).toEquiv

private lemma relativeSpecLinearEquiv_apply (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
      ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
        (tildeEquiv.functor.obj M))))) (m : M) :
    relativeSpecLinearEquiv M T t m = T.hom.pushforwardStructureAlgebraΓRingEquiv.symm
      (relativeSpecSymmetricAlgebraTildeHomEquiv M T t m) :=
  (rfl)

private lemma relativeSpecLinearEquiv_comp {T' T : Over (Spec R)} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
      ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
        (tildeEquiv.functor.obj M))))) (m : M) :
    relativeSpecLinearEquiv M T' (g ≫ t) m = g.left.appTop (relativeSpecLinearEquiv M T t m) := by
  rw [relativeSpecLinearEquiv_apply, relativeSpecLinearEquiv_apply,
    relativeSpecSymmetricAlgebraTildeHomEquiv_comp]
  exact (congrArg _ (CommMon.sectionsAlgHom_apply _ ⊤ _).symm).trans
    (Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_sectionsAlgHom g.left (Over.w g) _)

/-! ### Points of `Spec (Sym_R M)` -/

variable (R) in
-- The body is exposed so that the underlying scheme and structure morphism compute: the type of
-- `specSymmetricAlgebraOver_hom` depends on `specSymmetricAlgebraOver_left` holding by unfolding.
/-- The spectrum `Spec (Sym_R M)` of the symmetric algebra of an `R`-module `M`, as an affine
scheme over `Spec R`. -/
@[expose]
def specSymmetricAlgebraOver : AffineSchemeOver (Spec R) :=
  MorphismProperty.Over.mk ⊤ (Spec.algebraMap R (SymmetricAlgebra R M)) inferInstance

/-- The underlying scheme of `specSymmetricAlgebraOver R M` is `Spec (Sym_R M)`. -/
@[simp]
lemma specSymmetricAlgebraOver_left :
    (specSymmetricAlgebraOver R M).left = Spec (CommRingCat.of (SymmetricAlgebra R M)) :=
  (rfl)

/-- The structure morphism of `specSymmetricAlgebraOver R M` is `Spec` of the structure map
`R → Sym_R M`. -/
@[simp]
lemma specSymmetricAlgebraOver_hom :
    (specSymmetricAlgebraOver R M).hom = Spec.algebraMap R (SymmetricAlgebra R M) :=
  (rfl)

/-- Points of `Spec (Sym_R M)` over `T` are `R`-linear maps `M → Γ(T, ⊤)`: by the adjunction
`algΓAlgSpecAdjunction` between `Γ` and `Spec` over `Spec R`, they are `R`-algebra maps
`Sym_R M → Γ(T, ⊤)`. -/
private def specLinearEquiv (T : Over (Spec R)) :
    (T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj (specSymmetricAlgebraOver R M)) ≃
      (M →ₗ[R] ((algΓ R).obj T).unop) :=
  -- `specSymmetricAlgebraOver R M` is by definition `algSpec R` applied to `Sym_R M`.
  ((algΓAlgSpecAdjunction R).homEquiv T (op (CommAlgCat.of R (SymmetricAlgebra R M)))).symm.trans <|
    (opEquiv _ _).trans
      { toFun f := SymmetricAlgebra.lift.symm f.hom
        invFun φ := CommAlgCat.ofHom (SymmetricAlgebra.lift φ)
        left_inv f := CommAlgCat.hom_ext (SymmetricAlgebra.lift.apply_symm_apply f.hom)
        right_inv := SymmetricAlgebra.lift.symm_apply_apply }

private lemma specLinearEquiv_apply (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj (specSymmetricAlgebraOver R M))
    (m : M) :
    specLinearEquiv M T t m = t.left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (SymmetricAlgebra R M))).inv (SymmetricAlgebra.ι R M m)) :=
  (rfl)

private lemma specLinearEquiv_comp {T' T : Over (Spec R)} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj (specSymmetricAlgebraOver R M))
    (m : M) :
    specLinearEquiv M T' (g ≫ t) m = g.left.appTop (specLinearEquiv M T t m) := by
  rw [specLinearEquiv_apply, specLinearEquiv_apply, Over.comp_left, Scheme.Hom.comp_appTop]
  exact CommRingCat.comp_apply _ _ _

/-! ### The isomorphism -/

/-- Points of `Spec_{Spec R} (Sym M~)` and of `Spec (Sym_R M)` over `T` correspond, both being
`R`-linear maps `M → Γ(T, ⊤)`. -/
private def pointsEquiv (T : Over (Spec R)) :
    (T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
          (tildeEquiv.functor.obj M))))) ≃
      (T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj (specSymmetricAlgebraOver R M)) :=
  (relativeSpecLinearEquiv M T).trans (specLinearEquiv M T).symm

private lemma specLinearEquiv_pointsEquiv (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
      ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
        (tildeEquiv.functor.obj M))))) :
    specLinearEquiv M T (pointsEquiv M T t) = relativeSpecLinearEquiv M T t :=
  Equiv.apply_symm_apply _ _

private lemma pointsEquiv_comp {T' T : Over (Spec R)} (g : T' ⟶ T)
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
      ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
        (tildeEquiv.functor.obj M))))) :
    pointsEquiv M T' (g ≫ t) = g ≫ pointsEquiv M T t :=
  (specLinearEquiv M T').injective <| LinearMap.ext fun m ↦ by
    rw [specLinearEquiv_comp, specLinearEquiv_pointsEquiv, specLinearEquiv_pointsEquiv,
      relativeSpecLinearEquiv_comp]

variable (R) in
/-- **`Spec_{Spec R} (Sym M~)` is `Spec (Sym_R M)`.** For an `R`-module `M`, the relative spectrum
of the symmetric algebra of the quasicoherent sheaf `M~` on `Spec R` is isomorphic over `Spec R` to
the spectrum of the symmetric algebra of `M`. The isomorphism pulls back the coordinate function
`m ∈ M ⊆ Sym_R M` along a point to the value at `m` of the linear map of the point
(`appTop_comp_relativeSpecSymmetricAlgebraTildeIso_hom_left_ι`), and conversely
(`relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv`). -/
def relativeSpecSymmetricAlgebraTildeIso :
    (relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj (tildeEquiv.functor.obj M))) ≅
      specSymmetricAlgebraOver R M :=
  MorphismProperty.Over.isoMk
    { hom := (pointsEquiv M _ (𝟙 _)).left
      inv := ((pointsEquiv M _).symm (𝟙 _)).left
      hom_inv_id := congrArg CommaMorphism.left ((pointsEquiv M _).injective <|
        (pointsEquiv_comp M _ _).trans <|
          (congrArg (_ ≫ ·) (Equiv.apply_symm_apply _ _)).trans (Category.comp_id _))
      inv_hom_id := congrArg CommaMorphism.left <|
        (pointsEquiv_comp M _ _).symm.trans <|
          (congrArg _ (Category.comp_id _)).trans (Equiv.apply_symm_apply _ _) }
    (Over.w (pointsEquiv M _ (𝟙 _)))

/-- Composed with the isomorphism `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)`, a point `t` over
`Spec R` pulls back the coordinate function `m ∈ M ⊆ Sym_R M` to the value at `m` of the linear map
of `t` (`relativeSpecSymmetricAlgebraTildeHomEquiv`), read as a global function on `T`. -/
lemma appTop_comp_relativeSpecSymmetricAlgebraTildeIso_hom_left_ι (T : Over (Spec R))
    (t : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
      ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj
        (tildeEquiv.functor.obj M))))) (m : M) :
    (t.left ≫ (relativeSpecSymmetricAlgebraTildeIso R M).hom.left).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (SymmetricAlgebra R M))).inv
          (SymmetricAlgebra.ι R M m)) =
      T.hom.pushforwardStructureAlgebraΓRingEquiv.symm
        (relativeSpecSymmetricAlgebraTildeHomEquiv M T t m) :=
  -- The underlying morphism of the isomorphism is by construction that of the point
  -- `pointsEquiv M _ (𝟙 _)`, so the left side is
  -- `specLinearEquiv M T (t ≫ pointsEquiv M _ (𝟙 _)) m` (`specLinearEquiv_apply`), and
  -- `t ≫ pointsEquiv M _ (𝟙 _) = pointsEquiv M T t`.
  LinearMap.congr_fun ((congrArg (specLinearEquiv M T)
    ((pointsEquiv_comp M t (𝟙 _)).symm.trans (congrArg _ (Category.comp_id t)))).trans
      (specLinearEquiv_pointsEquiv M T t)) m

/-- The linear map of the point `s ≫ e⁻¹` of `Spec_{Spec R} (Sym M~)`, for a point `s` of
`Spec (Sym_R M)` over `Spec R` and `e` the isomorphism `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)`,
sends `m` to the pullback along `s` of the coordinate function `m ∈ M ⊆ Sym_R M`. -/
lemma relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv
    (T : Over (Spec R))
    (s : T ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj (specSymmetricAlgebraOver R M))
    (m : M) :
    T.hom.pushforwardStructureAlgebraΓRingEquiv.symm
        (relativeSpecSymmetricAlgebraTildeHomEquiv M T
          (s ≫ (MorphismProperty.Over.forget _ _ (Spec R)).map
            (relativeSpecSymmetricAlgebraTildeIso R M).inv) m) =
      s.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of (SymmetricAlgebra R M))).inv
        (SymmetricAlgebra.ι R M m)) :=
  -- The inverse of the isomorphism is by construction the point `(pointsEquiv M _).symm (𝟙 _)`,
  -- so the left side is `relativeSpecLinearEquiv M T (s ≫ (pointsEquiv M _).symm (𝟙 _)) m`
  -- (`relativeSpecLinearEquiv_apply`), and `pointsEquiv` sends that point to `s`.
  LinearMap.congr_fun ((specLinearEquiv_pointsEquiv M T _).symm.trans
    (congrArg (specLinearEquiv M T) ((pointsEquiv_comp M s _).trans
      ((congrArg (s ≫ ·) (Equiv.apply_symm_apply _ _)).trans (Category.comp_id s))))) m

end TauCeti.AlgebraicGeometry
