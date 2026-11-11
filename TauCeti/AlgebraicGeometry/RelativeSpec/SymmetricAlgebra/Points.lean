/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Tilde

/-!
# Points of affine linear spectra

For a module `M` over a commutative ring `R`, the points of `Spec (Sym_R M)` over `Spec S`, for a
commutative `R`-algebra `S`, are the `R`-linear maps `M → S` (`specSymmetricAlgebraHomEquiv`),
naturally in `S`, and a linear map `f : N → M` induces the morphism
`Spec (Sym_R M) ⟶ Spec (Sym_R N)` that precomposes these functionals with `f`
(`specSymmetricAlgebraMap`).

The comparison `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)` (`relativeSpecSymmetricAlgebraTildeIso`)
identifies these coordinates with the linear maps `M → Γ(Spec S, ⊤)` describing the points of the
relative spectrum (`relativeSpecSymmetricAlgebraTildeHomEquiv`), through `S ≅ Γ(Spec S, ⊤)`, and it
is natural in `M`.

## Main declarations

* `TauCeti.AlgebraicGeometry.specSymmetricAlgebraHomEquiv`: points of `Spec (Sym_R M)` over
  `Spec S` are `R`-linear maps `M → S`;
* `TauCeti.AlgebraicGeometry.specSymmetricAlgebraMap`: the morphism
  `Spec (Sym_R M) ⟶ Spec (Sym_R N)` induced by a linear map `N → M`;
* `relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv` and
  `specSymmetricAlgebraHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_hom`: the comparison
  `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)` on points;
* `relativeSpec_map_comp_relativeSpecSymmetricAlgebraTildeIso_hom`: its naturality in `M`.

## References

* The Stacks Project, Tag 01M1 (vector bundles).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
-/

public section

open CategoryTheory Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R : CommRingCat.{u}} (M : Type u) [AddCommMonoid M] [Module R M]

/-- Points of `Spec (Sym_R M)` over an affine test scheme `Spec S` are `R`-linear
functionals `M → S`. -/
def specSymmetricAlgebraHomEquiv (S : CommAlgCat.{u} R) :
    ((algSpec R).obj (op S) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M)))) ≃ (M →ₗ[R] S) :=
  (algSpecHomEquivAlgHom (CommAlgCat.of R (SymmetricAlgebra R M)) S).trans
    SymmetricAlgebra.lift.symm

/-- The point corresponding to a functional is the spectrum of its symmetric-algebra lift. -/
@[simp]
theorem specSymmetricAlgebraHomEquiv_symm_apply (S : CommAlgCat.{u} R) (g : M →ₗ[R] S) :
    (specSymmetricAlgebraHomEquiv M S).symm g =
      (algSpec R).map (CommAlgCat.ofHom (SymmetricAlgebra.lift g)).op := by
  simp [specSymmetricAlgebraHomEquiv, algSpecHomEquivAlgHom_symm_apply (R := R)]

/-- The spectrum of the lift of a functional has that functional as its point coordinates. -/
@[simp]
theorem specSymmetricAlgebraHomEquiv_map_lift (S : CommAlgCat.{u} R) (g : M →ₗ[R] S) :
    specSymmetricAlgebraHomEquiv M S
      ((algSpec R).map (CommAlgCat.ofHom (SymmetricAlgebra.lift g)).op) = g := by
  rw [← specSymmetricAlgebraHomEquiv_symm_apply, Equiv.apply_symm_apply]

/-- The coordinates of a point are obtained by restricting its algebra homomorphism to
symmetric-algebra generators. -/
theorem specSymmetricAlgebraHomEquiv_apply (S : CommAlgCat.{u} R)
    (p : (algSpec R).obj (op S) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M)))) (m : M) :
    specSymmetricAlgebraHomEquiv M S p m =
      algSpecHomEquivAlgHom (CommAlgCat.of R (SymmetricAlgebra R M)) S p
        (SymmetricAlgebra.ι R M m) := by
  rw [specSymmetricAlgebraHomEquiv, Equiv.trans_apply,
    ← SymmetricAlgebra.lift_ι_apply, Equiv.apply_symm_apply]

/-- The coordinates of an arbitrary point are its pullbacks of the symmetric-algebra
generators, transported from global functions to the test algebra. -/
theorem specSymmetricAlgebraHomEquiv_eq_appTop (S : CommAlgCat.{u} R)
    (p : (algSpec R).obj (op S) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M)))) (m : M) :
    specSymmetricAlgebraHomEquiv M S p m =
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom
        (p.left.appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (SymmetricAlgebra R M))).inv
            (SymmetricAlgebra.ι R M m))) := by
  rw [specSymmetricAlgebraHomEquiv_apply, algSpecHomEquivAlgHom_eq_appTop]

/-- Changing the test algebra postcomposes the linear functional with its algebra map. -/
@[simp]
theorem specSymmetricAlgebraHomEquiv_map_comp {S T : CommAlgCat.{u} R} (h : S ⟶ T)
    (p : (algSpec R).obj (op S) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M)))) :
    specSymmetricAlgebraHomEquiv M T ((algSpec R).map h.op ≫ p) =
      h.hom.toLinearMap.comp (specSymmetricAlgebraHomEquiv M S p) := by
  ext m
  simp only [specSymmetricAlgebraHomEquiv_apply,
    algSpecHomEquivAlgHom_map_comp (R := R), AlgHom.comp_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply]

/-- The point of a postcomposed functional is obtained by changing its test algebra. -/
theorem specSymmetricAlgebraHomEquiv_symm_comp {S T : CommAlgCat.{u} R} (h : S ⟶ T)
    (g : M →ₗ[R] S) :
    (specSymmetricAlgebraHomEquiv M T).symm (h.hom.toLinearMap.comp g) =
      (algSpec R).map h.op ≫ (specSymmetricAlgebraHomEquiv M S).symm g := by
  apply (specSymmetricAlgebraHomEquiv M T).injective
  simp

variable {M} {N : Type u} [AddCommMonoid N] [Module R N]

/-- A linear map induces the contravariant morphism of affine linear spectra. -/
def specSymmetricAlgebraMap (f : N →ₗ[R] M) :
    (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N))) :=
  (algSpec R).map (CommAlgCat.ofHom (SymmetricAlgebra.map R f)).op

/-- The underlying scheme morphism is `Spec` of the induced symmetric-algebra map. -/
@[simp]
theorem specSymmetricAlgebraMap_left (f : N →ₗ[R] M) :
    (specSymmetricAlgebraMap f).left =
      Spec.map (CommRingCat.ofHom (SymmetricAlgebra.map R f).toRingHom) :=
  algSpec_map_left_ofAlgHom R (SymmetricAlgebra.map R f)

/-- The identity linear map induces the identity scheme morphism. -/
@[simp]
theorem specSymmetricAlgebraMap_id :
    specSymmetricAlgebraMap (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  simp [specSymmetricAlgebraMap]

/-- Composing linear maps reverses the order of the induced scheme morphisms. -/
@[simp]
theorem specSymmetricAlgebraMap_comp {P : Type u} [AddCommMonoid P] [Module R P]
    (f : N →ₗ[R] M) (g : P →ₗ[R] N) :
    specSymmetricAlgebraMap (f.comp g) =
      specSymmetricAlgebraMap f ≫ specSymmetricAlgebraMap g := by
  simp only [specSymmetricAlgebraMap, ← SymmetricAlgebra.map_comp_map,
    CommAlgCat.ofHom_comp, op_comp, Functor.map_comp]

/-- On points, the morphism induced by `f` precomposes linear functionals with `f`. -/
@[simp]
theorem specSymmetricAlgebraHomEquiv_comp_specSymmetricAlgebraMap (f : N →ₗ[R] M)
    (S : CommAlgCat.{u} R) (p : (algSpec R).obj (op S) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M)))) :
    specSymmetricAlgebraHomEquiv N S (p ≫ specSymmetricAlgebraMap f) =
      (specSymmetricAlgebraHomEquiv M S p).comp f := by
  ext n
  rw [specSymmetricAlgebraHomEquiv_apply, specSymmetricAlgebraMap,
    algSpecHomEquivAlgHom_comp (R := R)]
  simp [specSymmetricAlgebraHomEquiv_apply]

/-- The affine linear spectrum used by relative Spec is the symmetric-algebra object of
`algSpec` after forgetting its affine-morphism property. -/
@[simp]
theorem specSymmetricAlgebraOver_forget (M : ModuleCat.{u} R) :
    (MorphismProperty.Over.forget _ _ (Spec R)).obj (specSymmetricAlgebraOver M) =
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) :=
  -- Forgetting the affine-morphism property leaves `Over.mk` of `Spec.map` of the
  -- algebra map, exactly the defining object of `algSpec`. Its public object lemma
  -- computes only the structure morphism, so this bundled identification is definitional.
  (rfl)

/-- The affine-spectrum isomorphism induced by a linear equivalence agrees with the
contravariant morphism induced by its inverse linear map. -/
@[simp]
theorem specSymmetricAlgebraOverIso_forget_map_hom {M N : ModuleCat.{u} R}
    (e : M ≃ₗ[R] N) :
    (MorphismProperty.Over.forget _ _ (Spec R)).map (specSymmetricAlgebraOverIso e).hom =
      specSymmetricAlgebraMap e.symm.toLinearMap := by
  apply Over.OverMorphism.ext
  rw [← Over.forget_map, ← Functor.comp_map]
  -- Across the `MorphismProperty.Over.forget` wrapper, `@IsAffineHom` has implicit scheme
  -- binders; plain `rw` cannot typecheck it as `MorphismProperty Scheme` at implicit
  -- transparency. `erw` unfolds it so the composite-forget lemma applies.
  erw [MorphismProperty.Over.forget_comp_forget_map]
  rw [specSymmetricAlgebraOverIso_hom_left, specSymmetricAlgebraMap_left,
    SymmetricAlgebra.mapEquiv_symm]
  congr 2
  exact congrArg (fun f ↦ f.toRingHom) (SymmetricAlgebra.mapEquiv_toAlgHom R e.symm)

end

/-! ### Comparison with the relative spectrum of `M~` -/

noncomputable section

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)


/-- Under `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)`, a point `p` of `Spec (Sym_R M)` over `Spec S`
becomes the point of `Spec_{Spec R} (Sym M~)` whose linear map `M → Γ(Spec S, ⊤)` is the linear
functional `M → S` of `p` followed by `S ≅ Γ(Spec S, ⊤)`. -/
theorem relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv
    (S : CommAlgCat.{u} R)
    (p : (algSpec R).obj (op S) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M)))) (m : M) :
    relativeSpecSymmetricAlgebraTildeHomEquiv M _
        (p ≫ (MorphismProperty.Over.forget _ _ (Spec R)).map
          (relativeSpecSymmetricAlgebraTildeIso M).inv) m =
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv (specSymmetricAlgebraHomEquiv M S p m) := by
  rw [relativeSpecSymmetricAlgebraTildeHomEquiv_eq_appTop, specSymmetricAlgebraHomEquiv_eq_appTop]
  have h : (p ≫ (MorphismProperty.Over.forget _ _ (Spec R)).map
      (relativeSpecSymmetricAlgebraTildeIso M).inv).left ≫
        (relativeSpecSymmetricAlgebraTildeIso M).hom.left = p.left := by
    have e := congrArg (fun f ↦ f.left) (relativeSpecSymmetricAlgebraTildeIso M).inv_hom_id
    exact (Over.comp_left _ _ _ _ _).trans ((Category.assoc _ _ _).trans
      ((congrArg (p.left ≫ ·) e).trans (Category.comp_id _)))
  rw [h]
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso _).hom_inv_id _).symm

/-- Under `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)`, a point `t` of `Spec_{Spec R} (Sym M~)` over
`Spec S` becomes the point of `Spec (Sym_R M)` whose linear functional `M → S` is the linear map
`M → Γ(Spec S, ⊤)` of `t` followed by `Γ(Spec S, ⊤) ≅ S`. -/
theorem specSymmetricAlgebraHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_hom
    (S : CommAlgCat.{u} R)
    (t : (algSpec R).obj (op S) ⟶ (MorphismProperty.Over.forget _ _ (Spec R)).obj
      ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M))))) (m : M) :
    specSymmetricAlgebraHomEquiv M S (t ≫ (MorphismProperty.Over.forget _ _ (Spec R)).map
        (relativeSpecSymmetricAlgebraTildeIso M).hom) m =
      (Scheme.ΓSpecIso (CommRingCat.of S)).hom
        (relativeSpecSymmetricAlgebraTildeHomEquiv M _ t m) := by
  -- composites are combined as terms: rewriting cannot build motives across the
  -- `MorphismProperty.Over` wrapper
  have e : (t ≫ (MorphismProperty.Over.forget _ _ (Spec R)).map
      (relativeSpecSymmetricAlgebraTildeIso M).hom) ≫
        (MorphismProperty.Over.forget _ _ (Spec R)).map
          (relativeSpecSymmetricAlgebraTildeIso M).inv = t :=
    (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ((MorphismProperty.Over.forget _ _
      (Spec R)).mapIso (relativeSpecSymmetricAlgebraTildeIso M)).hom_inv_id).trans
        (Category.comp_id t))
  have h := (congrArg (fun x ↦ relativeSpecSymmetricAlgebraTildeHomEquiv M _ x m) e).symm.trans
    (relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv
      M S _ m)
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso _).inv_hom_id _).symm.trans
    (congrArg (Scheme.ΓSpecIso _).hom h.symm)

variable {M} {N : ModuleCat.{u} R}

/-- The comparison `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)` is natural in `M`: it identifies the
relative spectrum of `Sym f~` with the spectrum of `Sym_R f`, for `f : N ⟶ M`. -/
theorem relativeSpec_map_comp_relativeSpecSymmetricAlgebraTildeIso_hom (f : N ⟶ M) :
    (MorphismProperty.Over.forget _ _ (Spec R)).map ((relativeSpec (Spec R)).map
        ((symmetricAlgebra (Spec R)).map ((tildeEquiv (R := R)).functor.map f)).op) ≫
      (MorphismProperty.Over.forget _ _ (Spec R)).map (relativeSpecSymmetricAlgebraTildeIso N).hom =
    (MorphismProperty.Over.forget _ _ (Spec R)).map (relativeSpecSymmetricAlgebraTildeIso M).hom ≫
      specSymmetricAlgebraMap f.hom := by
  let e :=
    (MorphismProperty.Over.forget _ _ (Spec R)).mapIso (relativeSpecSymmetricAlgebraTildeIso M)
  refine (Iso.inv_comp_eq e).1 ?_
  apply (specSymmetricAlgebraHomEquiv N (CommAlgCat.of R (SymmetricAlgebra R M))).injective
  refine LinearMap.ext fun n ↦ ?_
  -- both sides are compared on the points of the identity of `Spec (Sym_R M)`; the composites are
  -- combined as terms since rewriting cannot build motives across `MorphismProperty.Over`
  have h₁ := specSymmetricAlgebraHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_hom N
    (CommAlgCat.of R (SymmetricAlgebra R M)) (e.inv ≫
      (MorphismProperty.Over.forget _ _ (Spec R)).map ((relativeSpec (Spec R)).map
        ((symmetricAlgebra (Spec R)).map ((tildeEquiv (R := R)).functor.map f)).op)) n
  have h₂ := relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpec_map f _ e.inv n
  have h₃ := relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv
    M (CommAlgCat.of R (SymmetricAlgebra R M)) (𝟙 _) (f n)
  have h₄ := specSymmetricAlgebraHomEquiv_comp_specSymmetricAlgebraMap f.hom
    (CommAlgCat.of R (SymmetricAlgebra R M)) (𝟙 _)
  refine ((congrArg (fun x ↦ specSymmetricAlgebraHomEquiv N _ x n)
    (Category.assoc _ _ _).symm).trans h₁).trans ?_
  refine (congrArg (Scheme.ΓSpecIso _).hom (h₂.trans ((congrArg
    (fun x ↦ relativeSpecSymmetricAlgebraTildeHomEquiv M _ x (f n))
      (Category.id_comp _).symm).trans h₃))).trans ?_
  refine (ConcreteCategory.congr_hom (Scheme.ΓSpecIso _).inv_hom_id _).trans ?_
  exact (congrArg (fun g ↦ g n) ((congrArg (specSymmetricAlgebraHomEquiv N _)
    (Category.id_comp _).symm).trans h₄)).symm

end

end TauCeti.AlgebraicGeometry
