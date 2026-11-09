/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Scalar
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LinearPoints

/-!
# Recognizing linear morphisms of affine linear spectra

For arbitrary modules `M` and `N` over a commutative ring `R`, a scheme morphism
`Spec (Sym M) ⟶ Spec (Sym N)` over `Spec R` is induced by a unique linear map `N → M`
if its action on points commutes with every scalar in every commutative test algebra.
In particular, this condition forces additivity by applying
`TauCeti.SymmetricAlgebra.linearPoints_add_of_smul` to `specSymmetricAlgebraPointsMap`;
no characteristic or finiteness hypothesis is needed. Testing only the scalars of `R`
would not suffice.

`specSymmetricAlgebraHomEquiv` identifies actual affine-scheme points with linear functionals,
naturally in the test algebra. The recognition theorem transports the algebraic result
`TauCeti.SymmetricAlgebra.existsUnique_linearMap_of_linearPoints_smul` along this identification.

The same holds for the relative spectra `𝕍(F) = Spec_{Spec R} (Sym F)` of quasicoherent sheaves on
`Spec R`, with the scalar condition replaced by the module structure of `𝕍(F)` over the affine line
`𝔸¹_{Spec R}` (`modObjRelativeSpecSymmetricAlgebra`): a morphism `𝕍(F) ⟶ 𝕍(F')` over `Spec R`
commuting with the actions of `𝔸¹_{Spec R}` is the relative spectrum of `Sym a` for a unique
`a : F' ⟶ F` (`existsUnique_relativeSpec_map_of_isModHom`). Under the comparison
`Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)` (`relativeSpecSymmetricAlgebraTildeIso`), points over
`Spec S` become `R`-linear maps `M → S` and the action of `c ∈ S` becomes multiplication by `c`,
so this follows from the affine criterion above.

The morphisms `Spec_X (Sym a)` are the underlying morphisms of the morphisms of linear schemes
`(linearSpec X).obj (op F) ⟶ (linearSpec X).obj (op F')`, that is of the morphisms preserving
the gradings of the coordinate algebras, since `linearSpec X` is full (`linearSpecEquiv`). Over
`Spec R` the results here therefore identify the morphisms commuting with scalar multiplication
with the grading-preserving ones. They assume an affine base, as they are deduced from the
comparison with `Spec (Sym_R M)`.

## Main declarations

* `TauCeti.AlgebraicGeometry.specSymmetricAlgebraHomEquiv`: points of `Spec (Sym_R M)` over
  `Spec S` are `R`-linear maps `M → S`;
* `TauCeti.AlgebraicGeometry.existsUnique_specSymmetricAlgebraMap_of_smul`: a morphism
  `Spec (Sym_R M) ⟶ Spec (Sym_R N)` commuting with scalars on points is induced by a unique linear
  map `N → M`;
* `relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv` and
  `relativeSpec_map_comp_relativeSpecSymmetricAlgebraTildeIso_hom`: the comparison
  `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)` on points, and its naturality in `M`;
* `TauCeti.AlgebraicGeometry.existsUnique_relativeSpec_map_tilde_of_isModHom` and
  `TauCeti.AlgebraicGeometry.existsUnique_relativeSpec_map_of_isModHom`: a morphism
  `Spec_{Spec R} (Sym F) ⟶ Spec_{Spec R} (Sym F')` commuting with the actions of the affine line is
  the relative spectrum of `Sym a` for a unique `a : F' ⟶ F`, and
  `TauCeti.AlgebraicGeometry.isModHom_iff_exists_relativeSpec_map` states the equivalence.

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

/-- A morphism of affine linear spectra induces a natural transformation of linear point
functors, without any assumption that the morphism itself is linear. -/
def specSymmetricAlgebraPointsMap
    (ψ : (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N)))) :
    SymmetricAlgebra.linearPoints R M ⟶ SymmetricAlgebra.linearPoints R N where
  app S := TypeCat.ofHom fun g ↦ specSymmetricAlgebraHomEquiv N S
    ((specSymmetricAlgebraHomEquiv M S).symm g ≫ ψ)
  naturality S T h := by
    apply ConcreteCategory.hom_ext
    intro g
    simp only [CategoryTheory.comp_apply, TypeCat.ofHom_apply,
      specSymmetricAlgebraHomEquiv_symm_comp,
      Category.assoc, specSymmetricAlgebraHomEquiv_map_comp]

/-- The induced transformation is computed by composing the corresponding scheme point. -/
@[simp]
theorem specSymmetricAlgebraPointsMap_app
    (ψ : (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N))))
    (S : CommAlgCat.{u} R) (g : M →ₗ[R] S) :
    (specSymmetricAlgebraPointsMap ψ).app S g = specSymmetricAlgebraHomEquiv N S
      ((specSymmetricAlgebraHomEquiv M S).symm g ≫ ψ) :=
  (rfl)

/-- Scheme morphisms are determined by their action on affine linear-spectrum points. -/
theorem specSymmetricAlgebraPointsMap_injective :
    Function.Injective (specSymmetricAlgebraPointsMap (R := R) (M := M) (N := N)) := by
  intro ψ χ h
  let S := CommAlgCat.of R (SymmetricAlgebra R M)
  let p := specSymmetricAlgebraHomEquiv M S (𝟙 _)
  have hp : (specSymmetricAlgebraPointsMap ψ).app S p =
      (specSymmetricAlgebraPointsMap χ).app S p :=
    congrArg (fun τ : SymmetricAlgebra.linearPoints R M ⟶
      SymmetricAlgebra.linearPoints R N ↦ τ.app S p) h
  rw [specSymmetricAlgebraPointsMap_app, specSymmetricAlgebraPointsMap_app] at hp
  have hp' := (specSymmetricAlgebraHomEquiv N S).injective hp
  simpa only [p, Equiv.symm_apply_apply, Category.id_comp] using hp'

/-- The transformation induced by the spectrum of `Sym f` is precomposition with `f`. -/
@[simp]
theorem specSymmetricAlgebraPointsMap_specSymmetricAlgebraMap (f : N →ₗ[R] M) :
    specSymmetricAlgebraPointsMap (specSymmetricAlgebraMap f) =
      SymmetricAlgebra.linearPointsMap R f := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro g
  simp only [specSymmetricAlgebraPointsMap_app (R := R),
    specSymmetricAlgebraHomEquiv_comp_specSymmetricAlgebraMap (R := R),
    Equiv.apply_symm_apply, SymmetricAlgebra.linearPointsMap_app_apply R f]

/-- A scheme morphism of affine linear spectra whose action on points commutes with all
test-algebra scalars is induced by a unique linear map. In particular this criterion works
over finite and nonreduced rings, with arbitrary modules. -/
theorem existsUnique_specSymmetricAlgebraMap_of_smul
    (ψ : (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N))))
    (hψ : ∀ (S : CommAlgCat.{u} R) (c : S) (g : M →ₗ[R] S),
      (specSymmetricAlgebraPointsMap ψ).app S (c • g) =
        c • ((specSymmetricAlgebraPointsMap ψ).app S g : N →ₗ[R] S)) :
    ∃! f : N →ₗ[R] M, ψ = specSymmetricAlgebraMap f := by
  obtain ⟨f, hf, hu⟩ := SymmetricAlgebra.existsUnique_linearMap_of_linearPoints_smul
    R (specSymmetricAlgebraPointsMap ψ) hψ
  refine ⟨f, specSymmetricAlgebraPointsMap_injective (hf.trans
    (specSymmetricAlgebraPointsMap_specSymmetricAlgebraMap f).symm), ?_⟩
  intro g hg
  apply hu
  rw [hg, specSymmetricAlgebraPointsMap_specSymmetricAlgebraMap]

/-- The scalar-equivariance criterion is equivalent to being induced by a linear map. -/
theorem specSymmetricAlgebraPointsMap_smul_iff_exists_specSymmetricAlgebraMap
    (ψ : (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N)))) :
    (∀ (S : CommAlgCat.{u} R) (c : S) (g : M →ₗ[R] S),
      (specSymmetricAlgebraPointsMap ψ).app S (c • g) =
        c • ((specSymmetricAlgebraPointsMap ψ).app S g : N →ₗ[R] S)) ↔
      ∃ f : N →ₗ[R] M, ψ = specSymmetricAlgebraMap f := by
  constructor
  · intro h
    exact (existsUnique_specSymmetricAlgebraMap_of_smul ψ h).exists
  · rintro ⟨f, rfl⟩ S c g
    rw [specSymmetricAlgebraPointsMap_specSymmetricAlgebraMap]
    exact SymmetricAlgebra.linearPointsMap_app_smul R f S c g

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

/-! ### Relative spectra over an affine base -/

noncomputable section

open MonoidalCategory CartesianMonoidalCategory

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

/-- **Scalar multiples under `Spec_{Spec R} (Sym M~) ≅ Spec (Sym_R M)`.** For a commutative
`R`-algebra `S`, the point of `Spec (Sym_R M)` over `Spec S` given by `c • φ`, for `c ∈ S` and a
linear functional `φ : M → S`, corresponds to the scalar multiple, by the function `c` on `Spec S`,
of the point corresponding to `φ`, for the action of the affine line on
`Spec_{Spec R} (Sym M~)`. -/
theorem specSymmetricAlgebraHomEquiv_symm_smul_comp_relativeSpecSymmetricAlgebraTildeIso_inv
    (S : CommAlgCat.{u} R) (c : S) (φ : M →ₗ[R] S) :
    (specSymmetricAlgebraHomEquiv M S).symm (c • φ) ≫
        (MorphismProperty.Over.forget _ _ (Spec R)).map
          (relativeSpecSymmetricAlgebraTildeIso M).inv =
      lift ((AffineSpace.homAsOverEquiv _).symm fun _ ↦ (Scheme.ΓSpecIso (CommRingCat.of S)).inv c)
          ((specSymmetricAlgebraHomEquiv M S).symm φ ≫
            (MorphismProperty.Over.forget _ _ (Spec R)).map
              (relativeSpecSymmetricAlgebraTildeIso M).inv) ≫
        relativeSpecSymmetricAlgebraSMul _ := by
  apply (relativeSpecSymmetricAlgebraTildeHomEquiv M _).injective
  ext m
  simp only [relativeSpecSymmetricAlgebraTildeHomEquiv_lift_comp_smul, Equiv.apply_symm_apply,
    relativeSpecSymmetricAlgebraTildeHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_inv,
    LinearMap.smul_apply, smul_eq_mul, map_mul]
  exact congrArg (· * _) (congrFun (Equiv.apply_symm_apply
    (AffineSpace.homAsOverEquiv ((algSpec R).obj (op S)))
    fun _ : PUnit.{u + 1} ↦ (Scheme.ΓSpecIso (CommRingCat.of S)).inv c) PUnit.unit).symm

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

/-- **Linear morphisms of linear spectra over `Spec R`.** For `R`-modules `M` and `N`, a morphism
`Spec_{Spec R} (Sym M~) ⟶ Spec_{Spec R} (Sym N~)` over `Spec R` that commutes with the actions of
the affine line `𝔸¹_{Spec R}` is the relative spectrum of `Sym f~` for a unique linear map
`f : N ⟶ M`. -/
theorem existsUnique_relativeSpec_map_tilde_of_isModHom
    (g : (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M)))) ⟶
      (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj N)))))
    [IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) g] :
    ∃! f : N ⟶ M, g = (MorphismProperty.Over.forget _ _ (Spec R)).map ((relativeSpec (Spec R)).map
      ((symmetricAlgebra (Spec R)).map ((tildeEquiv (R := R)).functor.map f)).op) := by
  -- `g` becomes a morphism `ψ : Spec (Sym_R M) ⟶ Spec (Sym_R N)`, to which the affine criterion
  -- `existsUnique_specSymmetricAlgebraMap_of_smul` applies. The isomorphisms are stated with
  -- `algSpec` targets, so that all composites below share their intermediate objects.
  let eM : (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj M)))) ≅
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) :=
    (MorphismProperty.Over.forget _ _ (Spec R)).mapIso (relativeSpecSymmetricAlgebraTildeIso M)
  let eN : (MorphismProperty.Over.forget _ _ (Spec R)).obj ((relativeSpec (Spec R)).obj
        (op ((symmetricAlgebra (Spec R)).obj ((tildeEquiv (R := R)).functor.obj N)))) ≅
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N))) :=
    (MorphismProperty.Over.forget _ _ (Spec R)).mapIso (relativeSpecSymmetricAlgebraTildeIso N)
  let ψ := eM.inv ≫ g ≫ eN.hom
  have hg : relativeSpecSymmetricAlgebraSMul _ ≫ g =
      (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R) ◁ g) ≫ relativeSpecSymmetricAlgebraSMul _ :=
    IsModHom.smul_hom (A := 𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) (f := g)
  have hψ (S : CommAlgCat.{u} R) (c : S) (φ : M →ₗ[R] S) :
      (specSymmetricAlgebraPointsMap ψ).app S (c • φ) =
        c • ((specSymmetricAlgebraPointsMap ψ).app S φ : N →ₗ[R] S) := by
    refine LinearMap.ext fun n ↦ ?_
    let a := (AffineSpace.homAsOverEquiv ((algSpec R).obj (op S))).symm
      fun _ : PUnit.{u + 1} ↦ (Scheme.ΓSpecIso (CommRingCat.of S)).inv c
    let p := (specSymmetricAlgebraHomEquiv M S).symm φ
    -- the point of `c • φ` is the scalar multiple `a • (p ≫ eM.inv)`, and `g` is linear
    have key : (specSymmetricAlgebraHomEquiv M S).symm (c • φ) ≫ ψ =
        (lift a ((p ≫ eM.inv) ≫ g) ≫ relativeSpecSymmetricAlgebraSMul _) ≫ eN.hom := by
      have h₁ := congrArg (· ≫ g ≫ eN.hom)
        (specSymmetricAlgebraHomEquiv_symm_smul_comp_relativeSpecSymmetricAlgebraTildeIso_inv
          M S c φ)
      have h₂ := Category.assoc ((specSymmetricAlgebraHomEquiv M S).symm (c • φ)) eM.inv
        (g ≫ eN.hom)
      have h₃ := Category.assoc (lift a (p ≫ eM.inv)) (relativeSpecSymmetricAlgebraSMul _)
        (g ≫ eN.hom)
      have h₄ := congrArg (fun x ↦ lift a (p ≫ eM.inv) ≫ x) (Category.assoc
        (relativeSpecSymmetricAlgebraSMul _) g eN.hom).symm
      have h₅ := congrArg (fun x ↦ lift a (p ≫ eM.inv) ≫ x ≫ eN.hom) hg
      have h₆ := congrArg (fun x ↦ lift a (p ≫ eM.inv) ≫ x) (Category.assoc
        (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R) ◁ g) (relativeSpecSymmetricAlgebraSMul _)
          eN.hom)
      have h₇ := (Category.assoc (lift a (p ≫ eM.inv))
        (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R) ◁ g)
          (relativeSpecSymmetricAlgebraSMul _ ≫ eN.hom)).symm
      have h₈ := congrArg (· ≫ relativeSpecSymmetricAlgebraSMul _ ≫ eN.hom)
        (lift_whiskerLeft a (p ≫ eM.inv) g)
      have h₉ := (Category.assoc (lift a ((p ≫ eM.inv) ≫ g))
        (relativeSpecSymmetricAlgebraSMul _) eN.hom).symm
      exact h₂.symm.trans (h₁.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans (h₇.trans
        (h₈.trans h₉)))))))
    have hp : p ≫ ψ = ((p ≫ eM.inv) ≫ g) ≫ eN.hom :=
      (Category.assoc p eM.inv (g ≫ eN.hom)).symm.trans (Category.assoc (p ≫ eM.inv) g eN.hom).symm
    have h₁ := specSymmetricAlgebraHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_hom N S
      (lift a ((p ≫ eM.inv) ≫ g) ≫ relativeSpecSymmetricAlgebraSMul _) n
    have h₂ := relativeSpecSymmetricAlgebraTildeHomEquiv_lift_comp_smul N a ((p ≫ eM.inv) ≫ g) n
    have h₃ := specSymmetricAlgebraHomEquiv_comp_relativeSpecSymmetricAlgebraTildeIso_hom N S
      ((p ≫ eM.inv) ≫ g) n
    have ha : AffineSpace.homAsOverEquiv ((algSpec R).obj (op S)) a PUnit.unit =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv c :=
      congrFun (Equiv.apply_symm_apply _ _) PUnit.unit
    refine (congrArg (fun x ↦ specSymmetricAlgebraHomEquiv N S x n) key).trans
      (h₁.trans ((congrArg (Scheme.ΓSpecIso (CommRingCat.of S)).hom h₂).trans ?_))
    refine (congrArg (fun x ↦ (Scheme.ΓSpecIso (CommRingCat.of S)).hom (x * _)) ha).trans
      ((map_mul _ _ _).trans ?_)
    refine (congrArg (· * _) (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv_hom_id c)).trans ?_
    exact congrArg (c * ·) (h₃.symm.trans (congrArg (fun x ↦ specSymmetricAlgebraHomEquiv N S x n)
      hp.symm))
  obtain ⟨f, hf, hu⟩ := existsUnique_specSymmetricAlgebraMap_of_smul ψ hψ
  have hm (f' : N ⟶ M) :
      eM.inv ≫ (MorphismProperty.Over.forget _ _ (Spec R)).map ((relativeSpec (Spec R)).map
        ((symmetricAlgebra (Spec R)).map ((tildeEquiv (R := R)).functor.map f')).op) ≫ eN.hom =
      specSymmetricAlgebraMap f'.hom :=
    (Iso.inv_comp_eq eM).2 (relativeSpec_map_comp_relativeSpecSymmetricAlgebraTildeIso_hom f')
  refine ⟨ModuleCat.ofHom f, ?_, fun f' hf' ↦ ModuleCat.hom_ext (hu f'.hom ?_)⟩
  · have h := (hf.trans (hm (ModuleCat.ofHom f)).symm)
    exact (cancel_epi eM.inv).1 ((cancel_mono eN.hom).1
      ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)))
  · exact (congrArg (fun x ↦ eM.inv ≫ x ≫ eN.hom) hf').trans (hm f')

/-- **Linear morphisms of linear spectra over `Spec R`.** For quasicoherent sheaves `F` and `F'` on
`Spec R`, a morphism `Spec_{Spec R} (Sym F) ⟶ Spec_{Spec R} (Sym F')` over `Spec R` that commutes
with the actions of the affine line `𝔸¹_{Spec R}` is the relative spectrum of `Sym a` for a unique
`a : F' ⟶ F`. -/
theorem existsUnique_relativeSpec_map_of_isModHom {F F' : QuasicoherentSheaf (Spec R)}
    (g : (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj F))) ⟶
      (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj F'))))
    [IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) g] :
    ∃! a : F' ⟶ F, g = (MorphismProperty.Over.forget _ _ (Spec R)).map
      ((relativeSpec (Spec R)).map ((symmetricAlgebra (Spec R)).map a).op) := by
  -- transport `g` along `M~ ≅ F` and `N~ ≅ F'`, for `M` and `N` the global sections
  let e : (tildeEquiv (R := R)).functor.obj ((tildeEquiv (R := R)).inverse.obj F) ≅ F :=
    (tildeEquiv (R := R)).counitIso.app F
  let e' : (tildeEquiv (R := R)).functor.obj ((tildeEquiv (R := R)).inverse.obj F') ≅ F' :=
    (tildeEquiv (R := R)).counitIso.app F'
  let m {G G' : QuasicoherentSheaf (Spec R)} (a : G' ⟶ G) :=
    (MorphismProperty.Over.forget _ _ (Spec R)).map
      ((relativeSpec (Spec R)).map ((symmetricAlgebra (Spec R)).map a).op)
  have hm {G G' G'' : QuasicoherentSheaf (Spec R)} (a : G'' ⟶ G') (b : G' ⟶ G) :
      m (a ≫ b) = m b ≫ m a := by
    simp only [m, Functor.map_comp, op_comp]
  have hm₁ (G : QuasicoherentSheaf (Spec R)) : m (𝟙 G) = 𝟙 _ := by
    simp only [m, CategoryTheory.Functor.map_id, op_id]
  have : IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) (m e.inv) :=
    isModHom_relativeSpec_map e.inv
  have : IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) (m e'.hom) :=
    isModHom_relativeSpec_map e'.hom
  obtain ⟨f, hf, hu⟩ := existsUnique_relativeSpec_map_tilde_of_isModHom (m e.inv ≫ g ≫ m e'.hom)
  refine ⟨e'.inv ≫ (tildeEquiv (R := R)).functor.map f ≫ e.hom, ?_, fun a ha ↦ ?_⟩
  · have h₁ : m e.hom ≫ m e.inv = 𝟙 _ :=
      (hm e.inv e.hom).symm.trans ((congrArg m e.inv_hom_id).trans (hm₁ F))
    have h₂ : m e'.hom ≫ m e'.inv = 𝟙 _ :=
      (hm e'.inv e'.hom).symm.trans ((congrArg m e'.inv_hom_id).trans (hm₁ F'))
    calc g = (m e.hom ≫ m e.inv) ≫ g ≫ m e'.hom ≫ m e'.inv := by
          rw [h₁, h₂, Category.id_comp, Category.comp_id]
      _ = m e.hom ≫ (m e.inv ≫ g ≫ m e'.hom) ≫ m e'.inv := by
          simp only [Category.assoc]
      _ = m e.hom ≫ m ((tildeEquiv (R := R)).functor.map f) ≫ m e'.inv :=
          congrArg (fun x ↦ m e.hom ≫ x ≫ m e'.inv) hf
      _ = _ := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ m e'.inv)
          (hm _ e.hom).symm).trans (hm e'.inv _).symm)
  · let b := e'.hom ≫ a ≫ e.inv
    have hb := (tildeEquiv (R := R)).functor.map_preimage b
    have k₁ : m e.inv ≫ g ≫ m e'.hom = m e.inv ≫ m a ≫ m e'.hom :=
      congrArg (fun x ↦ m e.inv ≫ x ≫ m e'.hom) ha
    have k₂ : m b = m e.inv ≫ m a ≫ m e'.hom := by
      simp only [b, hm, Category.assoc]
    have k₃ : m ((tildeEquiv (R := R)).functor.map ((tildeEquiv (R := R)).functor.preimage b)) =
        m b :=
      congrArg m hb
    have hf₀ := hu ((tildeEquiv (R := R)).functor.preimage b) (k₁.trans (k₂.symm.trans k₃.symm))
    rw [hf₀] at hb
    simp [hb, b]

/-- Over `Spec R`, a morphism `Spec_{Spec R} (Sym F) ⟶ Spec_{Spec R} (Sym F')` commutes with the
actions of the affine line exactly when it is the relative spectrum of `Sym a` for some
`a : F' ⟶ F`. -/
theorem isModHom_iff_exists_relativeSpec_map {F F' : QuasicoherentSheaf (Spec R)}
    (g : (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj F))) ⟶
      (MorphismProperty.Over.forget _ _ (Spec R)).obj
        ((relativeSpec (Spec R)).obj (op ((symmetricAlgebra (Spec R)).obj F')))) :
    IsModHom (𝔸(PUnit.{u + 1}; Spec R).asOver (Spec R)) g ↔
      ∃ a : F' ⟶ F, g = (MorphismProperty.Over.forget _ _ (Spec R)).map
        ((relativeSpec (Spec R)).map ((symmetricAlgebra (Spec R)).map a).op) := by
  refine ⟨fun _ ↦ (existsUnique_relativeSpec_map_of_isModHom g).exists, ?_⟩
  rintro ⟨a, rfl⟩
  infer_instance

end

end TauCeti.AlgebraicGeometry
