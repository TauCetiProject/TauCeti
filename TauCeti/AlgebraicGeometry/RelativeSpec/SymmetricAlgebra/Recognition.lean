/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.HopfSpec
public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.AlgebraicGeometry.RelativeSpec.SymmetricAlgebra.Tilde
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
It provides the affine morphism calculation used to compare linear structures on schemes with
gradings on their coordinate algebras. The scalar condition below is stated in point coordinates;
no assertion about descent over a nonaffine base is made here.

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

end TauCeti.AlgebraicGeometry
