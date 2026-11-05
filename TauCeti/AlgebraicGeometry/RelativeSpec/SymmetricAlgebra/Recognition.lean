/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LinearPoints

/-!
# Recognizing linear morphisms of affine linear spectra

For arbitrary modules `M` and `N` over a commutative ring `R`, a scheme morphism
`Spec (Sym M) ⟶ Spec (Sym N)` over `Spec R` is induced by a unique linear map `N → M`
if its action on points commutes with every scalar in every commutative test algebra.
In particular, this condition forces additivity; no characteristic or finiteness hypothesis
is needed. Testing only the scalars of `R` would not suffice.

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

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- Points of `Spec (Sym_R M)` over an affine test scheme `Spec S` are `R`-linear
functionals `M → S`. -/
def specSymmetricAlgebraHomEquiv (S : CommAlgCat.{u} R) :
    ((algSpec R).obj (op S) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M)))) ≃ (M →ₗ[R] S) :=
  ((algSpec.fullyFaithful (R := R)).homEquiv.symm.trans
    (opEquiv (op S) (op (CommAlgCat.of R (SymmetricAlgebra R M))))).trans
      (ConcreteCategory.homEquiv.trans SymmetricAlgebra.lift.symm)

/-- The point corresponding to a functional is the spectrum of its symmetric-algebra lift. -/
@[simp]
theorem specSymmetricAlgebraHomEquiv_symm_apply (S : CommAlgCat.{u} R) (g : M →ₗ[R] S) :
    (specSymmetricAlgebraHomEquiv M S).symm g =
      (algSpec R).map (CommAlgCat.ofHom (SymmetricAlgebra.lift g)).op :=
  (rfl)

/-- The spectrum of the lift of a functional has that functional as its point coordinates. -/
@[simp]
theorem specSymmetricAlgebraHomEquiv_map_lift (S : CommAlgCat.{u} R) (g : M →ₗ[R] S) :
    specSymmetricAlgebraHomEquiv M S
      ((algSpec R).map (CommAlgCat.ofHom (SymmetricAlgebra.lift g)).op) = g :=
  (specSymmetricAlgebraHomEquiv M S).apply_symm_apply g

/-- Changing the test algebra postcomposes the linear functional with its algebra map. -/
@[simp]
theorem specSymmetricAlgebraHomEquiv_comp {S T : CommAlgCat.{u} R} (h : S ⟶ T)
    (p : (algSpec R).obj (op S) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M)))) :
    specSymmetricAlgebraHomEquiv M T ((algSpec R).map h.op ≫ p) =
      h.hom.toLinearMap.comp (specSymmetricAlgebraHomEquiv M S p) := by
  obtain ⟨g, rfl⟩ := (specSymmetricAlgebraHomEquiv M S).symm.surjective p
  apply (specSymmetricAlgebraHomEquiv M T).symm.injective
  simp only [specSymmetricAlgebraHomEquiv_map_lift, Equiv.symm_apply_apply,
    specSymmetricAlgebraHomEquiv_symm_apply]
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  apply SymmetricAlgebra.algHom_ext
  ext m
  simp

variable {M} {N : ModuleCat.{u} R}

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
  (rfl)

/-- The identity linear map induces the identity scheme morphism. -/
@[simp]
theorem specSymmetricAlgebraMap_id :
    specSymmetricAlgebraMap (LinearMap.id : M →ₗ[R] M) = 𝟙 _ := by
  simp [specSymmetricAlgebraMap]

/-- Composing linear maps reverses the order of the induced scheme morphisms. -/
theorem specSymmetricAlgebraMap_comp {P : ModuleCat.{u} R}
    (f : N →ₗ[R] M) (g : P →ₗ[R] N) :
    specSymmetricAlgebraMap (f.comp g) =
      specSymmetricAlgebraMap f ≫ specSymmetricAlgebraMap g := by
  simp only [specSymmetricAlgebraMap, ← SymmetricAlgebra.map_comp_map,
    CommAlgCat.ofHom_comp, op_comp, Functor.map_comp]

/-- On points, the morphism induced by `f` precomposes linear functionals with `f`. -/
@[simp]
theorem specSymmetricAlgebraHomEquiv_comp_map (f : N →ₗ[R] M)
    (S : CommAlgCat.{u} R) (p : (algSpec R).obj (op S) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M)))) :
    specSymmetricAlgebraHomEquiv N S (p ≫ specSymmetricAlgebraMap f) =
      (specSymmetricAlgebraHomEquiv M S p).comp f := by
  obtain ⟨g, rfl⟩ := (specSymmetricAlgebraHomEquiv M S).symm.surjective p
  apply (specSymmetricAlgebraHomEquiv N S).symm.injective
  simp only [specSymmetricAlgebraHomEquiv_map_lift, Equiv.symm_apply_apply,
    specSymmetricAlgebraHomEquiv_symm_apply, specSymmetricAlgebraMap]
  rw [← Functor.map_comp, ← op_comp]
  congr 2
  apply CommAlgCat.hom_ext
  apply SymmetricAlgebra.algHom_ext
  ext n
  simp

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
    have hn := specSymmetricAlgebraHomEquiv_comp M h
      ((specSymmetricAlgebraHomEquiv M S).symm g)
    have hs : (specSymmetricAlgebraHomEquiv M T).symm (h.hom.toLinearMap.comp g) =
        (algSpec R).map h.op ≫ (specSymmetricAlgebraHomEquiv M S).symm g := by
      apply (specSymmetricAlgebraHomEquiv M T).injective
      simpa only [Equiv.apply_symm_apply] using hn.symm
    -- Evaluate bundled type-category compositions before applying the point formulas.
    change specSymmetricAlgebraHomEquiv N T
      ((specSymmetricAlgebraHomEquiv M T).symm (h.hom.toLinearMap.comp g) ≫ ψ) =
        h.hom.toLinearMap.comp (specSymmetricAlgebraHomEquiv N S
          ((specSymmetricAlgebraHomEquiv M S).symm g ≫ ψ))
    rw [hs, Category.assoc, specSymmetricAlgebraHomEquiv_comp]

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
    Function.Injective (specSymmetricAlgebraPointsMap (M := M) (N := N)) := by
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
theorem specSymmetricAlgebraPointsMap_map (f : N →ₗ[R] M) :
    specSymmetricAlgebraPointsMap (specSymmetricAlgebraMap f) =
      SymmetricAlgebra.linearPointsMap R f := by
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro g
  rw [SymmetricAlgebra.linearPointsMap_app_apply]
  exact (specSymmetricAlgebraHomEquiv_comp_map f S _).trans
    (congrArg (fun g : M →ₗ[R] S ↦ g.comp f)
      ((specSymmetricAlgebraHomEquiv M S).apply_symm_apply g))

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
    (specSymmetricAlgebraPointsMap_map f).symm), ?_⟩
  intro g hg
  apply hu
  rw [hg, specSymmetricAlgebraPointsMap_map]

/-- The scalar-equivariance criterion is equivalent to being induced by a linear map. -/
theorem specSymmetricAlgebraPointsMap_smul_iff
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
    rw [specSymmetricAlgebraPointsMap_map]
    exact SymmetricAlgebra.linearPointsMap_app_smul R f S c g

/-- Scalar equivariance of a scheme morphism forces additivity on every test algebra. -/
theorem specSymmetricAlgebraPointsMap_add_of_smul
    (ψ : (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R M))) ⟶
      (algSpec R).obj (op (CommAlgCat.of R (SymmetricAlgebra R N))))
    (hψ : ∀ (S : CommAlgCat.{u} R) (c : S) (g : M →ₗ[R] S),
      (specSymmetricAlgebraPointsMap ψ).app S (c • g) =
        c • ((specSymmetricAlgebraPointsMap ψ).app S g : N →ₗ[R] S))
    (S : CommAlgCat.{u} R) (p q : M →ₗ[R] S) :
    (specSymmetricAlgebraPointsMap ψ).app S (p + q) =
      (specSymmetricAlgebraPointsMap ψ).app S p +
        (specSymmetricAlgebraPointsMap ψ).app S q := by
  obtain ⟨f, rfl⟩ := (specSymmetricAlgebraPointsMap_smul_iff ψ).mp hψ
  simp only [specSymmetricAlgebraPointsMap_map,
    SymmetricAlgebra.linearPointsMap_app_apply]
  exact LinearMap.add_comp f q p

end

end TauCeti.AlgebraicGeometry
