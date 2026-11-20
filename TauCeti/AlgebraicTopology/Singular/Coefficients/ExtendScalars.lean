/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Coefficients.MapCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-!
# Flat base change of singular homology

Let `f : R →+* S` be a flat homomorphism of commutative rings. Extension of scalars along `f` is
then an exact functor `ModuleCat R ⥤ ModuleCat S` preserving coproducts, so it commutes with
singular homology (`CategoryTheory.Functor.singularHomologyFunctorObjCompIso`), naturally in the
space. Since `S ⊗_R R ≅ S`, this compares `S ⊗_R Hₙ(X; R)` with `Hₙ(X; S)`, compatibly with the
maps induced by continuous maps. The main case is `ℤ →+* K` for a field `K` of characteristic zero,
such as `ℚ` or `ℝ`, which compares integral homology with rational or real homology.

This file records two consequences. If `Hₙ(X; R)` is a finite `R`-module, then `Hₙ(X; S)` is a
finite `S`-module (`RingHom.Flat.finite_singularHomology`). And for a self-map `g : X ⟶ X` with
`Hₙ(X; R)` free of finite rank, the endomorphism induced by `g` on `Hₙ(X; S)` is conjugate to the
base change of the one on `Hₙ(X; R)`, so

`det (𝟙 - g_* | Hₙ(X; S)) = f (det (𝟙 - g_* | Hₙ(X; R)))`

(`RingHom.Flat.det_id_sub_singularHomologyMap_eq`). For `ℤ →+* K` this says that `𝟙 - g_*` is
invertible on `Hₙ(X; K)` exactly when its integral determinant is nonzero, which is how a
condition on rational or real Betti numbers, such as `b₁ = 1` for a mapping torus, becomes the
integral hypothesis `det (𝟙 - φ_*) ≠ 0` of the Wang sequence computations.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (change of coefficients).
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w

namespace RingHom.Flat

variable {R S : Type w} [CommRing R] [CommRing S] {f : R →+* S}

/-- The flat base change comparison `S ⊗_R Hₙ(X; R) ≃ Hₙ(X; S)`, as a linear equivalence
intertwining the maps induced by every self-map of `X`. -/
private theorem exists_linearEquiv_extendScalars (hf : f.Flat) (X : TopCat.{w}) (n : ℕ) :
    ∃ e : (ModuleCat.extendScalars f).obj
        ((((singularChainComplexFunctor (ModuleCat.{w} R)).obj (ModuleCat.of R R)).obj X).homology
          n) ≃ₗ[S]
        (((singularChainComplexFunctor (ModuleCat.{w} S)).obj (ModuleCat.of S S)).obj X).homology n,
      ∀ (g : X ⟶ X) y, e ((ModuleCat.extendScalars f).map (HomologicalComplex.homologyMap
          (((singularChainComplexFunctor (ModuleCat.{w} R)).obj (ModuleCat.of R R)).map g) n) y) =
        HomologicalComplex.homologyMap
          (((singularChainComplexFunctor (ModuleCat.{w} S)).obj (ModuleCat.of S S)).map g) n
            (e y) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  have : (ModuleCat.extendScalars.{w, w, w} f).Additive :=
    Functor.additive_of_preserves_binary_products _
  let _ : Algebra R S := f.toAlgebra
  -- Exact extension of scalars commutes with singular homology, followed by `S ⊗_R R ≅ S`.
  let η := (ModuleCat.extendScalars f).singularHomologyFunctorObjCompIso (ModuleCat.of R R) n ≪≫
    (singularHomologyFunctor (ModuleCat.{w} S) n).mapIso
      (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso
  exact ⟨(η.app X).toLinearEquiv, fun g y ↦
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (η.hom.naturality g)) y⟩

/-- If `Hₙ(X; R)` is a finite `R`-module, then `Hₙ(X; S)` is a finite `S`-module, for a flat ring
homomorphism `f : R →+* S`. -/
theorem finite_singularHomology (hf : f.Flat) (X : TopCat.{w}) (n : ℕ)
    [Module.Finite R ((((singularChainComplexFunctor (ModuleCat.{w} R)).obj
      (ModuleCat.of R R)).obj X).homology n)] :
    Module.Finite S ((((singularChainComplexFunctor (ModuleCat.{w} S)).obj
      (ModuleCat.of S S)).obj X).homology n) := by
  obtain ⟨e, -⟩ := exists_linearEquiv_extendScalars hf X n
  -- The algebra structure through which `ModuleCat.extendScalars f` makes `S ⊗_R Hₙ(X; R)` an
  -- `S`-module.
  let _ : Algebra R S := ((algebraMap S S).comp f).toAlgebra
  have : Module.Finite S ((ModuleCat.extendScalars f).obj
      ((((singularChainComplexFunctor (ModuleCat.{w} R)).obj (ModuleCat.of R R)).obj X).homology
        n)) :=
    Module.Finite.base_change R S _
  exact Module.Finite.equiv e

/-- **Determinants of `𝟙 - g_*` under flat base change**: for a flat ring homomorphism
`f : R →+* S` and a self-map `g` of a space `X` whose homology `Hₙ(X; R)` is free of finite rank,
`det (𝟙 - g_* | Hₙ(X; S)) = f (det (𝟙 - g_* | Hₙ(X; R)))`. -/
theorem det_id_sub_singularHomologyMap_eq (hf : f.Flat) (X : TopCat.{w}) (g : X ⟶ X) (n : ℕ)
    [Module.Free R ((((singularChainComplexFunctor (ModuleCat.{w} R)).obj
      (ModuleCat.of R R)).obj X).homology n)]
    [Module.Finite R ((((singularChainComplexFunctor (ModuleCat.{w} R)).obj
      (ModuleCat.of R R)).obj X).homology n)] :
    (LinearMap.id - (HomologicalComplex.homologyMap
      (((singularChainComplexFunctor (ModuleCat.{w} S)).obj (ModuleCat.of S S)).map g) n).hom).det =
      f (LinearMap.id - (HomologicalComplex.homologyMap
        (((singularChainComplexFunctor (ModuleCat.{w} R)).obj (ModuleCat.of R R)).map g)
          n).hom).det := by
  let A :=
    (((singularChainComplexFunctor (ModuleCat.{w} R)).obj (ModuleCat.of R R)).obj X).homology n
  let B :=
    (((singularChainComplexFunctor (ModuleCat.{w} S)).obj (ModuleCat.of S S)).obj X).homology n
  let φ : A ⟶ A := HomologicalComplex.homologyMap
    (((singularChainComplexFunctor (ModuleCat.{w} R)).obj (ModuleCat.of R R)).map g) n
  let ψ : B ⟶ B := HomologicalComplex.homologyMap
    (((singularChainComplexFunctor (ModuleCat.{w} S)).obj (ModuleCat.of S S)).map g) n
  obtain ⟨e, he⟩ := exists_linearEquiv_extendScalars hf X n
  have hnat (y : (ModuleCat.extendScalars f).obj A) :
      e ((ModuleCat.extendScalars f).map φ y) = ψ (e y) :=
    he g y
  -- `𝟙 - ψ` is conjugate under `e` to the extension of scalars of `𝟙 - φ`.
  have hconj : LinearMap.id - ψ.hom =
      (e : _ →ₗ[S] _) ∘ₗ (LinearMap.id - ((ModuleCat.extendScalars f).map φ).hom) ∘ₗ
        (e.symm : _ →ₗ[S] _) := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    simp [hnat]
  rw [hconj, LinearMap.det_conj]
  -- By definition `ModuleCat.extendScalars f` sends a morphism to its base change along this
  -- algebra structure, whose algebra map is `f`; so `h` is the goal up to unfolding.
  let _ : Algebra R S := ((algebraMap S S).comp f).toAlgebra
  have h := LinearMap.det_baseChange (A := S) (LinearMap.id - φ.hom)
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_id] at h
  exact h

end RingHom.Flat
