/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

/-!
# Duals of tensor coinvariants and group cohomology with coefficients in an internal hom

Let `A` be a `k`-linear representation of `G` and `N` a `k`-module. For a representation `X`, a
`k`-linear map `(A ⊗ X)_G ⟶ N` out of the tensor coinvariants is the same as a morphism of
representations `A ⊗ X ⟶ N` to the trivial representation (`Rep.coinvariantsAdjunction`), which is
the same as a morphism of representations `X ⟶ Homₖ(A, N)` into the internal hom
(`Rep.MonoidalClosed.linearHomEquiv`). The first step is the `k`-linear form
`Rep.coinvariantsHomLinearEquiv` of the coinvariants adjunction. The composite `k`-linear
equivalence is `Rep.coinvariantsTensorHomLinearEquiv`; it sends `f` to `x ↦ (a ↦ f ⟦a ⊗ x⟧)` and
is natural in `X`.

Applied degreewise to a chain complex `P` of representations, it identifies the cochain complex
`Hom((A ⊗ P)_G, N)` with `Hom_G(P, Homₖ(A, N))`
(`HomologicalComplex.coinvariantsTensorObjLinearYonedaObjIso`). When `P` is a projective
resolution of the trivial representation `k`, the cohomology of the second complex is group
cohomology, so

`Hⁿ(G, Homₖ(A, N)) ≅ Hⁿ(Hom((A ⊗ P)_G, N))`

(`Rep.groupCohomologyIhomIso`). The complex `(A ⊗ P)_G` is the one whose homology is Mathlib's
group homology `Hₙ(G, A)` (`groupHomologyIso`), so this is the cochain-level form of the duality
between the group homology of `A` and the group cohomology of `Homₖ(A, N)`. It is how cohomology
with local coefficients, computed from twisted chains of the form `(A ⊗ P)_G`, is compared with
group cohomology.

## Main definitions

* `Rep.coinvariantsHomLinearEquiv`: `Hom(X_G, N) ≃ₗ[k] Hom_G(X, N)`.
* `Rep.coinvariantsTensorHomLinearEquiv`: `Hom((A ⊗ X)_G, N) ≃ₗ[k] Hom_G(X, Homₖ(A, N))`.
* `HomologicalComplex.coinvariantsTensorObjLinearYonedaObjIso`: the isomorphism of cochain
  complexes `Hom((A ⊗ P)_G, N) ≅ Hom_G(P, Homₖ(A, N))`.
* `Rep.groupCohomologyIhomIso`: `Hⁿ(G, Homₖ(A, N)) ≅ Hⁿ(Hom((A ⊗ P)_G, N))` for a projective
  resolution `P` of `k`.

## References

* K. S. Brown, *Cohomology of Groups*, GTM 87, Springer, 1982, Section III.2 and
  Proposition VI.7.1.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory

universe u

variable {k G : Type u} [CommRing k] [Group G]

namespace Rep

variable (A : Rep.{u} k G) (N : Type u) [AddCommGroup N] [Module k N]

/-- **Maps out of coinvariants are invariant maps**: the bijection of the adjunction
`Rep.coinvariantsAdjunction` between `k`-linear maps `X_G ⟶ N` and morphisms of representations
`X ⟶ N` to the trivial representation is `k`-linear. -/
def coinvariantsHomLinearEquiv (X : Rep.{u} k G) :
    ((coinvariantsFunctor k G).obj X ⟶ ModuleCat.of k N) ≃ₗ[k] (X ⟶ Rep.trivial k G N) :=
  { (coinvariantsAdjunction k G).homEquiv X (ModuleCat.of k N) with
    map_add' _ _ := by ext; simp [Rep.add_hom, Adjunction.homEquiv_unit]
    map_smul' _ _ := by ext; simp [Rep.smul_hom, Adjunction.homEquiv_unit] }

/-- The invariant map corresponding to `f : X_G ⟶ N` is `f` composed with the projection to the
coinvariants. -/
@[simp]
theorem coinvariantsHomLinearEquiv_apply_hom_apply {X : Rep.{u} k G}
    (f : (coinvariantsFunctor k G).obj X ⟶ ModuleCat.of k N) (x : X) :
    (coinvariantsHomLinearEquiv N X f).hom x = f (Representation.Coinvariants.mk X.ρ x) :=
  (rfl)

/-- The map out of the coinvariants corresponding to `φ : X ⟶ N` sends the class of `x` to
`φ x`. -/
-- Match before simplification changes the presentation of the coinvariants carrier.
@[simp↓]
theorem coinvariantsHomLinearEquiv_symm_apply_mk {X : Rep.{u} k G} (φ : X ⟶ Rep.trivial k G N)
    (x : X) :
    (coinvariantsHomLinearEquiv N X).symm φ (Representation.Coinvariants.mk X.ρ x) = φ.hom x := by
  have h := coinvariantsHomLinearEquiv_apply_hom_apply N ((coinvariantsHomLinearEquiv N X).symm φ) x
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **Maps out of tensor coinvariants are morphisms into the internal hom**: for representations
`A` and `X` of `G` and a `k`-module `N`, the `k`-linear maps `(A ⊗ X)_G ⟶ N` correspond
`k`-linearly to the morphisms of representations `X ⟶ Homₖ(A, N)`, where `N` carries the trivial
action. The map `f` corresponds to `x ↦ (a ↦ f ⟦a ⊗ x⟧)`
(`Rep.coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply`). -/
def coinvariantsTensorHomLinearEquiv (X : Rep.{u} k G) :
    (((coinvariantsTensor k G).obj A).obj X ⟶ ModuleCat.of k N) ≃ₗ[k]
      (X ⟶ (Rep.ihom A).obj (Rep.trivial k G N)) :=
  coinvariantsHomLinearEquiv N (A ⊗ X) ≪≫ₗ MonoidalClosed.linearHomEquiv A X (Rep.trivial k G N)

variable {A N}

/-- The morphism corresponding to a map `f : (A ⊗ X)_G ⟶ N` sends `x` to `a ↦ f ⟦a ⊗ x⟧`. -/
-- Match before simplification changes the presentation of the tensor carrier.
@[simp↓]
theorem coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply {X : Rep.{u} k G}
    (f : ((coinvariantsTensor k G).obj A).obj X ⟶ ModuleCat.of k N) (x : X) (a : A) :
    -- The carrier of `Homₖ(A, N)` is `A →ₗ[k] N` only up to unfolding, so the coercion is named.
    DFunLike.coe (F := A →ₗ[k] N) ((coinvariantsTensorHomLinearEquiv A N X f).hom x) a =
      f (coinvariantsTensorMk A X a x) :=
  (rfl)

/-- The map corresponding to a morphism `φ : X ⟶ Homₖ(A, N)` sends `⟦a ⊗ x⟧` to `φ x a`. -/
-- Match before simplification changes the presentation of the tensor carrier.
@[simp↓]
theorem coinvariantsTensorHomLinearEquiv_symm_apply_coinvariantsTensorMk {X : Rep.{u} k G}
    (φ : X ⟶ (Rep.ihom A).obj (Rep.trivial k G N)) (a : A) (x : X) :
    (coinvariantsTensorHomLinearEquiv A N X).symm φ (coinvariantsTensorMk A X a x) =
      DFunLike.coe (F := A →ₗ[k] N) (φ.hom x) a := by
  have h := coinvariantsTensorHomLinearEquiv_apply_hom_apply_apply
    ((coinvariantsTensorHomLinearEquiv A N X).symm φ) x a
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- **The correspondence is natural in the representation**: precomposing a map out of
`(A ⊗ X')_G` with the map induced by `g : X ⟶ X'` corresponds to precomposing with `g`. -/
theorem coinvariantsTensorHomLinearEquiv_comp {X X' : Rep.{u} k G} (g : X ⟶ X')
    (f : ((coinvariantsTensor k G).obj A).obj X' ⟶ ModuleCat.of k N) :
    coinvariantsTensorHomLinearEquiv A N X (((coinvariantsTensor k G).obj A).map g ≫ f) =
      g ≫ coinvariantsTensorHomLinearEquiv A N X' f := by
  -- `(A ⊗ -)_G` sends `g` to the map of coinvariants induced by `A ◁ g`, so this is the
  -- naturality of the hom-equivalences of the coinvariants and internal-hom adjunctions.
  change (ihom.adjunction A).homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _
    ((coinvariantsFunctor k G).map ((tensorLeft A).map g) ≫ f)) =
      g ≫ (ihom.adjunction A).homEquiv _ _ ((coinvariantsAdjunction k G).homEquiv _ _ f)
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]

end Rep

namespace HomologicalComplex

variable {α : Type*} [AddRightCancelSemigroup α] [One α] (A : Rep.{u} k G)
  (P : ChainComplex (Rep.{u} k G) α) (N : Type u) [AddCommGroup N] [Module k N]

/-- **Duals of tensor coinvariants of a complex**: for a chain complex `P` of representations of
`G`, a representation `A` and a `k`-module `N`, the cochain complex `Hom((A ⊗ P)_G, N)` is
isomorphic to the complex `Hom_G(P, Homₖ(A, N))` of morphisms into the internal hom, by
`Rep.coinvariantsTensorHomLinearEquiv` in each degree. -/
def coinvariantsTensorObjLinearYonedaObjIso :
    (P.coinvariantsTensorObj A).linearYonedaObj k (ModuleCat.of k N) ≅
      P.linearYonedaObj k ((Rep.ihom A).obj (Rep.trivial k G N)) :=
  Hom.isoOfComponents (fun i ↦ (Rep.coinvariantsTensorHomLinearEquiv A N (P.X i)).toModuleIso)
    fun i j _ ↦ ModuleCat.hom_ext <| LinearMap.ext fun f ↦
      Rep.coinvariantsTensorHomLinearEquiv_comp (P.d j i) f

/-- The isomorphism is `Rep.coinvariantsTensorHomLinearEquiv` in each degree. -/
@[simp]
theorem coinvariantsTensorObjLinearYonedaObjIso_hom_f_apply (i : α)
    (f : ((P.coinvariantsTensorObj A).linearYonedaObj k (ModuleCat.of k N)).X i) :
    (P.coinvariantsTensorObjLinearYonedaObjIso A N).hom.f i f =
      Rep.coinvariantsTensorHomLinearEquiv A N (P.X i) f :=
  (rfl)

/-- The inverse isomorphism is the inverse of `Rep.coinvariantsTensorHomLinearEquiv` in each
degree. -/
@[simp]
theorem coinvariantsTensorObjLinearYonedaObjIso_inv_f_apply (i : α)
    (φ : (P.linearYonedaObj k ((Rep.ihom A).obj (Rep.trivial k G N))).X i) :
    (P.coinvariantsTensorObjLinearYonedaObjIso A N).inv.f i φ =
      (Rep.coinvariantsTensorHomLinearEquiv A N (P.X i)).symm φ :=
  (rfl)

end HomologicalComplex

namespace Rep

variable (A : Rep.{u} k G) (N : Type u) [AddCommGroup N] [Module k N]

/-- **Group cohomology with coefficients in an internal hom, from tensor coinvariants**: for a
projective resolution `P` of the trivial representation `k`, a representation `A` and a
`k`-module `N`, the group cohomology `Hⁿ(G, Homₖ(A, N))` is the cohomology of the cochain complex
`Hom((A ⊗ P)_G, N)` dual to the complex computing the group homology of `A`. -/
def groupCohomologyIhomIso (n : ℕ) (P : ProjectiveResolution (Rep.trivial k G k)) :
    groupCohomology ((Rep.ihom A).obj (Rep.trivial k G N)) n ≅
      ((P.complex.coinvariantsTensorObj A).linearYonedaObj k (ModuleCat.of k N)).homology n :=
  groupCohomologyIso _ n P ≪≫ (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (P.complex.coinvariantsTensorObjLinearYonedaObjIso A N).symm

end Rep
