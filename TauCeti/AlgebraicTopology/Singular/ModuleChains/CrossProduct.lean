/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.Singular.EilenbergZilber

/-!
# The simplicial cross product of singular chains with coefficients in a ring

For a commutative ring `k`, the shuffle map of Eilenberg and Mac Lane (`TopCat.shuffle`) with
coefficients `k` and `k` lands in the singular chains with coefficients in `k ⊗ k`.  Composing with
the coefficient change along the unitor `k ⊗ k ≅ k` gives the **simplicial cross product**
`C(X; k) ⊗ C(Y; k) ⟶ C(X × Y; k)` of singular chains with coefficients in `k`.

## Main definitions and results

* `TauCeti.singularCrossProduct`: the simplicial cross product.
* `TauCeti.singularCrossProduct_naturality`: its naturality in both spaces.
* `TauCeti.singularAugment_singularCrossProduct`: the augmentation of the cross product of the
  chains of two points with coefficients `a` and `b` is `a * b`.
* `TauCeti.quasiIso_singularCrossProduct`: the simplicial cross product is a quasi-isomorphism
  (Eilenberg–Zilber).

## References

* S. Eilenberg and S. Mac Lane, *On the groups `H(Π, n)`, I*, Ann. of Math. 58 (1953).
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory HomologicalComplex Limits TensorProduct Simplicial

universe u

namespace TauCeti

variable (k : Type u) [CommRing k]

/-- The **simplicial cross product** of singular chains with coefficients in `k`,
`C(X; k) ⊗ C(Y; k) ⟶ C(X × Y; k)`: the shuffle map with the coefficients `k ⊗ k` identified with
`k` by the unitor. -/
def singularCrossProduct (X Y : TopCat.{u}) :
    (singularChains k).obj X ⊗ (singularChains k).obj Y ⟶ (singularChains k).obj (X ⊗ Y) :=
  TopCat.shuffle X Y (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k)) ≫
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).map
      (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y)

/-- The simplicial cross product is the shuffle map followed by the coefficient change along the
unitor. -/
theorem singularCrossProduct_def (X Y : TopCat.{u}) :
    singularCrossProduct k X Y =
      TopCat.shuffle X Y (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k)) ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).map
          (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y) :=
  (rfl)

/-- The simplicial cross product is natural in both spaces. -/
@[reassoc]
theorem singularCrossProduct_naturality {X X' Y Y' : TopCat.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    ((singularChains k).map f ⊗ₘ (singularChains k).map g) ≫ singularCrossProduct k X' Y' =
      singularCrossProduct k X Y ≫ (singularChains k).map (f ⊗ₘ g) := by
  have h1 := TopCat.shuffle_naturality (C := ModuleCat.{u} k) f g (𝟙_ _) (𝟙_ _)
  have h2 := ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} k)).map
    (λ_ (𝟙_ (ModuleCat.{u} k))).hom).naturality (f ⊗ₘ g)
  rw [singularCrossProduct_def, singularCrossProduct_def]
  -- `h1` is stated for the chain maps induced by `TopCat.toSSet.map f`, which are by definition
  -- the maps `(singularChains k).map f`
  exact (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ _) h1).trans <|
    (Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm

/-- The augmentation of the simplicial cross product of the chains of two singular points with
coefficients `a` and `b` is `a * b`. -/
theorem singularAugment_singularCrossProduct (X Y : TopCat.{u})
    (σ : (TopCat.toSSet.obj X) _⦋0⦌) (τ : (TopCat.toSSet.obj Y) _⦋0⦌) (a b : k) :
    singularAugment k (X ⊗ Y) ((singularCrossProduct k X Y).f 0
      ((ιTensorObj ((singularChains k).obj X) ((singularChains k).obj Y) 0 0 0 rfl).hom
        (simplexChain σ a ⊗ₜ[k] simplexChain τ b))) = a * b := by
  -- the shuffle map on the vertices `σ` and `τ` is the vertex `(σ, τ)` of the product
  have h1 := TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f_zero (C := ModuleCat.{u} k)
    (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k)) σ τ
  -- and the coefficient change acts on the coefficient before the inclusion of the simplex
  have h2 := SSet.ιChainComplex_chainComplexFunctor_map_app_f (C := ModuleCat.{u} k)
    (λ_ (𝟙_ (ModuleCat.{u} k))).hom (X := TopCat.toSSet.obj (X ⊗ Y))
    ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app _
      ((σ, τ) : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) _⦋0⦌))
  have e1 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h1) (a ⊗ₜ[k] b)
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h2) (a ⊗ₜ[k] b)
  have e3 : (λ_ (𝟙_ (ModuleCat.{u} k))).hom.hom (a ⊗ₜ[k] b) = a * b := by simp
  have e4 : (singularCrossProduct k X Y).f 0
      ((ιTensorObj ((singularChains k).obj X) ((singularChains k).obj Y) 0 0 0 rfl).hom
        (simplexChain σ a ⊗ₜ[k] simplexChain τ b)) =
      simplexChain ((Functor.LaxMonoidal.μ TopCat.toSSet X Y).app _
        ((σ, τ) : (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) _⦋0⦌)) (a * b) :=
    (congrArg (fun z ↦ (((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{u} k)).map (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y)).f 0 z) e1).trans
      (e2.trans (congrArg _ e3))
  rw [e4]
  exact singularAugment_simplexChain _ _ _

/-- **The simplicial cross product is a quasi-isomorphism**: the shuffle map is a homotopy
equivalence (Eilenberg–Zilber), and the coefficient change along the unitor is an isomorphism. -/
instance quasiIso_singularCrossProduct (X Y : TopCat.{u}) :
    QuasiIso (singularCrossProduct k X Y) := by
  have h1 : QuasiIso (TopCat.shuffle X Y (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k))) := by
    have := (TopCat.eilenbergZilberHomotopyEquiv (C := ModuleCat.{u} k) X Y
      (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k))).quasiIso_inv
    simpa [TopCat.eilenbergZilberHomotopyEquiv_inv] using this
  rw [singularCrossProduct_def]
  have h3 : QuasiIso (((AlgebraicTopology.singularChainComplexFunctor
      (ModuleCat.{u} k)).map (λ_ (𝟙_ (ModuleCat.{u} k))).hom).app (X ⊗ Y)) :=
    quasiIso_of_isIso _
  exact (quasiIso_iff_comp_left
    (TopCat.shuffle X Y (𝟙_ (ModuleCat.{u} k)) (𝟙_ (ModuleCat.{u} k))) _).2 h3

end TauCeti

end

end
