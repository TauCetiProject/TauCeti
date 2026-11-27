/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Relative
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Zero
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import TauCeti.CategoryTheory.Linear.Int

/-!
# The Kronecker map of singular cohomology

Let `C` be a `k`-linear abelian category with coproducts. For a space `X`, the Kronecker map of
singular cochains is the Kronecker map `TauCeti.ChainComplex.kronecker` of the singular chain
complex of `X` with coefficients in `R`: it evaluates a singular cohomology class in
`Hⁿ(X; R, M)` on singular homology classes in `Hₙ(X; R)`, giving a `k`-linear map
`Hⁿ(X; R, M) →ₗ[k] (Hₙ(X; R) ⟶ M)`. On the classes of a cocycle `φ` and a cycle `z` it is `φ`
evaluated on `z`. It is natural in `X`: evaluating the pull-back `f^*α` of a class along a
continuous map `f` is evaluating `α` after pushing forward along `f`.

For coefficients in modules over a commutative ring `k`, take `C := ModuleCat k` and `R := k`;
then this is the evaluation `⟨α, x⟩ ∈ M` of a class `α ∈ Hⁿ(X; M)` on a class `x ∈ Hₙ(X; k)`,
which is how cohomology classes are paired with fundamental classes of manifolds. When `M` is an
injective object, for instance a vector space over a field `k`, the Kronecker map is a
`k`-linear equivalence `Hⁿ(X; M) ≃ₗ[k] Hom(Hₙ(X; k), M)`: the universal coefficient theorem in
the case where its `Ext¹`-term vanishes.

## Main definitions and results

* `TopCat.singularKronecker`: the Kronecker map of singular cohomology, the Kronecker map of the
  singular chain complex (`TopCat.singularKronecker_def`), with
  `TopCat.singularKronecker_homologyπ` computing it on classes of cocycles and cycles and
  `TopCat.singularKronecker_naturality` its naturality in the space and
  `TopCat.singularKronecker_singularCohomologyChainCoefficientMap` its naturality in the chain
  coefficients.
* `TopCat.singularKronecker_instLinear`: with values in `ℤ`, the Kronecker map does not depend on
  which of the two `ℤ`-linear structures of `ModuleCat ℤ` is used.
* `TopCat.singularKronecker_bijective`, `TopCat.singularKroneckerEquiv`: for an injective
  coefficient object `M`, the Kronecker map is bijective, a `k`-linear equivalence.
* `TopCat.singularKronecker_bijective_zero`: in degree zero the Kronecker map is bijective for
  every coefficient object.
* `TopCat.isIso_singularCohomologyMap_zero_of_isIso_singularHomologyFunctor_map`,
  `TopCat.isIso_singularCohomologyMap_zero_of_pathConnectedSpace`: so a map inducing an
  isomorphism on `H₀`, for instance a map between path-connected spaces, induces one on `H⁰`.
* `TopCat.singularKronecker_constSingularCocycle`: the class of the constant `0`-cocycle with
  value `e : R ⟶ M` evaluates on zeroth homology as the augmentation followed by `e`.
* `TopPair.singularKronecker`: the Kronecker map `Hⁿ(X, A; R, M) →ₗ[k] (Hₙ(X, A; R) ⟶ M)` of
  relative singular cohomology, the Kronecker map of the relative singular chain complex, with
  `TopPair.singularKronecker_homologyπ` and `TopPair.singularKronecker_naturality`;
  `TopPair.singularKronecker_singularCohomologyπ` compares it with the absolute Kronecker map, and
  `TopPair.singularKronecker_bijective` is its bijectivity for an injective coefficient object.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] {R M : C}

/-- **The Kronecker map of singular cohomology** `Hⁿ(X; R, M) →ₗ[k] (Hₙ(X; R) ⟶ M)`: it sends the
class of a singular cocycle `φ` to the morphism which on the class of a singular cycle is `φ`
evaluated on that cycle (`TopCat.singularKronecker_homologyπ`). -/
def singularKronecker (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] (n : ℕ) :
    X.singularCohomology R k M n →ₗ[k] (((singularHomologyFunctor C n).obj R).obj X ⟶ M) :=
  TauCeti.ChainComplex.kronecker k ((toSSet.obj X).chainComplex R) M n

/-- The Kronecker map of singular cohomology is the Kronecker map of the singular chain complex. -/
lemma singularKronecker_def (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] (n : ℕ) :
    X.singularKronecker (R := R) (M := M) k n =
      TauCeti.ChainComplex.kronecker k ((toSSet.obj X).chainComplex R) M n :=
  (rfl)

/-- The Kronecker map on the classes of a singular cocycle and a singular cycle is the cocycle
evaluated on the cycle. -/
@[simp, reassoc]
lemma singularKronecker_homologyπ (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] (n : ℕ)
    (φ : (X.singularCochainComplex R k M).cycles n) :
    ((toSSet.obj X).chainComplex R).homologyπ n ≫
        X.singularKronecker k n ((X.singularCochainComplex R k M).homologyπ n φ) =
      ((toSSet.obj X).chainComplex R).iCycles n ≫
        (X.singularCochainComplex R k M).iCycles n φ :=
  TauCeti.ChainComplex.kronecker_homologyπ n φ

/-- **Naturality of the Kronecker map**, `⟨f^*α, x⟩ = ⟨α, f_*x⟩`: for a continuous map
`f : X ⟶ Y`, evaluating the pull-back of a singular cohomology class of `Y` is evaluating the class
after pushing forward along `f`. -/
lemma singularKronecker_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (k : Type*) [Ring k]
    [Linear k C] (n : ℕ) (α : Y.singularCohomology R k M n) :
    X.singularKronecker k n (TopCat.singularCohomologyMap f n α) =
      ((singularHomologyFunctor C n).obj R).map f ≫ Y.singularKronecker k n α :=
  TauCeti.ChainComplex.kronecker_naturality (SSet.chainComplexMap (toSSet.map f) R) n α

/-- Evaluation of singular cohomology on homology commutes with changing the coefficient
object by postcomposition on singular cochains. -/
lemma singularKronecker_coefficient_naturality (X : TopCat.{w}) (k : Type*) [Ring k]
    [Linear k C] {N : C} (g : M ⟶ N) (n : ℕ) (α : X.singularCohomology R k M n) :
    X.singularKronecker k n
        (HomologicalComplex.homologyMap
          (((toSSet.obj X).chainComplex R).linearYonedaObjMap k g) n α) =
      X.singularKronecker k n α ≫ g :=
  TauCeti.ChainComplex.kronecker_coefficient_naturality g n α

/-- **Naturality of the Kronecker map in the chain coefficients**, `⟨f^*α, x⟩ = ⟨α, f_*x⟩`: for a
morphism `f : R' ⟶ R` of chain coefficients, evaluating the class
`TopCat.singularCohomologyChainCoefficientMap` pulled back along `f` on `Hₙ(X; R')` is evaluating
`α` after the map `Hₙ(X; R') ⟶ Hₙ(X; R)` induced by `f`. -/
lemma singularKronecker_singularCohomologyChainCoefficientMap (X : TopCat.{w}) (k : Type*)
    [Ring k] [Linear k C] {R' : C} (f : R' ⟶ R) (n : ℕ) (α : X.singularCohomology R k M n) :
    X.singularKronecker k n (X.singularCohomologyChainCoefficientMap k M f n α) =
      ((singularHomologyFunctor C n).map f).app X ≫ X.singularKronecker k n α :=
  TauCeti.ChainComplex.kronecker_naturality
    (((SSet.chainComplexFunctor C).map f).app (toSSet.obj X)) n α

variable (R M) in
/-- The Kronecker map of singular cohomology does not depend on how the `k`-linear structure of `C`
is presented: it commutes with the identification `eqToHom` of the two cohomology modules along an
equality `L₁ = L₂` of `k`-linear structures. -/
lemma singularKronecker_eqToHom {k : Type*} [Ring k] (L₁ L₂ : Linear k C) (h : L₁ = L₂)
    (X : TopCat.{w}) (n : ℕ) (a : @TopCat.singularCohomology _ _ _ _ R k _ L₁ M X n) :
    @TopCat.singularKronecker _ _ _ _ R M X k _ L₂ n (eqToHom (congrArg (fun L : Linear k C ↦
        @TopCat.singularCohomology _ _ _ _ R k _ L M X n) h) a) =
      @TopCat.singularKronecker _ _ _ _ R M X k _ L₁ n a := by
  subst h
  simp

/-- The Kronecker map of singular cohomology with values in `ℤ`, for chain coefficients in a
`ℤ`-module `R`, is the same for the `ℤ`-linear structure `ModuleCat.instLinear` of a category of
modules and the structure `Linear.preadditiveIntLinear` of a preadditive category. -/
lemma singularKronecker_instLinear (R : ModuleCat.{0} ℤ) (X : TopCat.{0}) (n : ℕ)
    (a : @TopCat.singularCohomology _ _ _ _ R ℤ _ ModuleCat.instLinear (ModuleCat.of ℤ ℤ) X n) :
    @TopCat.singularKronecker _ _ _ _ R (ModuleCat.of ℤ ℤ) X ℤ _ ModuleCat.instLinear n a =
      @TopCat.singularKronecker _ _ _ _ R (ModuleCat.of ℤ ℤ) X ℤ _ Linear.preadditiveIntLinear n
        a := by
  have h := singularKronecker_eqToHom R (ModuleCat.of ℤ ℤ) Linear.preadditiveIntLinear
    ModuleCat.instLinear (Subsingleton.elim _ _) X n a
  -- with values in `ℤ`, the two `ℤ`-module structures on the cochain groups `Hom(Cₙ, ℤ)` both
  -- unfold to integer multiplication, so the two cohomology modules agree up to definitional
  -- equality and the comparison `eqToHom` is the identity
  have h₁ : eqToHom (congrArg (fun L : Linear ℤ (ModuleCat.{0} ℤ) ↦
      @TopCat.singularCohomology _ _ _ _ R ℤ _ L (ModuleCat.of ℤ ℤ) X n)
        (Subsingleton.elim Linear.preadditiveIntLinear ModuleCat.instLinear)) = 𝟙 _ :=
    eqToHom_refl _ _
  rw [h₁] at h
  exact h

/-- **The universal coefficient theorem for injective coefficients**: for an injective object
`M`, the Kronecker map `Hⁿ(X; R, M) →ₗ[k] (Hₙ(X; R) ⟶ M)` of singular cohomology is bijective. -/
theorem singularKronecker_bijective (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C]
    [Injective M] (n : ℕ) : Function.Bijective (X.singularKronecker (R := R) (M := M) k n) :=
  TauCeti.ChainComplex.kronecker_bijective n

/-- **The universal coefficient theorem for injective coefficients**: for an injective object
`M`, the Kronecker map of singular cohomology is a `k`-linear equivalence
`Hⁿ(X; R, M) ≃ₗ[k] (Hₙ(X; R) ⟶ M)`. -/
def singularKroneckerEquiv (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] [Injective M]
    (n : ℕ) :
    X.singularCohomology R k M n ≃ₗ[k] (((singularHomologyFunctor C n).obj R).obj X ⟶ M) :=
  TauCeti.ChainComplex.kroneckerEquiv k ((toSSet.obj X).chainComplex R) M n

/-- **The universal coefficient theorem in degree zero**: for every coefficient object `M`, the
Kronecker map `H⁰(X; R, M) →ₗ[k] (H₀(X; R) ⟶ M)` is bijective, as no differential leaves the
degree-zero singular chains. -/
theorem singularKronecker_bijective_zero (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] :
    Function.Bijective (X.singularKronecker (R := R) (M := M) k 0) :=
  TauCeti.ChainComplex.kronecker_bijective_of_isIso 0

/-- The equivalence `TopCat.singularKroneckerEquiv` is the Kronecker map. -/
@[simp]
lemma singularKroneckerEquiv_apply (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C]
    [Injective M] (n : ℕ) (α : X.singularCohomology R k M n) :
    X.singularKroneckerEquiv k n α = X.singularKronecker k n α :=
  TauCeti.ChainComplex.kroneckerEquiv_apply n α

/-- **The Kronecker pairing of a constant `0`-cocycle**: evaluating the class of the constant
`0`-cocycle with value `e : R ⟶ M` on zeroth homology is the augmentation followed by `e`. For `e`
the identity, the unit class of `H⁰(X; R)` pairs with zeroth homology as the augmentation. -/
@[simp, reassoc]
lemma singularKronecker_constSingularCocycle (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C]
    (e : R ⟶ M) :
    X.singularKronecker k 0
        ((X.singularCochainComplex R k M).homologyπ 0 (X.constSingularCocycle k e)) =
      X.singularHomology₀ε R ≫ e :=
  -- The constant cochain evaluates a vertex to `e`, and the augmentation sends its class to `𝟙 R`.
  -- Zeroth singular homology is the homology of the singular chain complex only after unfolding
  -- `singularHomologyFunctor`, so `Category.assoc` is applied as a term rather than rewritten.
  SSet.homology₀_hom_ext R fun x ↦ by
    rw [SSet.ιHomology₀_def]
    refine (Category.assoc _ _ _).trans ?_
    simp only [singularKronecker_homologyπ, HomologicalComplex.liftCycles_i_assoc,
      iCycles_constSingularCocycle, SSet.ιChainComplex_constCochain]
    exact ((Category.assoc _ _ _).trans
      (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε_assoc (X := toSSet.obj X) R x e)).symm

/-- **A map inducing an isomorphism on `H₀` induces one on `H⁰`**, for every coefficient object
`M`: in degree zero the Kronecker maps are bijective (`TopCat.singularKronecker_bijective_zero`)
and they intertwine `f^*` with precomposition by `f_*` (`TopCat.singularKronecker_naturality`). -/
theorem isIso_singularCohomologyMap_zero_of_isIso_singularHomologyFunctor_map {X Y : TopCat.{w}}
    (f : X ⟶ Y) (k : Type*) [Ring k] [Linear k C]
    [IsIso (((singularHomologyFunctor C 0).obj R).map f)] :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) f 0) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  obtain ⟨hX, -⟩ := X.singularKronecker_bijective_zero (R := R) (M := M) k
  obtain ⟨hY, hY'⟩ := Y.singularKronecker_bijective_zero (R := R) (M := M) k
  refine ⟨fun α β h ↦ ?_, fun β ↦ ?_⟩
  · -- `f_*` is an epimorphism, so precomposing with it is injective.
    have := congrArg (X.singularKronecker k 0) h
    simp only [singularKronecker_naturality, cancel_epi] at this
    exact hY this
  · -- Pull the value of `β` back along the inverse of `f_*` and lift it through the Kronecker map.
    obtain ⟨α, hα⟩ := hY' (inv (((singularHomologyFunctor C 0).obj R).map f) ≫
      X.singularKronecker k 0 β)
    refine ⟨α, hX ?_⟩
    rw [singularKronecker_naturality, hα, IsIso.hom_inv_id_assoc]

/-- **`H⁰` does not see the difference between path-connected spaces**: a map between
path-connected spaces induces an isomorphism on `H⁰` with every coefficient object, since it
induces one on `H₀`, where both augmentations are isomorphisms. -/
theorem isIso_singularCohomologyMap_zero_of_pathConnectedSpace {X Y : TopCat.{w}}
    [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y) (k : Type*) [Ring k] [Linear k C] :
    IsIso (TopCat.singularCohomologyMap (R := R) (k := k) (M := M) f 0) :=
  have e : ((singularHomologyFunctor C 0).obj R).map f ≫ Y.singularHomology₀ε R =
      X.singularHomology₀ε R :=
    SSet.homologyMap_homology₀ε R (toSSet.map f)
  have : IsIso (((singularHomologyFunctor C 0).obj R).map f) := IsIso.of_isIso_fac_right e
  isIso_singularCohomologyMap_zero_of_isIso_singularHomologyFunctor_map f k

end TopCat

namespace TopPair

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] {R M : C}

/-- **The Kronecker map of relative singular cohomology** `Hⁿ(X, A; R, M) →ₗ[k] (Hₙ(X, A; R) ⟶ M)`
of a topological pair: it sends the class of a relative singular cocycle `φ` to the morphism
which on the class of a relative singular cycle is `φ` evaluated on that cycle
(`TopPair.singularKronecker_homologyπ`). -/
def singularKronecker (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C] (n : ℕ) :
    P.singularCohomology R k M n →ₗ[k] (P.singularHomology R n ⟶ M) :=
  TauCeti.ChainComplex.kronecker k (P.singularChainComplex R) M n

/-- The Kronecker map of relative singular cohomology is the Kronecker map of the relative singular
chain complex. -/
lemma singularKronecker_def (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C] (n : ℕ) :
    P.singularKronecker (R := R) (M := M) k n =
      TauCeti.ChainComplex.kronecker k (P.singularChainComplex R) M n :=
  (rfl)

/-- The relative Kronecker map on the classes of a relative singular cocycle and a relative
singular cycle is the cocycle evaluated on the cycle. -/
@[simp, reassoc]
lemma singularKronecker_homologyπ (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C] (n : ℕ)
    (φ : (P.singularCochainComplex R k M).cycles n) :
    (P.singularChainComplex R).homologyπ n ≫
        P.singularKronecker k n ((P.singularCochainComplex R k M).homologyπ n φ) =
      (P.singularChainComplex R).iCycles n ≫ (P.singularCochainComplex R k M).iCycles n φ :=
  TauCeti.ChainComplex.kronecker_homologyπ n φ

/-- **Naturality of the relative Kronecker map**, `⟨f^*α, x⟩ = ⟨α, f_*x⟩`: for a map of
topological pairs `f : P ⟶ P'`, evaluating the pull-back of a relative class of `P'` is evaluating
the class after pushing forward along `f`. -/
lemma singularKronecker_naturality {P P' : TopPair.{w}} (f : P ⟶ P') (k : Type*) [Ring k]
    [Linear k C] (n : ℕ) (α : P'.singularCohomology R k M n) :
    P.singularKronecker k n (TopPair.singularCohomologyMap f n α) =
      P.singularHomologyMap f R n ≫ P'.singularKronecker k n α :=
  TauCeti.ChainComplex.kronecker_naturality (singularChainComplexMap f R) n α

/-- **The universal coefficient theorem for injective coefficients, relative form**: for an
injective object `M`, the Kronecker map `Hⁿ(X, A; R, M) →ₗ[k] (Hₙ(X, A; R) ⟶ M)` of relative
singular cohomology is bijective. -/
theorem singularKronecker_bijective (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    [Injective M] (n : ℕ) : Function.Bijective (P.singularKronecker (R := R) (M := M) k n) :=
  TauCeti.ChainComplex.kronecker_bijective n

/-- Evaluating the image in `Hⁿ(X; R, M)` of a relative class `α ∈ Hⁿ(X, A; R, M)` is evaluating
`α` after the map `Hₙ(X; R) ⟶ Hₙ(X, A; R)`. -/
lemma singularKronecker_singularCohomologyπ (P : TopPair.{w}) (k : Type*) [Ring k] [Linear k C]
    (n : ℕ) (α : P.singularCohomology R k M n) :
    P.fst.singularKronecker k n (P.singularCohomologyπ R k M n α) =
      P.singularHomologyπ R n ≫ P.singularKronecker k n α :=
  TauCeti.ChainComplex.kronecker_naturality (P.singularChainComplexπ R) n α

end TopPair
