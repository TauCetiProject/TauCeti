/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import TauCeti.Algebra.Homology.Monoidal.Homology.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.CrossProduct
public import TauCeti.AlgebraicTopology.Cohomology.UniversalCoefficient
public import TauCeti.AlgebraicTopology.Singular.Kunneth.Basic

/-!
# The Künneth theorem for singular cohomology over a field

For topological spaces `X` and `Y`, the cohomology cross products
`Hᵖ(X; R, M) ⊗ H^q(Y; S, N) ⟶ Hⁿ(X × Y; R ⊗ S, P)` with `p + q = n`, along a coefficient pairing
`μ : M ⊗ N ⟶ P` (`TauCeti.singularCross`), assemble into the **cohomology Künneth map**

`⨁_{p + q = n} Hᵖ(X; R, M) ⊗ H^q(Y; S, N) ⟶ Hⁿ(X × Y; R ⊗ S, P)`

(`TopCat.singularCohomologyKunneth`), whose source is the degree `n` part of the tensor product of
the graded `k`-modules `H*(X; R, M)` and `H*(Y; S, N)`.

The Kronecker pairing of the cohomology cross product with the homology cross product is the
product of the Kronecker pairings, `⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`
(`TopCat.singularHomologyCross_comp_singularKronecker_singularCross`), and vanishes when the
degrees of `a` and `x` differ
(`TopCat.singularHomologyCross_comp_singularKronecker_singularCross_of_ne`).  Under
Eilenberg–Zilber both cross products are represented by tensor products, of cocycles and of
cycles, so this is the algebraic identity
`TauCeti.ChainComplex.homologyCross_comp_kronecker_cup`.

Over a field `k`, or more generally a commutative semisimple ring, with coefficients in `k`
itself, cohomology is the dual of homology: every module is projective, so the Kronecker map
`Hᵖ(X; k) ⟶ Hom(Hₚ(X; k), k)` is an isomorphism
(`TopCat.singularKroneckerEquivOfProjectiveHomology`).  The homology Künneth theorem
(`TopCat.singularHomologyKunnethIso`) identifies `Hₙ(X × Y; k ⊗ k)` with
`⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y; k)`, and when `Hₚ(X; k)` is finitely generated the canonical map
`Hom(Hₚ(X; k), k) ⊗ Hom(H_q(Y; k), k) ⟶ Hom(Hₚ(X; k) ⊗ H_q(Y; k), k)` is an isomorphism
(`dualTensorHomEquiv`).  By the pairing identity, under these isomorphisms the cohomology Künneth
map is the direct sum of these canonical maps, which gives the **Künneth theorem for cohomology
over a field** (`TopCat.singularCohomologyKunnethIso`): if every `Hₚ(X; k)` is finitely generated,
for instance if `X` has finite CW type (`TauCeti.finite_singularHomology_of_finiteCWType`), the
cross product induces an isomorphism

`⨁_{p + q = n} Hᵖ(X; k) ⊗ H^q(Y; k) ≅ Hⁿ(X × Y; k)`.

Only the homology of one factor needs to be finitely generated; no hypothesis is placed on `Y`.
Here `Hⁿ(X × Y; k)` is computed from the singular chains `C(X × Y; k ⊗ k)`, whose coefficient
module `k ⊗ k ≅ k` is the one carried by the cross product, and the pairing `k ⊗ k ⟶ k` is
multiplication.

## Main definitions and results

* `TopCat.singularHomologyCross_comp_singularKronecker_singularCross` and
  `TopCat.singularHomologyCross_comp_singularKronecker_singularCross_of_ne`: the Kronecker pairing
  of cross products.
* `TopCat.singularCohomologyKunneth`: the cohomology Künneth map, characterized on summands by
  `TopCat.singularCohomologyKunneth_ιTensorObj_tmul`, with
  `TopCat.singularCohomologyKunneth_naturality` its naturality in both spaces.
* `TopCat.singularCohomologyKunnethIso`, `TopCat.isIso_singularCohomologyKunneth` and
  `TopCat.singularCohomologyKunneth_bijective`: the Künneth theorem for cohomology over a
  commutative semisimple ring, for instance a field.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, the cross product and Theorem 3.15, and Section 3.B, the homology Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]
  {R S M N P : C} (μ : M ⊗ N ⟶ P)

/-- The Kronecker pairing on `X × Y` of the cohomology cross product, restricted along the shuffle
map, is the Kronecker pairing on the tensor product of singular chain complexes of the cross
product of cocycles, by Eilenberg–Zilber. -/
private lemma homologyMap_shuffle_comp_singularKronecker_singularCross (X Y : TopCat.{w})
    (p q n : ℕ) (h : p + q = n)
    (a : X.singularCohomology R k M p) (b : Y.singularCohomology S k N q) :
    homologyMap (shuffle X Y R S) n ≫
        TauCeti.ChainComplex.kronecker k ((toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S)) P n
          (TauCeti.singularCross k X Y μ p q n h a b) =
      TauCeti.ChainComplex.kronecker k
        (HomologicalComplex.tensorObj ((toSSet.obj X).chainComplex R)
          ((toSSet.obj Y).chainComplex S)) P n
        (TauCeti.ChainComplex.cup k (𝟙 (HomologicalComplex.tensorObj
          ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S))) μ p q n h a b) := by
  rw [← TauCeti.singularEilenbergZilberCohomologyIso_hom_singularCross,
    TauCeti.singularEilenbergZilberCohomologyIso_hom]
  exact (TauCeti.ChainComplex.kronecker_naturality (k := k) (shuffle X Y R S) n _).symm

variable (X Y : TopCat.{w}) (p q : ℕ)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The Kronecker pairing of cross products**, `⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`: the
evaluation of the cohomology cross product `a × b ∈ Hⁿ(X × Y; R ⊗ S, P)` on the image of the
homology cross product `Hₚ(X; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)` is the tensor product of the
evaluations of `a` and `b`, followed by the coefficient pairing `μ`. -/
theorem singularHomologyCross_comp_singularKronecker_singularCross (n : ℕ) (h : p + q = n)
    (a : X.singularCohomology R k M p) (b : Y.singularCohomology S k N q) :
    singularHomologyCross X Y R S p q n h ≫
        (X ⊗ Y).singularKronecker k n (TauCeti.singularCross k X Y μ p q n h a b) =
      (X.singularKronecker k p a ⊗ₘ Y.singularKronecker k q b) ≫ μ := by
  simp only [singularHomologyCross_def, singularKronecker_def]
  -- the homology cross product is the algebraic one followed by the shuffle map
  exact (Category.assoc _ _ _).trans
    ((_ ≫= homologyMap_shuffle_comp_singularKronecker_singularCross μ X Y p q n h a b).trans
      (TauCeti.ChainComplex.homologyCross_comp_kronecker_cup _ _ μ p q n h a b))

/-- **The Kronecker pairing of cross products of different degrees vanishes**: for `p ≠ p'`, the
cohomology cross product of classes of degrees `p'` and `q'` evaluates to zero on the image of the
homology cross product `Hₚ(X; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)`. -/
theorem singularHomologyCross_comp_singularKronecker_singularCross_of_ne {p' q' n : ℕ}
    (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    (a : X.singularCohomology R k M p') (b : Y.singularCohomology S k N q') :
    singularHomologyCross X Y R S p q n h ≫
      (X ⊗ Y).singularKronecker k n (TauCeti.singularCross k X Y μ p' q' n h' a b) = 0 := by
  simp only [singularHomologyCross_def, singularKronecker_def]
  -- the homology cross product is the algebraic one followed by the shuffle map
  exact (Category.assoc _ _ _).trans
    ((_ ≫= homologyMap_shuffle_comp_singularKronecker_singularCross μ X Y p' q' n h' a b).trans
      (TauCeti.ChainComplex.homologyCross_comp_kronecker_cup_of_ne _ _ μ p q h h' hp a b))

end General

section Kunneth

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- **The cohomology Künneth map** `⨁_{p + q = n} Hᵖ(X; R, M) ⊗ H^q(Y; S, N) ⟶ Hⁿ(X × Y; R ⊗ S, P)`,
whose restriction to the summand `Hᵖ(X; R, M) ⊗ H^q(Y; S, N)` is the cohomology cross product
`TauCeti.singularCross` along the coefficient pairing `μ`. -/
def singularCohomologyKunneth (X Y : TopCat.{w}) (R S : C) (k : Type v) [CommRing k] [Linear k C]
    [MonoidalLinear k C] {M N P : C} (μ : M ⊗ N ⟶ P) (n : ℕ) :
    GradedObject.Monoidal.tensorObj (fun p ↦ X.singularCohomology R k M p)
        (fun q ↦ Y.singularCohomology S k N q) n ⟶
      (X ⊗ Y).singularCohomology (R ⊗ S) k P n :=
  GradedObject.Monoidal.tensorObjDesc fun p q h ↦
    ModuleCat.ofHom (TensorProduct.lift (TauCeti.singularCross k X Y μ p q n h))

/-- The cohomology Künneth map restricts to the cohomology cross product on each summand. -/
@[simp]
lemma singularCohomologyKunneth_ιTensorObj_tmul (X Y : TopCat.{w}) {R S : C} {k : Type v}
    [CommRing k] [Linear k C] [MonoidalLinear k C] {M N P : C} (μ : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : p + q = n)
    (a : X.singularCohomology R k M p) (b : Y.singularCohomology S k N q) :
    singularCohomologyKunneth X Y R S k μ n
        (GradedObject.Monoidal.ιTensorObj (fun p ↦ X.singularCohomology R k M p)
          (fun q ↦ Y.singularCohomology S k N q) p q n h (a ⊗ₜ b)) =
      TauCeti.singularCross k X Y μ p q n h a b := by
  rw [singularCohomologyKunneth, ← ConcreteCategory.comp_apply]
  exact (ConcreteCategory.congr_hom (GradedObject.Monoidal.ι_tensorObjDesc _ p q h) _).trans
    (TensorProduct.lift.tmul (f' := TauCeti.singularCross k X Y μ p q n h) a b)

/-- **Naturality of the cohomology Künneth map** in both spaces: for continuous maps
`f : X ⟶ X'` and `g : Y ⟶ Y'`, pulling back by `f^* ⊗ g^*` and then applying the Künneth map of
`X` and `Y` is applying the Künneth map of `X'` and `Y'` and then pulling back by `(f × g)^*`. -/
@[reassoc]
lemma singularCohomologyKunneth_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (R S : C) (k : Type v) [CommRing k] [Linear k C] [MonoidalLinear k C] {M N P : C}
    (μ : M ⊗ N ⟶ P) (n : ℕ) :
    GradedObject.Monoidal.tensorHom
          (fun p ↦ TopCat.singularCohomologyMap (R := R) (k := k) (M := M) f p)
          (fun q ↦ TopCat.singularCohomologyMap (R := S) (k := k) (M := N) g q) n ≫
        singularCohomologyKunneth X Y R S k μ n =
      singularCohomologyKunneth X' Y' R S k μ n ≫ TopCat.singularCohomologyMap (f ⊗ₘ g) n := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦
    ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  simp [TauCeti.singularCross_naturality]

end Kunneth

section Semisimple

variable {k : Type w} [CommRing k] (X Y : TopCat.{w})

/-- The evaluation of a class of `Hⁿ(X × Y; k ⊗ k, k)` on the image of
`Hₚ(X; k) ⊗ H_q(Y; k)` under the homology cross product. -/
private def restrictCross (p q n : ℕ) (h : p + q = n) :
    (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n →ₗ[k]
      (((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X ⊗
          ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ (ModuleCat.{w} k))).obj Y ⟶
        𝟙_ (ModuleCat.{w} k)) :=
  Linear.leftComp k _ (singularHomologyCross X Y _ _ p q n h) ∘ₗ (X ⊗ Y).singularKronecker k n

private lemma restrictCross_apply (p q n : ℕ) (h : p + q = n)
    (α : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n) :
    restrictCross X Y p q n h α =
      singularHomologyCross X Y _ _ p q n h ≫ (X ⊗ Y).singularKronecker k n α :=
  rfl

/-- On the summand `Hᵖ'(X; k) ⊗ H^q'(Y; k)`, the Künneth map followed by evaluation on
`Hₚ(X; k) ⊗ H_q(Y; k)` vanishes when `p ≠ p'`. -/
private lemma restrictCross_singularCohomologyKunneth_ιTensorObj_of_ne {p q p' q' n : ℕ}
    (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    (u : (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p' ⊗
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q' :)) :
    restrictCross X Y p q n h
      (singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
        (λ_ (𝟙_ (ModuleCat.{w} k))).hom n
        (GradedObject.Monoidal.ιTensorObj
          (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
          (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
          p' q' n h' u)) = 0 := by
  induction u using TensorProduct.inductionOn with
  | tmul a b =>
    rw [singularCohomologyKunneth_ιTensorObj_tmul, restrictCross_apply,
      singularHomologyCross_comp_singularKronecker_singularCross_of_ne _ X Y p q h h' hp]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

variable [IsSemisimpleRing k]

attribute [local instance] Module.projective_of_isSemisimpleRing

/-- For finitely generated `Hₚ(X; k)`, the Kronecker maps identify `Hᵖ(X; k) ⊗ H^q(Y; k)` with the
dual of `Hₚ(X; k) ⊗ H_q(Y; k)`, through `Hom(A, k) ⊗ Hom(B, k) ≅ Hom(A ⊗ B, k)` for finitely
generated projective `A`. -/
private def kroneckerTensorEquiv (p q : ℕ)
    [Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)] :
    TensorProduct k (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) ≃ₗ[k]
      (((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X ⊗
          ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ (ModuleCat.{w} k))).obj Y ⟶
        𝟙_ (ModuleCat.{w} k)) :=
  TensorProduct.congr
      ((X.singularKroneckerEquivOfProjectiveHomology _ _ p).trans ModuleCat.homLinearEquiv)
      ((Y.singularKroneckerEquivOfProjectiveHomology _ _ q).trans ModuleCat.homLinearEquiv) ≪≫ₗ
    dualTensorHomEquiv k _ _ ≪≫ₗ TensorProduct.lift.equiv (RingHom.id k) _ _ _ ≪≫ₗ
      (ModuleCat.homLinearEquiv (S := k)
        (M := ((singularHomologyFunctor (ModuleCat.{w} k) p).obj (𝟙_ (ModuleCat.{w} k))).obj X ⊗
          ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ (ModuleCat.{w} k))).obj Y)
        (N := 𝟙_ (ModuleCat.{w} k))).symm

private lemma kroneckerTensorEquiv_tmul (p q : ℕ)
    [Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
      (𝟙_ (ModuleCat.{w} k))).obj X)]
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
    (b : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    kroneckerTensorEquiv X Y p q (a ⊗ₜ b) =
      (X.singularKronecker k p a ⊗ₘ Y.singularKronecker k q b) ≫
        (λ_ (𝟙_ (ModuleCat.{w} k))).hom := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun x y ↦ ?_
  simp [kroneckerTensorEquiv]
  -- `ModuleCat.homLinearEquiv` and its inverse are `ModuleCat.Hom.hom` and `ModuleCat.ofHom`, and
  -- both sides are `⟨a, x⟩ * ⟨b, y⟩`
  rfl

variable [∀ p, Module.Finite k (((singularHomologyFunctor (ModuleCat.{w} k) p).obj
  (𝟙_ (ModuleCat.{w} k))).obj X)]

/-- On the summand `Hᵖ(X; k) ⊗ H^q(Y; k)`, the Künneth map followed by evaluation on
`Hₚ(X; k) ⊗ H_q(Y; k)` is the identification `kroneckerTensorEquiv`. -/
private lemma restrictCross_singularCohomologyKunneth_ιTensorObj (p q n : ℕ) (h : p + q = n)
    (u : (X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p ⊗
      Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q :)) :
    restrictCross X Y p q n h
      (singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
        (λ_ (𝟙_ (ModuleCat.{w} k))).hom n
        (GradedObject.Monoidal.ιTensorObj
          (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
          (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
          p q n h u)) =
      kroneckerTensorEquiv X Y p q u := by
  induction u using TensorProduct.inductionOn with
  | tmul a b =>
    rw [singularCohomologyKunneth_ιTensorObj_tmul, restrictCross_apply,
      singularHomologyCross_comp_singularKronecker_singularCross, kroneckerTensorEquiv_tmul]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The inverse of the cohomology Künneth map, as a linear map: a class of
`Hⁿ(X × Y; k ⊗ k, k)` is sent to the sum over `p + q = n` of the preimages under
`kroneckerTensorEquiv` of its evaluations on the images of `Hₚ(X; k) ⊗ H_q(Y; k)`. -/
private def singularCohomologyKunnethInvAux (n : ℕ) :
    (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n →ₗ[k]
      GradedObject.Monoidal.tensorObj (C := ModuleCat.{w} k)
        (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n :=
  ∑ x : Finset.antidiagonal n,
    (GradedObject.Monoidal.ιTensorObj
      (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
      (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
      x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2)).hom ∘ₗ
    (kroneckerTensorEquiv X Y x.1.1 x.1.2).symm.toLinearMap ∘ₗ
      restrictCross X Y x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2)

/-- The inverse of the cohomology Künneth map. -/
private def singularCohomologyKunnethInv (n : ℕ) :
    (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n ⟶
      GradedObject.Monoidal.tensorObj
        (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n :=
  ModuleCat.ofHom (singularCohomologyKunnethInvAux X Y n)

private lemma singularCohomologyKunnethInv_apply (n : ℕ)
    (α : (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n) :
    singularCohomologyKunnethInv X Y n α = ∑ x : Finset.antidiagonal n,
      GradedObject.Monoidal.ιTensorObj
        (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q)
        x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2)
        ((kroneckerTensorEquiv X Y x.1.1 x.1.2).symm
          (restrictCross X Y x.1.1 x.1.2 n (Finset.mem_antidiagonal.1 x.2) α)) :=
  LinearMap.sum_apply _ _ α

private lemma singularCohomologyKunneth_comp_singularCohomologyKunnethInv (n : ℕ) :
    singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n ≫
      singularCohomologyKunnethInv X Y n = 𝟙 _ := by
  refine GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ModuleCat.hom_ext ?_
  ext u
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Category.comp_id]
  rw [singularCohomologyKunnethInv_apply, Fintype.sum_eq_single ⟨(p, q), by simpa using h⟩]
  · rw [restrictCross_singularCohomologyKunneth_ιTensorObj, LinearEquiv.symm_apply_apply]
  · intro x hx
    have hxp : x.1.1 ≠ p := fun hxp ↦ hx (Subtype.ext (Prod.ext hxp (by
      have := Finset.mem_antidiagonal.1 x.2
      dsimp only
      omega)))
    rw [restrictCross_singularCohomologyKunneth_ιTensorObj_of_ne X Y _ h hxp, map_zero, map_zero]

private lemma singularCohomologyKunnethInv_comp_singularCohomologyKunneth (n : ℕ) :
    singularCohomologyKunnethInv X Y n ≫
      singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n = 𝟙 _ := by
  ext α : 2
  -- classes of `Hⁿ(X × Y; k ⊗ k, k)` are determined by their evaluations on homology classes, and
  -- the homology Künneth isomorphism decomposes `Hₙ(X × Y; k ⊗ k)` into the images of the
  -- homology cross products
  refine ((X ⊗ Y).singularKronecker_bijective_of_projective_homology _ _ n).1 ?_
  refine (cancel_epi (singularHomologyKunnethIso X Y (𝟙_ (ModuleCat.{w} k))
    (𝟙_ (ModuleCat.{w} k)) n).hom).1 (GradedObject.Monoidal.tensorObj_ext _ _ fun p q h ↦ ?_)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply,
    singularHomologyKunnethIso_hom, ι_singularHomologyKunneth_assoc]
  rw [← restrictCross_apply, ← restrictCross_apply, singularCohomologyKunnethInv_apply, map_sum,
    map_sum, Fintype.sum_eq_single ⟨(p, q), by simpa using h⟩]
  · rw [restrictCross_singularCohomologyKunneth_ιTensorObj, LinearEquiv.apply_symm_apply]
  · intro x hx
    have hxp : p ≠ x.1.1 := fun hxp ↦ hx (Subtype.ext (Prod.ext hxp.symm (by
      have := Finset.mem_antidiagonal.1 x.2
      dsimp only
      omega)))
    exact restrictCross_singularCohomologyKunneth_ιTensorObj_of_ne X Y h _ hxp _

/-- **The Künneth isomorphism for cohomology**: over a commutative semisimple ring `k`, for
instance a field, if the homology `Hₚ(X; k)` is finitely generated in every degree, the cohomology
cross product induces an isomorphism `⨁_{p + q = n} Hᵖ(X; k) ⊗ H^q(Y; k) ≅ Hⁿ(X × Y; k)`.  Here
the product is computed from singular chains with coefficients in `k ⊗ k ≅ k`, and the pairing
`k ⊗ k ⟶ k` is multiplication. -/
def singularCohomologyKunnethIso (n : ℕ) :
    GradedObject.Monoidal.tensorObj
        (fun p ↦ X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p)
        (fun q ↦ Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) n ≅
      (X ⊗ Y).singularCohomology (𝟙_ (ModuleCat.{w} k) ⊗ 𝟙_ (ModuleCat.{w} k)) k
        (𝟙_ (ModuleCat.{w} k)) n where
  hom := singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n
  inv := singularCohomologyKunnethInv X Y n
  hom_inv_id := singularCohomologyKunneth_comp_singularCohomologyKunnethInv X Y n
  inv_hom_id := singularCohomologyKunnethInv_comp_singularCohomologyKunneth X Y n

@[simp]
lemma singularCohomologyKunnethIso_hom (n : ℕ) :
    (singularCohomologyKunnethIso X Y n).hom =
      singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n :=
  (rfl)

/-- Over a commutative semisimple ring, the cohomology Künneth map is an isomorphism when the
homology of `X` is finitely generated in every degree. -/
instance isIso_singularCohomologyKunneth (n : ℕ) :
    IsIso (singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k)) (𝟙_ (ModuleCat.{w} k)) k
      (λ_ (𝟙_ (ModuleCat.{w} k))).hom n) :=
  (singularCohomologyKunnethIso X Y n).isIso_hom

/-- **The Künneth theorem for cohomology**: over a commutative semisimple ring `k`, for instance a
field, if the homology `Hₚ(X; k)` is finitely generated in every degree, the cohomology Künneth map
`⨁_{p + q = n} Hᵖ(X; k) ⊗ H^q(Y; k) ⟶ Hⁿ(X × Y; k)` is bijective. -/
theorem singularCohomologyKunneth_bijective (n : ℕ) :
    Function.Bijective (singularCohomologyKunneth X Y (𝟙_ (ModuleCat.{w} k))
      (𝟙_ (ModuleCat.{w} k)) k (λ_ (𝟙_ (ModuleCat.{w} k))).hom n) :=
  (singularCohomologyKunnethIso X Y n).toLinearEquiv.bijective

end Semisimple

end TopCat
