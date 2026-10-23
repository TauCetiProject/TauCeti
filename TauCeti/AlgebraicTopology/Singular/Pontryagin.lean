/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.CrossProduct
public import TauCeti.Topology.Category.TopCat.MonObj

/-!
# The Pontryagin product in singular homology

Let `G` be a monoid object in `TopCat`, for instance a topological monoid or a topological group,
with multiplication `μ_G : G × G ⟶ G`, and let `R` be a monoid object of the coefficient category,
with multiplication `μ_R : R ⊗ R ⟶ R`, for instance the unit `𝟙_ C`, which is the ring `k` in
`ModuleCat k`.  The **Pontryagin product** is the morphism

`Hₚ(G; R) ⊗ H_q(G; R) ⟶ Hₙ(G; R)`, for `p + q = n`,

sending `a ⊗ b` to `(μ_G)_* (a × b)`, the homology cross product followed by the maps induced by
the two multiplications.  This file proves:

* naturality in morphisms of monoid objects `G ⟶ G'`, for instance continuous monoid
  homomorphisms (`TopCat.pontryaginProduct_naturality`), and in morphisms of monoid objects of
  coefficients (`TopCat.pontryaginProduct_coefficient_naturality`);
* associativity, `(a · b) · c = a · (b · c)` with no sign
  (`TopCat.pontryaginProduct_assoc`), from the associativity of the cross product
  (`TopCat.singularHomologyCross_assoc`) and of the two multiplications;
* graded commutativity, `a · b = (-1)^(p * q) b · a` for a commutative monoid object `G` and
  commutative coefficients in a braided category (`TopCat.pontryaginProduct_comm`), from the
  graded commutativity of the cross product (`TopCat.singularHomologyCross_comp_map_braiding`).

As for `TopCat.singularHomologyCross`, the definition and the naturality and commutativity
statements only assume that tensoring preserves the cokernels the cross product uses, while
associativity assumes that tensoring with any object preserves cokernels, as in `ModuleCat`.

## Main definitions and results

* `TopCat.pontryaginProduct`: the Pontryagin product `Hₚ(G; R) ⊗ H_q(G; R) ⟶ Hₙ(G; R)`.
* `TopCat.homologyπ_tensorHom_pontryaginProduct`: its value on classes of cycles.
* `TopCat.pontryaginProduct_naturality`, `TopCat.pontryaginProduct_coefficient_naturality`:
  naturality in the monoid object and in the coefficients.
* `TopCat.pontryaginProduct_assoc`: associativity.
* `TopCat.pontryaginProduct_comm`: graded commutativity.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.C, the Pontryagin product on the homology of an H-space.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex MonObj

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

section Product

variable (G : TopCat.{w}) [MonObj G] (R : C) [MonObj R] (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj G).chainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).X ((ComplexShape.down ℕ).prev q)))]

/-- **The Pontryagin product** `Hₚ(G; R) ⊗ H_q(G; R) ⟶ Hₙ(G; R)` for `p + q = n`, on the
singular homology of a monoid object `G` of `TopCat` with coefficients in a monoid object `R`:
the homology cross product followed by the maps induced by the multiplications of the
coefficients and of `G`. -/
def pontryaginProduct :
    ((singularHomologyFunctor C p).obj R).obj G ⊗ ((singularHomologyFunctor C q).obj R).obj G ⟶
      ((singularHomologyFunctor C n).obj R).obj G :=
  singularHomologyCross G G R R p q n h ≫ ((singularHomologyFunctor C n).map μ[R]).app (G ⊗ G) ≫
    ((singularHomologyFunctor C n).obj R).map μ[G]

/-- The Pontryagin product is the homology cross product followed by the maps induced by the
multiplications of the coefficients and of `G`. -/
lemma pontryaginProduct_def :
    pontryaginProduct G R p q n h =
      singularHomologyCross G G R R p q n h ≫
        ((singularHomologyFunctor C n).map μ[R]).app (G ⊗ G) ≫
          ((singularHomologyFunctor C n).obj R).map μ[G] :=
  (rfl)

/-- The Pontryagin product of the classes of two singular cycles is the class of the image of
their shuffle product under the chain maps induced by the two multiplications. -/
@[reassoc]
lemma homologyπ_tensorHom_pontryaginProduct :
    (((toSSet.obj G).chainComplex R).homologyπ p ⊗ₘ ((toSSet.obj G).chainComplex R).homologyπ q) ≫
        pontryaginProduct G R p q n h =
      cyclesCross ((toSSet.obj G).chainComplex R) ((toSSet.obj G).chainComplex R) p q n h ≫
        cyclesMap (shuffle G G R R ≫
          ((SSet.chainComplexFunctor C).map μ[R]).app (toSSet.obj (G ⊗ G)) ≫
            SSet.chainComplexMap (toSSet.map μ[G]) R) n ≫
          ((toSSet.obj G).chainComplex R).homologyπ n := by
  -- the singular homology maps are by definition those of the induced chain maps
  refine ((Category.assoc _ _ _).symm.trans
    (homologyπ_tensorHom_singularHomologyCross G G R R p q n h =≫ _)).trans ?_
  refine (Category.assoc _ _ _).trans (_ ≫= (Category.assoc _ _ _).trans ?_)
  rw [cyclesMap_comp_assoc, cyclesMap_comp_assoc]
  exact _ ≫= ((homologyπ_naturality_assoc _ n _).trans (_ ≫= homologyπ_naturality _ n))

end Product

section Naturality

variable {G G' : TopCat.{w}} [MonObj G] [MonObj G'] (f : G ⟶ G') [IsMonHom f]
  (R : C) [MonObj R] (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj G).chainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).X ((ComplexShape.down ℕ).prev q)))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj G').chainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G').chainComplex R).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G').chainComplex R).X ((ComplexShape.down ℕ).prev q)))]

/-- **Naturality of the Pontryagin product** in the monoid object: a morphism of monoid objects
`f : G ⟶ G'`, for instance a continuous monoid homomorphism, satisfies
`f_* a · f_* b = f_* (a · b)`. -/
@[reassoc]
lemma pontryaginProduct_naturality :
    (((singularHomologyFunctor C p).obj R).map f ⊗ₘ ((singularHomologyFunctor C q).obj R).map f) ≫
        pontryaginProduct G' R p q n h =
      pontryaginProduct G R p q n h ≫ ((singularHomologyFunctor C n).obj R).map f := by
  rw [pontryaginProduct_def, pontryaginProduct_def, singularHomologyCross_naturality_assoc,
    NatTrans.naturality_assoc, ← Functor.map_comp, ← IsMonHom.mul_hom, Functor.map_comp]
  simp only [Category.assoc]

end Naturality

section CoefficientNaturality

variable (G : TopCat.{w}) [MonObj G] {R R' : C} [MonObj R] [MonObj R'] (φ : R ⟶ R') [IsMonHom φ]
  (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj G).chainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).X ((ComplexShape.down ℕ).prev q)))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj G).chainComplex R').homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R').cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R').X ((ComplexShape.down ℕ).prev q)))]

/-- **Naturality of the Pontryagin product** in the coefficients: a morphism of monoid objects
`φ : R ⟶ R'` satisfies `φ_* a · φ_* b = φ_* (a · b)`. -/
@[reassoc]
lemma pontryaginProduct_coefficient_naturality :
    (((singularHomologyFunctor C p).map φ).app G ⊗ₘ ((singularHomologyFunctor C q).map φ).app G) ≫
        pontryaginProduct G R' p q n h =
      pontryaginProduct G R p q n h ≫ ((singularHomologyFunctor C n).map φ).app G := by
  rw [pontryaginProduct_def, pontryaginProduct_def,
    singularHomologyCross_coefficient_naturality_assoc, ← NatTrans.comp_app_assoc,
    ← Functor.map_comp, ← IsMonHom.mul_hom, Functor.map_comp, NatTrans.comp_app_assoc]
  simp only [Category.assoc, NatTrans.naturality]

end CoefficientNaturality

section Associativity

variable [∀ T : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft T)]
  [∀ T : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight T)]

variable (G : TopCat.{w}) [MonObj G] (R : C) [MonObj R] (p q r pq qr n : ℕ)
  (hpq : p + q = pq) (hqr : q + r = qr) (hn : pq + r = n) (hn' : p + qr = n)

/-- **Associativity of the Pontryagin product**: `(a · b) · c = a · (b · c)`, with no sign. -/
@[reassoc]
lemma pontryaginProduct_assoc :
    pontryaginProduct G R p q pq hpq ▷ ((singularHomologyFunctor C r).obj R).obj G ≫
        pontryaginProduct G R pq r n hn =
      (α_ _ _ _).hom ≫ ((singularHomologyFunctor C p).obj R).obj G ◁
          pontryaginProduct G R q r qr hqr ≫
        pontryaginProduct G R p qr n hn' := by
  -- move the inner multiplications past the outer cross product
  have hL : pontryaginProduct G R p q pq hpq ▷ ((singularHomologyFunctor C r).obj R).obj G ≫
      singularHomologyCross G G R R pq r n hn =
      singularHomologyCross G G R R p q pq hpq ▷ ((singularHomologyFunctor C r).obj R).obj G ≫
        singularHomologyCross (G ⊗ G) G (R ⊗ R) R pq r n hn ≫
          ((singularHomologyFunctor C n).map (μ[R] ▷ R)).app ((G ⊗ G) ⊗ G) ≫
            ((singularHomologyFunctor C n).obj (R ⊗ R)).map (μ[G] ▷ G) := by
    have h1 := singularHomologyCross_coefficient_naturality (G ⊗ G) G μ[R] (𝟙 R) pq r n hn
    have h2 := singularHomologyCross_naturality μ[G] (𝟙 G) R R pq r n hn
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, tensorHom_id] at h1 h2
    rw [pontryaginProduct_def, comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
      h2, reassoc_of% h1]
  have hR : ((singularHomologyFunctor C p).obj R).obj G ◁ pontryaginProduct G R q r qr hqr ≫
      singularHomologyCross G G R R p qr n hn' =
      ((singularHomologyFunctor C p).obj R).obj G ◁ singularHomologyCross G G R R q r qr hqr ≫
        singularHomologyCross G (G ⊗ G) R (R ⊗ R) p qr n hn' ≫
          ((singularHomologyFunctor C n).map (R ◁ μ[R])).app (G ⊗ (G ⊗ G)) ≫
            ((singularHomologyFunctor C n).obj (R ⊗ R)).map (G ◁ μ[G]) := by
    have h1 := singularHomologyCross_coefficient_naturality G (G ⊗ G) (𝟙 R) μ[R] p qr n hn'
    have h2 := singularHomologyCross_naturality (𝟙 G) μ[G] R R p qr n hn'
    simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, id_tensorHom] at h1 h2
    rw [pontryaginProduct_def, whiskerLeft_comp, whiskerLeft_comp, Category.assoc, Category.assoc,
      h2, reassoc_of% h1]
  -- then combine the multiplications of the coefficients and of `G`
  have hmul {S : C} {X : TopCat.{w}} (a : S ⟶ R ⊗ R) (f : X ⟶ G ⊗ G) :
      ((singularHomologyFunctor C n).map a).app X ≫
          ((singularHomologyFunctor C n).obj (R ⊗ R)).map f ≫
            ((singularHomologyFunctor C n).map μ[R]).app (G ⊗ G) ≫
              ((singularHomologyFunctor C n).obj R).map μ[G] =
        ((singularHomologyFunctor C n).map (a ≫ μ[R])).app X ≫
          ((singularHomologyFunctor C n).obj R).map (f ≫ μ[G]) := by
    rw [NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc, ← Functor.map_comp,
      ← Functor.map_comp]
  rw [pontryaginProduct_def G R pq r n hn, pontryaginProduct_def G R p qr n hn', reassoc_of% hL,
    reassoc_of% hR, hmul, hmul, MonObj.mul_assoc R, MonObj.mul_assoc G,
    (singularHomologyFunctor C n).map_comp (α_ R R R).hom, NatTrans.comp_app,
    ((singularHomologyFunctor C n).obj R).map_comp (α_ G G G).hom, Category.assoc,
    ← NatTrans.naturality_assoc, singularHomologyCross_assoc_assoc]

end Associativity

section Commutativity

variable [BraidedCategory C]

variable (G : TopCat.{w}) [MonObj G] [IsCommMonObj G] (R : C) [MonObj R] [IsCommMonObj R]
  (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj G).chainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).X ((ComplexShape.down ℕ).prev q)))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj G).chainComplex R).homology q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).cycles p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj G).chainComplex R).X ((ComplexShape.down ℕ).prev p)))]

/-- **Graded commutativity of the Pontryagin product**: for a commutative monoid object `G` and
commutative coefficients, `a · b = (-1)^(p * q) b · a` for `a ∈ Hₚ(G; R)` and `b ∈ H_q(G; R)`. -/
lemma pontryaginProduct_comm :
    pontryaginProduct G R p q n h =
      ((-1 : ℤ) ^ (p * q)) • ((β_ _ _).hom ≫ pontryaginProduct G R q p n (by omega)) := by
  -- both multiplications are invariant under the braiding, which then moves to the cross product
  have hR : (singularHomologyFunctor C n).map μ[R] =
      (singularHomologyFunctor C n).map (β_ R R).hom ≫ (singularHomologyFunctor C n).map μ[R] := by
    rw [← Functor.map_comp, IsCommMonObj.mul_comm]
  have hG : ((singularHomologyFunctor C n).obj R).map μ[G] =
      ((singularHomologyFunctor C n).obj R).map (β_ G G).hom ≫
        ((singularHomologyFunctor C n).obj R).map μ[G] := by
    rw [← Functor.map_comp, IsCommMonObj.mul_comm]
  rw [pontryaginProduct_def, pontryaginProduct_def]
  conv_lhs => rw [hR, hG]
  rw [NatTrans.comp_app, Category.assoc, ← NatTrans.naturality_assoc,
    singularHomologyCross_comp_map_braiding_assoc, Preadditive.zsmul_comp, Category.assoc]

end Commutativity

end TopCat
