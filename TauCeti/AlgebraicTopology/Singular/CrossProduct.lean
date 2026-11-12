/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Bifunctor.Homotopy
public import TauCeti.Algebra.Homology.Monoidal.Homology.Associativity
public import TauCeti.Algebra.Homology.Monoidal.Homology.Braiding
public import TauCeti.AlgebraicTopology.Singular.EilenbergZilber
public import TauCeti.AlgebraicTopology.Singular.KoszulBraiding

/-!
# The cross product in singular homology

For topological spaces `X` and `Y` and coefficient objects `R` and `S`, the homology cross
product is the morphism

`Hₚ(X; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)`, for `p + q = n`.

It is the cross product `HomologicalComplex.homologyCross` of the singular chain complexes,
`Hₚ(C(X; R)) ⊗ H_q(C(Y; S)) ⟶ Hₙ(C(X; R) ⊗ C(Y; S))`, followed by the map on homology induced
by the Eilenberg–Mac Lane shuffle map `C(X; R) ⊗ C(Y; S) ⟶ C(X × Y; R ⊗ S)`.  On classes of
cycles `a` and `b` it is the class of the shuffle product `a × b`.  It is natural in both spaces
and in both coefficient objects.  As for `HomologicalComplex.homologyCross`, each declaration
only assumes that tensoring preserves cokernels for the three objects the construction uses:
`tensorLeft` of `Hₚ(C(X; R))`, and `tensorRight` of the cycles `Z_q(C(Y; S))` and of the chains
`C_{q+1}(Y; S)`.  For `ModuleCat` these are found by instance search.

By the Eilenberg–Zilber theorem the shuffle map is a chain homotopy equivalence with homotopy
inverse the Alexander–Whitney map, so the map induced by Alexander–Whitney on homology recovers
the algebraic cross product (`TopCat.singularHomologyCross_comp_homologyMap_alexanderWhitney`).
So the Künneth theorem over a field, that the direct sum over all `p + q = n` of the homology
cross products `Hₚ(X; k) ⊗ H_q(Y; k) ⟶ Hₙ(X × Y; k)` is an isomorphism, reduces to the
corresponding statement for the direct sum of the algebraic cross products of the singular chain
complexes.

The cross product is associative: the map induced by the associators of the spaces and of the
coefficients sends `(a × b) × c` to `a × (b × c)`, with no sign
(`TopCat.singularHomologyCross_assoc`).  Under the Eilenberg–Zilber isomorphisms this is the
coassociativity of the Alexander–Whitney map (`TopCat.alexanderWhitney_coassoc`) together with
the associativity of the algebraic cross product (`HomologicalComplex.homologyCross_assoc`).
Since it involves the cross products of the intermediate complexes `C(X; R) ⊗ C(Y; S)` and
`C(Y; S) ⊗ C(Z; T)`, this statement assumes that tensoring with any object preserves cokernels,
as in `ModuleCat`.  It makes iterated cross products independent of the bracketing.

In a braided coefficient category the cross product is graded commutative: the swap
`X × Y ⟶ Y × X`, together with the coefficient braiding `R ⊗ S ⟶ S ⊗ R`, sends `a × b` to
`(-1)^(p * q) b × a` for `a ∈ Hₚ(X; R)` and `b ∈ H_q(Y; S)`
(`TopCat.singularHomologyCross_comp_map_braiding`).  At chain level, the shuffle map commutes
with the interchange of factors up to homotopy, with the Koszul sign
(`TopCat.koszulBraidingShuffleHomotopy`); on homology this sign is that of the algebraic cross
product (`TauCeti.NatChainComplex.homologyCross_comp_homologyMap_koszulBraidingHom`).  With
coefficients in the monoidal unit, such as `k` in `ModuleCat k`, and `𝟙_ C ⊗ 𝟙_ C` identified
with `𝟙_ C` through the left unitor, the statement needs no coefficient braiding
(`TopCat.singularHomologyCross_comp_map_leftUnitor_comp_map_braiding`).

## Main definitions and results

* `TopCat.singularHomologyCross`: the homology cross product.
* `TopCat.homologyπ_tensorHom_singularHomologyCross`: its value on classes of cycles.
* `TopCat.singularHomologyCross_naturality` and
  `TopCat.singularHomologyCross_coefficient_naturality`: naturality in the spaces and in the
  coefficients.
* `TopCat.singularHomologyCross_comp_homologyMap_alexanderWhitney`: under the Eilenberg–Zilber
  isomorphism, the homology cross product is the cross product of the singular chain complexes.
* `TopCat.singularHomologyCross_assoc`: associativity of the homology cross product.
* `TopCat.singularHomologyCross_comp_map_braiding` and
  `TopCat.singularHomologyCross_comp_map_leftUnitor_comp_map_braiding`: graded commutativity of
  the homology cross product.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the cross product in homology.
* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

/-- **The homology cross product** `Hₚ(X; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)` for `p + q = n`:
the cross product of the singular chain complexes followed by the shuffle map. -/
def singularHomologyCross (X Y : TopCat.{w}) (R S : C) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    ((singularHomologyFunctor C p).obj R).obj X ⊗ ((singularHomologyFunctor C q).obj S).obj Y ⟶
      ((singularHomologyFunctor C n).obj (R ⊗ S)).obj (X ⊗ Y) :=
  homologyCross ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) p q n h ≫
    homologyMap (shuffle X Y R S) n

/-- The homology cross product is the cross product of the singular chain complexes followed by
the map induced by the shuffle map. -/
lemma singularHomologyCross_def (X Y : TopCat.{w}) (R S : C) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    singularHomologyCross X Y R S p q n h =
      homologyCross ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) p q n h ≫
        homologyMap (shuffle X Y R S) n :=
  (rfl)

/-- The cross product of the classes of two singular cycles is the class of their shuffle
product. -/
@[simp, reassoc]
lemma homologyπ_tensorHom_singularHomologyCross (X Y : TopCat.{w}) (R S : C) (p q n : ℕ)
    (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    (((toSSet.obj X).chainComplex R).homologyπ p ⊗ₘ ((toSSet.obj Y).chainComplex S).homologyπ q) ≫
        singularHomologyCross X Y R S p q n h =
      cyclesCross ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) p q n h ≫
        cyclesMap (shuffle X Y R S) n ≫
          ((toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S)).homologyπ n :=
  (homologyπ_tensorHom_homologyCross_assoc _ _ p q n h _).trans
    (cyclesCross _ _ p q n h ≫= homologyπ_naturality (shuffle X Y R S) n)

/-- **Naturality of the homology cross product** in both spaces:
`f_* a × g_* b = (f × g)_* (a × b)`. -/
@[reassoc]
lemma singularHomologyCross_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (R S : C) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X').chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    (((singularHomologyFunctor C p).obj R).map f ⊗ₘ ((singularHomologyFunctor C q).obj S).map g) ≫
        singularHomologyCross X' Y' R S p q n h =
      singularHomologyCross X Y R S p q n h ≫
        ((singularHomologyFunctor C n).obj (R ⊗ S)).map (f ⊗ₘ g) := by
  -- `Hₙ(f)` is by definition the homology of the induced chain map, so the statement is the
  -- naturality of the algebraic cross product followed by that of the shuffle map.
  have hsh : HomologicalComplex.tensorHom (SSet.chainComplexMap (toSSet.map f) R)
      (SSet.chainComplexMap (toSSet.map g) S) ≫ shuffle X' Y' R S =
        shuffle X Y R S ≫ SSet.chainComplexMap (toSSet.map (f ⊗ₘ g)) (R ⊗ S) :=
    shuffle_naturality f g R S
  have := homologyCross_naturality_assoc (SSet.chainComplexMap (toSSet.map f) R)
    (SSet.chainComplexMap (toSSet.map g) S) p q n h (homologyMap (shuffle X' Y' R S) n)
  rw [← homologyMap_comp, hsh, homologyMap_comp] at this
  exact this.trans (Category.assoc _ _ _).symm

/-- **Naturality of the homology cross product** in both coefficient objects. -/
@[reassoc]
lemma singularHomologyCross_coefficient_naturality (X Y : TopCat.{w}) {R S R' S' : C}
    (φ : R ⟶ R') (ψ : S ⟶ S') (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R').homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S').cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S').X ((ComplexShape.down ℕ).prev q)))] :
    (((singularHomologyFunctor C p).map φ).app X ⊗ₘ ((singularHomologyFunctor C q).map ψ).app Y) ≫
        singularHomologyCross X Y R' S' p q n h =
      singularHomologyCross X Y R S p q n h ≫
        ((singularHomologyFunctor C n).map (φ ⊗ₘ ψ)).app (X ⊗ Y) := by
  -- `Hₙ(-; φ)` is by definition the homology of the induced chain map, so the statement is the
  -- naturality of the algebraic cross product followed by that of the shuffle map.
  have hsh : HomologicalComplex.tensorHom (((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X))
      (((SSet.chainComplexFunctor C).map ψ).app (toSSet.obj Y)) ≫ shuffle X Y R' S' =
        shuffle X Y R S ≫ ((SSet.chainComplexFunctor C).map (φ ⊗ₘ ψ)).app (toSSet.obj (X ⊗ Y)) :=
    shuffle_coefficient_naturality X Y φ ψ
  have := homologyCross_naturality_assoc (((SSet.chainComplexFunctor C).map φ).app (toSSet.obj X))
    (((SSet.chainComplexFunctor C).map ψ).app (toSSet.obj Y)) p q n h
    (homologyMap (shuffle X Y R' S') n)
  rw [← homologyMap_comp, hsh, homologyMap_comp] at this
  exact this.trans (Category.assoc _ _ _).symm

/-- **The homology cross product under Eilenberg–Zilber**: following the homology cross product
by the map induced by the Alexander–Whitney map gives the cross product of the singular chain
complexes.  Since the Alexander–Whitney map is a chain homotopy equivalence, this identifies the
homology cross product with the algebraic one. -/
@[simp, reassoc]
lemma singularHomologyCross_comp_homologyMap_alexanderWhitney (X Y : TopCat.{w}) (R S : C)
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    singularHomologyCross X Y R S p q n h ≫ homologyMap (alexanderWhitney X Y R S) n =
      homologyCross ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) p q n h :=
  (Category.assoc _ _ _).trans <| (homologyCross _ _ p q n h ≫=
    homologyMap_shuffle_comp_homologyMap_alexanderWhitney X Y R S n).trans (Category.comp_id _)

section Associativity

variable [∀ T : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft T)]
  [∀ T : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight T)]

variable (X Y Z : TopCat.{w}) (R S T : C) (p q r pq qr n : ℕ)
  (hpq : p + q = pq) (hqr : q + r = qr) (hn : pq + r = n) (hn' : p + qr = n)

/-- `singularHomologyCross_assoc` followed by the map induced on homology by `AW_{X, Y × Z}` and
`C(X) ◁ AW_{Y, Z}`, with the singular homology objects and maps unfolded to the homology of the
singular chain complexes.  Both sides become iterated algebraic cross products. -/
private lemma singularHomologyCross_assoc_comp_homologyMap :
    ((homologyCross _ _ p q pq hpq ≫ homologyMap (shuffle X Y R S) pq) ▷
        ((toSSet.obj Z).chainComplex T).homology r ≫
      (homologyCross _ _ pq r n hn ≫ homologyMap (shuffle (X ⊗ Y) Z (R ⊗ S) T) n) ≫
      homologyMap (((SSet.chainComplexFunctor C).map (α_ R S T).hom).app
        (toSSet.obj ((X ⊗ Y) ⊗ Z))) n ≫
      homologyMap (SSet.chainComplexMap (toSSet.map (α_ X Y Z).hom) (R ⊗ S ⊗ T)) n) ≫
        homologyMap (alexanderWhitney X (Y ⊗ Z) R (S ⊗ T) ≫
          (toSSet.obj X).chainComplex R ◁ alexanderWhitney Y Z S T) n =
      ((α_ _ _ _).hom ≫
        ((toSSet.obj X).chainComplex R).homology p ◁
          (homologyCross _ _ q r qr hqr ≫ homologyMap (shuffle Y Z S T) qr) ≫
        (homologyCross _ _ p qr n hn' ≫ homologyMap (shuffle X (Y ⊗ Z) R (S ⊗ T)) n)) ≫
        homologyMap (alexanderWhitney X (Y ⊗ Z) R (S ⊗ T) ≫
          (toSSet.obj X).chainComplex R ◁ alexanderWhitney Y Z S T) n := by
  -- naturality of the algebraic cross product in each factor; the whiskerings of complexes are
  -- by definition the tensor products with identities
  have hR : homologyCross ((toSSet.obj X).chainComplex R)
      ((toSSet.obj (Y ⊗ Z)).chainComplex (S ⊗ T)) p qr n hn' ≫
        homologyMap ((toSSet.obj X).chainComplex R ◁ alexanderWhitney Y Z S T) n =
        _ ◁ homologyMap (alexanderWhitney Y Z S T) qr ≫ homologyCross _ _ p qr n hn' := by
    have := homologyCross_naturality (𝟙 ((toSSet.obj X).chainComplex R))
      (alexanderWhitney Y Z S T) p qr n hn'
    rw [homologyMap_id, id_tensorHom] at this
    exact this.symm
  have hL : homologyCross ((toSSet.obj (X ⊗ Y)).chainComplex (R ⊗ S))
      ((toSSet.obj Z).chainComplex T) pq r n hn ≫
        homologyMap (alexanderWhitney X Y R S ▷ (toSSet.obj Z).chainComplex T) n =
        homologyMap (alexanderWhitney X Y R S) pq ▷ _ ≫ homologyCross _ _ pq r n hn := by
    have := homologyCross_naturality (alexanderWhitney X Y R S)
      (𝟙 ((toSSet.obj Z).chainComplex T)) pq r n hn
    rw [homologyMap_id, tensorHom_id] at this
    exact this.symm
  -- the coassociativity of the Alexander–Whitney map, on homology
  have hA : homologyMap (((SSet.chainComplexFunctor C).map (α_ R S T).hom).app
        (toSSet.obj ((X ⊗ Y) ⊗ Z))) n ≫
      homologyMap (SSet.chainComplexMap (toSSet.map (α_ X Y Z).hom) (R ⊗ S ⊗ T)) n ≫
      homologyMap (alexanderWhitney X (Y ⊗ Z) R (S ⊗ T)) n ≫
      homologyMap ((toSSet.obj X).chainComplex R ◁ alexanderWhitney Y Z S T) n =
        homologyMap (alexanderWhitney (X ⊗ Y) Z (R ⊗ S) T) n ≫
          homologyMap (alexanderWhitney X Y R S ▷ (toSSet.obj Z).chainComplex T) n ≫
          homologyMap (α_ ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S)
            ((toSSet.obj Z).chainComplex T)).hom n := by
    simp only [← homologyMap_comp, alexanderWhitney_coassoc]
  simp only [homologyMap_comp, Category.assoc, comp_whiskerRight, whiskerLeft_comp]
  rw [hA, homologyMap_shuffle_comp_homologyMap_alexanderWhitney_assoc, reassoc_of% hL,
    homologyMap_shuffle_comp_homologyMap_alexanderWhitney_assoc, hR,
    ← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, ← whiskerLeft_comp_assoc,
    ← whiskerLeft_comp_assoc]
  simp only [Category.assoc, homologyMap_shuffle_comp_homologyMap_alexanderWhitney]
  -- `homologyCross` lands in the homology of `HomologicalComplex.tensorObj`, which is the
  -- monoidal tensor product of complexes only up to unfolding
  erw [Category.comp_id, Category.comp_id]
  exact homologyCross_assoc ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S)
    ((toSSet.obj Z).chainComplex T) p q r pq qr n hpq hqr hn hn'

/-- **Associativity of the homology cross product**: the map induced by the associator
`(X × Y) × Z ⟶ X × (Y × Z)` and the coefficient associator `(R ⊗ S) ⊗ T ⟶ R ⊗ (S ⊗ T)` sends
`(a × b) × c` to `a × (b × c)`, with no sign. -/
@[reassoc]
lemma singularHomologyCross_assoc :
    singularHomologyCross X Y R S p q pq hpq ▷ ((singularHomologyFunctor C r).obj T).obj Z ≫
        singularHomologyCross (X ⊗ Y) Z (R ⊗ S) T pq r n hn ≫
        ((singularHomologyFunctor C n).map (α_ R S T).hom).app ((X ⊗ Y) ⊗ Z) ≫
        ((singularHomologyFunctor C n).obj (R ⊗ S ⊗ T)).map (α_ X Y Z).hom =
      (α_ _ _ _).hom ≫
        ((singularHomologyFunctor C p).obj R).obj X ◁ singularHomologyCross Y Z S T q r qr hqr ≫
        singularHomologyCross X (Y ⊗ Z) R (S ⊗ T) p qr n hn' := by
  -- `AW_{X, Y × Z}` followed by `C(X) ◁ AW_{Y, Z}` is a homotopy equivalence, so the map it
  -- induces on homology is an isomorphism and can be cancelled
  let e : HomotopyEquiv ((toSSet.obj (X ⊗ Y ⊗ Z)).chainComplex (R ⊗ S ⊗ T))
      ((toSSet.obj X).chainComplex R ⊗
        ((toSSet.obj Y).chainComplex S ⊗ (toSSet.obj Z).chainComplex T)) :=
    (eilenbergZilberHomotopyEquiv X (Y ⊗ Z) R (S ⊗ T)).trans
      (HomotopyEquiv.mapBifunctor (curriedTensor C) (ComplexShape.down ℕ) (HomotopyEquiv.refl _)
        (eilenbergZilberHomotopyEquiv Y Z S T))
  have he : e.hom = alexanderWhitney X (Y ⊗ Z) R (S ⊗ T) ≫
      (toSSet.obj X).chainComplex R ◁ alexanderWhitney Y Z S T := by
    simp [e, whiskerLeft_eq_mapBifunctorMap]
  have : IsIso (homologyMap e.hom n) := (e.toHomologyIso n).isIso_hom
  rw [he] at this
  -- the singular homology objects and maps are by definition those of the singular chains
  exact (cancel_mono (homologyMap (alexanderWhitney X (Y ⊗ Z) R (S ⊗ T) ≫
    (toSSet.obj X).chainComplex R ◁ alexanderWhitney Y Z S T) n)).1
    (singularHomologyCross_assoc_comp_homologyMap X Y Z R S T p q r pq qr n hpq hqr hn hn')

end Associativity

section Braided

variable [BraidedCategory C]

variable (X Y : TopCat.{w}) (R S : C) (p q n : ℕ) (h : p + q = n)
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj Y).chainComplex S).homology q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj X).chainComplex R).cycles p))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj X).chainComplex R).X ((ComplexShape.down ℕ).prev p)))]

/-- **Graded commutativity of the homology cross product**: the map induced by the swap
`X × Y ⟶ Y × X` and the coefficient braiding `R ⊗ S ⟶ S ⊗ R` sends the cross product `a × b` of
`a ∈ Hₚ(X; R)` and `b ∈ H_q(Y; S)` to `(-1)^(p * q) b × a`. -/
@[reassoc (attr := simp)]
lemma singularHomologyCross_comp_map_braiding :
    singularHomologyCross X Y R S p q n h ≫
        ((singularHomologyFunctor C n).map (β_ R S).hom).app (X ⊗ Y) ≫
          ((singularHomologyFunctor C n).obj (S ⊗ R)).map (β_ X Y).hom =
      ((-1 : ℤ) ^ (p * q)) • ((β_ _ _).hom ≫ singularHomologyCross Y X S R q p n (by omega)) := by
  -- the singular homology maps are by definition those of the induced chain maps
  have key := (homologyCross _ _ p q n h ≫= (homologyMap_comp _ _ n).symm).trans <|
    (homologyCross _ _ p q n h ≫=
      (koszulBraidingShuffleHomotopy X Y R S).homologyMap_eq n).symm.trans <|
      (homologyCross _ _ p q n h ≫= homologyMap_comp _ _ n).trans <|
        TauCeti.NatChainComplex.homologyCross_comp_homologyMap_koszulBraidingHom_assoc _ _ p q n h _
  simp only [homologyMap_comp, Preadditive.zsmul_comp, Category.assoc] at key
  exact (Category.assoc _ _ _).trans key

/-- **Graded commutativity of the homology cross product with coefficients in the unit**: with
coefficients in the monoidal unit `𝟙_ C`, for instance `k` in `ModuleCat k`, and the product of
coefficients identified with `𝟙_ C` through the left unitor, the map induced by the swap
`X × Y ⟶ Y × X` sends `a × b` to `(-1)^(p * q) b × a`. -/
@[reassoc (attr := simp)]
lemma singularHomologyCross_comp_map_leftUnitor_comp_map_braiding
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex (𝟙_ C)).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex (𝟙_ C)).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex (𝟙_ C)).X ((ComplexShape.down ℕ).prev q)))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj Y).chainComplex (𝟙_ C)).homology q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj X).chainComplex (𝟙_ C)).cycles p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj X).chainComplex (𝟙_ C)).X ((ComplexShape.down ℕ).prev p)))] :
    singularHomologyCross X Y (𝟙_ C) (𝟙_ C) p q n h ≫
        ((singularHomologyFunctor C n).map (λ_ (𝟙_ C)).hom).app (X ⊗ Y) ≫
          ((singularHomologyFunctor C n).obj (𝟙_ C)).map (β_ X Y).hom =
      ((-1 : ℤ) ^ (p * q)) • ((β_ _ _).hom ≫
        singularHomologyCross Y X (𝟙_ C) (𝟙_ C) q p n (by omega) ≫
          ((singularHomologyFunctor C n).map (λ_ (𝟙_ C)).hom).app (Y ⊗ X)) := by
  -- the braiding of the unit with itself is the identity: `β_{𝟙,𝟙} ≫ λ_𝟙 = ρ_𝟙 = λ_𝟙`
  have hunit : (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom := by
    rw [braiding_leftUnitor, unitors_equal]
  have hmap : ((singularHomologyFunctor C n).map (λ_ (𝟙_ C)).hom).app (Y ⊗ X) =
      ((singularHomologyFunctor C n).map (β_ (𝟙_ C) (𝟙_ C)).hom).app (Y ⊗ X) ≫
        ((singularHomologyFunctor C n).map (λ_ (𝟙_ C)).hom).app (Y ⊗ X) := by
    rw [← NatTrans.comp_app, ← Functor.map_comp, hunit]
  rw [← NatTrans.naturality, hmap, NatTrans.naturality_assoc,
    singularHomologyCross_comp_map_braiding_assoc, Preadditive.zsmul_comp, Category.assoc,
    ← hmap]

end Braided

end TopCat
