/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth
public import TauCeti.AlgebraicTopology.Singular.CrossProduct

/-!
# The Künneth theorem for singular homology over a field and with projective homology

For topological spaces `X` and `Y` and coefficient objects `R` and `S`, the homology cross
products `Hₚ(X; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)` with `p + q = n`
(`TopCat.singularHomologyCross`) assemble into the **Künneth map**

`⨁_{p + q = n} Hₚ(X; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)`,

whose source is the degree `n` part of the tensor product of the graded objects `H(X; R)` and
`H(Y; S)`.  It is the algebraic Künneth map `HomologicalComplex.homologyKunneth` of the singular
chain complexes followed by the map induced by the shuffle map, and it is natural in both spaces
and in both coefficient objects.  Since the shuffle map is a chain homotopy equivalence
(Eilenberg–Zilber), the Künneth map is an isomorphism exactly when the algebraic Künneth map of
the singular chain complexes is.

For modules `M` and `N` over a commutative ring `k`, the algebraic Künneth map is an isomorphism
when the cycles of the singular chain complexes `C(X; M)` and `C(Y; N)` split off their terms and
their homology splits off their cycles
(`HomologicalComplex.isIso_homologyKunneth_of_isSplitMono_of_isSplitEpi`).
This gives the **Künneth theorem**: the cross product induces an isomorphism

`⨁_{p + q = n} Hₚ(X; M) ⊗ H_q(Y; N) ≅ Hₙ(X × Y; M ⊗ N)`.

The splitting hypotheses hold in two standard situations.

* For semisimple modules `M` and `N`, the singular chain modules `Cₙ(X; M) = ⨁ M` and
  `Cₙ(Y; N) = ⨁ N` are semisimple, so every submodule splits off.  Over a commutative semisimple
  ring `k`, for instance a field, every module is semisimple, and with `M = N = k`, along the
  unitor `k ⊗ k ≅ k`, this is the classical form
  `⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y; k) ≅ Hₙ(X × Y; k)`.
* When the cycles split off and the homology modules `Hₚ(X; M)` and `H_q(Y; N)` are projective,
  the projection of the cycles onto the homology splits
  (`TopCat.isIso_singularHomologyKunneth_of_projective`).  Over a principal ideal domain `k`
  with projective `M` and `N`, for instance `M = N = k`, the boundaries are submodules of the
  projective chain modules, so the cycles split off
  (`HomologicalComplex.isSplitMono_iCycles_of_isPrincipalIdealRing`, with
  `SSet.projective_chainComplex_X`), and this covers spaces whose homology is free, as for
  products of spheres.

## Main definitions and results

* `TopCat.singularHomologyKunneth`: the Künneth map, characterized on summands by
  `TopCat.ι_singularHomologyKunneth`.
* `TopCat.singularHomologyKunneth_naturality` and
  `TopCat.singularHomologyKunneth_coefficient_naturality`: naturality in the spaces and in the
  coefficients.
* `TopCat.isIso_singularHomologyKunneth_iff`: the Künneth map is an isomorphism exactly when the
  algebraic Künneth map of the singular chain complexes is.
* `TopCat.singularHomologyKunnethIso`: the Künneth isomorphism when the cycles and the homology of
  the singular chain complexes split off, for instance for all coefficient modules over a field.
* `TopCat.isIso_singularHomologyKunneth_of_projective`: the Künneth theorem when the cycles split
  off and the homology is projective.
* `TopCat.singularHomologyKunnethUnitIso`: its form `⨁ Hₚ(X; k) ⊗ H_q(Y; k) ≅ Hₙ(X × Y; k)`
  with coefficients in the ring itself.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.B, the Künneth formula.
* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section General

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryWithHomology C]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCoproducts.{w} C]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft T)]
  [∀ (T : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight T)]

section Kunneth

variable (X Y : TopCat.{w}) (R S : C) (n : ℕ)
  [∀ p, PreservesColimitsOfShape WalkingParallelPair
    (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
  [∀ q, PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]

/-- **The Künneth map** `⨁_{p + q = n} Hₚ(X; R) ⊗ H_q(Y; S) ⟶ Hₙ(X × Y; R ⊗ S)`, whose
restriction to the summand `Hₚ(X; R) ⊗ H_q(Y; S)` is the homology cross product
`TopCat.singularHomologyCross`. -/
def singularHomologyKunneth :
    GradedObject.Monoidal.tensorObj (fun p ↦ ((singularHomologyFunctor C p).obj R).obj X)
        (fun q ↦ ((singularHomologyFunctor C q).obj S).obj Y) n ⟶
      ((singularHomologyFunctor C n).obj (R ⊗ S)).obj (X ⊗ Y) :=
  homologyKunneth ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) n ≫
    homologyMap (shuffle X Y R S) n

/-- The Künneth map is the algebraic Künneth map of the singular chain complexes followed by the
map induced by the shuffle map. -/
lemma singularHomologyKunneth_def :
    singularHomologyKunneth X Y R S n =
      homologyKunneth ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) n ≫
        homologyMap (shuffle X Y R S) n :=
  (rfl)

/-- The Künneth map restricts to the homology cross product on each summand. -/
@[reassoc (attr := simp)]
lemma ι_singularHomologyKunneth (p q : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj (fun p ↦ ((singularHomologyFunctor C p).obj R).obj X)
        (fun q ↦ ((singularHomologyFunctor C q).obj S).obj Y) p q n h ≫
      singularHomologyKunneth X Y R S n = singularHomologyCross X Y R S p q n h :=
  (ι_homologyKunneth_assoc ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) n p q h
    _).trans (singularHomologyCross_def X Y R S p q n h).symm

/-- **The Künneth map under Eilenberg–Zilber**: following the Künneth map by the map induced by
the Alexander–Whitney map gives the algebraic Künneth map of the singular chain complexes. -/
@[simp, reassoc]
lemma singularHomologyKunneth_comp_homologyMap_alexanderWhitney :
    singularHomologyKunneth X Y R S n ≫ homologyMap (alexanderWhitney X Y R S) n =
      homologyKunneth ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S) n := by
  -- The shuffle map followed by the Alexander–Whitney map is homotopic to the identity.
  have h : homologyMap (shuffle X Y R S) n ≫ homologyMap (alexanderWhitney X Y R S) n = 𝟙 _ := by
    rw [← homologyMap_comp, (shuffleAlexanderWhitneyHomotopy X Y R S).homologyMap_eq,
      homologyMap_id]
  -- `Hₙ(X × Y; R ⊗ S)` is by definition the homology of the singular chain complex, so the
  -- Künneth map followed by the Alexander–Whitney map is the algebraic Künneth map.
  exact (Category.assoc _ _ _).trans ((homologyKunneth _ _ n ≫= h).trans (Category.comp_id _))

/-- The Künneth map is an isomorphism exactly when the algebraic Künneth map of the singular
chain complexes is, since the shuffle map is a chain homotopy equivalence. -/
theorem isIso_singularHomologyKunneth_iff :
    IsIso (singularHomologyKunneth X Y R S n) ↔
      IsIso (homologyKunneth ((toSSet.obj X).chainComplex R)
        ((toSSet.obj Y).chainComplex S) n) := by
  have : IsIso (homologyMap (shuffle X Y R S) n) := by
    rw [← eilenbergZilberHomotopyEquiv_inv]
    exact ((eilenbergZilberHomotopyEquiv X Y R S).symm.toHomologyIso n).isIso_hom
  -- `Hₙ(X × Y; R ⊗ S)` is by definition the homology of the singular chain complex, so the
  -- Künneth map is the algebraic one followed by this isomorphism.
  exact isIso_comp_right_iff (homologyKunneth _ _ n) (homologyMap (shuffle X Y R S) n)

end Kunneth

section Naturality

/-- **Naturality of the Künneth map** in both spaces. -/
@[reassoc]
lemma singularHomologyKunneth_naturality {X Y X' Y' : TopCat.{w}} (f : X ⟶ X') (g : Y ⟶ Y')
    (R S : C) (n : ℕ)
    [∀ p, PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [∀ p, PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X').chainComplex R).homology p))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).cycles q))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y').chainComplex S).X ((ComplexShape.down ℕ).prev q)))] :
    GradedObject.Monoidal.tensorHom (fun p ↦ ((singularHomologyFunctor C p).obj R).map f)
          (fun q ↦ ((singularHomologyFunctor C q).obj S).map g) n ≫
        singularHomologyKunneth X' Y' R S n =
      singularHomologyKunneth X Y R S n ≫
        ((singularHomologyFunctor C n).obj (R ⊗ S)).map (f ⊗ₘ g) := by
  ext p q h
  simp [singularHomologyCross_naturality]

/-- **Naturality of the Künneth map** in both coefficient objects. -/
@[reassoc]
lemma singularHomologyKunneth_coefficient_naturality (X Y : TopCat.{w}) {R S R' S' : C}
    (φ : R ⟶ R') (ψ : S ⟶ S') (n : ℕ)
    [∀ p, PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R).homology p))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).cycles q))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S).X ((ComplexShape.down ℕ).prev q)))]
    [∀ p, PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((toSSet.obj X).chainComplex R').homology p))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S').cycles q))]
    [∀ q, PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((toSSet.obj Y).chainComplex S').X ((ComplexShape.down ℕ).prev q)))] :
    GradedObject.Monoidal.tensorHom (fun p ↦ ((singularHomologyFunctor C p).map φ).app X)
          (fun q ↦ ((singularHomologyFunctor C q).map ψ).app Y) n ≫
        singularHomologyKunneth X Y R' S' n =
      singularHomologyKunneth X Y R S n ≫
        ((singularHomologyFunctor C n).map (φ ⊗ₘ ψ)).app (X ⊗ Y) := by
  ext p q h
  simp [singularHomologyCross_coefficient_naturality]

end Naturality

end General

section Split

variable {k : Type w} [CommRing k]

section

variable (X Y : TopCat.{w}) (M N : ModuleCat.{w} k)
  [∀ p, IsSplitMono (((toSSet.obj X).chainComplex M).iCycles p)]
  [∀ p, IsSplitEpi (((toSSet.obj X).chainComplex M).homologyπ p)]
  [∀ q, IsSplitMono (((toSSet.obj Y).chainComplex N).iCycles q)]
  [∀ q, IsSplitEpi (((toSSet.obj Y).chainComplex N).homologyπ q)]

/-- **The Künneth theorem for split singular chains**: if the cycles of the singular chain
complexes `C(X; M)` and `C(Y; N)` split off their terms and their homology splits off their
cycles, the Künneth map `⨁_{p + q = n} Hₚ(X; M) ⊗ H_q(Y; N) ⟶ Hₙ(X × Y; M ⊗ N)` is an
isomorphism.  This holds for semisimple modules `M` and `N` over a commutative ring `k`, for
instance any modules over a field, since the singular chain modules are then semisimple. -/
instance isIso_singularHomologyKunneth (n : ℕ) : IsIso (singularHomologyKunneth X Y M N n) :=
  (isIso_singularHomologyKunneth_iff X Y M N n).mpr inferInstance

/-- **The Künneth isomorphism** `⨁_{p + q = n} Hₚ(X; M) ⊗ H_q(Y; N) ≅ Hₙ(X × Y; M ⊗ N)`, induced
by the homology cross product, when the cycles of the singular chain complexes split off their
terms and their homology splits off their cycles; for instance for semisimple modules `M` and `N`
over a commutative ring, such as any modules over a field. -/
def singularHomologyKunnethIso (n : ℕ) :
    GradedObject.Monoidal.tensorObj (fun p ↦ ((singularHomologyFunctor _ p).obj M).obj X)
        (fun q ↦ ((singularHomologyFunctor _ q).obj N).obj Y) n ≅
      ((singularHomologyFunctor _ n).obj (M ⊗ N)).obj (X ⊗ Y) :=
  asIso (singularHomologyKunneth X Y M N n)

@[simp]
lemma singularHomologyKunnethIso_hom (n : ℕ) :
    (singularHomologyKunnethIso X Y M N n).hom = singularHomologyKunneth X Y M N n :=
  (rfl)

end

/-- **The Künneth theorem with projective homology**: if the cycles of the singular chain
complexes `C(X; M)` and `C(Y; N)` split off their terms and the singular homology modules
`Hₚ(X; M)` and `H_q(Y; N)` are all projective, the Künneth map
`⨁_{p + q = n} Hₚ(X; M) ⊗ H_q(Y; N) ⟶ Hₙ(X × Y; M ⊗ N)` is an isomorphism.  Over a principal
ideal domain, with projective `M` and `N`, the `IsSplitMono` hypotheses on the cycles are found by
instance search (`HomologicalComplex.isSplitMono_iCycles_of_isPrincipalIdealRing`), once
`TauCeti.Algebra.Homology.PrincipalIdealRing` is imported. -/
theorem isIso_singularHomologyKunneth_of_projective (X Y : TopCat.{w}) (M N : ModuleCat.{w} k)
    [∀ p, IsSplitMono (((toSSet.obj X).chainComplex M).iCycles p)]
    [hX : ∀ p, Projective (((singularHomologyFunctor _ p).obj M).obj X)]
    [∀ q, IsSplitMono (((toSSet.obj Y).chainComplex N).iCycles q)]
    [hY : ∀ q, Projective (((singularHomologyFunctor _ q).obj N).obj Y)] (n : ℕ) :
    IsIso (singularHomologyKunneth X Y M N n) :=
  -- `Hₚ(X; M)` is by definition the homology of the singular chain complex `C(X; M)`.
  have (p : ℕ) : Projective (((toSSet.obj X).chainComplex M).homology p) := hX p
  have (q : ℕ) : Projective (((toSSet.obj Y).chainComplex N).homology q) := hY q
  inferInstance

variable [IsSemisimpleRing k]

/-- **The Künneth isomorphism with coefficients in the ring**:
`⨁_{p + q = n} Hₚ(X; k) ⊗ H_q(Y; k) ≅ Hₙ(X × Y; k)` over a commutative semisimple ring `k`, for
instance a field.  It is the Künneth isomorphism for `M = N = k` followed by the map induced by
the unitor `k ⊗ k ≅ k`. -/
def singularHomologyKunnethUnitIso (X Y : TopCat.{w}) (n : ℕ) :
    GradedObject.Monoidal.tensorObj
        (fun p ↦ ((singularHomologyFunctor _ p).obj (𝟙_ (ModuleCat.{w} k))).obj X)
        (fun q ↦ ((singularHomologyFunctor _ q).obj (𝟙_ (ModuleCat.{w} k))).obj Y) n ≅
      ((singularHomologyFunctor _ n).obj (𝟙_ (ModuleCat.{w} k))).obj (X ⊗ Y) :=
  singularHomologyKunnethIso X Y _ _ n ≪≫
    ((singularHomologyFunctor _ n).mapIso (λ_ (𝟙_ (ModuleCat.{w} k)))).app (X ⊗ Y)

/-- On the summand `Hₚ(X; k) ⊗ H_q(Y; k)`, the Künneth isomorphism with coefficients in the ring
is the homology cross product followed by the map induced by the unitor `k ⊗ k ≅ k`. -/
@[reassoc (attr := simp)]
lemma ι_singularHomologyKunnethUnitIso_hom (X Y : TopCat.{w}) (p q n : ℕ) (h : p + q = n) :
    GradedObject.Monoidal.ιTensorObj
        (fun p ↦ ((singularHomologyFunctor _ p).obj (𝟙_ (ModuleCat.{w} k))).obj X)
        (fun q ↦ ((singularHomologyFunctor _ q).obj (𝟙_ (ModuleCat.{w} k))).obj Y) p q n h ≫
      (singularHomologyKunnethUnitIso X Y n).hom =
    singularHomologyCross X Y _ _ p q n h ≫
      ((singularHomologyFunctor _ n).map (λ_ (𝟙_ (ModuleCat.{w} k))).hom).app (X ⊗ Y) := by
  simp [singularHomologyKunnethUnitIso]

end Split

end TopCat
