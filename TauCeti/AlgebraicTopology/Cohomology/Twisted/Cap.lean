/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.Basic
public import TauCeti.Algebra.Homology.Monoidal.Summand
public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Relative
public import TauCeti.AlgebraicTopology.Singular.Twisted.AlexanderWhitney

/-!
# Cap products with local coefficients

Let `L` and `K` be local systems of modules over a commutative ring `R` on a space `X`, and let
`M` be an `R`-module. A twisted cochain of degree `p` with values in `M` is a morphism
`φ : C_p(X; L) ⟶ M`, so it reads a coefficient of `L` at the initial vertex of a simplex. Its cap
product with a chain twisted by `L ⊗ K` is a chain twisted by `M ⊗ K`, the tensor product of the
constant system `M` with `K`: a singular `(p + q)`-simplex `σ` with coefficient `a ⊗ b` goes to its
back `q`-face, with coefficient `φ(a') ⊗ b'`, where `a'` is `a` placed on the front `p`-face of
`σ` and `b'` is `b` transported along the edge of `σ` from vertex `0` to vertex `p`, the initial
vertex of the back face (`TauCeti.LocalCoefficientSystem.ιTwistedChainComplex_capChain`).
This is Hatcher's front-face/back-face formula `σ ⌢ φ = φ(σ|[v₀, …, v_p]) σ|[v_p, …, v_n]` with
the coefficients paired at `v₀` and the result transported to the first vertex of the surviving
back face.

The construction applies the cap product of chains and cochains along a diagonal,
`TauCeti.ChainComplex.capChain`, to the twisted Alexander–Whitney diagonal
`TauCeti.LocalCoefficientSystem.twistedAlexanderWhitneyDiagonal`, with the action
`TauCeti.LocalCoefficientSystem.twistedChainComplexAction` of `M` on the chains twisted by `K`,
which sends `m ⊗ (σ, b)` to `(σ, m ⊗ b)`. So it satisfies the boundary formula
`∂(x ⌢ φ) = (-1)^p (∂x ⌢ φ - x ⌢ δφ)` (`TauCeti.ChainComplex.capChain_comp_d`) and descends to the
cap product of twisted cohomology and twisted homology,

`Hᵖ(X; L, M) ⟶ (Hₙ(X; L ⊗ K) ⟶ H_q(X; M ⊗ K))`,  `p + q = n`,

(`TauCeti.LocalCoefficientSystem.twistedCap`), which is `R`-linear in the cohomology class,
natural in both coefficient systems (`TauCeti.LocalCoefficientSystem.twistedCap_naturality`) and
satisfies the projection formula `f_*(x ⌢ f^*α) = f_*x ⌢ α` for continuous maps
(`TauCeti.LocalCoefficientSystem.twistedCap_space_naturality`). Any pairing of local systems
`M ⊗ K ⟶ K'` or `T ⟶ L ⊗ K` is then applied by a change of coefficients on homology. For instance,
if `o` is a local system with `o ⊗ o` isomorphic to the constant system `R`, such as the
orientation system of a real vector bundle, capping with a class with coefficients in `o` sends
untwisted homology to homology twisted by `o`.

For a pair `(X, A)`, a relative cochain vanishes on the front faces of the simplices of `A`, so the
cap product descends to relative chains: the twisted diagonal read in relative chains in its first
factor gives the relative diagonal `C(X, A; L ⊗ K) ⟶ C(X, A; L) ⊗ C(X; K)`
(`TopPair.twistedAlexanderWhitneyDiagonal`), and with it the relative cap product

`Hᵖ(X, A; L, M) ⟶ (Hₙ(X, A; L ⊗ K) ⟶ H_q(X; M ⊗ K))`

(`TopPair.twistedCap`), which agrees with the absolute one on the image of relative cohomology
(`TopPair.twistedCap_twistedCohomologyπ`). This is the form of the homology Thom map
`x ↦ π_*(x ⌢ u)` of a possibly non-orientable vector bundle `E` with Thom pair `(E, E₀)`, when the
Thom class `u` is a relative class with coefficients in the orientation system of `E`.

## Main definitions and results

* `TauCeti.LocalCoefficientSystem.twistedChainComplexAction`: the action
  `M ⊗ C(X; K) ⟶ C(X; M ⊗ K)`, computed on simplices by
  `TauCeti.LocalCoefficientSystem.whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f`,
  natural in `K` and in the space.
* `TauCeti.LocalCoefficientSystem.ιTwistedChainComplex_capChain`: the cap product of a simplex and
  a twisted cochain.
* `TauCeti.LocalCoefficientSystem.twistedCap`: the cap product on twisted (co)homology, with
  `TauCeti.LocalCoefficientSystem.twistedCap_homologyπ` computing it on classes of cycles and
  cocycles, `TauCeti.LocalCoefficientSystem.twistedCap_naturality` its naturality in the
  coefficient systems and `TauCeti.LocalCoefficientSystem.twistedCap_space_naturality` the
  projection formula.
* `TopPair.twistedAlexanderWhitneyDiagonal` and `TopPair.twistedCap`: the relative diagonal and
  the relative cap product, with `TopPair.twistedCap_homologyπ`,
  `TopPair.twistedCap_twistedCohomologyπ` and `TopPair.twistedCap_naturality`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 3.3 and 3.H.
* A. Dold, *Lectures on Algebraic Topology*, Chapters VII–VIII.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open scoped Simplicial

universe v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type (max v w)} [CommRing R] {X : TopCat.{v}}

section Action

variable (M : ModuleCat.{max v w} R) (K : LocalCoefficientSystem.{max v w, v, max v w} R X)

/-- Tensoring with `M` preserves the coproduct decomposition of twisted chains. -/
private def isColimitTensorLeftTwistedChains (n : SimplexCategoryᵒᵖ) :
    IsColimit ((tensorLeft M).mapCocone (Cofan.mk ((twistedChains K).obj n) (ιTwistedChains K))) :=
  isColimitOfPreserves (tensorLeft M) (isColimitCofanTwistedChains K n)

private lemma tensorLeft_twistedChains_hom_ext {n : SimplexCategoryᵒᵖ} {A : ModuleCat.{max v w} R}
    {f g : M ⊗ (twistedChains K).obj n ⟶ A}
    (h : ∀ σ, (M ◁ ιTwistedChains K σ) ≫ f = (M ◁ ιTwistedChains K σ) ≫ g) : f = g :=
  (isColimitTensorLeftTwistedChains M K n).hom_ext fun ⟨σ⟩ ↦ h σ

/-- The degree-`n` component of the action: `m ⊗ (σ, b) ↦ (σ, m ⊗ b)`. -/
private def twistedChainsActionApp (n : SimplexCategoryᵒᵖ) :
    M ⊗ (twistedChains K).obj n ⟶ (twistedChains ((constantFunctor X).obj M ⊗ K)).obj n :=
  (isColimitTensorLeftTwistedChains M K n).desc
    { pt := _
      ι := Discrete.natTrans fun σ ↦ ιTwistedChains ((constantFunctor X).obj M ⊗ K) σ.as }

@[reassoc]
private lemma whiskerLeft_ιTwistedChains_twistedChainsActionApp (n : SimplexCategoryᵒᵖ)
    (σ : (TopCat.toSSet.obj X).obj n) :
    (M ◁ ιTwistedChains K σ) ≫ twistedChainsActionApp M K n =
      ιTwistedChains ((constantFunctor X).obj M ⊗ K) σ :=
  (isColimitTensorLeftTwistedChains M K n).fac _ ⟨σ⟩

/-- The action of `M` on the simplicial module of chains twisted by `K`, with values in the chains
twisted by `M ⊗ K`. -/
private def twistedChainsAction :
    ((SimplicialObject.whiskering _ _).obj (tensorLeft M)).obj (twistedChains K) ⟶
      twistedChains ((constantFunctor X).obj M ⊗ K) where
  app := twistedChainsActionApp M K
  naturality {m n} α := by
    apply tensorLeft_twistedChains_hom_ext
    intro σ
    change (M ◁ ιTwistedChains K σ) ≫ (M ◁ (twistedChains K).map α) ≫
      twistedChainsActionApp M K n = _
    rw [← whiskerLeft_comp_assoc, ιTwistedChains_map, whiskerLeft_comp_assoc,
      whiskerLeft_ιTwistedChains_twistedChainsActionApp]
    -- the transport of `M ⊗ K` is the identity of `M` tensored with the transport of `K`
    have h : ((constantFunctor X).obj M ⊗ K).map (vertexTransport α σ) =
        M ◁ K.map (vertexTransport α σ) := by
      simp [Monoidal.tensorObj_map]
    exact (congrArg (· ≫ _) h.symm).trans
      ((ιTwistedChains_map _ α σ).symm.trans
        (whiskerLeft_ιTwistedChains_twistedChainsActionApp_assoc M K m σ _).symm)

/-- The inverse alternating-face comparison preserves each simplex inclusion. -/
@[reassoc]
private lemma ιTwistedChains_isoAlternatingFaceMapComplex_inv_f
    (L : LocalCoefficientSystem.{max v w, v, max v w} R X) (q : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋q⦌) :
    ιTwistedChains L σ ≫ (twistedChainComplexIsoAlternatingFaceMapComplex L).inv.f q =
      ιTwistedChainComplex L q σ := by
  rw [← ιTwistedChainComplex_isoAlternatingFaceMapComplex_hom_f, Category.assoc, ← comp_f,
    Iso.hom_inv_id, id_f, Category.comp_id]

/-- **The action of the coefficient module `M` on twisted chains**: the chain map
`M ⊗ C(X; K) ⟶ C(X; M ⊗ K)` sending `m ⊗ (σ, b)` to `(σ, m ⊗ b)`, where `M ⊗ K` is the tensor
product of the constant system `M` with `K`. It is the action along which twisted cochains with
values in `M` cap twisted chains. -/
def twistedChainComplexAction :
    ((tensorLeft M).mapHomologicalComplex _).obj K.twistedChainComplex ⟶
      ((constantFunctor X).obj M ⊗ K).twistedChainComplex :=
  ((tensorLeft M).mapHomologicalComplex _).map
      (twistedChainComplexIsoAlternatingFaceMapComplex K).hom ≫
    (alternatingFaceMapComplexCompMapHomologicalComplexIso (tensorLeft M)).hom.app
      (twistedChains K) ≫
      (alternatingFaceMapComplex _).map (twistedChainsAction M K) ≫
        (twistedChainComplexIsoAlternatingFaceMapComplex _).inv

/-- On the summand of a simplex, the action of `M` sends `m ⊗ b` to the coefficient `m ⊗ b` of the
same simplex. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f (q : ℕ)
    (σ : (TopCat.toSSet.obj X) _⦋q⦌) :
    (M ◁ ιTwistedChainComplex K q σ) ≫ (twistedChainComplexAction M K).f q =
      ιTwistedChainComplex ((constantFunctor X).obj M ⊗ K) q σ := by
  have hf : (twistedChainComplexAction M K).f q =
      (M ◁ (twistedChainComplexIsoAlternatingFaceMapComplex K).hom.f q) ≫
        twistedChainsActionApp M K _ ≫
          (twistedChainComplexIsoAlternatingFaceMapComplex _).inv.f q := by
    simp [twistedChainComplexAction, twistedChainsAction]
  rw [hf, ← whiskerLeft_comp_assoc, ιTwistedChainComplex_isoAlternatingFaceMapComplex_hom_f]
  exact (whiskerLeft_ιTwistedChains_twistedChainsActionApp_assoc M K _ σ _).trans
    (ιTwistedChains_isoAlternatingFaceMapComplex_inv_f _ q σ)

variable {M K} in
/-- Two chain maps out of `M ⊗ C(X; K)` agree in a degree as soon as they agree on every
simplex summand. -/
lemma tensorLeft_twistedChainComplex_hom_ext {q : ℕ} {A : ModuleCat.{max v w} R}
    {f g : M ⊗ K.twistedChainComplex.X q ⟶ A}
    (h : ∀ σ, (M ◁ ιTwistedChainComplex K q σ) ≫ f = (M ◁ ιTwistedChainComplex K q σ) ≫ g) :
    f = g :=
  (isColimitOfPreserves (tensorLeft M) (isColimitTwistedChainComplexXCofan K q)).hom_ext
    fun ⟨σ⟩ ↦ h σ

variable {M K} {K' : LocalCoefficientSystem.{max v w, v, max v w} R X}

/-- The action of `M` commutes with changes of the local coefficient system `K`. -/
@[reassoc]
lemma twistedChainComplexAction_naturality (θ : K ⟶ K') :
    twistedChainComplexAction M K ≫
        twistedChainComplexCoefficientMap ((constantFunctor X).obj M ◁ θ) =
      ((tensorLeft M).mapHomologicalComplex _).map (twistedChainComplexCoefficientMap θ) ≫
        twistedChainComplexAction M K' := by
  ext q : 1
  apply tensorLeft_twistedChainComplex_hom_ext
  intro σ
  have h₁ : (M ◁ ιTwistedChainComplex K q σ) ≫ (twistedChainComplexAction M K ≫
      twistedChainComplexCoefficientMap ((constantFunctor X).obj M ◁ θ)).f q =
        (M ◁ θ.app (initialVertex σ)) ≫
          ιTwistedChainComplex ((constantFunctor X).obj M ⊗ K') q σ := by
    rw [comp_f]
    exact (whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f_assoc M K q σ _).trans
      (ιTwistedChainComplex_twistedChainComplexCoefficientMap_f _ q σ)
  have h₂ : (M ◁ ιTwistedChainComplex K q σ) ≫
      (((tensorLeft M).mapHomologicalComplex _).map (twistedChainComplexCoefficientMap θ) ≫
        twistedChainComplexAction M K').f q =
        (M ◁ θ.app (initialVertex σ)) ≫
          ιTwistedChainComplex ((constantFunctor X).obj M ⊗ K') q σ := by
    rw [comp_f, Functor.mapHomologicalComplex_map_f]
    change (M ◁ ιTwistedChainComplex K q σ) ≫
      (M ◁ (twistedChainComplexCoefficientMap θ).f q) ≫ _ = _
    rw [← whiskerLeft_comp_assoc, ιTwistedChainComplex_twistedChainComplexCoefficientMap_f,
      whiskerLeft_comp_assoc, whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f]
  exact h₁.trans h₂.symm

section Space

variable {Y : TopCat.{v}} (f : X ⟶ Y) (M : ModuleCat.{max v w} R)
  (K : LocalCoefficientSystem.{max v w, v, max v w} R Y)

/-- The identification of the tensor product of the constant system `M` on `X` with the pullback
of `K` along `f : X ⟶ Y` with the pullback of `M ⊗ K`; it is the identity on every fibre. -/
abbrev pullbackConstantTensorIso :
    (constantFunctor X).obj M ⊗ (pullback f.hom).obj K ≅
      (pullback f.hom).obj ((constantFunctor Y).obj M ⊗ K) :=
  whiskerRightIso (pullbackConstantIso f.hom M).symm _ ≪≫
    (pullbackTensorIso f.hom ((constantFunctor Y).obj M) K).symm

/-- The action of `M` commutes with continuous maps: acting on the chains of `X` twisted by the
pullback of `K` and pushing forward along `f` is pushing forward and acting on the chains of `Y`
twisted by `K`. -/
@[reassoc]
lemma twistedChainComplexAction_space_naturality :
    twistedChainComplexAction M ((pullback f.hom).obj K) ≫
        twistedChainComplexCoefficientMap (pullbackConstantTensorIso f M K).hom ≫
          twistedChainComplexMap f ((constantFunctor Y).obj M ⊗ K) =
      ((tensorLeft M).mapHomologicalComplex _).map (twistedChainComplexMap f K) ≫
        twistedChainComplexAction M K := by
  ext q : 1
  apply tensorLeft_twistedChainComplex_hom_ext
  intro σ
  have hξ : (pullbackConstantTensorIso f M K).hom.app (initialVertex σ) = 𝟙 _ := by
    simp [pullbackConstantTensorIso]
  have h₁ : (M ◁ ιTwistedChainComplex ((pullback f.hom).obj K) q σ) ≫
      (twistedChainComplexAction M ((pullback f.hom).obj K) ≫
        twistedChainComplexCoefficientMap (pullbackConstantTensorIso f M K).hom ≫
          twistedChainComplexMap f ((constantFunctor Y).obj M ⊗ K)).f q =
        ιTwistedChainComplex ((constantFunctor Y).obj M ⊗ K) q ((TopCat.toSSet.map f).app _ σ) := by
    rw [comp_f, comp_f]
    refine (whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f_assoc _ _ q σ _).trans ?_
    refine (ιTwistedChainComplex_twistedChainComplexCoefficientMap_f_assoc _ q σ _).trans ?_
    exact (congrArg (· ≫ _) hξ).trans ((Category.id_comp _).trans
      (ιTwistedChainComplex_twistedChainComplexMap_f f _ q σ))
  have h₂ : (M ◁ ιTwistedChainComplex ((pullback f.hom).obj K) q σ) ≫
      (((tensorLeft M).mapHomologicalComplex _).map (twistedChainComplexMap f K) ≫
        twistedChainComplexAction M K).f q =
        ιTwistedChainComplex ((constantFunctor Y).obj M ⊗ K) q ((TopCat.toSSet.map f).app _ σ) := by
    rw [comp_f, Functor.mapHomologicalComplex_map_f]
    change (M ◁ ιTwistedChainComplex ((pullback f.hom).obj K) q σ) ≫
      (M ◁ (twistedChainComplexMap f K).f q) ≫ _ = _
    rw [← whiskerLeft_comp_assoc, ιTwistedChainComplex_twistedChainComplexMap_f]
    exact whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f M K q _
  exact h₁.trans h₂.symm

end Space

end Action

section Cap

variable (L K : LocalCoefficientSystem.{max v w, v, max v w} R X) (M : ModuleCat.{max v w} R)

/-- **The cap product of a simplex and a twisted cochain**: a cochain `φ` of degree `p` caps the
singular `(p + q)`-simplex `σ`, with a coefficient of `L ⊗ K` at its initial vertex, to the back
`q`-face of `σ`. The coefficient of `L` is evaluated by `φ` on the front `p`-face, which has the
same initial vertex, and the coefficient of `K` is transported along the edge from vertex `0` to
vertex `p`, the initial vertex of the back face. -/
lemma ιTwistedChainComplex_capChain (p q n : ℕ) (h : p + q = n)
    (φ : L.twistedChainComplex.X p ⟶ M) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ιTwistedChainComplex (L ⊗ K) n σ ≫
        TauCeti.ChainComplex.capChain R (twistedAlexanderWhitneyDiagonal L K)
          (twistedChainComplexAction M K) p q n h φ =
      ((L.map (vertexTransport (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
          ιTwistedChainComplex L p
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ⊗ₘ
        K.map (vertexTransport (SimplexCategory.subinterval p q (by omega)).op σ)) ≫
        ιTwistedChainComplex ((constantFunctor X).obj M ⊗ K) q
          ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) := by
  subst h
  -- The cochain kills every bidegree except `(p, q)`. State the surviving term for an arbitrary
  -- equal back degree: rewriting `p + q - p` directly gives an ill-typed motive, because both the
  -- subinterval bound and the tensor-summand equality depend on that degree.
  have key : ∀ (j : ℕ) (hj : j = q) (hj' : p + j ≤ p + q) (hj'' : p + j = p + q),
      ((L.map (vertexTransport (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
          ιTwistedChainComplex L p
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ)) ⊗ₘ
        (K.map (vertexTransport (SimplexCategory.subinterval p j hj').op σ) ≫
          ιTwistedChainComplex K j
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p j hj').op σ))) ≫
          ιTensorObj L.twistedChainComplex K.twistedChainComplex p j (p + q) hj'' ≫
            TauCeti.ChainComplex.tensorCochain ((twistedChainComplexAction M K).f q) φ
              (𝟙 (K.twistedChainComplex.X q)) (p + q) =
        ((L.map (vertexTransport (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
            ιTwistedChainComplex L p
              ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫
                φ) ⊗ₘ
          K.map (vertexTransport (SimplexCategory.subinterval p q (by omega)).op σ)) ≫
          ιTwistedChainComplex ((constantFunctor X).obj M ⊗ K) q
            ((TopCat.toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) := by
    rintro _ rfl _ _
    rw [TauCeti.ChainComplex.ιTensorObj_tensorCochain, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.assoc, tensorHom_def_assoc, whiskerLeft_comp_assoc,
      ← tensorHom_def_assoc]
    exact congrArg (_ ≫ ·)
      (whiskerLeft_ιTwistedChainComplex_twistedChainComplexAction_f M K _ _)
  rw [TauCeti.ChainComplex.capChain_apply,
    ιTwistedChainComplex_twistedAlexanderWhitneyDiagonal_f_assoc]
  dsimp only [Monoidal.tensorObj_obj]
  rw [Preadditive.sum_comp, Finset.sum_eq_single ⟨p, by omega⟩]
  · simp only [Category.assoc]
    exact key (p + q - p) (by omega) _ _
  · rintro i - hi
    rw [Category.assoc, TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne_left _ _ _ _
      (fun h ↦ hi (Fin.ext h)), comp_zero]
  · simp

/-- **The cap product of twisted cohomology and twisted homology**,
`Hᵖ(X; L, M) ⟶ (Hₙ(X; L ⊗ K) ⟶ H_q(X; M ⊗ K))` for `p + q = n`: the cap product along the twisted
Alexander–Whitney diagonal and the action of `M` on the chains twisted by `K`. It is `R`-linear in
the cohomology class. -/
def twistedCap (p q n : ℕ) (h : p + q = n) :
    L.twistedCohomology R M p →ₗ[R]
      ((L ⊗ K).twistedHomology n ⟶ ((constantFunctor X).obj M ⊗ K).twistedHomology q) :=
  TauCeti.ChainComplex.cap R (twistedAlexanderWhitneyDiagonal L K) (twistedChainComplexAction M K)
    p q n h

/-- The cap product of the classes of a twisted cycle and a twisted cocycle is the class of their
cap product. -/
@[reassoc (attr := simp)]
lemma twistedCap_homologyπ (p q n : ℕ) (h : p + q = n)
    (φ : (L.twistedCochainComplex R M).cycles p) :
    (L ⊗ K).twistedChainComplex.homologyπ n ≫
        twistedCap L K M p q n h ((L.twistedCochainComplex R M).homologyπ p φ) =
      TauCeti.ChainComplex.capCycles R (twistedAlexanderWhitneyDiagonal L K)
          (twistedChainComplexAction M K) p q n h φ ≫
        ((constantFunctor X).obj M ⊗ K).twistedChainComplex.homologyπ q :=
  TauCeti.ChainComplex.cap_homologyπ _ _ _ _ _ _ _

variable {L K M} {L' K' : LocalCoefficientSystem.{max v w, v, max v w} R X}

/-- **Naturality of the cap product in the coefficient systems**: for morphisms `η : L ⟶ L'` and
`θ : K ⟶ K'`, capping with the pulled-back class `η^* α` and changing coefficients along `θ` is
changing coefficients along `η ⊗ θ` and capping with `α`. -/
lemma twistedCap_naturality (η : L ⟶ L') (θ : K ⟶ K') (p q n : ℕ) (h : p + q = n)
    (α : L'.twistedCohomology R M p) :
    twistedCap L K M p q n h (twistedCohomologyCoefficientMap R M η p α) ≫
        twistedHomologyCoefficientMap ((constantFunctor X).obj M ◁ θ) q =
      twistedHomologyCoefficientMap (η ⊗ₘ θ) n ≫ twistedCap L' K' M p q n h α :=
  TauCeti.ChainComplex.cap_naturality _ _ _ _ _ _ _ _
    (twistedAlexanderWhitneyDiagonal_naturality η θ) (twistedChainComplexAction_naturality θ)
    p q n h α

section Space

variable {Y : TopCat.{v}} (f : X ⟶ Y) (L K : LocalCoefficientSystem.{max v w, v, max v w} R Y)
  (M : ModuleCat.{max v w} R)

/-- **The projection formula for the twisted cap product**: for `f : X ⟶ Y`, a class `α` of
`Hᵖ(Y; L, M)` and a class `x` of `Hₙ(X; f^*L ⊗ f^*K)`, `f_*(x ⌢ f^*α) = f_*x ⌢ α`, where the
pushforwards are taken after the canonical identifications `f^*L ⊗ f^*K ≅ f^*(L ⊗ K)` and
`M ⊗ f^*K ≅ f^*(M ⊗ K)`. -/
lemma twistedCap_space_naturality (p q n : ℕ) (h : p + q = n) (α : L.twistedCohomology R M p) :
    twistedCap ((pullback f.hom).obj L) ((pullback f.hom).obj K) M p q n h
        (twistedCohomologyMap R M f L p α) ≫
        twistedHomologyCoefficientMap (pullbackConstantTensorIso f M K).hom q ≫
          twistedHomologyMap f ((constantFunctor Y).obj M ⊗ K) q =
      twistedHomologyCoefficientMap (pullbackTensorIso f.hom L K).inv n ≫
        twistedHomologyMap f (L ⊗ K) n ≫ twistedCap L K M p q n h α := by
  have hD : (twistedChainComplexCoefficientMap (pullbackTensorIso f.hom L K).inv ≫
      twistedChainComplexMap f (L ⊗ K)) ≫ twistedAlexanderWhitneyDiagonal L K =
        twistedAlexanderWhitneyDiagonal ((pullback f.hom).obj L) ((pullback f.hom).obj K) ≫
          (twistedChainComplexMap f L ⊗ₘ twistedChainComplexMap f K) := by
    rw [Category.assoc, twistedAlexanderWhitneyDiagonal_space_naturality,
      ← twistedChainComplexCoefficientMap_comp_assoc, Iso.inv_hom_id,
      twistedChainComplexCoefficientMap_id, Category.id_comp]
  have hcap := TauCeti.ChainComplex.cap_naturality (k := R) (twistedAlexanderWhitneyDiagonal L K)
    (twistedChainComplexAction M K)
    (twistedAlexanderWhitneyDiagonal ((pullback f.hom).obj L) ((pullback f.hom).obj K))
    (twistedChainComplexAction M ((pullback f.hom).obj K))
    (twistedChainComplexCoefficientMap (pullbackTensorIso f.hom L K).inv ≫
      twistedChainComplexMap f (L ⊗ K))
    (twistedChainComplexMap f L) (twistedChainComplexMap f K)
    (twistedChainComplexCoefficientMap (pullbackConstantTensorIso f M K).hom ≫
      twistedChainComplexMap f ((constantFunctor Y).obj M ⊗ K)) hD
    (twistedChainComplexAction_space_naturality f M K) p q n h α
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    Category.assoc] at hcap
  exact hcap

end Space

end Cap

end TauCeti.LocalCoefficientSystem

namespace TopPair

open TauCeti TauCeti.LocalCoefficientSystem

variable {R : Type (max v w)} [CommRing R] (P : TopPair.{v})
  (L K : LocalCoefficientSystem.{max v w, v, max v w} R P.fst) (M : ModuleCat.{max v w} R)

/-- The twisted Alexander–Whitney diagonal, followed by the quotient onto relative chains in its
first factor, vanishes on the chains of the subspace: the front face of a simplex of the subspace
lies in the subspace. -/
private lemma twistedChainComplexMap_twistedAlexanderWhitneyDiagonal_twistedChainComplexπ :
    LocalCoefficientSystem.twistedChainComplexMap P.map (L ⊗ K) ≫
      L.twistedAlexanderWhitneyDiagonal K ≫
        (P.twistedChainComplexπ L ⊗ₘ 𝟙 K.twistedChainComplex) = 0 := by
  rw [twistedAlexanderWhitneyDiagonal_space_naturality_assoc, tensorHom_comp_tensorHom,
    P.twistedChainComplexMap_comp_twistedChainComplexπ L]
  exact (congrArg (fun t ↦ _ ≫ _ ≫ t) (HomologicalComplex.zero_tensorHom _)).trans
    (by simp only [comp_zero])

/-- **The relative twisted Alexander–Whitney diagonal** `C(X, A; L ⊗ K) ⟶ C(X, A; L) ⊗ C(X; K)` of
a pair `(X, A)`: the twisted diagonal, read in relative chains in its first factor, which descends
to the relative chains twisted by `L ⊗ K`. -/
def twistedAlexanderWhitneyDiagonal :
    P.twistedChainComplex (L ⊗ K) ⟶ P.twistedChainComplex L ⊗ K.twistedChainComplex :=
  P.twistedChainComplexDesc (L ⊗ K)
    (L.twistedAlexanderWhitneyDiagonal K ≫ (P.twistedChainComplexπ L ⊗ₘ 𝟙 K.twistedChainComplex))
    (twistedChainComplexMap_twistedAlexanderWhitneyDiagonal_twistedChainComplexπ P L K)

/-- The relative diagonal is the absolute diagonal read in relative chains. -/
@[reassoc (attr := simp)]
lemma twistedChainComplexπ_twistedAlexanderWhitneyDiagonal :
    P.twistedChainComplexπ (L ⊗ K) ≫ P.twistedAlexanderWhitneyDiagonal L K =
      L.twistedAlexanderWhitneyDiagonal K ≫
        (P.twistedChainComplexπ L ⊗ₘ 𝟙 K.twistedChainComplex) :=
  P.twistedChainComplexπ_comp_twistedChainComplexDesc _ _ _

/-- **The relative cap product with local coefficients**,
`Hᵖ(X, A; L, M) ⟶ (Hₙ(X, A; L ⊗ K) ⟶ H_q(X; M ⊗ K))` for `p + q = n`: a relative cochain vanishes
on the front faces of the simplices of `A`, so capping with it descends to relative chains. It is
`R`-linear in the cohomology class. -/
def twistedCap (p q n : ℕ) (h : p + q = n) :
    P.twistedCohomology L R M p →ₗ[R]
      (P.twistedHomology (L ⊗ K) n ⟶ ((constantFunctor P.fst).obj M ⊗ K).twistedHomology q) :=
  TauCeti.ChainComplex.cap R (P.twistedAlexanderWhitneyDiagonal L K)
    (twistedChainComplexAction M K) p q n h

/-- The relative cap product of the classes of a relative twisted cycle and a relative twisted
cocycle is the class of their cap product. -/
@[reassoc (attr := simp)]
lemma twistedCap_homologyπ (p q n : ℕ) (h : p + q = n)
    (φ : (P.twistedCochainComplex L R M).cycles p) :
    (P.twistedChainComplex (L ⊗ K)).homologyπ n ≫
        P.twistedCap L K M p q n h ((P.twistedCochainComplex L R M).homologyπ p φ) =
      TauCeti.ChainComplex.capCycles R (P.twistedAlexanderWhitneyDiagonal L K)
          (twistedChainComplexAction M K) p q n h φ ≫
        ((constantFunctor P.fst).obj M ⊗ K).twistedChainComplex.homologyπ q :=
  TauCeti.ChainComplex.cap_homologyπ _ _ _ _ _ _ _

/-- **The relative and absolute cap products agree**: capping with the image in `Hᵖ(X; L, M)` of a
relative class `α` is passing to relative homology and capping with `α`. -/
lemma twistedCap_twistedCohomologyπ (p q n : ℕ) (h : p + q = n)
    (α : P.twistedCohomology L R M p) :
    LocalCoefficientSystem.twistedCap L K M p q n h (P.twistedCohomologyπ L R M p α) =
      P.twistedHomologyπ (L ⊗ K) n ≫ P.twistedCap L K M p q n h α := by
  have hcap := TauCeti.ChainComplex.cap_naturality (k := R) (P.twistedAlexanderWhitneyDiagonal L K)
    (twistedChainComplexAction M K) (L.twistedAlexanderWhitneyDiagonal K)
    (twistedChainComplexAction M K) (P.twistedChainComplexπ (L ⊗ K)) (P.twistedChainComplexπ L)
    (𝟙 _) (𝟙 _) (P.twistedChainComplexπ_twistedAlexanderWhitneyDiagonal L K) (by simp) p q n h α
  rwa [HomologicalComplex.homologyMap_id, Category.comp_id] at hcap

variable {P L K M} {L' K' : LocalCoefficientSystem.{max v w, v, max v w} R P.fst}

/-- The relative diagonal commutes with changes of both local coefficient systems. -/
@[reassoc]
lemma twistedAlexanderWhitneyDiagonal_naturality (η : L ⟶ L') (θ : K ⟶ K') :
    P.twistedChainComplexCoefficientMap (η ⊗ₘ θ) ≫ P.twistedAlexanderWhitneyDiagonal L' K' =
      P.twistedAlexanderWhitneyDiagonal L K ≫
        (P.twistedChainComplexCoefficientMap η ⊗ₘ
          LocalCoefficientSystem.twistedChainComplexCoefficientMap θ) := by
  ext : 1
  rw [twistedChainComplexπ_comp_twistedChainComplexCoefficientMap_assoc,
    twistedChainComplexπ_twistedAlexanderWhitneyDiagonal,
    twistedChainComplexπ_twistedAlexanderWhitneyDiagonal_assoc,
    LocalCoefficientSystem.twistedAlexanderWhitneyDiagonal_naturality_assoc,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
    twistedChainComplexπ_comp_twistedChainComplexCoefficientMap, Category.id_comp,
    Category.comp_id]

/-- **Naturality of the relative cap product in the coefficient systems**: for morphisms
`η : L ⟶ L'` and `θ : K ⟶ K'`, capping with the pulled-back relative class `η^* α` and changing
coefficients along `θ` is changing relative coefficients along `η ⊗ θ` and capping with `α`. -/
lemma twistedCap_naturality (η : L ⟶ L') (θ : K ⟶ K') (p q n : ℕ) (h : p + q = n)
    (α : P.twistedCohomology L' R M p) :
    P.twistedCap L K M p q n h (P.twistedCohomologyCoefficientMap R M η p α) ≫
        LocalCoefficientSystem.twistedHomologyCoefficientMap ((constantFunctor P.fst).obj M ◁ θ) q =
      P.twistedHomologyCoefficientMap (η ⊗ₘ θ) n ≫ P.twistedCap L' K' M p q n h α :=
  TauCeti.ChainComplex.cap_naturality _ _ _ _ _ _ _ _
    (TopPair.twistedAlexanderWhitneyDiagonal_naturality η θ)
    (twistedChainComplexAction_naturality θ) p q n h α

end TopPair
