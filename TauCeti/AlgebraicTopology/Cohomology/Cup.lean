/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cup
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney

/-!
# The cup product in singular cohomology

Let `C` be a `k`-linear abelian monoidal category with coproducts.  For a space `X`, the
Alexander–Whitney diagonal `TopCat.alexanderWhitneyDiagonal u X` is the chain map
`C(X; T) ⟶ C(X; R) ⊗ C(X; S)` obtained from a coefficient morphism `u : T ⟶ R ⊗ S`, the map
induced by the diagonal `X ⟶ X × X`, and the Alexander–Whitney map
`TopCat.alexanderWhitney X X R S`.  It sends a singular simplex `σ` to
`∑_{p + q = n} σ|[0, …, p] ⊗ σ|[p, …, n]`, and is natural in `X`.

The cup product of singular cochains is the cup product of cochains along this diagonal
(`TauCeti.ChainComplex.cupCochain`), for a pairing `μ : M ⊗ N ⟶ P` of coefficient objects: a
cochain `φ` of degree `p` with values in `M` and a cochain `ψ` of degree `q` with values in `N`
give the cochain of degree `n = p + q` with values in `P` whose value on a singular simplex `σ` is
`μ (φ (σ|[0, …, p]) ⊗ ψ (σ|[p, …, n]))`, precomposed with `u`
(`TopCat.ιChainComplex_cupCochain_alexanderWhitneyDiagonal`).  It satisfies the Leibniz rule
`TauCeti.ChainComplex.d_comp_cupCochain`, and so descends to the `k`-bilinear cup product
`TopCat.singularCup` on singular cohomology, which is natural in `X`.

For the cohomology of `X` with coefficients in modules over a commutative ring `k`, take
`C := ModuleCat k`, `R = S = T = 𝟙_ (ModuleCat k)` (the module `k`) and `u = (λ_ _).inv`; then
`φ ⌣ ψ` evaluates `σ` to `μ (φ (σ|[0, …, p]) ⊗ ψ (σ|[p, …, n]))`, the cup product of Hatcher,
Section 3.2.

## Main definitions and results

* `TopCat.alexanderWhitneyDiagonal`: the Alexander–Whitney diagonal of a space, with
  `TopCat.alexanderWhitneyDiagonal_naturality` its naturality.
* `TopCat.ιChainComplex_cupCochain_alexanderWhitneyDiagonal`: the cup product of singular
  cochains on a singular simplex.
* `TopCat.singularCup`: the cup product on singular cohomology, with `TopCat.singularCup_homologyπ`
  computing it on classes of cocycles and `TopCat.singularCup_naturality` its naturality.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Simplicial
  HomologicalComplex

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  {R S T : C} (u : T ⟶ R ⊗ S)

/-- **The Alexander–Whitney diagonal** `C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of a space `X`: the
coefficient morphism `u : T ⟶ R ⊗ S`, followed by the chain map induced by the diagonal
`X ⟶ X × X` and by the Alexander–Whitney map `TopCat.alexanderWhitney X X R S`. -/
def alexanderWhitneyDiagonal (X : TopCat.{w}) :
    (toSSet.obj X).chainComplex T ⟶ (toSSet.obj X).chainComplex R ⊗ (toSSet.obj X).chainComplex S :=
  ((SSet.chainComplexFunctor C).map u).app _ ≫
    SSet.chainComplexMap (toSSet.map (lift (𝟙 X) (𝟙 X))) (R ⊗ S) ≫ alexanderWhitney X X R S

/-- The Alexander–Whitney diagonal sends a singular `n`-simplex `σ` to
`∑_{p + q = n} σ|[0, …, p] ⊗ σ|[p, …, n]`, after the coefficient morphism `u`. -/
@[reassoc (attr := simp)]
lemma ιChainComplex_alexanderWhitneyDiagonal_f {X : TopCat.{w}} {n : ℕ}
    (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫ (alexanderWhitneyDiagonal u X).f n =
      u ≫ ∑ p : Fin (n + 1),
        ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ⊗ₘ
          (toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval p (n - p) (by omega)).op σ)) ≫
          ιTensorObj _ _ (p : ℕ) (n - p) n (by omega) := by
  have hfst : (toSSet.map (fst X X)).app _ ((toSSet.map (lift (𝟙 X) (𝟙 X))).app _ σ) = σ := by
    rw [← NatTrans.comp_app_apply, ← CategoryTheory.Functor.map_comp, lift_fst,
      CategoryTheory.Functor.map_id]
    rfl
  have hsnd : (toSSet.map (snd X X)).app _ ((toSSet.map (lift (𝟙 X) (𝟙 X))).app _ σ) = σ := by
    rw [← NatTrans.comp_app_apply, ← CategoryTheory.Functor.map_comp, lift_snd,
      CategoryTheory.Functor.map_id]
    rfl
  simp only [alexanderWhitneyDiagonal, comp_f,
    TauCeti.SSet.ιChainComplex_chainComplexFunctor_map_app_f_assoc, SSet.ι_chainComplexMap_f_assoc,
    ιChainComplex_alexanderWhitney_f, hfst, hsnd]
  -- the simplex of `Sing X ⊗ Sing X` is the pair `(σ, σ)`
  exact congrArg (u ≫ ·) (SSet.ιChainComplex_alexanderWhitney_f (toSSet.obj X) (toSSet.obj X) R S
    (n := n) (σ, σ))

/-- The Alexander–Whitney diagonal is natural in the space. -/
@[reassoc]
lemma alexanderWhitneyDiagonal_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) :
    SSet.chainComplexMap (toSSet.map f) T ≫ alexanderWhitneyDiagonal u Y =
      alexanderWhitneyDiagonal u X ≫
        (SSet.chainComplexMap (toSSet.map f) R ⊗ₘ SSet.chainComplexMap (toSSet.map f) S) := by
  have hdiag : f ≫ lift (𝟙 Y) (𝟙 Y) = lift (𝟙 X) (𝟙 X) ≫ (f ⊗ₘ f) := by
    ext <;> simp
  rw [alexanderWhitneyDiagonal, alexanderWhitneyDiagonal, Category.assoc, Category.assoc,
    ((SSet.chainComplexFunctor C).map u).naturality_assoc,
    ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp, hdiag, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp_assoc, alexanderWhitney_naturality]

variable {M N P : C} (μ : M ⊗ N ⟶ P)

/-- **The cup product of singular cochains on a simplex**: for cochains `φ` of degree `p` and `ψ`
of degree `q`, the value of `φ ⌣ ψ` on a singular `(p + q)`-simplex `σ` is `φ` of the front
`p`-face of `σ` tensored with `ψ` of its back `q`-face, followed by `μ`, after the coefficient
morphism `u`. -/
lemma ιChainComplex_cupCochain_alexanderWhitneyDiagonal (X : TopCat.{w}) (p q n : ℕ)
    (h : p + q = n) (φ : ((toSSet.obj X).chainComplex R).X p ⟶ M)
    (ψ : ((toSSet.obj X).chainComplex S).X q ⟶ N) (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫
        TauCeti.ChainComplex.cupCochain k (alexanderWhitneyDiagonal u X) μ p q n h φ ψ =
      u ≫ (((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ⊗ₘ
          ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ ψ)) ≫ μ := by
  subst h
  -- the summand of bidegree `(p, j)` for `j = q`, stated for any such `j`
  have key : ∀ (j : ℕ) (hj : j = q) (hj' : p + j ≤ p + q) (hj'' : p + j = p + q),
      ((toSSet.obj X).ιChainComplex
          ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ⊗ₘ
        (toSSet.obj X).ιChainComplex (R := S)
          ((toSSet.obj X).map (SimplexCategory.subinterval p j hj').op σ)) ≫
        ιTensorObj _ _ p j (p + q) hj'' ≫ TauCeti.ChainComplex.tensorCochain μ φ ψ (p + q) =
      (((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ⊗ₘ
          ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ ψ)) ≫ μ := by
    rintro _ rfl _ _
    rw [TauCeti.ChainComplex.ιTensorObj_tensorCochain, tensorHom_comp_tensorHom_assoc]
  rw [TauCeti.ChainComplex.cupCochain_apply, ιChainComplex_alexanderWhitneyDiagonal_f_assoc,
    Preadditive.sum_comp, Finset.sum_eq_single ⟨p, by omega⟩]
  · simp only [Category.assoc]
    exact congrArg (u ≫ ·) (key (p + q - p) (by omega) _ _)
  · rintro i - hi
    rw [Category.assoc, TauCeti.ChainComplex.ιTensorObj_tensorCochain_of_ne _ _ _ _
      (fun h ↦ hi (Fin.ext h)), comp_zero]
  · simp

variable (k) in
/-- **The cup product on singular cohomology**,
`Hᵖ(X; R, M) × H^q(X; S, N) ⟶ Hⁿ(X; T, P)` for `p + q = n`: the cup product of cohomology classes
along the Alexander–Whitney diagonal `TopCat.alexanderWhitneyDiagonal u X` and the pairing
`μ : M ⊗ N ⟶ P`, `k`-bilinear and natural in `X` (`TopCat.singularCup_naturality`). -/
def singularCup (X : TopCat.{w}) (p q n : ℕ) (h : p + q = n) :
    X.singularCohomology R k M p →ₗ[k] X.singularCohomology S k N q →ₗ[k]
      X.singularCohomology T k P n :=
  TauCeti.ChainComplex.cup k (alexanderWhitneyDiagonal u X) μ p q n h

/-- The cup product of the classes of two singular cocycles is the class of their cup product. -/
@[simp]
lemma singularCup_homologyπ (X : TopCat.{w}) (p q n : ℕ) (h : p + q = n)
    (a : (X.singularCochainComplex R k M).cycles p)
    (b : (X.singularCochainComplex S k N).cycles q) :
    singularCup k u μ X p q n h ((X.singularCochainComplex R k M).homologyπ p a)
        ((X.singularCochainComplex S k N).homologyπ q b) =
      (X.singularCochainComplex T k P).homologyπ n
        (TauCeti.ChainComplex.cupCycles k (alexanderWhitneyDiagonal u X) μ p q n h a b) :=
  TauCeti.ChainComplex.cup_homologyπ _ _ _ _ _ _ _ _

/-- **Naturality of the cup product**: for a continuous map `f : X ⟶ Y`, pulling back two
cohomology classes of `Y` along `f` and cupping them is pulling back their cup product. -/
lemma singularCup_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (p q n : ℕ) (h : p + q = n)
    (α : Y.singularCohomology R k M p) (β : Y.singularCohomology S k N q) :
    singularCup k u μ X p q n h (TopCat.singularCohomologyMap f p α)
        (TopCat.singularCohomologyMap f q β) =
      TopCat.singularCohomologyMap f n (singularCup k u μ Y p q n h α β) :=
  TauCeti.ChainComplex.cup_naturality _ μ _ _ _ _ (alexanderWhitneyDiagonal_naturality u f)
    p q n h α β

end TopCat
