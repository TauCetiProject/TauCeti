/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney.Basic

/-!
# The cap product of singular homology and cohomology

Let `C` be a `k`-linear monoidal category with coproducts.  For a space `X`, the cap product of
singular chains and cochains is the cap product of chains and cochains
`TauCeti.ChainComplex.capChain` along the Alexander–Whitney diagonal
`X.alexanderWhitneyDiagonal u : C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of a coefficient morphism
`u : T ⟶ R ⊗ S`, and along the chain map `M ⊗ C(X; S) ⟶ C(X; P)` induced by a coefficient pairing
`μ : M ⊗ S ⟶ P` (`SSet.chainComplexPairing`, which needs `M ⊗ -` to preserve coproducts).  A
cochain `φ` of degree `p` with values in `M` caps a singular simplex `σ` of degree `n = p + q` to
the singular `q`-simplex given by the back `q`-face of `σ`, with coefficient `φ` of the front
`p`-face of `σ` paired with `S` through `μ`, after the coefficient morphism `u`
(`TopCat.ιChainComplex_capChain_alexanderWhitneyDiagonal`).  It satisfies the boundary formula
`TauCeti.ChainComplex.capChain_comp_d`, `∂(σ ⌢ φ) = (-1)^p (∂σ ⌢ φ - σ ⌢ δφ)`, and so, when `C` is
moreover abelian, descends to the cap product `TopCat.singularCap` of singular cohomology with
singular homology, which is `k`-linear in the cohomology class and natural in `X` (the projection
formula `f_*(x ⌢ f^*α) = f_*x ⌢ α`, `TopCat.singularCap_naturality`).

For coefficients in modules over a commutative ring `k`, take `C := ModuleCat k`,
`R = S = T = 𝟙_ (ModuleCat k)` (the module `k`), `u = (λ_ _).inv` and `μ = (ρ_ M).hom`, the
action `M ⊗ k ⟶ M`; then `σ ⌢ φ = φ(σ|[0, …, p]) σ|[p, …, n]`, the cap product of Hatcher,
Section 3.3.

## Main definitions and results

* `TopCat.ιChainComplex_capChain_alexanderWhitneyDiagonal`: the cap product of a singular simplex
  and a singular cochain.
* `TopCat.singularCap`: the cap product `Hᵖ(X; R, M) ⟶ (Hₙ(X; T) ⟶ H_q(X; P))`, with
  `TopCat.singularCap_def` exhibiting it as a cap product of chains and cochains,
  `TopCat.singularCap_homologyπ` computing it on classes of cycles and cocycles and
  `TopCat.singularCap_naturality` its naturality.
* `TopCat.singularCapLinearMap`: capping with a fixed class `μ ∈ Hₙ(X; k)`, as a `k`-linear map
  `Hᵖ(X; k) → H_q(X; k)`, with `TopCat.singularCapLinearMap_naturality` its naturality.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Simplicial
  HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {k : Type*} [Semiring k] [Linear k C] [MonoidalLinear k C]
  {R S T M P : C} [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- **The cap product of a singular simplex and a singular cochain**: for a cochain `φ` of degree
`p`, the cap product of a singular `(p + q)`-simplex `σ` with `φ` is the back `q`-face of `σ`, with
coefficient `φ` of the front `p`-face of `σ` paired with `S` through `μ`, after the coefficient
morphism `u`. -/
lemma ιChainComplex_capChain_alexanderWhitneyDiagonal (X : TopCat.{w}) (u : T ⟶ R ⊗ S)
    (μ : M ⊗ S ⟶ P) (p q n : ℕ) (h : p + q = n) (φ : ((toSSet.obj X).chainComplex R).X p ⟶ M)
    (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫
        TauCeti.ChainComplex.capChain k (X.alexanderWhitneyDiagonal u)
          ((toSSet.obj X).chainComplexPairing μ) p q n h φ =
      u ≫ (((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ▷ S) ≫
          μ ≫ (toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) := by
  rw [TauCeti.ChainComplex.capChain_apply,
    ιChainComplex_alexanderWhitneyDiagonal_f_tensorCochain X u _ p q n h, Category.comp_id,
    tensorHom_def_assoc, SSet.whiskerLeft_ιChainComplex_chainComplexPairing_f]

end Chain

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M P : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- **The cap product of singular cohomology and singular homology**,
`Hᵖ(X; R, M) ⟶ (Hₙ(X; T) ⟶ H_q(X; P))` for `p + q = n`: the cap product of homology and
cohomology classes along the Alexander–Whitney diagonal `X.alexanderWhitneyDiagonal u` and the
chain map induced by the pairing `μ : M ⊗ S ⟶ P`, `k`-linear in the cohomology class and natural in
`X` (`TopCat.singularCap_naturality`). -/
def singularCap (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ P) (p q n : ℕ) (h : p + q = n) :
    X.singularCohomology R k M p →ₗ[k]
      (((singularHomologyFunctor C n).obj T).obj X ⟶ ((singularHomologyFunctor C q).obj P).obj X) :=
  TauCeti.ChainComplex.cap k (X.alexanderWhitneyDiagonal u) ((toSSet.obj X).chainComplexPairing μ)
    p q n h

/-- The singular cap product is the cap product of chains and cochains along the
Alexander–Whitney diagonal and the chain map induced by the coefficient pairing. -/
lemma singularCap_def (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ P) (p q n : ℕ) (h : p + q = n) :
    X.singularCap k u μ p q n h =
      TauCeti.ChainComplex.cap k (X.alexanderWhitneyDiagonal u)
        ((toSSet.obj X).chainComplexPairing μ) p q n h :=
  (rfl)

/-- The cap product of the class of a singular cycle with the class of a singular cocycle is the
class of their cap product. -/
@[simp, reassoc]
lemma singularCap_homologyπ (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ P) (p q n : ℕ) (h : p + q = n)
    (φ : (X.singularCochainComplex R k M).cycles p) :
    ((toSSet.obj X).chainComplex T).homologyπ n ≫
        X.singularCap k u μ p q n h ((X.singularCochainComplex R k M).homologyπ p φ) =
      TauCeti.ChainComplex.capCycles k (X.alexanderWhitneyDiagonal u)
          ((toSSet.obj X).chainComplexPairing μ) p q n h φ ≫
        ((toSSet.obj X).chainComplex P).homologyπ q :=
  TauCeti.ChainComplex.cap_homologyπ _ _ _ _ _ _ _

/-- **Naturality of the cap product**, the projection formula `f_*(x ⌢ f^*α) = f_*x ⌢ α`: for a
continuous map `f : X ⟶ Y`, capping with the pull-back of a cohomology class of `Y` and pushing
forward along `f` is pushing forward along `f` and capping with the class. -/
lemma singularCap_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (k : Type*) [Ring k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ P) (p q n : ℕ)
    (h : p + q = n) (α : Y.singularCohomology R k M p) :
    X.singularCap k u μ p q n h (TopCat.singularCohomologyMap f p α) ≫
        ((singularHomologyFunctor C q).obj P).map f =
      ((singularHomologyFunctor C n).obj T).map f ≫ Y.singularCap k u μ p q n h α :=
  TauCeti.ChainComplex.cap_naturality _ _ _ _ _ _ _ _
    (alexanderWhitneyDiagonal_naturality f u)
    (SSet.chainComplexPairing_naturality (toSSet.map f) μ).symm p q n h α

end Homology

section ModuleCat

variable (X : TopCat.{w}) (k : Type w) [CommRing k]

/-- **Capping with a homology class**: for `μ ∈ Hₙ(X; k)` and `p + q = n`, the `k`-linear map
`Hᵖ(X; k) → H_q(X; k)`, `α ↦ μ ⌢ α`, with the cap product taken along the unitors of
`𝟙_ (ModuleCat k)`. -/
def singularCapLinearMap {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p →ₗ[k]
      ((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ (ModuleCat.{w} k))).obj X where
  toFun α := (X.singularCap k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ (𝟙_ (ModuleCat.{w} k))).hom
    p q n h α).hom μ
  map_add' α β := by simp
  map_smul' c α := by simp

/-- `TopCat.singularCapLinearMap k h μ α` is the cap product `μ ⌢ α`. -/
@[simp]
theorem singularCapLinearMap_apply {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    X.singularCapLinearMap k h μ α =
      (X.singularCap k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ (𝟙_ (ModuleCat.{w} k))).hom
        p q n h α).hom μ :=
  (rfl)

/-- **Naturality of capping with a homology class**, `f_*(μ ⌢ f^*α) = f_*μ ⌢ α`: for a continuous
map `f : X ⟶ Y`, capping `μ ∈ Hₙ(X; k)` with the pull-back of `α ∈ Hᵖ(Y; k)` and pushing forward
is capping the push-forward of `μ` with `α`. -/
theorem singularCapLinearMap_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) {p q n : ℕ}
    (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X)
    (α : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    (((singularHomologyFunctor (ModuleCat.{w} k) q).obj (𝟙_ (ModuleCat.{w} k))).map f).hom
        (X.singularCapLinearMap k h μ (TopCat.singularCohomologyMap f p α)) =
      Y.singularCapLinearMap k h
        ((((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).map f).hom μ)
        α := by
  rw [singularCapLinearMap_apply, singularCapLinearMap_apply, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, singularCap_naturality, ModuleCat.hom_comp, LinearMap.comp_apply]

end ModuleCat

end TopCat
