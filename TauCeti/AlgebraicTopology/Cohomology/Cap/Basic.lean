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
* `TopCat.singularCapAddHom`: capping with a fixed class `z ∈ Hₙ(X; T)`, as an additive map
  `Hᵖ(X; R, M) →+ H_q(X; P)`, with `TopCat.singularCapAddHom_naturality` its naturality and
  `TopCat.singularCapAddHom_add`, `TopCat.singularCapAddHom_smul` and
  `TopCat.singularCapAddHom_zsmul` its additivity in the class.
* `TopCat.singularCapLinearMap`: capping with a fixed class `μ ∈ Hₙ(X; k)`, as a `k`-linear map
  `Hᵖ(X; k) → H_q(X; k)`, with `TopCat.singularCapLinearMap_naturality` its naturality.
* `TopCat.singularCapLinearMap_singularCohomologyChainCoefficientMap`: capping with a class whose
  chain coefficients are changed along an isomorphism to the unit object.
* `TopCat.singularCap_eqToHom`: the cap product does not depend on how the `k`-linear structure
  of `C` is presented.
* `TopCat.singularCap_coefficient_naturality`: compatible changes of every coefficient object
  commute with the native cap product on homology and cohomology.
* `TopCat.singularCap_coefficient_naturality_map`: the same square combined with a map of spaces.

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

/-- The singular cap product does not depend on how the `k`-linear structure of `C` is presented:
along an equality `L₁ = L₂` of `k`-linear structures, capping with the image of a class under the
identification `eqToHom` of the two cohomology modules is capping with the class. -/
lemma singularCap_eqToHom {k : Type*} [Ring k] (L₁ L₂ : Linear k C) (h : L₁ = L₂)
    [@MonoidalLinear k _ C _ _ L₁ _ _] [@MonoidalLinear k _ C _ _ L₂ _ _] (X : TopCat.{w})
    (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ P) (p q n : ℕ) (hpq : p + q = n)
    (a : @TopCat.singularCohomology _ _ _ _ R k _ L₁ M X p) :
    @TopCat.singularCap _ _ _ _ _ _ _ _ _ _ _ _ X k _ L₂ _ u μ p q n hpq
        (eqToHom (congrArg (fun L : Linear k C ↦
          @TopCat.singularCohomology _ _ _ _ R k _ L M X p) h) a) =
      @TopCat.singularCap _ _ _ _ _ _ _ _ _ _ _ _ X k _ L₁ _ u μ p q n hpq a := by
  subst h
  simp

section Coefficients

variable {R' S' T' M' P' : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M')]

/-- If `c ≫ u = u' ≫ (a ⊗ b)` and `(v ▷ S') ≫ μ' = (M ◁ b) ≫ μ ≫ e`, then cap with the
cochain pulled back by `a` and postcomposed by `v` equals cap between the homology maps
of `c` and `e`. -/
theorem singularCap_coefficient_naturality (X : TopCat.{w}) (k : Type*) [Ring k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (u' : T' ⟶ R' ⊗ S')
    (μ : M ⊗ S ⟶ P) (μ' : M' ⊗ S' ⟶ P')
    (a : R' ⟶ R) (b : S' ⟶ S) (c : T' ⟶ T) (v : M ⟶ M') (e : P ⟶ P')
    (hu : c ≫ u = u' ≫ (a ⊗ₘ b)) (hμ : (v ▷ S') ≫ μ' = (M ◁ b) ≫ μ ≫ e)
    (p q n : ℕ) (h : p + q = n) (α : X.singularCohomology R k M p) :
    X.singularCap k u' μ' p q n h
        (homologyMap (((toSSet.obj X).chainComplex R').linearYonedaObjMap k v) p
          (X.singularCohomologyChainCoefficientMap k M a p α)) =
      ((AlgebraicTopology.singularHomologyFunctor C n).map c).app X ≫
        X.singularCap k u μ p q n h α ≫
          ((AlgebraicTopology.singularHomologyFunctor C q).map e).app X := by
  rw [singularCap_def, singularCap_def]
  have ha :
      (NatTrans.mapHomologicalComplex ((tensoringLeft C).map v) _).app
          ((toSSet.obj X).chainComplex S') ≫ (toSSet.obj X).chainComplexPairing μ' =
        ((tensorLeft M).mapHomologicalComplex _).map
            (((SSet.chainComplexFunctor C).map b).app (toSSet.obj X)) ≫
          (toSSet.obj X).chainComplexPairing μ ≫
            ((SSet.chainComplexFunctor C).map e).app (toSSet.obj X) := by
    rw [SSet.whiskerRight_comp_chainComplexPairing,
      SSet.chainComplexPairing_comp_chainComplexFunctor_map_app,
      SSet.whiskerLeft_chainComplexFunctor_map_app_comp_chainComplexPairing]
    exact congrArg ((toSSet.obj X).chainComplexPairing) hμ
  let f := (TauCeti.ChainComplex.linearYonedaFunctor k M).map
    (((SSet.chainComplexFunctor C).map a).app (toSSet.obj X)).op
  let g := ((toSSet.obj X).chainComplex R').linearYonedaObjMap k v
  have hinput : homologyMap g p (X.singularCohomologyChainCoefficientMap k M a p α) =
      homologyMap (f ≫ g) p α :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans
      (ConcreteCategory.congr_hom (homologyMap_comp f g p).symm α)
  refine (congrArg (TauCeti.ChainComplex.cap k (X.alexanderWhitneyDiagonal u')
    ((toSSet.obj X).chainComplexPairing μ') p q n h) hinput).trans ?_
  exact TauCeti.ChainComplex.cap_coefficient_naturality
    (X.alexanderWhitneyDiagonal u) ((toSSet.obj X).chainComplexPairing μ)
    (X.alexanderWhitneyDiagonal u') ((toSSet.obj X).chainComplexPairing μ')
    (((SSet.chainComplexFunctor C).map c).app (toSSet.obj X))
    (((SSet.chainComplexFunctor C).map a).app (toSSet.obj X))
    (((SSet.chainComplexFunctor C).map b).app (toSSet.obj X)) v
    (((SSet.chainComplexFunctor C).map e).app (toSSet.obj X))
    (alexanderWhitneyDiagonal_coefficient_naturality X u u' a b c hu)
    (fun j ↦ congrArg (fun f ↦ f.f j) ha) p q n h α

/-- Coefficient transport commutes with the projection formula for a map of spaces. -/
theorem singularCap_coefficient_naturality_map {X Y : TopCat.{w}} (f : X ⟶ Y)
    (k : Type*) [Ring k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (u' : T' ⟶ R' ⊗ S') (μ : M ⊗ S ⟶ P) (μ' : M' ⊗ S' ⟶ P')
    (a : R' ⟶ R) (b : S' ⟶ S) (c : T' ⟶ T) (v : M ⟶ M') (e : P ⟶ P')
    (hu : c ≫ u = u' ≫ (a ⊗ₘ b)) (hμ : (v ▷ S') ≫ μ' = (M ◁ b) ≫ μ ≫ e)
    (p q n : ℕ) (h : p + q = n) (α : Y.singularCohomology R k M p) :
    X.singularCap k u' μ' p q n h
        (TopCat.singularCohomologyMap f p
          (homologyMap (((toSSet.obj Y).chainComplex R').linearYonedaObjMap k v) p
          (Y.singularCohomologyChainCoefficientMap k M a p α))) ≫
        ((AlgebraicTopology.singularHomologyFunctor C q).obj P').map f =
      ((AlgebraicTopology.singularHomologyFunctor C n).obj T').map f ≫
        ((AlgebraicTopology.singularHomologyFunctor C n).map c).app Y ≫
          Y.singularCap k u μ p q n h α ≫
            ((AlgebraicTopology.singularHomologyFunctor C q).map e).app Y := by
  rw [singularCap_naturality,
    singularCap_coefficient_naturality Y k u u' μ μ' a b c v e hu hμ p q n h]

end Coefficients

end Homology

section AddHom

variable {R₀ : Type w} [CommRing R₀] (k : Type*) [Ring k] [Linear k (ModuleCat.{w} R₀)]
  [MonoidalLinear k (ModuleCat.{w} R₀)] {R S T M P : ModuleCat.{w} R₀}
  (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ P)

/-- **Capping with a homology class**: for `z ∈ Hₙ(X; T)` and `p + q = n`, the additive map
`Hᵖ(X; R, M) →+ H_q(X; P)`, `α ↦ z ⌢ α`, for the cap product along the coefficient morphisms `u`
and `μ` (`TopCat.singularCap`). -/
def singularCapAddHom (X : TopCat.{w}) {p q n : ℕ} (h : p + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj X) :
    X.singularCohomology R k M p →+
      ((singularHomologyFunctor (ModuleCat.{w} R₀) q).obj P).obj X where
  toFun α := (X.singularCap k u μ p q n h α).hom z
  map_zero' := by simp
  map_add' α β := by simp

/-- `TopCat.singularCapAddHom k u μ X h z α` is the cap product `z ⌢ α`. -/
theorem singularCapAddHom_apply (X : TopCat.{w}) {p q n : ℕ} (h : p + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj X)
    (α : X.singularCohomology R k M p) :
    X.singularCapAddHom k u μ h z α = (X.singularCap k u μ p q n h α).hom z :=
  (rfl)

/-- Capping with a sum of homology classes is the sum of the caps:
`(z + z') ⌢ α = z ⌢ α + z' ⌢ α`. -/
@[simp]
theorem singularCapAddHom_add (X : TopCat.{w}) {p q n : ℕ} (h : p + q = n)
    (z z' : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj X) :
    X.singularCapAddHom k u μ h (z + z') =
      X.singularCapAddHom k u μ h z + X.singularCapAddHom k u μ h z' := by
  ext α
  simp [singularCapAddHom_apply]

/-- Capping with a scalar multiple of a homology class: `(r • z) ⌢ α = r • (z ⌢ α)`. -/
@[simp]
theorem singularCapAddHom_smul (X : TopCat.{w}) {p q n : ℕ} (h : p + q = n) (r : R₀)
    (z : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj X) :
    X.singularCapAddHom k u μ h (r • z) = r • X.singularCapAddHom k u μ h z := by
  ext α
  simp [singularCapAddHom_apply]

/-- Capping with an integer multiple of a homology class: `(d • z) ⌢ α = d • (z ⌢ α)`. -/
@[simp]
theorem singularCapAddHom_zsmul (X : TopCat.{w}) {p q n : ℕ} (h : p + q = n) (d : ℤ)
    (z : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj X) :
    X.singularCapAddHom k u μ h (d • z) = d • X.singularCapAddHom k u μ h z := by
  ext α
  simp [singularCapAddHom_apply]

/-- **Naturality of capping with a homology class**, `f_*(z ⌢ f^*α) = f_*z ⌢ α`, the projection
formula `TopCat.singularCap_naturality` evaluated at `z`. -/
theorem singularCapAddHom_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) {p q n : ℕ} (h : p + q = n)
    (z : ((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).obj X)
    (α : Y.singularCohomology R k M p) :
    (((singularHomologyFunctor (ModuleCat.{w} R₀) q).obj P).map f).hom
        (X.singularCapAddHom k u μ h z ((TopCat.singularCohomologyMap f p).hom α)) =
      Y.singularCapAddHom k u μ h
        ((((singularHomologyFunctor (ModuleCat.{w} R₀) n).obj T).map f).hom z) α := by
  rw [singularCapAddHom_apply, singularCapAddHom_apply, ← ModuleCat.comp_apply,
    singularCap_naturality, ModuleCat.comp_apply]

end AddHom

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

/-- `TopCat.singularCapLinearMap` is `TopCat.singularCapAddHom` along the unitors of
`𝟙_ (ModuleCat k)`. -/
theorem toAddMonoidHom_singularCapLinearMap {p q n : ℕ} (h : p + q = n)
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj (𝟙_ (ModuleCat.{w} k))).obj X) :
    (X.singularCapLinearMap k h μ).toAddMonoidHom =
      X.singularCapAddHom k (λ_ (𝟙_ (ModuleCat.{w} k))).inv (λ_ (𝟙_ (ModuleCat.{w} k))).hom h μ :=
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
  rw [singularCapLinearMap_apply, singularCapLinearMap_apply, ← singularCapAddHom_apply,
    ← singularCapAddHom_apply]
  exact singularCapAddHom_naturality k _ _ f h μ α

/-- **Capping across a change of chain coefficients**: for an isomorphism `e : A ≅ 𝟙_ (ModuleCat k)`
of chain coefficients, capping the image of `μ ∈ Hₙ(X; A)` under `e` with the pull-back along
`e⁻¹` of `α ∈ Hᵖ(X; A)` is the cap product of `μ` with `α` along the right unitors. -/
theorem singularCapLinearMap_singularCohomologyChainCoefficientMap {p q n : ℕ} (h : p + q = n)
    {A : ModuleCat.{w} k} (e : A ≅ 𝟙_ (ModuleCat.{w} k))
    (μ : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj A).obj X)
    (α : X.singularCohomology A k (𝟙_ (ModuleCat.{w} k)) p) :
    X.singularCapLinearMap k h
        ((((singularHomologyFunctor (ModuleCat.{w} k) n).map e.hom).app X).hom μ)
        (X.singularCohomologyChainCoefficientMap k (𝟙_ (ModuleCat.{w} k)) e.inv p α) =
      (X.singularCap k (ρ_ A).inv (ρ_ (𝟙_ (ModuleCat.{w} k))).hom p q n h α).hom μ := by
  have hc := singularCap_coefficient_naturality X k (ρ_ A).inv (λ_ (𝟙_ (ModuleCat.{w} k))).inv
    (ρ_ (𝟙_ (ModuleCat.{w} k))).hom (λ_ (𝟙_ (ModuleCat.{w} k))).hom
    e.inv (𝟙 _) e.inv (𝟙 _) (𝟙 _) (by simp [unitors_inv_equal]) (by simp [unitors_equal]) p q n h α
  rw [ChainComplex.linearYonedaObjMap_id, HomologicalComplex.homologyMap_id] at hc
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id,
    ConcreteCategory.id_apply] at hc
  rw [singularCapLinearMap_apply, hc, ModuleCat.hom_comp, LinearMap.comp_apply]
  congr 1
  exact (((singularHomologyFunctor (ModuleCat.{w} k) n).mapIso e).app X).hom_inv_id_apply μ

end ModuleCat

end TopCat
