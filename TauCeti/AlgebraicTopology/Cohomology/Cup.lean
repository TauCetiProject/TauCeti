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

Let `C` be a `k`-linear preadditive monoidal category with coproducts.  For a space `X`, the
cup product of singular cochains is the cup product of cochains
(`TauCeti.ChainComplex.cupCochain`) along the Alexander–Whitney diagonal
`X.alexanderWhitneyDiagonal u : C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of a coefficient morphism
`u : T ⟶ R ⊗ S` (`TopCat.alexanderWhitneyDiagonal`), for a pairing `μ : M ⊗ N ⟶ P` of
coefficient objects: a cochain `φ` of degree `p` with values in `M` and a cochain `ψ` of degree
`q` with values in `N` give the cochain of degree `n = p + q` with values in `P` whose value on a
singular simplex `σ` is `μ (φ (σ|[0, …, p]) ⊗ ψ (σ|[p, …, n]))`, precomposed with `u`
(`TopCat.ιChainComplex_cupCochain_alexanderWhitneyDiagonal`).  It satisfies the Leibniz rule
`TauCeti.ChainComplex.d_comp_cupCochain`, and so, when `C` is moreover abelian, descends to the
`k`-bilinear cup product `TopCat.singularCup` on singular cohomology, which is natural in `X`.

For the cohomology of `X` with coefficients in modules over a commutative ring `k`, take
`C := ModuleCat k`, `R = S = T = 𝟙_ (ModuleCat k)` (the module `k`) and `u = (λ_ _).inv`; then
`φ ⌣ ψ` evaluates `σ` to `μ (φ (σ|[0, …, p]) ⊗ ψ (σ|[p, …, n]))`, the cup product of Hatcher,
Section 3.2.

The cup product is associative and unital.  Associativity relates cup products along four
diagonals and four pairings, and holds when the coefficient morphisms are coassociative and the
pairings associative up to the associators; both sides then evaluate a simplex on its front,
middle and back faces.  The unit is the class of the constant `0`-cocycle
`TopCat.constSingularCocycle` whose value is the unit of the pairing.

## Main definitions and results

* `TopCat.ιChainComplex_cupCochain_alexanderWhitneyDiagonal`: the cup product of singular
  cochains on a singular simplex.
* `TopCat.singularCup`: the cup product on singular cohomology, with `TopCat.singularCup_homologyπ`
  computing it on classes of cocycles and `TopCat.singularCup_naturality` its naturality.
* `TopCat.cupCochain_alexanderWhitneyDiagonal_assoc` and `TopCat.singularCup_assoc`:
  associativity of the cup product of cochains and on cohomology.
* `TopCat.cupCochain_constCochain_left`, `TopCat.cupCochain_constCochain_right`,
  `TopCat.singularCup_constSingularCocycle_left` and
  `TopCat.singularCup_constSingularCocycle_right`: the unit laws.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, including the associativity and unit of the cup product.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicTopology Simplicial
  HomologicalComplex

universe w v u

namespace TopCat

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

section Cochain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {k : Type*} [CommSemiring k] [Linear k C] [MonoidalLinear k C]
  {R S T M N P : C}

/-- **The cup product of singular cochains on a simplex**: for cochains `φ` of degree `p` and `ψ`
of degree `q`, the value of `φ ⌣ ψ` on a singular `(p + q)`-simplex `σ` is `φ` of the front
`p`-face of `σ` tensored with `ψ` of its back `q`-face, followed by `μ`, after the coefficient
morphism `u`. -/
lemma ιChainComplex_cupCochain_alexanderWhitneyDiagonal (X : TopCat.{w}) (u : T ⟶ R ⊗ S)
    (μ : M ⊗ N ⟶ P) (p q n : ℕ)
    (h : p + q = n) (φ : ((toSSet.obj X).chainComplex R).X p ⟶ M)
    (ψ : ((toSSet.obj X).chainComplex S).X q ⟶ N) (σ : (toSSet.obj X) _⦋n⦌) :
    (toSSet.obj X).ιChainComplex σ ≫
        TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal u) μ p q n h φ ψ =
      u ≫ (((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ) ⊗ₘ
          ((toSSet.obj X).ιChainComplex
            ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ ψ)) ≫ μ := by
  rw [TauCeti.ChainComplex.cupCochain_apply,
    ιChainComplex_alexanderWhitneyDiagonal_f_tensorCochain X u μ p q n h]

section Laws

variable {R₁ R₂ R₃ T₁₂ T₂₃ M₁ M₂ M₃ M₁₂ M₂₃ : C}

/-- **Associativity of the cup product of singular cochains**: `(φ₁ ⌣ φ₂) ⌣ φ₃ = φ₁ ⌣ (φ₂ ⌣ φ₃)`,
for coefficient morphisms that are coassociative up to the associator (`hu`) and pairings that
are associative up to the associator (`hμ`).  Both sides evaluate a singular simplex on its front
`p`-face, its middle `q`-face and its back `r`-face.  In the usual case, where every coefficient
object is `𝟙_ C` and every coefficient morphism is `(λ_ _).inv`, `hu` holds by monoidal coherence
and `hμ` is the associativity of a ring object of coefficients. -/
lemma cupCochain_alexanderWhitneyDiagonal_assoc (X : TopCat.{w})
    {u₁₂ : T₁₂ ⟶ R₁ ⊗ R₂} {u : T ⟶ T₁₂ ⊗ R₃} {u₂₃ : T₂₃ ⟶ R₂ ⊗ R₃} {u' : T ⟶ R₁ ⊗ T₂₃}
    (hu : u ≫ u₁₂ ▷ R₃ ≫ (α_ R₁ R₂ R₃).hom = u' ≫ R₁ ◁ u₂₃)
    {μ₁₂ : M₁ ⊗ M₂ ⟶ M₁₂} {μ : M₁₂ ⊗ M₃ ⟶ P} {μ₂₃ : M₂ ⊗ M₃ ⟶ M₂₃} {μ' : M₁ ⊗ M₂₃ ⟶ P}
    (hμ : μ₁₂ ▷ M₃ ≫ μ = (α_ M₁ M₂ M₃).hom ≫ M₁ ◁ μ₂₃ ≫ μ')
    {p q r m m' n : ℕ} (h₁₂ : p + q = m) (h : m + r = n) (h₂₃ : q + r = m') (h' : p + m' = n)
    (φ₁ : ((toSSet.obj X).chainComplex R₁).X p ⟶ M₁)
    (φ₂ : ((toSSet.obj X).chainComplex R₂).X q ⟶ M₂)
    (φ₃ : ((toSSet.obj X).chainComplex R₃).X r ⟶ M₃) :
    TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal u) μ m r n h
        (TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal u₁₂) μ₁₂ p q m h₁₂ φ₁ φ₂)
        φ₃ =
      TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal u') μ' p m' n h' φ₁
        (TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal u₂₃) μ₂₃ q r m' h₂₃ φ₂
          φ₃) := by
  subst h₁₂ h h₂₃
  ext σ
  -- both sides evaluate `σ` on its faces `[0, …, p]`, `[p, …, p + q]` and `[p + q, …, n]`
  simp only [ιChainComplex_cupCochain_alexanderWhitneyDiagonal, ← Functor.map_comp_apply,
    ← op_comp, TauCeti.SimplexCategory.subinterval_comp_subinterval _ _ _ _ _ _ rfl, Nat.zero_add,
    Nat.add_zero]
  let f₁ : R₁ ⟶ M₁ := (toSSet.obj X).ιChainComplex
    ((toSSet.obj X).map (SimplexCategory.subinterval 0 p (by omega)).op σ) ≫ φ₁
  let f₂ : R₂ ⟶ M₂ := (toSSet.obj X).ιChainComplex
    ((toSSet.obj X).map (SimplexCategory.subinterval p q (by omega)).op σ) ≫ φ₂
  let f₃ : R₃ ⟶ M₃ := (toSSet.obj X).ιChainComplex
    ((toSSet.obj X).map (SimplexCategory.subinterval (p + q) r (by omega)).op σ) ≫ φ₃
  -- Fold the three local face evaluations into `f₁`, `f₂`, and `f₃` to display the coefficient
  -- equation. This `change` unfolds only these `let` bindings; subinterval bounds agree by
  -- proof irrelevance.
  change u ≫ ((u₁₂ ≫ (f₁ ⊗ₘ f₂) ≫ μ₁₂) ⊗ₘ f₃) ≫ μ =
    u' ≫ (f₁ ⊗ₘ (u₂₃ ≫ (f₂ ⊗ₘ f₃) ≫ μ₂₃)) ≫ μ'
  calc _ = u ≫ u₁₂ ▷ R₃ ≫ ((f₁ ⊗ₘ f₂) ⊗ₘ f₃) ≫ μ₁₂ ▷ M₃ ≫ μ := by
        simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.comp_id,
          Category.id_comp]
    _ = u' ≫ R₁ ◁ u₂₃ ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ f₃)) ≫ M₁ ◁ μ₂₃ ≫ μ' := by
        rw [hμ, associator_naturality_assoc, reassoc_of% hu]
    _ = _ := by
        simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.comp_id,
          Category.id_comp]

/-- **The left unit law for the cup product of singular cochains**: the constant `0`-cochain with
value `e` is a left unit, provided that `u` followed by `e` is the left unitor followed by some
`η : 𝟙_ C ⟶ M` which is a left unit for the pairing `μ`.  For coefficients in a ring object `M`
with unit `η`, take `R = S = 𝟙_ C`, `u = (λ_ _).inv` and `e = η`. -/
lemma cupCochain_constCochain_left (X : TopCat.{w})
    {u : S ⟶ R ⊗ S} {μ : M ⊗ N ⟶ N}
    {e : R ⟶ M} {η : 𝟙_ C ⟶ M} (hu : u ≫ e ▷ S = (λ_ S).inv ≫ η ▷ S)
    (hμ : η ▷ N ≫ μ = (λ_ N).hom) {q : ℕ} (h : 0 + q = q)
    (ψ : ((toSSet.obj X).chainComplex S).X q ⟶ N) :
    TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal u) μ 0 q q h
      ((toSSet.obj X).constCochain e) ψ = ψ := by
  ext σ
  simp only [ιChainComplex_cupCochain_alexanderWhitneyDiagonal,
    SSet.ιChainComplex_constCochain, TauCeti.SimplexCategory.subinterval_zero_eq_id,
    op_id, Functor.map_id_apply]
  calc u ≫ (e ⊗ₘ ((toSSet.obj X).ιChainComplex σ ≫ ψ)) ≫ μ =
        (λ_ S).inv ≫ η ▷ S ≫ M ◁ ((toSSet.obj X).ιChainComplex σ ≫ ψ) ≫ μ := by
          rw [tensorHom_def_assoc, reassoc_of% hu]
    _ = (λ_ S).inv ≫ 𝟙_ C ◁ ((toSSet.obj X).ιChainComplex σ ≫ ψ) ≫ (λ_ N).hom := by
          rw [← whisker_exchange_assoc, hμ]
    _ = (toSSet.obj X).ιChainComplex σ ≫ ψ := by
          rw [leftUnitor_naturality, Iso.inv_hom_id_assoc]

/-- **The right unit law for the cup product of singular cochains**: the constant `0`-cochain with
value `e` is a right unit, provided that `u` followed by `e` is the right unitor followed by some
`η : 𝟙_ C ⟶ N` which is a right unit for the pairing `μ`.  For coefficients in a ring object `N`
with unit `η`, take `R = S = 𝟙_ C`, `u = (ρ_ _).inv` (which is `(λ_ _).inv`) and `e = η`. -/
lemma cupCochain_constCochain_right (X : TopCat.{w})
    {u : R ⟶ R ⊗ S} {μ : M ⊗ N ⟶ M}
    {e : S ⟶ N} {η : 𝟙_ C ⟶ N} (hu : u ≫ R ◁ e = (ρ_ R).inv ≫ R ◁ η)
    (hμ : M ◁ η ≫ μ = (ρ_ M).hom) {p : ℕ} (h : p + 0 = p)
    (φ : ((toSSet.obj X).chainComplex R).X p ⟶ M) :
    TauCeti.ChainComplex.cupCochain k (X.alexanderWhitneyDiagonal u) μ p 0 p h
      φ ((toSSet.obj X).constCochain e) = φ := by
  ext σ
  simp only [ιChainComplex_cupCochain_alexanderWhitneyDiagonal,
    SSet.ιChainComplex_constCochain, TauCeti.SimplexCategory.subinterval_zero_eq_id,
    op_id, Functor.map_id_apply]
  calc u ≫ (((toSSet.obj X).ιChainComplex σ ≫ φ) ⊗ₘ e) ≫ μ =
        (ρ_ R).inv ≫ R ◁ η ≫ ((toSSet.obj X).ιChainComplex σ ≫ φ) ▷ N ≫ μ := by
          rw [tensorHom_def'_assoc, reassoc_of% hu]
    _ = (ρ_ R).inv ≫ ((toSSet.obj X).ιChainComplex σ ≫ φ) ▷ 𝟙_ C ≫ (ρ_ M).hom := by
          rw [whisker_exchange_assoc, hμ]
    _ = (toSSet.obj X).ιChainComplex σ ≫ φ := by
          rw [rightUnitor_naturality, Iso.inv_hom_id_assoc]

end Laws

end Cochain

section Cohomology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N P : C}

/-- **The cup product on singular cohomology**,
`Hᵖ(X; R, M) × H^q(X; S, N) ⟶ Hⁿ(X; T, P)` for `p + q = n`: the cup product of cohomology classes
along the Alexander–Whitney diagonal `X.alexanderWhitneyDiagonal u` and the pairing
`μ : M ⊗ N ⟶ P`, `k`-bilinear and natural in `X` (`TopCat.singularCup_naturality`). -/
def singularCup (X : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n) :
    X.singularCohomology R k M p →ₗ[k] X.singularCohomology S k N q →ₗ[k]
      X.singularCohomology T k P n :=
  TauCeti.ChainComplex.cup k (X.alexanderWhitneyDiagonal u) μ p q n h

/-- The cup product of the classes of two singular cocycles is the class of their cup product. -/
@[simp]
lemma singularCup_homologyπ (X : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n)
    (a : (X.singularCochainComplex R k M).cycles p)
    (b : (X.singularCochainComplex S k N).cycles q) :
    X.singularCup k u μ p q n h ((X.singularCochainComplex R k M).homologyπ p a)
        ((X.singularCochainComplex S k N).homologyπ q b) =
      (X.singularCochainComplex T k P).homologyπ n
        (TauCeti.ChainComplex.cupCycles k (X.alexanderWhitneyDiagonal u) μ p q n h a b) :=
  TauCeti.ChainComplex.cup_homologyπ _ _ _ _ _ _ _ _

/-- **Naturality of the cup product**: for a continuous map `f : X ⟶ Y`, pulling back two
cohomology classes of `Y` along `f` and cupping them is pulling back their cup product. -/
lemma singularCup_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ P)
    (p q n : ℕ) (h : p + q = n)
    (α : Y.singularCohomology R k M p) (β : Y.singularCohomology S k N q) :
    X.singularCup k u μ p q n h (TopCat.singularCohomologyMap f p α)
        (TopCat.singularCohomologyMap f q β) =
      TopCat.singularCohomologyMap f n (Y.singularCup k u μ p q n h α β) :=
  TauCeti.ChainComplex.cup_naturality _ μ _ _ _ _ (alexanderWhitneyDiagonal_naturality f u)
    p q n h α β

section Laws

variable {R₁ R₂ R₃ T₁₂ T₂₃ M₁ M₂ M₃ M₁₂ M₂₃ : C}

/-- **Associativity of the cup product on singular cohomology**: `(a ⌣ b) ⌣ c = a ⌣ (b ⌣ c)`,
for coefficient morphisms that are coassociative up to the associator (`hu`) and pairings that
are associative up to the associator (`hμ`), as in
`TopCat.cupCochain_alexanderWhitneyDiagonal_assoc`. -/
lemma singularCup_assoc (X : TopCat.{w}) (k : Type*) [CommRing k] [Linear k C]
    [MonoidalLinear k C]
    {u₁₂ : T₁₂ ⟶ R₁ ⊗ R₂} {u : T ⟶ T₁₂ ⊗ R₃} {u₂₃ : T₂₃ ⟶ R₂ ⊗ R₃} {u' : T ⟶ R₁ ⊗ T₂₃}
    (hu : u ≫ u₁₂ ▷ R₃ ≫ (α_ R₁ R₂ R₃).hom = u' ≫ R₁ ◁ u₂₃)
    {μ₁₂ : M₁ ⊗ M₂ ⟶ M₁₂} {μ : M₁₂ ⊗ M₃ ⟶ P} {μ₂₃ : M₂ ⊗ M₃ ⟶ M₂₃} {μ' : M₁ ⊗ M₂₃ ⟶ P}
    (hμ : μ₁₂ ▷ M₃ ≫ μ = (α_ M₁ M₂ M₃).hom ≫ M₁ ◁ μ₂₃ ≫ μ')
    {p q r m m' n : ℕ} (h₁₂ : p + q = m) (h : m + r = n) (h₂₃ : q + r = m') (h' : p + m' = n)
    (a : X.singularCohomology R₁ k M₁ p) (b : X.singularCohomology R₂ k M₂ q)
    (c : X.singularCohomology R₃ k M₃ r) :
    X.singularCup k u μ m r n h (X.singularCup k u₁₂ μ₁₂ p q m h₁₂ a b) c =
      X.singularCup k u' μ' p m' n h' a (X.singularCup k u₂₃ μ₂₃ q r m' h₂₃ b c) := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  obtain ⟨c, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ r c
  simp only [singularCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  simp only [TauCeti.ChainComplex.iCycles_cupCycles]
  exact TopCat.cupCochain_alexanderWhitneyDiagonal_assoc X hu hμ h₁₂ h h₂₃ h' _ _ _

/-- **The left unit law for the cup product on singular cohomology**: the class of the constant
`0`-cocycle with value `e` is a left unit, under the hypotheses of
`TopCat.cupCochain_constCochain_left`. -/
lemma singularCup_constSingularCocycle_left (X : TopCat.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] {u : S ⟶ R ⊗ S} {μ : M ⊗ N ⟶ N} {e : R ⟶ M}
    {η : 𝟙_ C ⟶ M} (hu : u ≫ e ▷ S = (λ_ S).inv ≫ η ▷ S) (hμ : η ▷ N ≫ μ = (λ_ N).hom)
    {q : ℕ} (h : 0 + q = q) (b : X.singularCohomology S k N q) :
    X.singularCup k u μ 0 q q h
      ((X.singularCochainComplex R k M).homologyπ 0
        (X.constSingularCocycle k e)) b = b := by
  obtain ⟨b, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q b
  rw [singularCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [TauCeti.ChainComplex.iCycles_cupCycles, TopCat.iCycles_constSingularCocycle]
  exact TopCat.cupCochain_constCochain_left X hu hμ h _

/-- **The right unit law for the cup product on singular cohomology**: the class of the constant
`0`-cocycle with value `e` is a right unit, under the hypotheses of
`TopCat.cupCochain_constCochain_right`. -/
lemma singularCup_constSingularCocycle_right (X : TopCat.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] {u : R ⟶ R ⊗ S} {μ : M ⊗ N ⟶ M} {e : S ⟶ N}
    {η : 𝟙_ C ⟶ N} (hu : u ≫ R ◁ e = (ρ_ R).inv ≫ R ◁ η) (hμ : M ◁ η ≫ μ = (ρ_ M).hom)
    {p : ℕ} (h : p + 0 = p) (a : X.singularCohomology R k M p) :
    X.singularCup k u μ p 0 p h a
      ((X.singularCochainComplex S k N).homologyπ 0
        (X.constSingularCocycle k e)) = a := by
  obtain ⟨a, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p a
  rw [singularCup_homologyπ]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [TauCeti.ChainComplex.iCycles_cupCycles, TopCat.iCycles_constSingularCocycle]
  exact TopCat.cupCochain_constCochain_right X hu hμ h _

end Laws

end Cohomology

end TopCat

namespace TauCeti

/-- The singular cup product is the cohomological product along the Alexander–Whitney diagonal. -/
lemma singularCup_def {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]
    [MonoidalCategory C] [MonoidalPreadditive C] (k : Type*) [CommRing k] [Linear k C]
    [MonoidalLinear k C] {X : TopCat.{w}} {R S T M N P : C}
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ P) (p q n : ℕ) (h : p + q = n) :
    X.singularCup k u μ p q n h =
      ChainComplex.cup k (X.alexanderWhitneyDiagonal u) μ p q n h :=
  (rfl)

end TauCeti
