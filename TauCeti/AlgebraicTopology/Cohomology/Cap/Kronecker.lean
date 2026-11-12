/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Relative
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker

/-!
# The Kronecker pairing of singular cap and cup products

For a space `X`, a coefficient morphism `u : T ⟶ R ⊗ S`, a singular cohomology class
`α ∈ Hᵖ(X; R, 𝟙)` with values in the tensor unit and a class `β ∈ H^q(X; S, N)`, the cap product
`x ⌢ α ∈ H_q(X; S)` of a class `x ∈ Hₙ(X; T)`, `n = p + q`, taken along the left unitor
`𝟙 ⊗ S ⟶ S`, satisfies

`⟨β, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`,

where the cup product is taken along `u` and the left unitor `𝟙 ⊗ N ⟶ N`
(`TopCat.singularCap_comp_singularKronecker`).  There is no sign: with the front-face convention
of the Alexander–Whitney diagonal both sides evaluate `α` on the front `p`-face and `β` on the back
`q`-face of each singular simplex.  For modules over a commutative ring `k`, with all coefficients
the module `k` and `u` the inverse left unitor, this is the identity
`⟨ψ, x ⌢ φ⟩ = ⟨φ ⌣ ψ, x⟩` of Hatcher, Section 3.3, which makes the cap product the adjoint of
the cup product under the Kronecker pairing.

The key chain-level input is `SSet.chainComplexPairing_leftUnitor_hom_f`, from
`TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing`: the action of the tensor unit on
singular chains is the left unitor.

For a class `α ∈ Hᵖ(X; R, M)` with values in an arbitrary object `M`, the cap product along a
pairing `μ : M ⊗ S ⟶ L` lands in `H_q(X; L)`, and the class to evaluate on it is a class
`ψ ∈ H^q(X; L, N')` which, pulled back along the chain map `M ⊗ C(X; S) ⟶ C(X; L)` of `μ`, is the
extension `(M ◁ β) ≫ ν` of a class `β ∈ H^q(X; S, N)` along a pairing `ν : M ⊗ N ⟶ N'`
(`ChainComplex.linearYonedaObjWhiskerLeft`).  Then again `⟨ψ, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`, with
the cup product along `u` and `ν` (`TopCat.singularCap_comp_singularKronecker_of_homologyMap_eq`).
When `μ` is invertible, every `β` has such an extension, through the isomorphism
`M ⊗ C(X; S) ≅ C(X; L)` (`TopCat.singularCap_comp_singularKronecker_of_isIso`, an instance of
`TauCeti.ChainComplex.cap_comp_kronecker_of_isIso`); for modules over `k`
this pairs `α ∈ Hᵖ(X; M)` with `β ∈ H^q(X; k)`, the general coefficient form of the identity.  For
a pair `(X, A)` the same identities hold for the relative cap product of a relative class
`α ∈ Hᵖ(X, A; R, M)` with a relative class `x ∈ Hₙ(X, A; T)`, with the relative cup product
`α ⌣ β ∈ Hⁿ(X, A; T, N')` along the relative Alexander–Whitney diagonal
(`TopPair.singularCap_comp_singularKronecker_of_homologyMap_eq` and
`TopPair.singularCap_comp_singularKronecker_of_isIso`).

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology HomologicalComplex

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T N : C}

/-- **The Kronecker pairing of a singular cap product**, `⟨β, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: for a class
`α` of degree `p` with values in the tensor unit and a class `β` of degree `q` with values in `N`,
capping a class of degree `n = p + q` with `α` along `u` and the left unitor, and then evaluating
`β`, is evaluating the cup product of `α` and `β` along `u` and the left unitor of `N`. -/
theorem singularCap_comp_singularKronecker (X : TopCat.{w}) (k : Type*) [CommRing k]
    [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (p q n : ℕ) (h : p + q = n)
    (α : X.singularCohomology R k (𝟙_ C) p) (β : X.singularCohomology S k N q) :
    X.singularCap k u (λ_ S).hom p q n h α ≫ X.singularKronecker k q β =
      X.singularKronecker k n (X.singularCup k u (λ_ N).hom p q n h α β) := by
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ p α
  obtain ⟨ψ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ q β
  rw [singularCap_def, singularKronecker_def, singularKronecker_def, TauCeti.singularCup_def]
  refine TauCeti.ChainComplex.cap_comp_kronecker _ _ _ p q n h φ ψ ψ ?_
  rw [SSet.chainComplexPairing_leftUnitor_hom_f]
  exact (leftUnitor_naturality _).symm

variable {M N' L : C} [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- **The Kronecker pairing of a singular cap product with general coefficients**,
`⟨ψ, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: for a class `α ∈ Hᵖ(X; R, M)`, cap along `u` and a pairing
`μ : M ⊗ S ⟶ L`, a class `ψ ∈ H^q(X; L, N')` and a class `β ∈ H^q(X; S, N)` such that `ψ`, pulled
back along the chain map `M ⊗ C(X; S) ⟶ C(X; L)` of `μ`, is the extension of `β` along a pairing
`ν : M ⊗ N ⟶ N'`, evaluating `ψ` on the cap product of a class of degree `n = p + q` with `α` is
evaluating on that class the cup product of `α` and `β` along `u` and `ν`. -/
theorem singularCap_comp_singularKronecker_of_homologyMap_eq (X : TopCat.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ L)
    (ν : M ⊗ N ⟶ N') (p q n : ℕ) (h : p + q = n) (α : X.singularCohomology R k M p)
    (ψ : X.singularCohomology L k N' q) (β : X.singularCohomology S k N q)
    (hψ : homologyMap (K := X.singularCochainComplex L k N')
        (L := ChainComplex.linearYonedaObj
          (((tensorLeft M).mapHomologicalComplex _).obj ((toSSet.obj X).chainComplex S)) k N')
        ((TauCeti.ChainComplex.linearYonedaFunctor k N').map
          ((toSSet.obj X).chainComplexPairing μ).op) q ψ =
      homologyMap (ChainComplex.linearYonedaObjWhiskerLeft k M _ ν) q β) :
    X.singularCap k u μ p q n h α ≫ X.singularKronecker k q ψ =
      X.singularKronecker k n (X.singularCup k u ν p q n h α β) := by
  rw [singularCap_def, singularKronecker_def, singularKronecker_def, TauCeti.singularCup_def]
  exact TauCeti.ChainComplex.cap_comp_kronecker_of_homologyMap_eq _ _ ν p q n h α ψ β hψ

/-- **The Kronecker pairing of a singular cap product along an invertible pairing**,
`⟨ν(M ⊗ β), x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: when the pairing `μ : M ⊗ S ⟶ L` is invertible, every class
`β ∈ H^q(X; S, N)` extends along `ν : M ⊗ N ⟶ N'` to a class of `H^q(X; L, N')`, through the
isomorphism `M ⊗ C(X; S) ≅ C(X; L)` of `μ`, and evaluating it on the cap product with
`α ∈ Hᵖ(X; R, M)` is evaluating the cup product of `α` and `β`.  For modules over a commutative
ring `k`, with `R = S = T = N = k`, `μ = ν` the right unitor of a module `M` and `u` the inverse
left unitor, this pairs a class `α ∈ Hᵖ(X; M)` and a class `β ∈ H^q(X; k)`. -/
theorem singularCap_comp_singularKronecker_of_isIso (X : TopCat.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ L) [IsIso μ]
    (ν : M ⊗ N ⟶ N') (p q n : ℕ) (h : p + q = n) (α : X.singularCohomology R k M p)
    (β : X.singularCohomology S k N q) :
    X.singularCap k u μ p q n h α ≫ X.singularKronecker k q
        (homologyMap (K := ChainComplex.linearYonedaObj
            (((tensorLeft M).mapHomologicalComplex _).obj ((toSSet.obj X).chainComplex S)) k N')
          (L := X.singularCochainComplex L k N')
          ((TauCeti.ChainComplex.linearYonedaFunctor k N').map
            (inv ((toSSet.obj X).chainComplexPairing μ)).op) q
          (homologyMap (ChainComplex.linearYonedaObjWhiskerLeft k M _ ν) q β)) =
      X.singularKronecker k n (X.singularCup k u ν p q n h α β) := by
  rw [singularCap_def, singularKronecker_def, singularKronecker_def, TauCeti.singularCup_def]
  exact TauCeti.ChainComplex.cap_comp_kronecker_of_isIso _ _ ν p q n h α β

end TopCat

namespace TopPair

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N N' L : C}
  [∀ J : Type w, PreservesColimitsOfShape (Discrete J) (tensorLeft M)]

/-- **The Kronecker pairing of a relative singular cap product**, `⟨ψ, x ⌢ α⟩ = ⟨α ⌣ β, x⟩`: for
a pair `(X, A)`, a relative class `α ∈ Hᵖ(X, A; R, M)` capped along `u` and a pairing
`μ : M ⊗ S ⟶ L` with a relative class `x ∈ Hₙ(X, A; T)`, `n = p + q`, and absolute classes
`ψ ∈ H^q(X; L, N')` and `β ∈ H^q(X; S, N)` related as in
`TopCat.singularCap_comp_singularKronecker_of_homologyMap_eq`, evaluating `ψ` on `x ⌢ α` is
evaluating on `x` the relative cup product `α ⌣ β ∈ Hⁿ(X, A; T, N')` along the relative
Alexander–Whitney diagonal `P.alexanderWhitneyDiagonal u` and `ν`. -/
theorem singularCap_comp_singularKronecker_of_homologyMap_eq (P : TopPair.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ L)
    (ν : M ⊗ N ⟶ N') (p q n : ℕ) (h : p + q = n) (α : P.singularCohomology R k M p)
    (ψ : P.fst.singularCohomology L k N' q) (β : P.fst.singularCohomology S k N q)
    (hψ : homologyMap (K := P.fst.singularCochainComplex L k N')
        (L := ChainComplex.linearYonedaObj
          (((tensorLeft M).mapHomologicalComplex _).obj
            ((TopCat.toSSet.obj P.fst).chainComplex S)) k N')
        ((TauCeti.ChainComplex.linearYonedaFunctor k N').map
          ((TopCat.toSSet.obj P.fst).chainComplexPairing μ).op) q ψ =
      homologyMap (ChainComplex.linearYonedaObjWhiskerLeft k M _ ν) q β) :
    P.singularCap k u μ p q n h α ≫ P.fst.singularKronecker k q ψ =
      P.singularKronecker k n
        (TauCeti.ChainComplex.cup k (P.alexanderWhitneyDiagonal u) ν p q n h α β) := by
  rw [singularCap_def, singularKronecker_def, TopCat.singularKronecker_def]
  exact TauCeti.ChainComplex.cap_comp_kronecker_of_homologyMap_eq _ _ ν p q n h α ψ β hψ

/-- **The Kronecker pairing of a relative singular cap product along an invertible pairing**:
the relative form of `TopCat.singularCap_comp_singularKronecker_of_isIso`. -/
theorem singularCap_comp_singularKronecker_of_isIso (P : TopPair.{w}) (k : Type*)
    [CommRing k] [Linear k C] [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ S ⟶ L) [IsIso μ]
    (ν : M ⊗ N ⟶ N') (p q n : ℕ) (h : p + q = n) (α : P.singularCohomology R k M p)
    (β : P.fst.singularCohomology S k N q) :
    P.singularCap k u μ p q n h α ≫ P.fst.singularKronecker k q
        (homologyMap (K := ChainComplex.linearYonedaObj
            (((tensorLeft M).mapHomologicalComplex _).obj
              ((TopCat.toSSet.obj P.fst).chainComplex S)) k N')
          (L := P.fst.singularCochainComplex L k N')
          ((TauCeti.ChainComplex.linearYonedaFunctor k N').map
            (inv ((TopCat.toSSet.obj P.fst).chainComplexPairing μ)).op) q
          (homologyMap (ChainComplex.linearYonedaObjWhiskerLeft k M _ ν) q β)) =
      P.singularKronecker k n
        (TauCeti.ChainComplex.cup k (P.alexanderWhitneyDiagonal u) ν p q n h α β) := by
  rw [singularCap_def, singularKronecker_def, TopCat.singularKronecker_def]
  exact TauCeti.ChainComplex.cap_comp_kronecker_of_isIso _ _ ν p q n h α β

end TopPair
