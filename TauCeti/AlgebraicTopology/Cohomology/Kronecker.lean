/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Basic

/-!
# The Kronecker map of singular cohomology

Let `C` be a `k`-linear abelian category with coproducts. For a space `X`, the Kronecker map of
singular cochains is the Kronecker map `TauCeti.ChainComplex.kronecker` of the singular chain
complex of `X` with coefficients in `R`: it evaluates a singular cohomology class in
`Hⁿ(X; R, M)` on singular homology classes in `Hₙ(X; R)`, giving a `k`-linear map
`Hⁿ(X; R, M) →ₗ[k] (Hₙ(X; R) ⟶ M)`. On the classes of a cocycle `φ` and a cycle `z` it is `φ`
evaluated on `z`. It is natural in `X`: evaluating the pull-back `f^*α` of a class along a
continuous map `f` is evaluating `α` after pushing forward along `f`.

For coefficients in modules over a commutative ring `k`, take `C := ModuleCat k` and `R := k`;
then this is the evaluation `⟨α, x⟩ ∈ M` of a class `α ∈ Hⁿ(X; M)` on a class `x ∈ Hₙ(X; k)`,
which is how cohomology classes are paired with fundamental classes of manifolds. When `M` is an
injective object, for instance a vector space over a field `k`, the Kronecker map is a
`k`-linear equivalence `Hⁿ(X; M) ≃ₗ[k] Hom(Hₙ(X; k), M)`: the universal coefficient theorem in
the case where its `Ext¹`-term vanishes.

## Main definitions and results

* `TopCat.singularKronecker`: the Kronecker map of singular cohomology, the Kronecker map of the
  singular chain complex (`TopCat.singularKronecker_def`), with
  `TopCat.singularKronecker_homologyπ` computing it on classes of cocycles and cycles and
  `TopCat.singularKronecker_naturality` its naturality.
* `TopCat.singularKroneckerEquiv`: for an injective coefficient object `M`, the Kronecker map is a
  `k`-linear equivalence.
* `TopCat.singularKronecker_bijective_zero`: in degree zero the Kronecker map is bijective for
  every coefficient object.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] {R M : C}

/-- **The Kronecker map of singular cohomology** `Hⁿ(X; R, M) →ₗ[k] (Hₙ(X; R) ⟶ M)`: it sends the
class of a singular cocycle `φ` to the morphism which on the class of a singular cycle is `φ`
evaluated on that cycle (`TopCat.singularKronecker_homologyπ`). -/
def singularKronecker (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] (n : ℕ) :
    X.singularCohomology R k M n →ₗ[k] (((singularHomologyFunctor C n).obj R).obj X ⟶ M) :=
  TauCeti.ChainComplex.kronecker k ((toSSet.obj X).chainComplex R) M n

/-- The Kronecker map of singular cohomology is the Kronecker map of the singular chain complex. -/
lemma singularKronecker_def (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] (n : ℕ) :
    X.singularKronecker (R := R) (M := M) k n =
      TauCeti.ChainComplex.kronecker k ((toSSet.obj X).chainComplex R) M n :=
  (rfl)

/-- The Kronecker map on the classes of a singular cocycle and a singular cycle is the cocycle
evaluated on the cycle. -/
@[simp, reassoc]
lemma singularKronecker_homologyπ (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] (n : ℕ)
    (φ : (X.singularCochainComplex R k M).cycles n) :
    ((toSSet.obj X).chainComplex R).homologyπ n ≫
        X.singularKronecker k n ((X.singularCochainComplex R k M).homologyπ n φ) =
      ((toSSet.obj X).chainComplex R).iCycles n ≫
        (X.singularCochainComplex R k M).iCycles n φ :=
  TauCeti.ChainComplex.kronecker_homologyπ n φ

/-- **Naturality of the Kronecker map**, `⟨f^*α, x⟩ = ⟨α, f_*x⟩`: for a continuous map
`f : X ⟶ Y`, evaluating the pull-back of a singular cohomology class of `Y` is evaluating the class
after pushing forward along `f`. -/
lemma singularKronecker_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (k : Type*) [Ring k]
    [Linear k C] (n : ℕ) (α : Y.singularCohomology R k M n) :
    X.singularKronecker k n (TopCat.singularCohomologyMap f n α) =
      ((singularHomologyFunctor C n).obj R).map f ≫ Y.singularKronecker k n α :=
  TauCeti.ChainComplex.kronecker_naturality (SSet.chainComplexMap (toSSet.map f) R) n α

/-- **The universal coefficient theorem for injective coefficients**: for an injective object
`M`, the Kronecker map of singular cohomology is a `k`-linear equivalence
`Hⁿ(X; R, M) ≃ₗ[k] (Hₙ(X; R) ⟶ M)`. -/
def singularKroneckerEquiv (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] [Injective M]
    (n : ℕ) :
    X.singularCohomology R k M n ≃ₗ[k] (((singularHomologyFunctor C n).obj R).obj X ⟶ M) :=
  TauCeti.ChainComplex.kroneckerEquiv k ((toSSet.obj X).chainComplex R) M n

/-- **The universal coefficient theorem in degree zero**: for every coefficient object `M`, the
Kronecker map `H⁰(X; R, M) →ₗ[k] (H₀(X; R) ⟶ M)` is bijective, as no differential leaves the
degree-zero singular chains. -/
theorem singularKronecker_bijective_zero (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C] :
    Function.Bijective (X.singularKronecker (R := R) (M := M) k 0) :=
  TauCeti.ChainComplex.kronecker_bijective_of_isIso 0

/-- The equivalence `TopCat.singularKroneckerEquiv` is the Kronecker map. -/
@[simp]
lemma singularKroneckerEquiv_apply (X : TopCat.{w}) (k : Type*) [Ring k] [Linear k C]
    [Injective M] (n : ℕ) (α : X.singularCohomology R k M n) :
    X.singularKroneckerEquiv k n α = X.singularKronecker k n α :=
  TauCeti.ChainComplex.kroneckerEquiv_apply n α

end TopCat
