/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Homology.PrincipalIdealRing
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The universal coefficient theorem for singular cohomology over a principal ideal domain

Let `k` be a principal ideal domain, for instance `ℤ`, let `R` be a projective `k`-module, for
instance `k` itself, and let `M` be any `k`-module.  For a topological space `X`, the singular
chain modules `Cₙ(X; R) = ⨁ R` are projective (`SSet.projective_chainComplex_X`).  Over a
principal ideal domain the cycles of such a complex are then free and split off its terms
(`TauCeti.Algebra.Homology.PrincipalIdealRing`).  These are the hypotheses of the algebraic
universal coefficient sequence (`TauCeti.Algebra.Homology.UniversalCoefficient.Basic`), so

`0 ⟶ Ext¹(Hₙ(X; R), M) ⟶ Hⁿ⁺¹(X; R, M) ⟶ Hom(Hₙ₊₁(X; R), M) ⟶ 0`

is exact, where the second map is the Kronecker map `TopCat.singularKronecker` evaluating
cohomology classes on homology classes.  The sequence splits, and the Kronecker map is surjective
in every degree, including degree `0`.  Both maps are natural in `X`.  The splitting
`TopCat.singularKroneckerSection` depends on a chosen retraction of the cycles in each degree and
need not be natural in `X`.

With `k = R = ℤ` this is the classical sequence
`0 ⟶ Ext(Hₙ(X; ℤ), M) ⟶ Hⁿ⁺¹(X; M) ⟶ Hom(Hₙ₊₁(X; ℤ), M) ⟶ 0` for an abelian group `M`.  For an
injective coefficient module the `Ext¹` term vanishes and the Kronecker map is an isomorphism over
any ring (`TopCat.singularKroneckerEquiv`).

## Main declarations

* `TopCat.singularExtToCohomology`: the map `Ext¹(Hₙ(X; R), M) →ₗ[k] Hⁿ⁺¹(X; R, M)`.
* `TopCat.singularExtToCohomology_injective` and
  `TopCat.exact_singularExtToCohomology_singularKronecker`: exactness at the first two places.
* `TopCat.singularKroneckerSection` and `TopCat.singularKronecker_singularKroneckerSection`: a
  `k`-linear right inverse of the Kronecker map, so that `TopCat.singularKronecker_surjective`
  gives exactness at the last place and the sequence splits.
* `TopCat.singularExtToCohomology_naturality`: naturality of the first map in `X`; the naturality
  of the Kronecker map is `TopCat.singularKronecker_naturality`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Abelian

universe w

namespace TopCat

variable {k : Type w} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k]
  (X : TopCat.{w}) (R M : ModuleCat.{w} k) [Module.Projective k R]

/-- **The `Ext` term of the universal coefficient sequence** of singular cohomology over a
principal ideal domain, the `k`-linear map `Ext¹(Hₙ(X; R), M) →ₗ[k] Hⁿ⁺¹(X; R, M)`.  It is the
algebraic map `TauCeti.ChainComplex.extToHomology` of the singular chain complex: an extension
class represented by a morphism `β : Bₙ ⟶ M` out of the singular boundaries goes to the class of
the cocycle `Cₙ₊₁(X; R) ⟶ Bₙ ⟶ M`. -/
def singularExtToCohomology (n : ℕ) :
    Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1 →ₗ[k]
      X.singularCohomology R k M (n + 1) :=
  TauCeti.ChainComplex.extToHomology k ((toSSet.obj X).chainComplex R) M (n + 1) n

/-- The `Ext` term of the universal coefficient sequence of singular cohomology is the algebraic
map `TauCeti.ChainComplex.extToHomology` of the singular chain complex. -/
lemma singularExtToCohomology_def (n : ℕ) :
    X.singularExtToCohomology R M n =
      TauCeti.ChainComplex.extToHomology k ((toSSet.obj X).chainComplex R) M (n + 1) n :=
  (rfl)

/-- **Injectivity in the universal coefficient sequence**: over a principal ideal domain, the map
`Ext¹(Hₙ(X; R), M) →ₗ[k] Hⁿ⁺¹(X; R, M)` is injective. -/
theorem singularExtToCohomology_injective (n : ℕ) :
    Function.Injective (X.singularExtToCohomology R M n) :=
  TauCeti.ChainComplex.extToHomology_injective rfl

/-- **Exactness in the middle of the universal coefficient sequence**: over a principal ideal
domain, a class in `Hⁿ⁺¹(X; R, M)` evaluates to zero on `Hₙ₊₁(X; R)` exactly when it comes from
`Ext¹(Hₙ(X; R), M)`. -/
theorem exact_singularExtToCohomology_singularKronecker (n : ℕ) :
    Function.Exact (X.singularExtToCohomology R M n)
      (X.singularKronecker (R := R) (M := M) k (n + 1)) := by
  rw [singularKronecker_def]
  exact TauCeti.ChainComplex.exact_extToHomology_kronecker rfl

/-- **The splitting of the universal coefficient sequence** of singular cohomology over a
principal ideal domain: a `k`-linear right inverse `Hom(Hₙ(X; R), M) →ₗ[k] Hⁿ(X; R, M)` of the
Kronecker map.  It sends `g` to the class of the cocycle `Cₙ(X; R) ⟶ Zₙ ⟶ Hₙ(X; R) ⟶ M`, through
a chosen retraction of the inclusion of the singular cycles, and need not be natural in `X`. -/
def singularKroneckerSection (n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X ⟶ M) →ₗ[k]
      X.singularCohomology R k M n :=
  TauCeti.ChainComplex.kroneckerSection k ((toSSet.obj X).chainComplex R) M n

/-- `TopCat.singularKroneckerSection` is a right inverse of the Kronecker map. -/
@[simp]
lemma singularKronecker_singularKroneckerSection (n : ℕ)
    (g : ((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X ⟶ M) :
    X.singularKronecker k n (X.singularKroneckerSection R M n g) = g := by
  rw [singularKronecker_def]
  exact TauCeti.ChainComplex.kronecker_kroneckerSection (X := (toSSet.obj X).chainComplex R) n g

/-- **Surjectivity in the universal coefficient sequence**: over a principal ideal domain, every
morphism `Hₙ(X; R) ⟶ M` is the evaluation of a class in `Hⁿ(X; R, M)`. -/
theorem singularKronecker_surjective (n : ℕ) :
    Function.Surjective (X.singularKronecker (R := R) (M := M) k n) :=
  fun g ↦ ⟨X.singularKroneckerSection R M n g, X.singularKronecker_singularKroneckerSection R M n g⟩

variable {X} in
/-- **Naturality of the universal coefficient sequence** in the space: for a continuous map
`f : X ⟶ Y`, pulling an extension back along `f_* : Hₙ(X; R) ⟶ Hₙ(Y; R)` and then including it in
the cohomology of `X` is including it in the cohomology of `Y` and then pulling back along `f`. -/
lemma singularExtToCohomology_naturality {Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (e : Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj Y) M 1) :
    X.singularExtToCohomology R M n
        ((Ext.mk₀ (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).map f)).comp e
          (zero_add 1)) =
      TopCat.singularCohomologyMap f (n + 1) (Y.singularExtToCohomology R M n e) :=
  TauCeti.ChainComplex.extToHomology_naturality (SSet.chainComplexMap (toSSet.map f) R) (n + 1) n e

end TopCat
