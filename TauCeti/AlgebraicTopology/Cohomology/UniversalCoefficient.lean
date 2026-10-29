/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.Algebra.Category.ModuleCat.Projective.Dimension
public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The universal coefficient theorem for singular cohomology

Let `k` be a hereditary commutative ring, expressed by requiring every `k`-module to have
projective dimension at most one. This holds for principal ideal domains, for instance `ℤ`
(`ModuleCat.hasProjectiveDimensionLE_one_of_isPrincipalIdealRing`). Let `R` be a projective
`k`-module, for instance `k` itself, and let `M` be any `k`-module. For a topological space `X`,
the singular chain modules `Cₙ(X; R) = ⨁ R` are projective (`SSet.projective_chainComplex_X`).
Their cycles are then projective and split off the terms
(`TauCeti.Algebra.Homology.HomologicalComplex.ProjectiveDimension`). These are the hypotheses
of the algebraic universal coefficient sequence
(`TauCeti.Algebra.Homology.UniversalCoefficient.Basic`), so

`0 ⟶ Ext¹(Hₙ(X; R), M) ⟶ Hⁿ⁺¹(X; R, M) ⟶ Hom(Hₙ₊₁(X; R), M) ⟶ 0`

is exact, where the second map is the Kronecker map `TopCat.singularKronecker` evaluating
cohomology classes on homology classes.  The sequence splits, and the Kronecker map is surjective
in every degree; in degree `0` it is bijective (`TopCat.singularKronecker_bijective_zero`).  Both
maps are natural in `X`.  The splitting `TopCat.singularKroneckerSection`, and the resulting
decomposition `TopCat.singularUniversalCoefficientEquiv`, depend on a chosen retraction of the
cycles in each degree and need not be natural in `X`.

With `k = R = ℤ` this is the classical sequence
`0 ⟶ Ext(Hₙ(X; ℤ), M) ⟶ Hⁿ⁺¹(X; M) ⟶ Hom(Hₙ₊₁(X; ℤ), M) ⟶ 0` for an abelian group `M`.  For an
injective coefficient module the `Ext¹` term vanishes and the Kronecker map is an isomorphism over
any ring (`TopCat.singularKroneckerEquiv`).

Over an arbitrary commutative ring `k` the cycles of the singular chain complex need not split off,
and there is no such short exact sequence in general.  It survives, with vanishing `Ext¹` term,
when the homology is projective: if `R` and every `Hₙ(X; R)` are projective, the singular chain
complex is a complex of projective modules with projective homology, so its cycles are projective
and split off (`ChainComplex.isSplitMono_iCycles_of_projective_homology`), and the Kronecker map
is an isomorphism `Hⁿ(X; R, M) ≃ₗ[k] Hom(Hₙ(X; R), M)` in every degree
(`TopCat.singularKroneckerEquivOfProjectiveHomology`).

## Main declarations

* `TopCat.singularKronecker_bijective_of_projective_homology` and
  `TopCat.singularKroneckerEquivOfProjectiveHomology`: over any commutative ring, the Kronecker
  map is an isomorphism when the coefficients and the homology are projective.
* `TopPair.singularKronecker_bijective_of_projective_homology` and
  `TopPair.singularKroneckerEquivOfProjectiveHomology`: the same for relative cohomology of a
  pair whose relative homology is projective.
* `TopCat.singularExtToCohomology`: the map `Ext¹(Hₙ(X; R), M) →ₗ[k] Hⁿ⁺¹(X; R, M)`, computed on
  extension classes by `TopCat.singularExtToCohomology_extClass_comp_mk₀`.
* `TopCat.singularExtToCohomology_injective` and
  `TopCat.exact_singularExtToCohomology_singularKronecker`: exactness at the first two places.
* `TopCat.singularKroneckerSection` and `TopCat.singularKronecker_singularKroneckerSection`: a
  `k`-linear right inverse of the Kronecker map, so that `TopCat.singularKronecker_surjective`
  gives exactness at the last place and the sequence splits.
* `TopCat.singularUniversalCoefficientEquiv`: the resulting decomposition
  `Hⁿ⁺¹(X; R, M) ≃ₗ[k] Ext¹(Hₙ(X; R), M) × Hom(Hₙ₊₁(X; R), M)`.
* `TopCat.singularExtToCohomology_naturality`: naturality of the first map in `X`; the naturality
  of the Kronecker map is `TopCat.singularKronecker_naturality`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Abelian

universe w

namespace TopCat

section ProjectiveHomology

variable {k : Type w} [CommRing k] (X : TopCat.{w}) (R M : ModuleCat.{w} k) [Module.Projective k R]
  [hX : ∀ n, Projective (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X)]

/-- **The universal coefficient theorem with projective homology**, over any commutative ring `k`:
for a projective coefficient module `R`, if the singular homology modules `Hₙ(X; R)` are all
projective, the Kronecker map `Hⁿ(X; R, M) →ₗ[k] (Hₙ(X; R) ⟶ M)` is bijective in every degree,
for every module `M`.  The singular chain modules are projective, so the cycles split off and the
`Ext¹` term of the universal coefficient sequence vanishes. -/
theorem singularKronecker_bijective_of_projective_homology (n : ℕ) :
    Function.Bijective (X.singularKronecker (R := R) (M := M) k n) := by
  -- `Hₙ(X; R)` is by definition the homology of the singular chain complex `C(X; R)`.
  have (n : ℕ) : Projective (((toSSet.obj X).chainComplex R).homology n) := hX n
  rw [singularKronecker_def]
  exact TauCeti.ChainComplex.kronecker_bijective_of_projective_homology n

/-- **The universal coefficient isomorphism with projective homology**: over any commutative ring,
for a projective coefficient module `R` such that every `Hₙ(X; R)` is projective, the Kronecker
map is a `k`-linear equivalence `Hⁿ(X; R, M) ≃ₗ[k] (Hₙ(X; R) ⟶ M)`.  This applies to `R = k`
whenever every `Hₙ(X; k)` is a free `k`-module, as for spheres. -/
def singularKroneckerEquivOfProjectiveHomology (n : ℕ) :
    X.singularCohomology R k M n ≃ₗ[k]
      (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X ⟶ M) :=
  LinearEquiv.ofBijective _ (X.singularKronecker_bijective_of_projective_homology R M n)

/-- The equivalence `TopCat.singularKroneckerEquivOfProjectiveHomology` is the Kronecker map. -/
@[simp]
lemma singularKroneckerEquivOfProjectiveHomology_apply (n : ℕ)
    (α : X.singularCohomology R k M n) :
    X.singularKroneckerEquivOfProjectiveHomology R M n α = X.singularKronecker k n α :=
  (rfl)

end ProjectiveHomology

section Hereditary

variable {k : Type w} [CommRing k] [∀ V : ModuleCat.{w} k, HasProjectiveDimensionLE V 1]
  (X : TopCat.{w}) (R M : ModuleCat.{w} k) [Module.Projective k R]

/-- **The `Ext` term of the universal coefficient sequence** of singular cohomology over a
hereditary commutative ring, the `k`-linear map `Ext¹(Hₙ(X; R), M) →ₗ[k] Hⁿ⁺¹(X; R, M)`.  It is the
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

/-- **The characterization of `TopCat.singularExtToCohomology`**: the class in
`Ext¹(Hₙ(X; R), M)` of a morphism `β : Bₙ ⟶ M` out of the singular boundaries
`Bₙ = ker(Zₙ ⟶ Hₙ(X; R))` goes to the class of the cocycle `Cₙ₊₁(X; R) ⟶ Bₙ ⟶ M`. -/
lemma singularExtToCohomology_extClass_comp_mk₀ (n : ℕ)
    (β : kernel (((toSSet.obj X).chainComplex R).homologyπ n) ⟶ M)
    (φ : (X.singularCochainComplex R k M).cycles (n + 1))
    (hφ : (X.singularCochainComplex R k M).iCycles (n + 1) φ =
      ((toSSet.obj X).chainComplex R).toBoundaries (n + 1) n ≫ β) :
    X.singularExtToCohomology R M n
        ((TauCeti.kernelSequence_shortExact
          (((toSSet.obj X).chainComplex R).homologyπ n)).extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      (X.singularCochainComplex R k M).homologyπ (n + 1) φ :=
  TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀ (n + 1) n β φ hφ

/-- **Injectivity in the universal coefficient sequence**: over a hereditary commutative ring,
the map
`Ext¹(Hₙ(X; R), M) →ₗ[k] Hⁿ⁺¹(X; R, M)` is injective. -/
theorem singularExtToCohomology_injective (n : ℕ) :
    Function.Injective (X.singularExtToCohomology R M n) :=
  TauCeti.ChainComplex.extToHomology_injective rfl

/-- **Exactness in the middle of the universal coefficient sequence**: over a hereditary commutative
ring, a class in `Hⁿ⁺¹(X; R, M)` evaluates to zero on `Hₙ₊₁(X; R)` exactly when it comes from
`Ext¹(Hₙ(X; R), M)`. -/
theorem exact_singularExtToCohomology_singularKronecker (n : ℕ) :
    Function.Exact (X.singularExtToCohomology R M n)
      (X.singularKronecker (R := R) (M := M) k (n + 1)) := by
  rw [singularKronecker_def]
  exact TauCeti.ChainComplex.exact_extToHomology_kronecker rfl

/-- **The splitting of the universal coefficient sequence** of singular cohomology over a
hereditary commutative ring: a `k`-linear right inverse `Hom(Hₙ(X; R), M) →ₗ[k] Hⁿ(X; R, M)` of the
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

/-- **Surjectivity in the universal coefficient sequence**: over a hereditary commutative ring,
every
morphism `Hₙ(X; R) ⟶ M` is the evaluation of a class in `Hⁿ(X; R, M)`. -/
theorem singularKronecker_surjective (n : ℕ) :
    Function.Surjective (X.singularKronecker (R := R) (M := M) k n) :=
  fun g ↦ ⟨X.singularKroneckerSection R M n g, X.singularKronecker_singularKroneckerSection R M n g⟩

/-- **The splitting of the universal coefficient sequence** of singular cohomology over a
hereditary commutative ring: a `k`-linear equivalence
`Hⁿ⁺¹(X; R, M) ≃ₗ[k] Ext¹(Hₙ(X; R), M) × Hom(Hₙ₊₁(X; R), M)` whose second component is the
Kronecker map (`TopCat.singularUniversalCoefficientEquiv_apply_snd`) and whose inverse restricts
to `TopCat.singularExtToCohomology` on the first factor
(`TopCat.singularUniversalCoefficientEquiv_symm_inl`).  It is built from the section
`TopCat.singularKroneckerSection` and is not natural in `X`. -/
def singularUniversalCoefficientEquiv (n : ℕ) :
    X.singularCohomology R k M (n + 1) ≃ₗ[k]
      Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1 ×
        (((singularHomologyFunctor (ModuleCat.{w} k) (n + 1)).obj R).obj X ⟶ M) :=
  ((X.exact_singularExtToCohomology_singularKronecker R M n).splitSurjectiveEquiv
    (X.singularExtToCohomology_injective R M n)
    ⟨X.singularKroneckerSection R M (n + 1),
      LinearMap.ext (X.singularKronecker_singularKroneckerSection R M (n + 1))⟩).1

/-- The inverse of the splitting `TopCat.singularUniversalCoefficientEquiv` restricts to the
inclusion `TopCat.singularExtToCohomology` of the `Ext` term on the first factor. -/
@[simp]
lemma singularUniversalCoefficientEquiv_symm_inl (n : ℕ)
    (e : Ext.{w} (((singularHomologyFunctor (ModuleCat.{w} k) n).obj R).obj X) M 1) :
    (X.singularUniversalCoefficientEquiv R M n).symm (e, 0) = X.singularExtToCohomology R M n e :=
  (LinearMap.congr_fun
    ((X.exact_singularExtToCohomology_singularKronecker R M n).splitSurjectiveEquiv
      (X.singularExtToCohomology_injective R M n) _).property.left e).symm

/-- The second component of the splitting `TopCat.singularUniversalCoefficientEquiv` is the
Kronecker map. -/
@[simp]
lemma singularUniversalCoefficientEquiv_apply_snd (n : ℕ)
    (x : X.singularCohomology R k M (n + 1)) :
    (X.singularUniversalCoefficientEquiv R M n x).2 = X.singularKronecker k (n + 1) x :=
  (LinearMap.congr_fun
    ((X.exact_singularExtToCohomology_singularKronecker R M n).splitSurjectiveEquiv
      (X.singularExtToCohomology_injective R M n) _).property.right x).symm

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

end Hereditary

end TopCat

namespace TopPair

variable {k : Type w} [CommRing k] (P : TopPair.{w}) (R M : ModuleCat.{w} k) [Module.Projective k R]
  [hP : ∀ n, Projective (P.singularHomology R n)]

/-- **The relative universal coefficient theorem with projective homology**, over any commutative
ring `k`: for a projective coefficient module `R`, if the relative singular homology modules
`Hₙ(X, A; R)` of a pair are all projective, the relative Kronecker map
`Hⁿ(X, A; R, M) →ₗ[k] (Hₙ(X, A; R) ⟶ M)` is bijective in every degree, for every module `M`.  The
relative singular chain modules are retracts of the absolute ones, hence projective. -/
theorem singularKronecker_bijective_of_projective_homology (n : ℕ) :
    Function.Bijective (P.singularKronecker (R := R) (M := M) k n) := by
  -- `Hₙ(X, A; R)` is by definition the homology of the relative singular chain complex.
  have (n : ℕ) : Projective ((P.singularChainComplex R).homology n) := hP n
  rw [singularKronecker_def]
  exact TauCeti.ChainComplex.kronecker_bijective_of_projective_homology n

/-- **The relative universal coefficient isomorphism with projective homology**: over any
commutative ring, for a projective coefficient module `R` such that every relative homology module
`Hₙ(X, A; R)` is projective, the relative Kronecker map is a `k`-linear equivalence
`Hⁿ(X, A; R, M) ≃ₗ[k] (Hₙ(X, A; R) ⟶ M)`. -/
def singularKroneckerEquivOfProjectiveHomology (n : ℕ) :
    P.singularCohomology R k M n ≃ₗ[k] (P.singularHomology R n ⟶ M) :=
  LinearEquiv.ofBijective _ (P.singularKronecker_bijective_of_projective_homology R M n)

/-- The equivalence `TopPair.singularKroneckerEquivOfProjectiveHomology` is the relative Kronecker
map. -/
@[simp]
lemma singularKroneckerEquivOfProjectiveHomology_apply (n : ℕ)
    (α : P.singularCohomology R k M n) :
    P.singularKroneckerEquivOfProjectiveHomology R M n α = P.singularKronecker k n α :=
  (rfl)

end TopPair
