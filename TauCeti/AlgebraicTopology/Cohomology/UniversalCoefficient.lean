/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.UniversalCoefficient.Naturality
public import TauCeti.Algebra.Homology.Projective.PID
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# The universal coefficient theorem for singular cohomology over a principal ideal domain

Let `k` be a principal ideal domain (more generally, a principal ideal ring without zero
divisors), let `R` be a projective `k`-module, for instance `R = k`, and let `M` be any `k`-module.
For a topological space `X` and `n : ℕ`, the sequence

`0 ⟶ Ext¹(Hₙ(X; R), M) ⟶ Hⁿ⁺¹(X; R, M) ⟶ Hom(Hₙ₊₁(X; R), M) ⟶ 0`

is exact, and split. The second map is the Kronecker map `TopCat.singularKronecker`, which
evaluates a cohomology class on homology classes; the first is
`TopCat.singularExtToCohomology`. Both maps are natural in `X`. In degree zero the Kronecker map
`H⁰(X; R, M) ⟶ Hom(H₀(X; R), M)` is itself bijective (`TopCat.singularKronecker_bijective_zero`).

This is the universal coefficient theorem of the chain complex `C(X; R)` with coefficients in `M`
(`TauCeti.ChainComplex.extToHomology`). Its hypotheses hold because the singular chain modules
`Cₙ(X; R) = ⨁ R` are projective (`SSet.projective_chainComplex_X`), and submodules of projective
modules over a principal ideal domain are projective, so the cycles of `C(X; R)` are projective
and split off (`HomologicalComplex.isSplitMono_iCycles`).

The splitting `TopCat.singularUniversalCoefficientEquiv` of the sequence depends on a choice of
retraction of the chains onto the cycles. It is not natural in `X`.

## Main declarations

* `TopCat.singularExtToCohomology`: the map `Ext¹(Hₙ(X; R), M) →ₗ[k] Hⁿ⁺¹(X; R, M)`, natural by
  `TopCat.singularExtToCohomology_naturality`.
* `TopCat.singularExtToCohomology_injective`,
  `TopCat.exact_singularExtToCohomology_singularKronecker` and
  `TopCat.singularKronecker_surjective`: exactness of the universal coefficient sequence.
* `TopCat.singularUniversalCoefficientEquiv`: a splitting
  `Hⁿ⁺¹(X; R, M) ≃ₗ[k] Ext¹(Hₙ(X; R), M) × Hom(Hₙ₊₁(X; R), M)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1, Theorem 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Abelian

universe t w u

namespace TopCat

variable {k : Type u} [CommRing k] [NoZeroDivisors k] [IsPrincipalIdealRing k] [Small.{w} k]
  [HasExt.{t} (ModuleCat.{w} k)] {R : ModuleCat.{w} k} [Projective R] {M : ModuleCat.{w} k}

variable (k) in
/-- **The `Ext` term of the universal coefficient sequence** of singular cohomology: the `k`-linear
map `Ext¹(Hₙ(X; R), M) →ₗ[k] Hⁿ⁺¹(X; R, M)`. The class in `Ext¹(Hₙ(X; R), M)` of a morphism
`β : Bₙ ⟶ M` out of the singular boundaries goes to the class of the cocycle
`Cₙ₊₁(X; R) ⟶ Bₙ ⟶ M` (`TopCat.singularExtToCohomology_extClass_comp_mk₀`). -/
def singularExtToCohomology (X : TopCat.{w}) (n : ℕ) :
    Ext.{t} (((singularHomologyFunctor _ n).obj R).obj X) M 1 →ₗ[k]
      X.singularCohomology R k M (n + 1) :=
  TauCeti.ChainComplex.extToHomology k ((toSSet.obj X).chainComplex R) M (n + 1) n

/-- **The characterization of `TopCat.singularExtToCohomology`**: the class in
`Ext¹(Hₙ(X; R), M)` of a morphism `β : Bₙ ⟶ M` out of the singular boundaries
`Bₙ = ker(Zₙ ⟶ Hₙ(X; R))` goes to the class of the cocycle `Cₙ₊₁(X; R) ⟶ Bₙ ⟶ M`. -/
lemma singularExtToCohomology_extClass_comp_mk₀ (X : TopCat.{w}) (n : ℕ)
    (β : kernel (((toSSet.obj X).chainComplex R).homologyπ n) ⟶ M)
    (φ : (X.singularCochainComplex R k M).cycles (n + 1))
    (hφ : (X.singularCochainComplex R k M).iCycles (n + 1) φ =
      kernel.lift _ (((toSSet.obj X).chainComplex R).toCycles (n + 1) n)
        (((toSSet.obj X).chainComplex R).toCycles_comp_homologyπ (n + 1) n) ≫ β) :
    X.singularExtToCohomology k n
        ((TauCeti.kernelSequence_shortExact
          (((toSSet.obj X).chainComplex R).homologyπ n)).extClass.comp (Ext.mk₀ β) (add_zero 1)) =
      (X.singularCochainComplex R k M).homologyπ (n + 1) φ :=
  TauCeti.ChainComplex.extToHomology_extClass_comp_mk₀ (n + 1) n β φ hφ

/-- **Injectivity in the universal coefficient sequence** of singular cohomology:
`Ext¹(Hₙ(X; R), M) ⟶ Hⁿ⁺¹(X; R, M)` is injective. -/
theorem singularExtToCohomology_injective (X : TopCat.{w}) (n : ℕ) :
    Function.Injective (X.singularExtToCohomology (R := R) (M := M) k n) :=
  TauCeti.ChainComplex.extToHomology_injective rfl

/-- **Exactness in the middle of the universal coefficient sequence** of singular cohomology: a
class in `Hⁿ⁺¹(X; R, M)` evaluates to zero on `Hₙ₊₁(X; R)` exactly when it comes from
`Ext¹(Hₙ(X; R), M)`. -/
theorem exact_singularExtToCohomology_singularKronecker (X : TopCat.{w}) (n : ℕ) :
    Function.Exact (X.singularExtToCohomology (R := R) (M := M) k n)
      (X.singularKronecker k (n + 1)) := by
  rw [singularKronecker_def]
  exact TauCeti.ChainComplex.exact_extToHomology_kronecker rfl

omit [HasExt.{t} (ModuleCat.{w} k)] in
/-- **Surjectivity in the universal coefficient sequence** of singular cohomology: every morphism
`Hₙ(X; R) ⟶ M` is the evaluation of a singular cohomology class. -/
theorem singularKronecker_surjective (X : TopCat.{w}) (n : ℕ) :
    Function.Surjective (X.singularKronecker (R := R) (M := M) k n) := by
  rw [singularKronecker_def]
  exact TauCeti.ChainComplex.kronecker_surjective_of_isSplitMono n

/-- **Naturality of the `Ext` term** of the universal coefficient sequence: for a continuous map
`f : X ⟶ Y`, pulling an extension of `Hₙ(Y; R)` back along `f_*` and then including it in
cohomology is including it first and pulling the class back along `f`. -/
lemma singularExtToCohomology_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (e : Ext.{t} (((singularHomologyFunctor _ n).obj R).obj Y) M 1) :
    X.singularExtToCohomology k n
        ((Ext.mk₀ (((singularHomologyFunctor _ n).obj R).map f)).comp e (zero_add 1)) =
      TopCat.singularCohomologyMap f (n + 1) (Y.singularExtToCohomology k n e) :=
  TauCeti.ChainComplex.extToHomology_naturality (SSet.chainComplexMap (toSSet.map f) R)
    (n + 1) n e

variable (k) in
/-- **The splitting of the universal coefficient sequence** of singular cohomology: a `k`-linear
equivalence `Hⁿ⁺¹(X; R, M) ≃ₗ[k] Ext¹(Hₙ(X; R), M) × Hom(Hₙ₊₁(X; R), M)` whose second
component is the Kronecker map (`TopCat.singularUniversalCoefficientEquiv_apply_snd`) and whose
inverse restricts to `TopCat.singularExtToCohomology` on the first factor
(`TopCat.singularUniversalCoefficientEquiv_symm_inl`). It is built from a chosen retraction of
the chains onto the cycles, through `TauCeti.ChainComplex.kroneckerSection`, and is not natural
in `X`. -/
def singularUniversalCoefficientEquiv (X : TopCat.{w}) (n : ℕ) :
    X.singularCohomology R k M (n + 1) ≃ₗ[k]
      Ext.{t} (((singularHomologyFunctor _ n).obj R).obj X) M 1 ×
        (((singularHomologyFunctor _ (n + 1)).obj R).obj X ⟶ M) :=
  ((X.exact_singularExtToCohomology_singularKronecker n).splitSurjectiveEquiv
    (X.singularExtToCohomology_injective n)
    ⟨TauCeti.ChainComplex.kroneckerSection k ((toSSet.obj X).chainComplex R) M (n + 1),
      LinearMap.ext fun g ↦ by
        have h : X.singularKronecker k (n + 1)
            (TauCeti.ChainComplex.kroneckerSection k ((toSSet.obj X).chainComplex R) M (n + 1)
              g) = g := by
          rw [singularKronecker_def]
          exact TauCeti.ChainComplex.kronecker_kroneckerSection
            (X := (toSSet.obj X).chainComplex R) (n + 1) g
        exact h⟩).1

/-- The inverse of the splitting `TopCat.singularUniversalCoefficientEquiv` restricts to the
inclusion `TopCat.singularExtToCohomology` of the `Ext` term on the first factor. -/
@[simp]
lemma singularUniversalCoefficientEquiv_symm_inl (X : TopCat.{w}) (n : ℕ)
    (e : Ext.{t} (((singularHomologyFunctor _ n).obj R).obj X) M 1) :
    (X.singularUniversalCoefficientEquiv k n).symm (e, 0) = X.singularExtToCohomology k n e :=
  (LinearMap.congr_fun ((X.exact_singularExtToCohomology_singularKronecker n).splitSurjectiveEquiv
    (X.singularExtToCohomology_injective n) _).property.left e).symm

/-- The second component of the splitting `TopCat.singularUniversalCoefficientEquiv` is the
Kronecker map. -/
@[simp]
lemma singularUniversalCoefficientEquiv_apply_snd (X : TopCat.{w}) (n : ℕ)
    (x : X.singularCohomology R k M (n + 1)) :
    (X.singularUniversalCoefficientEquiv k n x).2 = X.singularKronecker k (n + 1) x :=
  (LinearMap.congr_fun ((X.exact_singularExtToCohomology_singularKronecker n).splitSurjectiveEquiv
    (X.singularExtToCohomology_injective n) _).property.right x).symm

end TopCat
