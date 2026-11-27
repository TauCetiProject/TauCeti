/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.AlgebraicGeometry.IntersectionNumber.Weight
public import TauCeti.AlgebraicGeometry.SpecialFiber.Picard
import Mathlib.Algebra.Order.Field.Rat
import TauCeti.LinearAlgebra.Matrix.MulVec

/-!
# Line-bundle specialization on regular models

Let `R` be a discrete valuation ring with fraction field `K` and residue field `k`, and let
`toBase : X ⟶ Spec R` be a proper regular integral Noetherian scheme of dimension at most two
whose generic point lies over the generic point of `Spec R`. Building on generic-fibre Picard
excision (`TauCeti.AlgebraicGeometry.SpecialFiber.Picard`) and following
[Stacks, Chapter 55](https://stacks.math.columbia.edu/tag/0C2P) (specifically
[Tag 0CEI](https://stacks.math.columbia.edu/tag/0CEI)) and Liu, Section 9.1, this file establishes:

* **Multidegrees and weighted intersection matrix** (`reducedSpecialFiberMultidegree`,
  `specialFiberMultidegreeOnFiber`, `specialFiberMultidegree`,
  `specialFiberWeightedIntersectionMatrix`, `specialFiberMultidegree_comp_verticalLineBundleLinear`,
  `specialFiberMultidegree_verticalLineBundleLinear`): compatible `ℤ`-linear multidegree
  homomorphisms across `X_{s,red}`, `X_s`, and `X` sending `∏_i [𝒪_X(C_i)]^{v_i}` to `v ᵥ* A'`
  where `a'_{ij} = a_{ij} / w_j`.
* **Picard specialization and torsion lifting** (`specialFiberPicardSpecialization`,
  `mem_ker_specialFiberPicardSpecialization_iff`,
  `exists_dvd_specialFiberMultiplicity_and_pow_eq_one`,
  `existsUnique_pullback_genericFiberι_eq_and_specialFiberMultidegree_eq_zero_and_pow_eq_one`):
  descent of `specialFiberMultidegree` to `Pic(X_K) → (Component → ℤ) ⧸ range(vecMulLinear A')`,
  characterization of its kernel by multidegree-zero extensions to `X`, and unique `n`-torsion
  multidegree-zero model lifts on a proper flat regular model with connected special fibre when `n`
  is coprime to every common divisor of the component multiplicities.

## References

* [The Stacks Project, Chapter 55](https://stacks.math.columbia.edu/tag/0C2P):
  [Section 55.9](https://stacks.math.columbia.edu/tag/0C5Y)
  ([Tag 0C64](https://stacks.math.columbia.edu/tag/0C64)–
  [Tag 0C66](https://stacks.math.columbia.edu/tag/0C66)),
  [Tag 0C7H](https://stacks.math.columbia.edu/tag/0C7H), and
  [Tag 0CEI](https://stacks.math.columbia.edu/tag/0CEI).
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Order
open Set.Finite (mem_toFinset)
open scoped Matrix
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.LineBundleClass (intersectionNumber pullback pullbackHom)
open AlgebraicGeometry.Scheme.IdealSheafData (vanishingIdeal inclusion
  isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular)

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-! ### Multidegrees across `X`, `X_s`, and `(X_s)_red`, and the weighted intersection matrix -/

section Multidegree

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R]
  {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]

/-- The **weighted intersection matrix** `a'_{ij} = a_{ij} / w_j` of the special fibre of a regular
model, whose `(i, j)`-entry is `(C_j · C_i)_k / w_j`. When `A` is symmetric, `w_j ∣ a_{ij}` and
`a'_{ij}` is the degree of `𝒪_X(C_i)|_{C_j}` over the constant field `κ_j = H⁰(C_j, 𝒪_{C_j})`. -/
def specialFiberWeightedIntersectionMatrix [TauCeti.AlgebraicGeometry.IsRegular X]
    (hX : ∀ x : X, coheight x ≤ 2) (hη : toBase (genericPoint X) ≠ closedPoint R) :
    Matrix (toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset
      (toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset ℤ :=
  Matrix.of fun i j ↦ toBase.specialFiberIntersectionMatrix hX hη i j /
    (toBase.specialFiberWeight ((mem_toFinset _).mp j.property) : ℤ)

/-- Entrywise formula for `specialFiberWeightedIntersectionMatrix`. -/
@[simp]
theorem specialFiberWeightedIntersectionMatrix_apply [TauCeti.AlgebraicGeometry.IsRegular X]
    (hX : ∀ x : X, coheight x ≤ 2) (hη : toBase (genericPoint X) ≠ closedPoint R) (i j) :
    toBase.specialFiberWeightedIntersectionMatrix hX hη i j =
      toBase.specialFiberIntersectionMatrix hX hη i j /
        (toBase.specialFiberWeight ((mem_toFinset _).mp j.property) : ℤ) :=
  (rfl)

variable [IsProper toBase] (hX : ∀ x : X, coheight x ≤ 2)
  (hη : toBase (genericPoint X) ≠ closedPoint R)
  (h₁ : toBase.SpecialFiberCohomologyFiniteDimensional 1)

/-- `ℤ`-linear multidegree homomorphism `Additive (LineBundleClass Y) →ₗ[ℤ] (_ → ℤ)` for a
scheme `Y` receiving morphisms from the special-fibre components `C_i`. -/
private def componentMultidegreeLinear {Y : Scheme.{u}}
    (f : ∀ i : (toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
      (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subscheme ⟶ Y) :
    Additive (LineBundleClass Y) →ₗ[ℤ]
      ((toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :=
  let hom : Additive (LineBundleClass Y) →+
      ((toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :=
    { toFun a i :=
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        intersectionNumber (ResidueField R) (f i) a.toMul /
          (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ)
      map_zero' := funext fun i ↦ by
        let := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        rw [toMul_zero, LineBundleClass.intersectionNumber_one, Int.zero_ediv, Pi.zero_apply]
      map_add' a b := funext fun i ↦ by
        have hi : toBase i.val = closedPoint R := (mem_toFinset _).mp i.property
        let := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hi)
        have := isProper_subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hi)
        have := toBase.relativeDimensionLE_subscheme_vanishingIdeal_closure_singleton hX
          (fun h ↦ one_ne_zero (i.val.property.symm.trans (coheight_eq_zero.mpr h))) hi
        have := toBase.finiteDimensional_cohomology_zero_subscheme_closure_singleton hi
        have := h₁.finiteDimensional i.val hi
        have hdvd := toBase.specialFiberWeight_dvd_intersectionNumber hi (f i) a.toMul
        rw [toMul_add, LineBundleClass.intersectionNumber_mul_of_isIntegral,
          Int.add_ediv_of_dvd_left hdvd, Pi.add_apply] }
  hom.toIntLinearMap

/-- Componentwise evaluation of `componentMultidegreeLinear`. -/
private lemma componentMultidegreeLinear_apply {Y : Scheme.{u}} {f}
    (a : Additive (LineBundleClass Y)) (i) :
    toBase.componentMultidegreeLinear hX hη h₁ f a i =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (f i) a.toMul /
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) := rfl

/-- Multiplying the `i`-th coordinate of `componentMultidegreeLinear` by `w_i` recovers the
intersection number over the residue field. -/
private lemma componentMultidegreeLinear_mul_specialFiberWeight {Y : Scheme.{u}} {f}
    (a : Additive (LineBundleClass Y)) (i) :
    toBase.componentMultidegreeLinear hX hη h₁ f a i *
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (f i) a.toMul := by
  have hi : toBase i.val = closedPoint R := (mem_toFinset _).mp i.property
  rw [componentMultidegreeLinear_apply]
  exact Int.ediv_mul_cancel (toBase.specialFiberWeight_dvd_intersectionNumber hi (f i) a.toMul)

/-- `a` lies in `ker (componentMultidegreeLinear f)` if and only if every component intersection
number vanishes. -/
private lemma mem_ker_componentMultidegreeLinear_iff {Y : Scheme.{u}} {f}
    (a : Additive (LineBundleClass Y)) :
    a ∈ LinearMap.ker (toBase.componentMultidegreeLinear hX hη h₁ f) ↔
      ∀ i,
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        intersectionNumber (ResidueField R) (f i) a.toMul = 0 :=
  ⟨fun h i ↦ by
    have hm := toBase.componentMultidegreeLinear_mul_specialFiberWeight hX hη h₁
      (f := f) a i
    rw [LinearMap.mem_ker.mp h, Pi.zero_apply, zero_mul] at hm
    exact hm.symm,
   fun h ↦ LinearMap.mem_ker.mpr <| funext fun i ↦ by
    rw [componentMultidegreeLinear_apply, h i, Int.zero_ediv, Pi.zero_apply]⟩

/-- Linear functoriality of `componentMultidegreeLinear` along a morphism `g : Y ⟶ Z`. -/
private lemma componentMultidegreeLinear_comp_picardPullbackLinearMap {Y Z : Scheme.{u}} {f}
    {g : Y ⟶ Z} {f'} (hfg : ∀ i, f i ≫ g = f' i) :
    toBase.componentMultidegreeLinear hX hη h₁ f ∘ₗ g.picardPullbackLinearMap =
      toBase.componentMultidegreeLinear hX hη h₁ f' :=
  LinearMap.ext fun a ↦ funext fun i ↦ by
    let := subschemeOverResidueField
      (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
          ((mem_toFinset _).mp i.property))
    rw [LinearMap.comp_apply, componentMultidegreeLinear_apply, componentMultidegreeLinear_apply,
      toMul_picardPullbackLinearMap_apply,
      LineBundleClass.intersectionNumber_pullback, hfg i]

/-- The **multidegree on the reduced special fibre** `X_{s,red}`, sending `c` to the tuple of
degrees `deg_{κ_i}(c|_{C_i}) = (c · C_i)_k / w_i`. -/
def reducedSpecialFiberMultidegree :
    Additive (LineBundleClass (reducedSpecialFiber R toBase)) →ₗ[ℤ]
      ((toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :=
  toBase.componentMultidegreeLinear hX hη h₁ fun i ↦
    subschemeToReducedSpecialFiber
      ((ker_reducedSpecialFiberι_eq_radical R toBase).trans_le
        (toBase.radical_ker_specialFiberι_le_vanishingIdeal_closure_singleton
          ((mem_toFinset _).mp i.property)))

/-- Componentwise formula for `reducedSpecialFiberMultidegree`. -/
@[simp]
theorem reducedSpecialFiberMultidegree_apply
    (c : Additive (LineBundleClass (reducedSpecialFiber R toBase))) (i) :
    toBase.reducedSpecialFiberMultidegree hX hη h₁ c i =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (subschemeToReducedSpecialFiber
        ((ker_reducedSpecialFiberι_eq_radical R toBase).trans_le
          (toBase.radical_ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property)))) c.toMul /
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) := by
  rw [reducedSpecialFiberMultidegree, componentMultidegreeLinear_apply]

/-- Multiplying the `i`-th coordinate of `reducedSpecialFiberMultidegree c` by `w_i` recovers the
intersection number of `c` with `C_i` over the residue field. -/
theorem reducedSpecialFiberMultidegree_mul_specialFiberWeight
    (c : Additive (LineBundleClass (reducedSpecialFiber R toBase))) (i) :
    toBase.reducedSpecialFiberMultidegree hX hη h₁ c i *
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (subschemeToReducedSpecialFiber
        ((ker_reducedSpecialFiberι_eq_radical R toBase).trans_le
          (toBase.radical_ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property)))) c.toMul := by
  rw [reducedSpecialFiberMultidegree]
  exact toBase.componentMultidegreeLinear_mul_specialFiberWeight hX hη h₁ c i

/-- A line-bundle class on `X_{s,red}` lies in `ker reducedSpecialFiberMultidegree` if and only if
its intersection number with every component `C_i` vanishes. -/
theorem mem_ker_reducedSpecialFiberMultidegree_iff
    (c : Additive (LineBundleClass (reducedSpecialFiber R toBase))) :
    c ∈ LinearMap.ker (toBase.reducedSpecialFiberMultidegree hX hη h₁) ↔
      ∀ i : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        intersectionNumber (ResidueField R) (subschemeToReducedSpecialFiber
          ((ker_reducedSpecialFiberι_eq_radical R toBase).trans_le
            (toBase.radical_ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property)))) c.toMul = 0 := by
  rw [reducedSpecialFiberMultidegree]
  exact toBase.mem_ker_componentMultidegreeLinear_iff hX hη h₁ c

/-- The **multidegree on the scheme-theoretic special fibre** `X_s`, sending `b` to its component
degrees `deg_{κ_i}(b|_{C_i})`. -/
def specialFiberMultidegreeOnFiber :
    Additive (LineBundleClass (specialFiber R toBase).left) →ₗ[ℤ]
      ((toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :=
  toBase.componentMultidegreeLinear hX hη h₁ fun i ↦
    subschemeToSpecialFiber (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
      ((mem_toFinset _).mp i.property))

/-- Componentwise formula for `specialFiberMultidegreeOnFiber` (not `@[simp]` because `specialFiber`
is an `Over.pullback` abbreviation, so `simp` rewrites its scheme inside the domain of
`DFunLike.coe`). -/
theorem specialFiberMultidegreeOnFiber_apply
    (b : Additive (LineBundleClass (specialFiber R toBase).left)) (i) :
    toBase.specialFiberMultidegreeOnFiber hX hη h₁ b i =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (subschemeToSpecialFiber
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
          ((mem_toFinset _).mp i.property))) b.toMul /
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) := by
  rw [specialFiberMultidegreeOnFiber, componentMultidegreeLinear_apply]

/-- Multiplying the `i`-th coordinate of `specialFiberMultidegreeOnFiber b` by `w_i` recovers the
intersection number of `b` with `C_i` over the residue field. -/
theorem specialFiberMultidegreeOnFiber_mul_specialFiberWeight
    (b : Additive (LineBundleClass (specialFiber R toBase).left)) (i) :
    toBase.specialFiberMultidegreeOnFiber hX hη h₁ b i *
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (subschemeToSpecialFiber
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
          ((mem_toFinset _).mp i.property))) b.toMul := by
  rw [specialFiberMultidegreeOnFiber]
  exact toBase.componentMultidegreeLinear_mul_specialFiberWeight hX hη h₁ b i

/-- A line-bundle class on `X_s` lies in `ker specialFiberMultidegreeOnFiber` if and only if its
intersection number with every component `C_i` vanishes. -/
theorem mem_ker_specialFiberMultidegreeOnFiber_iff
    (b : Additive (LineBundleClass (specialFiber R toBase).left)) :
    b ∈ LinearMap.ker (toBase.specialFiberMultidegreeOnFiber hX hη h₁) ↔
      ∀ i : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        intersectionNumber (ResidueField R) (subschemeToSpecialFiber
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))) b.toMul = 0 := by
  rw [specialFiberMultidegreeOnFiber]
  exact toBase.mem_ker_componentMultidegreeLinear_iff hX hη h₁ b

/-- The **special-fibre multidegree** of a line-bundle class on `X`, sending `a` to the tuple
`i ↦ (a · C_i)_k / w_i` of degrees of `a|_{C_i}` over the constant fields `κ_i`. -/
def specialFiberMultidegree :
    Additive (LineBundleClass X) →ₗ[ℤ]
      ((toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :=
  toBase.componentMultidegreeLinear hX hη h₁ fun i ↦
    (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subschemeι

/-- Componentwise formula for `specialFiberMultidegree`. -/
@[simp]
theorem specialFiberMultidegree_apply (a : Additive (LineBundleClass X)) (i) :
    toBase.specialFiberMultidegree hX hη h₁ a i =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R)
        (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subschemeι a.toMul /
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) := by
  rw [specialFiberMultidegree, componentMultidegreeLinear_apply]

/-- `specialFiberMultidegreeOnFiber` factors linearly through pullback to `X_{s,red}`. -/
@[simp]
theorem
  reducedSpecialFiberMultidegree_comp_picardPullbackLinearMap_reducedSpecialFiberToSpecialFiber :
    toBase.reducedSpecialFiberMultidegree hX hη h₁ ∘ₗ
        (reducedSpecialFiberToSpecialFiber R toBase).picardPullbackLinearMap =
      toBase.specialFiberMultidegreeOnFiber hX hη h₁ := by
  rw [reducedSpecialFiberMultidegree, specialFiberMultidegreeOnFiber]
  exact toBase.componentMultidegreeLinear_comp_picardPullbackLinearMap hX hη h₁ fun _ ↦
    subschemeToReducedSpecialFiber_reducedSpecialFiberToSpecialFiber _

/-- `specialFiberMultidegree` factors linearly through pullback along `X_s ⟶ X`. -/
@[simp]
theorem specialFiberMultidegreeOnFiber_comp_picardPullbackLinearMap_specialFiberι :
    toBase.specialFiberMultidegreeOnFiber hX hη h₁ ∘ₗ
        (specialFiberι R toBase).picardPullbackLinearMap =
      toBase.specialFiberMultidegree hX hη h₁ := by
  rw [specialFiberMultidegreeOnFiber, specialFiberMultidegree]
  exact toBase.componentMultidegreeLinear_comp_picardPullbackLinearMap hX hη h₁ fun _ ↦
    subschemeToSpecialFiber_specialFiberι _

/-- `specialFiberMultidegree` factors linearly through pullback along `X_{s,red} ⟶ X`. -/
@[simp]
theorem reducedSpecialFiberMultidegree_comp_picardPullbackLinearMap_reducedSpecialFiberι :
    toBase.reducedSpecialFiberMultidegree hX hη h₁ ∘ₗ
        (reducedSpecialFiberι R toBase).picardPullbackLinearMap =
      toBase.specialFiberMultidegree hX hη h₁ := by
  rw [reducedSpecialFiberMultidegree, specialFiberMultidegree]
  exact toBase.componentMultidegreeLinear_comp_picardPullbackLinearMap hX hη h₁ fun _ ↦
    subschemeToReducedSpecialFiber_reducedSpecialFiberι _

/-- Multiplying the `i`-th coordinate of `specialFiberMultidegree a` by `w_i` recovers
`(a · C_i)_k` over the residue field. -/
theorem specialFiberMultidegree_mul_specialFiberWeight (a : Additive (LineBundleClass X)) (i) :
    toBase.specialFiberMultidegree hX hη h₁ a i *
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R)
        (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subschemeι a.toMul := by
  rw [specialFiberMultidegree]
  exact toBase.componentMultidegreeLinear_mul_specialFiberWeight hX hη h₁ a i

/-- A line-bundle class on `X` lies in `ker specialFiberMultidegree` if and only if its
intersection number with every component `C_i` vanishes. -/
theorem mem_ker_specialFiberMultidegree_iff (a : Additive (LineBundleClass X)) :
    a ∈ LinearMap.ker (toBase.specialFiberMultidegree hX hη h₁) ↔
      ∀ i : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        intersectionNumber (ResidueField R)
          (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subschemeι a.toMul = 0 := by
  rw [specialFiberMultidegree]
  exact toBase.mem_ker_componentMultidegreeLinear_iff hX hη h₁ a

section RegularMatrix

variable [TauCeti.AlgebraicGeometry.IsRegular X]

include h₁ in
/-- Local wrapper around `specialFiberIntersectionMatrix_isSymm` to supply `H⁰` finiteness from
properness. -/
private lemma specialFiberIntersectionMatrix_isSymm_of :
    (toBase.specialFiberIntersectionMatrix hX hη).IsSymm :=
  toBase.specialFiberIntersectionMatrix_isSymm hX hη
    (fun _ ↦ toBase.finiteDimensional_cohomology_zero_subscheme_closure_singleton)
    h₁.finiteDimensional

include h₁ in
/-- The weight `w_j` of `C_j` divides every entry `a_{ij}` in column `j` of the intersection
matrix. -/
theorem specialFiberWeight_dvd_specialFiberIntersectionMatrix_right (i j) :
    (toBase.specialFiberWeight ((mem_toFinset _).mp j.property) : ℤ) ∣
      toBase.specialFiberIntersectionMatrix hX hη i j := by
  rw [(toBase.specialFiberIntersectionMatrix_isSymm_of hX hη h₁).apply j i]
  exact toBase.specialFiberWeight_dvd_specialFiberIntersectionMatrix hX hη j i

include h₁ in
/-- Multiplying column `j` of `specialFiberWeightedIntersectionMatrix` by `w_j` recovers
`specialFiberIntersectionMatrix`. -/
theorem specialFiberWeightedIntersectionMatrix_mul_specialFiberWeight (i j) :
    toBase.specialFiberWeightedIntersectionMatrix hX hη i j *
        (toBase.specialFiberWeight ((mem_toFinset _).mp j.property) : ℤ) =
      toBase.specialFiberIntersectionMatrix hX hη i j :=
  Int.ediv_mul_cancel
    (toBase.specialFiberWeight_dvd_specialFiberIntersectionMatrix_right hX hη h₁ i j)

/-- **Multidegree of a component line bundle.** The multidegree of `[𝒪_X(C_i)]` is the `i`-th row
of `specialFiberWeightedIntersectionMatrix`. -/
theorem specialFiberMultidegree_inv_mk_toInvertibleSheaf (i) :
    toBase.specialFiberMultidegree hX hη h₁ (Additive.ofMul (LineBundleClass.mk
        (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
          i.val.property).toInvertibleSheaf)⁻¹) =
      toBase.specialFiberWeightedIntersectionMatrix hX hη i := funext fun j ↦ by
  rw [specialFiberMultidegree_apply, toMul_ofMul,
    ← toBase.specialFiberIntersectionMatrix_apply hX hη j i,
    (toBase.specialFiberIntersectionMatrix_isSymm_of hX hη h₁).apply i j,
    specialFiberWeightedIntersectionMatrix_apply]

/-- Simp normal form of `specialFiberMultidegree_inv_mk_toInvertibleSheaf` after
`LineBundleClass.inv_mk`. -/
@[simp]
theorem specialFiberMultidegree_mk_toInvertibleSheaf_dual (i) :
    toBase.specialFiberMultidegree hX hη h₁ (Additive.ofMul (LineBundleClass.mk
        (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
          i.val.property).toInvertibleSheaf.dual)) =
      toBase.specialFiberWeightedIntersectionMatrix hX hη i := by
  rw [← LineBundleClass.inv_mk, specialFiberMultidegree_inv_mk_toInvertibleSheaf]

/-- **Multidegree of a vertical Cartier divisor.** Composing `specialFiberMultidegree` with
`verticalLineBundleLinear` equals multiplication by `specialFiberWeightedIntersectionMatrix`. -/
theorem specialFiberMultidegree_comp_verticalLineBundleLinear :
    toBase.specialFiberMultidegree hX hη h₁ ∘ₗ
        toBase.verticalLineBundleLinear hX hη =
      (toBase.specialFiberWeightedIntersectionMatrix hX hη).vecMulLinear := by
  classical
  refine LinearMap.pi_ext fun i r ↦ ?_
  have hsingle : (Pi.single i r : _ → ℤ) = r • Pi.single i (1 : ℤ) := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [LinearMap.comp_apply, Matrix.vecMulLinear_apply, Matrix.single_vecMul]
  conv_lhs => rw [hsingle, map_smul, verticalLineBundleLinear_single]
  rw [map_smul, specialFiberMultidegree_inv_mk_toInvertibleSheaf]
  rfl

/-- Pointwise form of `specialFiberMultidegree_comp_verticalLineBundleLinear`. -/
@[simp]
theorem specialFiberMultidegree_verticalLineBundleLinear
    (v : (toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :
    toBase.specialFiberMultidegree hX hη h₁
        (toBase.verticalLineBundleLinear hX hη v) =
      v ᵥ* toBase.specialFiberWeightedIntersectionMatrix hX hη :=
  LinearMap.congr_fun
    (toBase.specialFiberMultidegree_comp_verticalLineBundleLinear hX hη h₁) v

end RegularMatrix

end Multidegree

/-! ### Generic-fibre Picard specialization and torsion lifting -/

section Specialization

variable {R : Type u} (K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))
  [IsIntegral X] [IsNoetherian X] [TauCeti.AlgebraicGeometry.IsRegular X] [IsProper toBase]
  (hX : ∀ x : X, coheight x ≤ 2) (hη : toBase (genericPoint X) ≠ closedPoint R)
  (h₁ : toBase.SpecialFiberCohomologyFiniteDimensional 1)

/-- Every model line-bundle class in the kernel of `Pic(X) → Pic(X_K)` has multidegree in the row
space of `specialFiberWeightedIntersectionMatrix`. -/
theorem specialFiberMultidegree_mem_range_of_pullback_genericFiberι_eq_one {a : LineBundleClass X}
    (ha : pullback (genericFiberι R K toBase) a = 1) :
    toBase.specialFiberMultidegree hX hη h₁ (Additive.ofMul a) ∈
      LinearMap.range (toBase.specialFiberWeightedIntersectionMatrix hX hη).vecMulLinear := by
  have ha' : Additive.ofMul a ∈ LinearMap.range (toBase.verticalLineBundleLinear hX hη) := by
    rw [toBase.range_verticalLineBundleLinear_eq_ker_picardPullbackLinearMap K hX hη,
      LinearMap.mem_ker, picardPullbackLinearMap_ofMul, ha, ofMul_one]
  obtain ⟨v, hv⟩ := ha'
  exact ⟨v, by rw [← hv, toBase.specialFiberMultidegree_verticalLineBundleLinear,
    Matrix.vecMulLinear_apply]⟩

omit [IsProper toBase] in
include hX in
/-- Surjectivity of the additive generic-fibre pullback homomorphism on `LineBundleClass`. -/
private lemma toAdditive_pullbackHom_genericFiberι_surjective :
    Function.Surjective (genericFiberι R K toBase).picardPullbackLinearMap.toAddMonoidHom :=
  fun b ↦ let ⟨a, ha⟩ := toBase.pullback_genericFiberι_surjective_of_isRegular K hX b.toMul
  ⟨Additive.ofMul a, Additive.toMul.injective (by
    rwa [LinearMap.toAddMonoidHom_coe, toMul_picardPullbackLinearMap_apply, toMul_ofMul])⟩

/-- The **Picard specialization homomorphism**
([Stacks, Tag 0CEI](https://stacks.math.columbia.edu/tag/0CEI); Liu, Section 9.1) from `Pic(X_K)`
to the cokernel of the weighted intersection matrix `A'`, obtained by lifting a class on `X_K` to
the regular model `X` and taking its multidegree on `(X_s)_red` modulo vertical classes. -/
def specialFiberPicardSpecialization :
    Additive (LineBundleClass (genericFiber R K toBase).left) →+
      (((toBase.finite_setOf_base_eq_closedPoint
            (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) ⧸
        LinearMap.range (toBase.specialFiberWeightedIntersectionMatrix hX hη).vecMulLinear) := by
  let p := (genericFiberι R K toBase).picardPullbackLinearMap.toAddMonoidHom
  let S := LinearMap.range (toBase.specialFiberWeightedIntersectionMatrix hX hη).vecMulLinear
  let φ : Additive (LineBundleClass X) →+ _ ⧸ S :=
    S.mkQ.toAddMonoidHom.comp (toBase.specialFiberMultidegree hX hη h₁).toAddMonoidHom
  have hker : p.ker ≤ φ.ker := fun a ha ↦ by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      LinearMap.toAddMonoidHom_coe, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← ofMul_toMul a]
    refine toBase.specialFiberMultidegree_mem_range_of_pullback_genericFiberι_eq_one
      K hX hη h₁ ?_
    simpa only [p, LinearMap.toAddMonoidHom_coe, toMul_picardPullbackLinearMap_apply,
      toMul_zero] using congrArg Additive.toMul (AddMonoidHom.mem_ker.mp ha)
  exact p.liftOfSurjective (toBase.toAdditive_pullbackHom_genericFiberι_surjective K hX) ⟨φ, hker⟩

/-- `specialFiberPicardSpecialization` sends the restriction of `a : LineBundleClass X` to the
quotient class of `specialFiberMultidegree a` (not `@[simp]` because `genericFiber` is an
`Over.pullback` abbreviation, so `simp` rewrites its scheme inside the domain of
`DFunLike.coe`). -/
theorem specialFiberPicardSpecialization_pullback (a : LineBundleClass X) :
    toBase.specialFiberPicardSpecialization K hX hη h₁
        (Additive.ofMul (pullback (genericFiberι R K toBase) a)) =
      Submodule.Quotient.mk (toBase.specialFiberMultidegree hX hη h₁ (Additive.ofMul a)) := by
  let p := (genericFiberι R K toBase).picardPullbackLinearMap.toAddMonoidHom
  have hpa : Additive.ofMul (pullback (genericFiberι R K toBase) a) = p (Additive.ofMul a) :=
    (picardPullbackLinearMap_ofMul (genericFiberι R K toBase) a).symm
  rw [specialFiberPicardSpecialization, hpa, AddMonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- **Exact kernel of `specialFiberPicardSpecialization`**
([Stacks, Tag 0CEI](https://stacks.math.columbia.edu/tag/0CEI); Liu, Section 9.1). A line-bundle
class `b` on `X_K` lies in `ker specialFiberPicardSpecialization` if and only if it extends to a
class `a` on the regular model `X` of multidegree zero on `(X_s)_red`. -/
theorem mem_ker_specialFiberPicardSpecialization_iff
    {b : LineBundleClass (genericFiber R K toBase).left} :
    Additive.ofMul b ∈ (toBase.specialFiberPicardSpecialization K hX hη h₁).ker ↔
      ∃ a : LineBundleClass X,
        pullback (genericFiberι R K toBase) a = b ∧
          toBase.specialFiberMultidegree hX hη h₁ (Additive.ofMul a) = 0 := by
  refine ⟨fun hb ↦ ?_, fun ⟨a, haK, ha⟩ ↦ ?_⟩
  · obtain ⟨a₀, rfl⟩ := toBase.pullback_genericFiberι_surjective_of_isRegular K hX b
    rw [AddMonoidHom.mem_ker, specialFiberPicardSpecialization_pullback,
      Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hb
    obtain ⟨v, hv⟩ := hb
    have hvert :
        pullback (genericFiberι R K toBase)
          (toBase.verticalLineBundleLinear hX hη v).toMul = 1 := by
      have hmem : toBase.verticalLineBundleLinear hX hη v ∈
          LinearMap.ker (genericFiberι R K toBase).picardPullbackLinearMap := by
        rw [← toBase.range_verticalLineBundleLinear_eq_ker_picardPullbackLinearMap K hX hη]
        exact LinearMap.mem_range.mpr ⟨v, rfl⟩
      simpa using congrArg Additive.toMul (LinearMap.mem_ker.mp hmem)
    refine ⟨a₀ * (toBase.verticalLineBundleLinear hX hη v).toMul⁻¹,
      by rw [LineBundleClass.pullback_mul, LineBundleClass.pullback_inv, hvert, inv_one, mul_one],
      ?_⟩
    rw [ofMul_mul, ofMul_inv, map_add, map_neg, ofMul_toMul,
      toBase.specialFiberMultidegree_verticalLineBundleLinear,
      ← Matrix.vecMulLinear_apply, hv, add_neg_cancel]
  · rw [← haK, AddMonoidHom.mem_ker, specialFiberPicardSpecialization_pullback, ha,
      Submodule.Quotient.mk_zero]

section Connected

variable [Flat toBase] {π : R}

include h₁ in
/-- On a regular proper flat model with connected special fibre, an integer vector `v` in the left
kernel of `specialFiberWeightedIntersectionMatrix` is a rational multiple of the multiplicity
vector `m`. -/
private lemma exists_rat_mul_specialFiberMultiplicity_of_vecMul_eq_zero
    (hπ : maximalIdeal R = Ideal.span {π})
    (hconn : _root_.IsPreconnected (toBase ⁻¹' {closedPoint R}))
    {v : (toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ}
    (hv : v ᵥ* toBase.specialFiberWeightedIntersectionMatrix hX hη = 0) :
    ∃ c : ℚ, ∀ j, (v j : ℚ) = c * (toBase.specialFiberMultiplicity π j : ℚ) := by
  have hreg : IsSMulRegular R π :=
    IsSMulRegular.of_ne_zero (toBase.ne_zero_of_base_ne_closedPoint hη hπ)
  have hAv : toBase.specialFiberIntersectionMatrix hX hη *ᵥ v = 0 := funext fun j ↦ by
    have hw := congrArg (· * (toBase.specialFiberWeight
      ((mem_toFinset _).mp j.property) : ℤ)) (congrFun hv j)
    rw [Pi.zero_apply, zero_mul, Matrix.vecMul, dotProduct, Finset.sum_mul] at hw
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← hw]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [(toBase.specialFiberIntersectionMatrix_isSymm_of hX hη h₁).apply i j,
      ← toBase.specialFiberWeightedIntersectionMatrix_mul_specialFiberWeight hX hη h₁ i j,
      mul_comm _ (v i), ← mul_assoc]
  have hmul : (toBase.specialFiberIntersectionMatrix hX hη).map (Int.cast : ℤ → ℚ) *ᵥ
      (fun j ↦ (v j : ℚ)) = 0 := by
    rw [Matrix.map_intCast_mulVec, hAv]
    exact funext fun _ ↦ Int.cast_zero
  exact (toBase.dotProduct_mulVec_specialFiberIntersectionMatrix_eq_zero_iff
    hX hη (fun _ ↦ toBase.finiteDimensional_cohomology_zero_subscheme_closure_singleton)
    h₁.finiteDimensional hπ hreg hconn (fun j ↦ (v j : ℚ))).mp (by rw [hmul, dotProduct_zero])

/-- **Isotropic vertical kernel on a connected special fibre.** On a regular proper flat model with
connected special fibre `X_s = ∑_i m_i C_i`, any model line-bundle class `a` that is trivial on
`X_K` and has multidegree zero on `(X_s)_red` satisfies `a ^ d = 1` for a positive integer `d`
dividing every component multiplicity `m_j`. -/
theorem exists_dvd_specialFiberMultiplicity_and_pow_eq_one
    (hπ : maximalIdeal R = Ideal.span {π})
    (hconn : _root_.IsPreconnected (toBase ⁻¹' {closedPoint R})) {a : LineBundleClass X}
    (haK : pullback (genericFiberι R K toBase) a = 1)
    (ha0 : toBase.specialFiberMultidegree hX hη h₁ (Additive.ofMul a) = 0) :
    ∃ d : ℕ, 0 < d ∧
      (∀ j : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        d ∣ toBase.specialFiberMultiplicity π j) ∧ a ^ d = 1 := by
  have hreg : IsSMulRegular R π :=
    IsSMulRegular.of_ne_zero (toBase.ne_zero_of_base_ne_closedPoint hη hπ)
  have ha_mem : Additive.ofMul a ∈ LinearMap.range (toBase.verticalLineBundleLinear hX hη) := by
    rw [toBase.range_verticalLineBundleLinear_eq_ker_picardPullbackLinearMap K hX hη,
      LinearMap.mem_ker, picardPullbackLinearMap_ofMul, haK, ofMul_one]
  obtain ⟨v, hv⟩ := ha_mem
  have ha_eq : a = ∏ i, (LineBundleClass.mk
      (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
        i.val.property).toInvertibleSheaf)⁻¹ ^ v i := by
    have := congrArg Additive.toMul hv
    rwa [toMul_verticalLineBundleLinear_apply, toMul_ofMul, eq_comm] at this
  rw [← hv, toBase.specialFiberMultidegree_verticalLineBundleLinear] at ha0
  obtain ⟨c, hc⟩ := toBase.exists_rat_mul_specialFiberMultiplicity_of_vecMul_eq_zero
    hX hη h₁ hπ hconn ha0
  have hrel (j) : v j * (c.den : ℤ) = c.num * (toBase.specialFiberMultiplicity π j : ℤ) :=
    Int.cast_injective (α := ℚ) <| by
      rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, hc j, mul_right_comm,
        Rat.mul_den_eq_num]
  refine ⟨c.den, c.den_pos, fun j ↦ ?_, ?_⟩
  · exact c.reduced.symm.dvd_of_dvd_mul_left (by
      simpa only [Int.natAbs_natCast, Int.natAbs_mul] using
        Int.natAbs_dvd_natAbs.mpr ⟨v j, (hrel j).symm.trans (mul_comm _ _)⟩)
  · rw [ha_eq]
    have hsp := toBase.prod_inv_mk_toInvertibleSheaf_vanishingIdeal_pow_eq_one hX hη hπ hreg
    rw [← Finset.prod_coe_sort] at hsp
    rw [← Finset.prod_pow, ← one_zpow c.num, ← hsp, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← zpow_natCast, ← zpow_mul, hrel i, mul_comm c.num, zpow_mul, zpow_natCast]

/-- An `n`-torsion model line bundle on a regular proper flat model with connected special fibre
that restricts to `1` on `X_K` and has multidegree `0` on `(X_s)_red` is trivial whenever `n` is
coprime to every common divisor of the component multiplicities. -/
theorem eq_one_of_pullback_genericFiberι_eq_one_of_coprime_specialFiberMultiplicity
    (hπ : maximalIdeal R = Ideal.span {π})
    (hconn : _root_.IsPreconnected (toBase ⁻¹' {closedPoint R})) {n : ℕ}
    (hcop : ∀ d : ℕ, (∀ j : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        d ∣ toBase.specialFiberMultiplicity π j) → Nat.Coprime n d)
    {a : LineBundleClass X} (haK : pullback (genericFiberι R K toBase) a = 1)
    (ha0 : toBase.specialFiberMultidegree hX hη h₁ (Additive.ofMul a) = 0)
    (han : a ^ n = 1) : a = 1 := by
  obtain ⟨d, -, hdvd, had⟩ :=
    toBase.exists_dvd_specialFiberMultiplicity_and_pow_eq_one K hX hη h₁ hπ hconn haK ha0
  exact (pow_eq_one_iff_of_coprime (hcop d hdvd)).mp ⟨han, had⟩

/-- **Unique `n`-torsion multidegree-zero lifting**
([Stacks, Chapter 55](https://stacks.math.columbia.edu/tag/0C2P),
[Tag 0CEI](https://stacks.math.columbia.edu/tag/0CEI); Liu, Section 9.1). On a regular proper flat
model with connected special fibre `X_s = ∑_i m_i C_i`, if `n` is coprime to every common divisor
of the multiplicities `m_i`, every `n`-torsion generic-fibre class `b` in
`ker specialFiberPicardSpecialization` admits a unique `n`-torsion extension `a` to `X` of
multidegree zero on `(X_s)_red`. -/
theorem existsUnique_pullback_genericFiberι_eq_and_specialFiberMultidegree_eq_zero_and_pow_eq_one
    (hπ : maximalIdeal R = Ideal.span {π})
    (hconn : _root_.IsPreconnected (toBase ⁻¹' {closedPoint R})) {n : ℕ}
    (hcop : ∀ d : ℕ, (∀ j : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        d ∣ toBase.specialFiberMultiplicity π j) → Nat.Coprime n d)
    {b : LineBundleClass (genericFiber R K toBase).left} (hbn : b ^ n = 1)
    (hbker : Additive.ofMul b ∈ (toBase.specialFiberPicardSpecialization K hX hη h₁).ker) :
    ∃! a : LineBundleClass X,
      pullback (genericFiberι R K toBase) a = b ∧
        toBase.specialFiberMultidegree hX hη h₁ (Additive.ofMul a) = 0 ∧ a ^ n = 1 := by
  obtain ⟨a₀, ha₀K, ha₀0⟩ :=
    (toBase.mem_ker_specialFiberPicardSpecialization_iff K hX hη h₁).mp hbker
  obtain ⟨d, -, hdvd, hadn⟩ :=
    toBase.exists_dvd_specialFiberMultiplicity_and_pow_eq_one K hX hη h₁ hπ hconn
      (by rw [LineBundleClass.pullback_pow, ha₀K, hbn])
      (by rw [ofMul_pow, map_nsmul, ha₀0, smul_zero])
  have hnd : (d : ℤ) * Nat.gcdB n d = 1 - (n : ℤ) * Nat.gcdA n d := by
    have h := Nat.gcd_eq_gcd_ab n d; rw [(hcop d hdvd).gcd_eq_one, Nat.cast_one] at h; omega
  let a : LineBundleClass X := a₀ ^ ((d : ℤ) * Nat.gcdB n d)
  have haK : pullback (genericFiberι R K toBase) a = b := by
    rw [LineBundleClass.pullback_zpow, ha₀K, hnd, zpow_sub, zpow_one, zpow_mul, zpow_natCast,
      hbn, one_zpow, inv_one, mul_one]
  have ha0 : toBase.specialFiberMultidegree hX hη h₁ (Additive.ofMul a) = 0 := by
    rw [ofMul_zpow, map_zsmul, ha₀0, smul_zero]
  have han : a ^ n = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_right_comm, mul_comm (d : ℤ) (n : ℤ), zpow_mul, zpow_mul,
      zpow_natCast, zpow_natCast, hadn, one_zpow]
  refine ⟨a, ⟨haK, ha0, han⟩, fun a' ⟨ha'K, ha'0, ha'n⟩ ↦ eq_of_mul_inv_eq_one <|
    toBase.eq_one_of_pullback_genericFiberι_eq_one_of_coprime_specialFiberMultiplicity
      K hX hη h₁ hπ hconn hcop (by simp [ha'K, haK])
      (by rw [ofMul_mul, ofMul_inv, map_add, map_neg, ha'0, ha0, neg_zero, add_zero])
      (by rw [mul_pow, inv_pow, ha'n, han, inv_one, mul_one])⟩

end Connected

end Specialization

end AlgebraicGeometry.Scheme.Hom

end
