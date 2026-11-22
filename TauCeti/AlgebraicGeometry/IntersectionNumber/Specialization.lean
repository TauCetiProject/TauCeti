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
import TauCeti.AlgebraicGeometry.SpecialFiber.Cohomology

/-!
# Line-bundle specialization on regular models

Let `R` be a discrete valuation ring with fraction field `K` and residue field `k`, and let
`toBase : X ⟶ Spec R` be a proper regular integral Noetherian scheme of dimension at most two
whose generic point lies over the generic point of `Spec R`. Building on generic-fibre Picard
excision (`TauCeti.AlgebraicGeometry.SpecialFiber.Picard`) and following
[Stacks, Chapter 55](https://stacks.math.columbia.edu/tag/0C2P) (specifically
[Tag 0CEI](https://stacks.math.columbia.edu/tag/0CEI)) and Liu, Section 9.1, this file establishes:

* **Multidegrees and weighted intersection matrix** (`SpecialFiberCohomologyFiniteDimensional`,
  `componentMultidegreeHom`, `reducedSpecialFiberMultidegree`, `specialFiberMultidegreeOnFiber`,
  `specialFiberMultidegree`, `specialFiberWeightedIntersectionMatrix`,
  `specialFiberMultidegree_prod_zpow`): compatible
  multidegree homomorphisms across `(X_s)_red`, `X_s`, and `X` sending `∏_i [𝒪_X(C_i)]^{v_i}` to
  `v ᵥ* A'` where `a'_{ij} = a_{ij} / w_j`.
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

/-- Every irreducible component `C` of the special fibre of `toBase` has finite-dimensional
`n`-th cohomology `H^n(C, 𝒪_C)` over the residue field of `R`. -/
abbrev SpecialFiberCohomologyFiniteDimensional {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) (n : ℕ) : Prop :=
  ∀ (η : CodimensionOnePoint X) (hc : toBase η = closedPoint R),
    letI :=
      subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hc)
    FiniteDimensional (ResidueField R) (Cohomology (InvertibleSheaf.trivial
      (vanishingIdeal ⟨closure {(η : X)}, isClosed_closure⟩).subscheme).obj n)

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

/-- Multidegree homomorphism `Additive (LineBundleClass Y) →+ (_ → ℤ)` for a scheme `Y` receiving
morphisms from the special-fibre components `C_i`. -/
def componentMultidegreeHom {Y : Scheme.{u}}
    (f : ∀ i : (toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
      (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subscheme ⟶ Y) :
    Additive (LineBundleClass Y) →+
      ((toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) where
  toFun a i :=
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
    let :=
      subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hi)
    have := isProper_subschemeOverResidueField
      (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hi)
    have := toBase.relativeDimensionLE_subscheme_vanishingIdeal_closure_singleton hX
      (fun h ↦ one_ne_zero (i.val.property.symm.trans (coheight_eq_zero.mpr h))) hi
    have := toBase.finiteDimensional_cohomology_trivial_subscheme_closure_singleton hX hi 0
    have := toBase.finiteDimensional_cohomology_trivial_subscheme_closure_singleton hX hi 1
    have hdvd : (toBase.specialFiberWeight hi : ℤ) ∣
        intersectionNumber (ResidueField R) (f i) a.toMul := by
      rw [specialFiberWeight_def]
      exact LineBundleClass.finrank_cohomology_zero_trivial_dvd_intersectionNumber (ResidueField R)
        (f i) (toBase.isField_globalSections_subscheme_closure_singleton hi) a.toMul
    rw [toMul_add, LineBundleClass.intersectionNumber_mul_of_isIntegral,
      Int.add_ediv_of_dvd_left hdvd, Pi.add_apply]

/-- Componentwise evaluation of `componentMultidegreeHom`. -/
theorem componentMultidegreeHom_apply {Y : Scheme.{u}} {f}
    (a : Additive (LineBundleClass Y)) (i) :
    toBase.componentMultidegreeHom hX hη f a i =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (f i) a.toMul /
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) := (rfl)

/-- Multiplying the `i`-th coordinate of `componentMultidegreeHom` by `w_i` recovers the
intersection number over the residue field. -/
theorem componentMultidegreeHom_mul_specialFiberWeight {Y : Scheme.{u}} {f}
    (a : Additive (LineBundleClass Y)) (i) :
    toBase.componentMultidegreeHom hX hη f a i *
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (f i) a.toMul := by
  have hi : toBase i.val = closedPoint R := (mem_toFinset _).mp i.property
  let := subschemeOverResidueField (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton hi)
  refine Int.ediv_mul_cancel (by
    rw [specialFiberWeight_def]
    exact LineBundleClass.finrank_cohomology_zero_trivial_dvd_intersectionNumber (ResidueField R) _
      (toBase.isField_globalSections_subscheme_closure_singleton hi) a.toMul)

/-- `componentMultidegreeHom` vanishes if and only if every component intersection number
vanishes. -/
private lemma componentMultidegreeHom_eq_zero_iff {Y : Scheme.{u}} {f} (a : LineBundleClass Y) :
    toBase.componentMultidegreeHom hX hη f (Additive.ofMul a) = 0 ↔
      ∀ i,
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        intersectionNumber (ResidueField R) (f i) a = 0 :=
  ⟨fun h i ↦ by
    have hm := toBase.componentMultidegreeHom_mul_specialFiberWeight hX hη
      (f := f) (Additive.ofMul a) i
    rw [h, Pi.zero_apply, zero_mul, toMul_ofMul] at hm
    exact hm.symm,
   fun h ↦ funext fun i ↦ by
    rw [componentMultidegreeHom_apply, toMul_ofMul, h i, Int.zero_ediv, Pi.zero_apply]⟩

/-- Functoriality of `componentMultidegreeHom` along a morphism `g : Y ⟶ Z`. -/
theorem componentMultidegreeHom_pullback {Y Z : Scheme.{u}} {f} {g : Y ⟶ Z} {f'}
    (hfg : ∀ i, f i ≫ g = f' i) (a : LineBundleClass Z) :
    toBase.componentMultidegreeHom hX hη f (Additive.ofMul (pullback g a)) =
      toBase.componentMultidegreeHom hX hη f' (Additive.ofMul a) := funext fun i ↦ by
  let := subschemeOverResidueField
    (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton ((mem_toFinset _).mp i.property))
  rw [componentMultidegreeHom_apply, componentMultidegreeHom_apply, toMul_ofMul, toMul_ofMul,
    LineBundleClass.intersectionNumber_pullback, hfg i]

/-- The **multidegree on the reduced special fibre** `(X_s)_red = V(√(𝔪·𝒪_X))`, sending `c` to the
tuple of degrees `deg_{κ_i}(c|_{C_i}) = (c · C_i)_k / w_i`. -/
def reducedSpecialFiberMultidegree :
    Additive (LineBundleClass (specialFiberι R toBase).ker.radical.subscheme) →+
      ((toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :=
  toBase.componentMultidegreeHom hX hη fun i ↦
    inclusion (toBase.radical_ker_specialFiberι_le_vanishingIdeal_closure_singleton
      ((mem_toFinset _).mp i.property))

/-- Componentwise formula for `reducedSpecialFiberMultidegree`. -/
@[simp]
theorem reducedSpecialFiberMultidegree_apply
    (c : Additive (LineBundleClass (specialFiberι R toBase).ker.radical.subscheme)) (i) :
    toBase.reducedSpecialFiberMultidegree hX hη c i =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (inclusion
        (toBase.radical_ker_specialFiberι_le_vanishingIdeal_closure_singleton
          ((mem_toFinset _).mp i.property))) c.toMul /
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) :=
  (rfl)

/-- Multiplying the `i`-th coordinate of `reducedSpecialFiberMultidegree c` by `w_i` recovers the
intersection number of `c` with `C_i` over the residue field. -/
theorem reducedSpecialFiberMultidegree_mul_specialFiberWeight
    (c : Additive (LineBundleClass (specialFiberι R toBase).ker.radical.subscheme)) (i) :
    toBase.reducedSpecialFiberMultidegree hX hη c i *
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (inclusion
        (toBase.radical_ker_specialFiberι_le_vanishingIdeal_closure_singleton
          ((mem_toFinset _).mp i.property))) c.toMul :=
  toBase.componentMultidegreeHom_mul_specialFiberWeight hX hη c i

/-- A line-bundle class on `(X_s)_red` has multidegree zero if and only if its intersection number
with every component `C_i` vanishes. -/
theorem reducedSpecialFiberMultidegree_eq_zero_iff
    (c : LineBundleClass (specialFiberι R toBase).ker.radical.subscheme) :
    toBase.reducedSpecialFiberMultidegree hX hη (Additive.ofMul c) = 0 ↔
      ∀ i : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        intersectionNumber (ResidueField R) (inclusion
          (toBase.radical_ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))) c = 0 :=
  toBase.componentMultidegreeHom_eq_zero_iff hX hη c

/-- The **multidegree on the scheme-theoretic special fibre** `X_s`, sending `b` to its component
degrees `deg_{κ_i}(b|_{C_i})`. -/
def specialFiberMultidegreeOnFiber :
    Additive (LineBundleClass (specialFiber R toBase).left) →+
      ((toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :=
  toBase.componentMultidegreeHom hX hη fun i ↦
    subschemeToSpecialFiber (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
      ((mem_toFinset _).mp i.property))

/-- Componentwise formula for `specialFiberMultidegreeOnFiber` (not `@[simp]` because `specialFiber`
is an `Over.pullback` abbreviation, so `simp` rewrites its scheme inside the domain of
`DFunLike.coe`). -/
theorem specialFiberMultidegreeOnFiber_apply
    (b : Additive (LineBundleClass (specialFiber R toBase).left)) (i) :
    toBase.specialFiberMultidegreeOnFiber hX hη b i =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (subschemeToSpecialFiber
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
          ((mem_toFinset _).mp i.property))) b.toMul /
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) :=
  (rfl)

/-- Multiplying the `i`-th coordinate of `specialFiberMultidegreeOnFiber b` by `w_i` recovers the
intersection number of `b` with `C_i` over the residue field. -/
theorem specialFiberMultidegreeOnFiber_mul_specialFiberWeight
    (b : Additive (LineBundleClass (specialFiber R toBase).left)) (i) :
    toBase.specialFiberMultidegreeOnFiber hX hη b i *
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R) (subschemeToSpecialFiber
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
          ((mem_toFinset _).mp i.property))) b.toMul :=
  toBase.componentMultidegreeHom_mul_specialFiberWeight hX hη b i

/-- A line-bundle class on `X_s` has multidegree zero if and only if its intersection number with
every component `C_i` vanishes. -/
theorem specialFiberMultidegreeOnFiber_eq_zero_iff
    (b : LineBundleClass (specialFiber R toBase).left) :
    toBase.specialFiberMultidegreeOnFiber hX hη (Additive.ofMul b) = 0 ↔
      ∀ i : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        intersectionNumber (ResidueField R) (subschemeToSpecialFiber
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))) b = 0 :=
  toBase.componentMultidegreeHom_eq_zero_iff hX hη b

/-- The **special-fibre multidegree** of a line-bundle class on `X`, sending `a` to the tuple
`i ↦ (a · C_i)_k / w_i` of degrees of `a|_{C_i}` over the constant fields `κ_i`. -/
def specialFiberMultidegree :
    Additive (LineBundleClass X) →+
      ((toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :=
  toBase.componentMultidegreeHom hX hη fun i ↦
    (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subschemeι

/-- Componentwise formula for `specialFiberMultidegree`. -/
@[simp]
theorem specialFiberMultidegree_apply (a : Additive (LineBundleClass X)) (i) :
    toBase.specialFiberMultidegree hX hη a i =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R)
        (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subschemeι a.toMul /
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) :=
  (rfl)

/-- `specialFiberMultidegreeOnFiber` factors through restriction from `X_s` to `(X_s)_red`. -/
theorem specialFiberMultidegreeOnFiber_eq_reducedSpecialFiberMultidegree_pullback
    (b : LineBundleClass (specialFiber R toBase).left) :
    toBase.specialFiberMultidegreeOnFiber hX hη (Additive.ofMul b) =
      toBase.reducedSpecialFiberMultidegree hX hη (Additive.ofMul (pullback
        (subschemeToSpecialFiber (specialFiberι R toBase).ker.le_radical) b)) :=
  (toBase.componentMultidegreeHom_pullback hX hη
    (fun _ ↦ inclusion_subschemeToSpecialFiber _ _) b).symm

/-- `specialFiberMultidegree` factors through restriction from `X` to `X_s`. -/
theorem specialFiberMultidegree_eq_specialFiberMultidegreeOnFiber_pullback
    (a : LineBundleClass X) :
    toBase.specialFiberMultidegree hX hη (Additive.ofMul a) =
      toBase.specialFiberMultidegreeOnFiber hX hη
        (Additive.ofMul (pullback (specialFiberι R toBase) a)) :=
  (toBase.componentMultidegreeHom_pullback hX hη
    (fun _ ↦ subschemeToSpecialFiber_specialFiberι _) a).symm

/-- Pulling back a line-bundle class from `X` to `(X_s)_red` preserves its multidegree. -/
@[simp]
theorem reducedSpecialFiberMultidegree_pullback_subschemeι (a : LineBundleClass X) :
    toBase.reducedSpecialFiberMultidegree hX hη
        (Additive.ofMul (pullback (specialFiberι R toBase).ker.radical.subschemeι a)) =
      toBase.specialFiberMultidegree hX hη (Additive.ofMul a) :=
  toBase.componentMultidegreeHom_pullback hX hη
    (fun _ ↦ Scheme.IdealSheafData.inclusion_subschemeι _) a

/-- Multiplying the `i`-th coordinate of `specialFiberMultidegree a` by `w_i` recovers
`(a · C_i)_k` over the residue field. -/
theorem specialFiberMultidegree_mul_specialFiberWeight (a : Additive (LineBundleClass X)) (i) :
    toBase.specialFiberMultidegree hX hη a i *
        (toBase.specialFiberWeight ((mem_toFinset _).mp i.property) : ℤ) =
      letI := subschemeOverResidueField
        (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
            ((mem_toFinset _).mp i.property))
      intersectionNumber (ResidueField R)
        (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subschemeι a.toMul :=
  toBase.componentMultidegreeHom_mul_specialFiberWeight hX hη a i

/-- A line-bundle class on `X` has special-fibre multidegree zero if and only if its intersection
number with every component `C_i` vanishes. -/
theorem specialFiberMultidegree_eq_zero_iff (a : LineBundleClass X) :
    toBase.specialFiberMultidegree hX hη (Additive.ofMul a) = 0 ↔
      ∀ i : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        letI := subschemeOverResidueField
          (toBase.ker_specialFiberι_le_vanishingIdeal_closure_singleton
              ((mem_toFinset _).mp i.property))
        intersectionNumber (ResidueField R)
          (vanishingIdeal ⟨closure {(i.val : X)}, isClosed_closure⟩).subschemeι a = 0 :=
  toBase.componentMultidegreeHom_eq_zero_iff hX hη a

section RegularMatrix

variable [TauCeti.AlgebraicGeometry.IsRegular X]

/-- The weight `w_j` of `C_j` divides every entry `a_{ij}` in column `j` of the intersection
matrix. -/
theorem specialFiberWeight_dvd_specialFiberIntersectionMatrix_right (i j) :
    (toBase.specialFiberWeight ((mem_toFinset _).mp j.property) : ℤ) ∣
      toBase.specialFiberIntersectionMatrix hX hη i j := by
  rw [(toBase.specialFiberIntersectionMatrix_isSymm hX hη).apply j i]
  exact toBase.specialFiberWeight_dvd_specialFiberIntersectionMatrix hX hη j i

/-- Multiplying column `j` of `specialFiberWeightedIntersectionMatrix` by `w_j` recovers
`specialFiberIntersectionMatrix`. -/
theorem specialFiberWeightedIntersectionMatrix_mul_specialFiberWeight (i j) :
    toBase.specialFiberWeightedIntersectionMatrix hX hη i j *
        (toBase.specialFiberWeight ((mem_toFinset _).mp j.property) : ℤ) =
      toBase.specialFiberIntersectionMatrix hX hη i j :=
  Int.ediv_mul_cancel
    (toBase.specialFiberWeight_dvd_specialFiberIntersectionMatrix_right hX hη i j)

/-- **Multidegree of a component line bundle.** The multidegree of `[𝒪_X(C_i)]` is the `i`-th row
of `specialFiberWeightedIntersectionMatrix`. -/
theorem specialFiberMultidegree_inv_mk_toInvertibleSheaf (i) :
    toBase.specialFiberMultidegree hX hη (Additive.ofMul (LineBundleClass.mk
        (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
          i.val.property).toInvertibleSheaf)⁻¹) =
      toBase.specialFiberWeightedIntersectionMatrix hX hη i := funext fun j ↦ by
  rw [specialFiberMultidegree_apply, toMul_ofMul,
    ← toBase.specialFiberIntersectionMatrix_apply hX hη j i,
    (toBase.specialFiberIntersectionMatrix_isSymm hX hη).apply i j,
    specialFiberWeightedIntersectionMatrix_apply]

/-- Simp normal form of `specialFiberMultidegree_inv_mk_toInvertibleSheaf` after
`LineBundleClass.inv_mk`. -/
@[simp]
theorem specialFiberMultidegree_mk_toInvertibleSheaf_dual (i) :
    toBase.specialFiberMultidegree hX hη (Additive.ofMul (LineBundleClass.mk
        (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
          i.val.property).toInvertibleSheaf.dual)) =
      toBase.specialFiberWeightedIntersectionMatrix hX hη i := by
  rw [← LineBundleClass.inv_mk, specialFiberMultidegree_inv_mk_toInvertibleSheaf]

/-- **Multidegree of a vertical divisor class.** For any integer vector `v` on the special-fibre
components, the multidegree of `∏_i [𝒪_X(C_i)]^{v_i}` is `v ᵥ* A'`. -/
theorem specialFiberMultidegree_prod_zpow
    (v : (toBase.finite_setOf_base_eq_closedPoint
        (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) :
    toBase.specialFiberMultidegree hX hη (Additive.ofMul (∏ i, (LineBundleClass.mk
        (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
          i.val.property).toInvertibleSheaf)⁻¹ ^ v i)) =
      v ᵥ* toBase.specialFiberWeightedIntersectionMatrix hX hη := funext fun j ↦ by
  rw [ofMul_prod, map_sum, Finset.sum_apply, Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [ofMul_zpow, map_zsmul, Pi.smul_apply, smul_eq_mul,
    specialFiberMultidegree_inv_mk_toInvertibleSheaf]

end RegularMatrix

end Multidegree

/-! ### Generic-fibre Picard specialization and torsion lifting -/

section Specialization

variable {R : Type u} (K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R))
  [IsIntegral X] [IsNoetherian X] [TauCeti.AlgebraicGeometry.IsRegular X] [IsProper toBase]
  (hX : ∀ x : X, coheight x ≤ 2) (hη : toBase (genericPoint X) ≠ closedPoint R)

/-- Every model line-bundle class in the kernel of `Pic(X) → Pic(X_K)` has multidegree in the row
space of `specialFiberWeightedIntersectionMatrix`. -/
theorem specialFiberMultidegree_mem_range_of_pullback_genericFiberι_eq_one {a : LineBundleClass X}
    (ha : pullback (genericFiberι R K toBase) a = 1) :
    toBase.specialFiberMultidegree hX hη (Additive.ofMul a) ∈
      LinearMap.range (toBase.specialFiberWeightedIntersectionMatrix hX hη).vecMulLinear := by
  obtain ⟨v, rfl⟩ := (toBase.pullback_genericFiberι_eq_one_iff_of_isRegular K hX hη).mp ha
  exact ⟨v, (toBase.specialFiberMultidegree_prod_zpow hX hη v).symm⟩

omit [IsProper toBase] in
include hX in
/-- Surjectivity of the additive generic-fibre pullback homomorphism on `LineBundleClass`. -/
private lemma toAdditive_pullbackHom_genericFiberι_surjective :
    Function.Surjective (MonoidHom.toAdditive (pullbackHom (genericFiberι R K toBase))) :=
  fun b ↦ let ⟨a, ha⟩ := toBase.pullback_genericFiberι_surjective_of_isRegular K hX b.toMul
  ⟨Additive.ofMul a, Additive.toMul.injective (by
    rwa [MonoidHom.toAdditive_apply_apply, LineBundleClass.pullbackHom_apply, toMul_ofMul])⟩

/-- The **Picard specialization homomorphism**
([Stacks, Tag 0CEI](https://stacks.math.columbia.edu/tag/0CEI); Liu, Section 9.1) from `Pic(X_K)`
to the cokernel of the weighted intersection matrix `A'`, obtained by lifting a class on `X_K` to
the regular model `X` and taking its multidegree on `(X_s)_red` modulo vertical classes. -/
def specialFiberPicardSpecialization :
    Additive (LineBundleClass (genericFiber R K toBase).left) →+
      (((toBase.finite_setOf_base_eq_closedPoint
            (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset → ℤ) ⧸
        LinearMap.range (toBase.specialFiberWeightedIntersectionMatrix hX hη).vecMulLinear) := by
  let p := MonoidHom.toAdditive (pullbackHom (genericFiberι R K toBase))
  let S := LinearMap.range (toBase.specialFiberWeightedIntersectionMatrix hX hη).vecMulLinear
  let φ : Additive (LineBundleClass X) →+ _ ⧸ S :=
    S.mkQ.toAddMonoidHom.comp (toBase.specialFiberMultidegree hX hη)
  have hker : p.ker ≤ φ.ker := fun a ha ↦ by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← ofMul_toMul a]
    refine toBase.specialFiberMultidegree_mem_range_of_pullback_genericFiberι_eq_one
      K hX hη ?_
    simpa only [p, MonoidHom.toAdditive_apply_apply, LineBundleClass.pullbackHom_apply,
      toMul_ofMul, toMul_zero] using congrArg Additive.toMul (AddMonoidHom.mem_ker.mp ha)
  exact p.liftOfSurjective (toBase.toAdditive_pullbackHom_genericFiberι_surjective K hX) ⟨φ, hker⟩

/-- `specialFiberPicardSpecialization` sends the restriction of `a : LineBundleClass X` to the
quotient class of `specialFiberMultidegree a` (not `@[simp]` because `genericFiber` is an
`Over.pullback` abbreviation, so `simp` rewrites its scheme inside the domain of
`DFunLike.coe`). -/
theorem specialFiberPicardSpecialization_pullback (a : LineBundleClass X) :
    toBase.specialFiberPicardSpecialization K hX hη
        (Additive.ofMul (pullback (genericFiberι R K toBase) a)) =
      Submodule.Quotient.mk (toBase.specialFiberMultidegree hX hη (Additive.ofMul a)) := by
  let p := MonoidHom.toAdditive (pullbackHom (genericFiberι R K toBase))
  have hpa : Additive.ofMul (pullback (genericFiberι R K toBase) a) = p (Additive.ofMul a) :=
    Additive.toMul.injective (by simp [p])
  rw [specialFiberPicardSpecialization, hpa,
    AddMonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- **Exact kernel of `specialFiberPicardSpecialization`**
([Stacks, Tag 0CEI](https://stacks.math.columbia.edu/tag/0CEI); Liu, Section 9.1). A line-bundle
class `b` on `X_K` lies in `ker specialFiberPicardSpecialization` if and only if it extends to a
class `a` on the regular model `X` of multidegree zero on `(X_s)_red`. -/
theorem mem_ker_specialFiberPicardSpecialization_iff
    {b : LineBundleClass (genericFiber R K toBase).left} :
    Additive.ofMul b ∈ (toBase.specialFiberPicardSpecialization K hX hη).ker ↔
      ∃ a : LineBundleClass X,
        pullback (genericFiberι R K toBase) a = b ∧
          toBase.specialFiberMultidegree hX hη (Additive.ofMul a) = 0 := by
  refine ⟨fun hb ↦ ?_, fun ⟨a, haK, ha⟩ ↦ ?_⟩
  · obtain ⟨a₀, rfl⟩ := toBase.pullback_genericFiberι_surjective_of_isRegular K hX b
    rw [AddMonoidHom.mem_ker, specialFiberPicardSpecialization_pullback,
      Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hb
    obtain ⟨v, hv⟩ := hb
    let vert : LineBundleClass X := ∏ i, (LineBundleClass.mk
      (isEffectiveCartier_vanishingIdeal_closure_singleton_of_isRegular hX
        i.val.property).toInvertibleSheaf)⁻¹ ^ v i
    have hvert : pullback (genericFiberι R K toBase) vert = 1 :=
      (toBase.pullback_genericFiberι_eq_one_iff_of_isRegular K hX hη).mpr ⟨v, rfl⟩
    refine ⟨a₀ * vert⁻¹, by simp [hvert], ?_⟩
    rw [ofMul_mul, ofMul_inv, map_add, map_neg,
      toBase.specialFiberMultidegree_prod_zpow hX hη v,
      ← Matrix.vecMulLinear_apply, hv, add_neg_cancel]
  · rw [← haK, AddMonoidHom.mem_ker, specialFiberPicardSpecialization_pullback, ha,
      Submodule.Quotient.mk_zero]

section Connected

variable [Flat toBase] {π : R}

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
    rw [(toBase.specialFiberIntersectionMatrix_isSymm hX hη).apply i j,
      ← toBase.specialFiberWeightedIntersectionMatrix_mul_specialFiberWeight hX hη i j,
      mul_comm _ (v i), ← mul_assoc]
  have hmul : (toBase.specialFiberIntersectionMatrix hX hη).map (Int.cast : ℤ → ℚ) *ᵥ
      (fun j ↦ (v j : ℚ)) = 0 := funext fun j ↦ by
    simpa [hAv, Function.comp_def] using
      (RingHom.map_mulVec (Int.castRingHom ℚ)
        (toBase.specialFiberIntersectionMatrix hX hη) v j).symm
  exact (toBase.dotProduct_mulVec_specialFiberIntersectionMatrix_eq_zero_iff
    hX hη hπ hreg hconn (fun j ↦ (v j : ℚ))).mp (by rw [hmul, dotProduct_zero])

/-- **Isotropic vertical kernel on a connected special fibre.** On a regular proper flat model with
connected special fibre `X_s = ∑_i m_i C_i`, any model line-bundle class `a` that is trivial on
`X_K` and has multidegree zero on `(X_s)_red` satisfies `a ^ d = 1` for a positive integer `d`
dividing every component multiplicity `m_j`. -/
theorem exists_dvd_specialFiberMultiplicity_and_pow_eq_one
    (hπ : maximalIdeal R = Ideal.span {π})
    (hconn : _root_.IsPreconnected (toBase ⁻¹' {closedPoint R})) {a : LineBundleClass X}
    (haK : pullback (genericFiberι R K toBase) a = 1)
    (ha0 : toBase.specialFiberMultidegree hX hη (Additive.ofMul a) = 0) :
    ∃ d : ℕ, 0 < d ∧
      (∀ j : (toBase.finite_setOf_base_eq_closedPoint
          (toBase.maximalIdeal_ne_bot_of_base_ne_closedPoint hη) hη).toFinset,
        d ∣ toBase.specialFiberMultiplicity π j) ∧ a ^ d = 1 := by
  have hreg : IsSMulRegular R π :=
    IsSMulRegular.of_ne_zero (toBase.ne_zero_of_base_ne_closedPoint hη hπ)
  obtain ⟨v, rfl⟩ := (toBase.pullback_genericFiberι_eq_one_iff_of_isRegular K hX hη).mp haK
  rw [toBase.specialFiberMultidegree_prod_zpow hX hη v] at ha0
  obtain ⟨c, hc⟩ := toBase.exists_rat_mul_specialFiberMultiplicity_of_vecMul_eq_zero
    hX hη hπ hconn ha0
  have hrel (j) : v j * (c.den : ℤ) = c.num * (toBase.specialFiberMultiplicity π j : ℤ) :=
    Int.cast_injective (α := ℚ) <| by
      rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, hc j, mul_right_comm,
        Rat.mul_den_eq_num]
  refine ⟨c.den, c.den_pos, fun j ↦ ?_, ?_⟩
  · exact c.reduced.symm.dvd_of_dvd_mul_left (by
      simpa only [Int.natAbs_natCast, Int.natAbs_mul] using
        Int.natAbs_dvd_natAbs.mpr ⟨v j, (hrel j).symm.trans (mul_comm _ _)⟩)
  · have hsp := toBase.prod_inv_mk_toInvertibleSheaf_vanishingIdeal_pow_eq_one hX hη hπ hreg
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
    (ha0 : toBase.specialFiberMultidegree hX hη (Additive.ofMul a) = 0)
    (han : a ^ n = 1) : a = 1 := by
  obtain ⟨d, -, hdvd, had⟩ :=
    toBase.exists_dvd_specialFiberMultiplicity_and_pow_eq_one K hX hη hπ hconn haK ha0
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
    (hbker : Additive.ofMul b ∈ (toBase.specialFiberPicardSpecialization K hX hη).ker) :
    ∃! a : LineBundleClass X,
      pullback (genericFiberι R K toBase) a = b ∧
        toBase.specialFiberMultidegree hX hη (Additive.ofMul a) = 0 ∧ a ^ n = 1 := by
  obtain ⟨a₀, ha₀K, ha₀0⟩ :=
    (toBase.mem_ker_specialFiberPicardSpecialization_iff K hX hη).mp hbker
  obtain ⟨d, -, hdvd, hadn⟩ :=
    toBase.exists_dvd_specialFiberMultiplicity_and_pow_eq_one K hX hη hπ hconn
      (by rw [LineBundleClass.pullback_pow, ha₀K, hbn])
      (by rw [ofMul_pow, map_nsmul, ha₀0, smul_zero])
  have hnd : (d : ℤ) * Nat.gcdB n d = 1 - (n : ℤ) * Nat.gcdA n d := by
    have h := Nat.gcd_eq_gcd_ab n d; rw [(hcop d hdvd).gcd_eq_one, Nat.cast_one] at h; omega
  let a : LineBundleClass X := a₀ ^ ((d : ℤ) * Nat.gcdB n d)
  have haK : pullback (genericFiberι R K toBase) a = b := by
    rw [LineBundleClass.pullback_zpow, ha₀K, hnd, zpow_sub, zpow_one, zpow_mul, zpow_natCast,
      hbn, one_zpow, inv_one, mul_one]
  have ha0 : toBase.specialFiberMultidegree hX hη (Additive.ofMul a) = 0 := by
    rw [ofMul_zpow, map_zsmul, ha₀0, smul_zero]
  have han : a ^ n = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_right_comm, mul_comm (d : ℤ) (n : ℤ), zpow_mul, zpow_mul,
      zpow_natCast, zpow_natCast, hadn, one_zpow]
  refine ⟨a, ⟨haK, ha0, han⟩, fun a' ⟨ha'K, ha'0, ha'n⟩ ↦ eq_of_mul_inv_eq_one <|
    toBase.eq_one_of_pullback_genericFiberι_eq_one_of_coprime_specialFiberMultiplicity
      K hX hη hπ hconn hcop (by simp [ha'K, haK])
      (by rw [ofMul_mul, ofMul_inv, map_add, map_neg, ha'0, ha0, neg_zero, add_zero])
      (by rw [mul_pow, inv_pow, ha'n, han, inv_one, mul_one])⟩

end Connected

end Specialization

end AlgebraicGeometry.Scheme.Hom

end
